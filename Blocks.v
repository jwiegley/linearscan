Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.Range.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MBlocks (Mach : Machine).

Include MScanState Mach.

Section Blocks.

Open Scope program_scope.

Variables blockType1 : Set.
Variables blockType2 : Set.
Variables opType1    : Set.
Variables opType2    : Set.
Variables varType    : Set.

(* The simplest way to get information about the IR instructions from the
   caller is to receive the following data:

   NonEmpty (BlockId * NonEmpty (OpId * NonEmpty vars))

   We receive an ordered list of blocks identified by an number pickedq by the
   caller.  Each block is associated with a sequence of operations (the caller
   should not inform us of empty blocks), and each operation relates to a
   nonempty set of variables (the caller should not inform us of instructions
   without variables).

   In addition to this basic information, a set of functions associated with
   blocks and operations is necessary in order to determine extra details
   about those structures, such as the block IDs of all successors of a
   specific block.  These are the [BlockInfo] and [OpInfo] records,
   respectively.
*)

Inductive VarKind := Input | Temp | Output.

(* When use of a variable is encountered, one or more actions should be taken: *)
Inductive VarAction := Spill | Restore | RestoreAndSpill.

(* [VarInfo] abstracts information about the caller's notion of variables
   associated with an operation. *)
Record VarInfo (varType : Set) := {
  varId       : varType -> nat;     (* from 0 to highest var index *)
  varKind     : varType -> VarKind;
  regRequired : varType -> bool
}.

Variable vinfo : VarInfo varType.

Inductive OpKind := Normal | LoopBegin | LoopEnd | Call.

Record AllocInfo := {
  allocReg    : PhysReg;
  allocAction : option VarAction
}.

(* The [OpInfo] structure is a collection of functions that allow us to
   determine information about each operation coming from the caller's
   side. *)
Record OpInfo (opType1 opType2 varType : Set) := {
  opKind      : opType1 -> OpKind;
  opRefs      : opType1 -> seq varType * seq PhysReg;
  applyAllocs : opType1 -> seq (nat * AllocInfo) -> opType2
}.

Variable oinfo : OpInfo opType1 opType2 varType.

Record BlockInfo (blockType1 blockType2 opType1 opType2 : Set) := {
  blockOps    : blockType1 -> seq opType1;
  setBlockOps : blockType1 -> seq opType2 -> blockType2
}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.

Definition BlockList := NonEmpty blockType1.

Definition BoundedRange (pos : nat) :=
  { r : RangeSig | pos <= NE_head (ups r.1) }.

Definition transportBoundedRange {base : nat} `(Hlt : base < prev)
  (x : BoundedRange prev) : BoundedRange base.
  case: x => [r H].
  apply: exist.
  apply: r.
  exact/(leq_trans _ H)/ltnW.
Defined.

(* jww (2015-01-12): Some of the things described by Wimmer in the section on
   dealing with computing of intervals have yet to be done:

   - Loop handling (reordering blocks to optimize allocation)
   - Extending of ranges for input/output variables
   - Purging registers at call sites
   - Exception handling optimization
*)

Record BuildState := {
  bsPos  : nat;
  bsVars : seq (option (BoundedRange bsPos.*2.+1));
  bsRegs : Vec (option (BoundedRange bsPos.*2.+1)) maxReg
}.

Definition foldOps {a} (f : a -> opType1 -> a) (z : a) :
  BlockList -> a :=
  NE_foldl (fun bacc blk => foldl f bacc (blockOps binfo blk)) z.

Definition foldOpsRev {a} (f : a -> opType1 -> a) (z : a)
  (blocks : BlockList) : a :=
  foldl (fun bacc blk => foldl f bacc (rev (blockOps binfo blk)))
        z (rev blocks).

Definition countOps : BlockList -> nat :=
  foldOps (fun acc _ => acc.+1) 0.

Definition mapAccumLOps {a} (f : a -> opType1 -> (a * opType2)) :
  a -> BlockList -> a * NonEmpty blockType2 :=
  NE_mapAccumL (fun z blk =>
    let: (z', ops) := mapAccumL f z (blockOps binfo blk) in
    (z', setBlockOps binfo blk ops)).

Definition processOperations (blocks : BlockList) : BuildState.
  have := foldOps (fun x op => let: (n, m) := x in
    (n.+1, foldl (fun m v => maxn m (varId vinfo v))
                 m (fst (opRefs oinfo op))))
    (0, 0) blocks.
  move=> [opCount highestVar].
  pose z := {| bsPos  := opCount
             ; bsVars := nseq highestVar.+1 None
             ; bsRegs := vconst None |}.
  apply: (foldOpsRev _ z blocks).
  case=> [pos vars regs] op.
  have H: forall n, n.*2.+1 < (n.+1).*2.+1
    by move=> n; rewrite doubleS.
  case: pos => [|pos] in vars regs *.
    exact {| bsPos  := 0
           ; bsVars := vars
           ; bsRegs := regs |}.
  move: (opRefs oinfo op) => [varRefs regRefs].
  apply: {| bsPos  := pos
          ; bsVars := _
          ; bsRegs := _ |}.
  - have: seq (option (BoundedRange pos.*2.+1)).
      have vars' := vars.
      move/(map (option_map (transportBoundedRange (H pos)))) in vars'.
      apply: foldl _ vars' varRefs => vars' v.
      set upos := {| uloc   := pos.*2.+1
                   ; regReq := regRequired vinfo v |}.
      have Hodd : odd upos by rewrite /= odd_double.
      apply: (set_nth None vars' (varId vinfo v) _).
      apply: Some _.
      case: (nth None vars (varId vinfo v)) => [[r /= Hlt]|].
      + apply: exist _ (exist _ _ (R_Cons Hodd r.2 _)) _ => //=.
        rewrite doubleS in Hlt.
        exact/ltnW.
      + by exists (exist _ _ (R_Sing Hodd)) => //.
    exact.
  - have: Vec (option (BoundedRange pos.*2.+1)) maxReg.
      have regs' := regs.
      move/(vmap (option_map (transportBoundedRange (H pos)))) in regs'.
      apply: foldl _ regs' regRefs => regs' reg.
      set upos := {| uloc   := pos.*2.+1
                   ; regReq := true |}.
      have Hodd : odd upos by rewrite /= odd_double.
      apply: (vreplace regs' reg _).
      apply: Some _.
      case: (vnth regs reg) => [[r /= Hlt]|].
      + apply: exist _ (exist _ _ (R_Cons Hodd r.2 _)) _ => //=.
        rewrite doubleS in Hlt.
        exact/ltnW.
      + by exists (exist _ _ (R_Sing Hodd)) => //.
    exact.
Defined.

Definition BlockState := IState SSError BlockList BlockList.

(* jww (2014-11-19): Note that we are currently not computing the block order
   in any intelligent way. This is covered in quite some depth in Christian
   Wimmer's thesis.  At the moment we're simply accepting whatever block order
   is passed to us by the caller.  However, implementing this function
   properly is a strong means of improving the accuracy and efficiency of this
   algorithm. *)
Definition computeBlockOrder : BlockState unit := return_ tt.

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations : BlockState unit := return_ tt.
  (* let f n op := *)
  (*   (n.+2, {| opId    := n *)
  (*           ; opMeta  := opMeta op *)
  (*           ; opKind  := opKind op *)
  (*           ; varRefs := varRefs op *)
  (*           ; regRefs := regRefs op |}) in *)
  (* imodify SSError (@snd _ _ \o mapAccumLOps f 1). *)

(* jww (2014-12-01): The following two functions are used for computing
   accurate live ranges. they constitute a dataflow analysis which determines
   the true live range for variables referenced from loops.  At the moment
   these are being left unimplemented, but this is very likely something that
   will need to be done for the sake of the correctness of the algorithm. *)
Definition computeLocalLiveSets : BlockState unit := return_ tt.

Definition computeGlobalLiveSets : BlockState unit := return_ tt.

Definition buildIntervals : BlockState (ScanStateSig InUse) :=
  let mkint (vid : nat)
            (ss : ScanStateSig Pending)
            (pos : nat)
            (mx : option (BoundedRange pos.*2.+1))
            (f : forall sd, ScanState Pending sd -> forall d, Interval d
                   -> ScanStateSig Pending) :=
      let: exist _ st := ss in
      if mx is Some (exist r _)
      then f _ st _ (I_Sing vid Whole r.2)
           (* jww (2015-01-20): At the present time there is no use of
              "lifetime holes", and so [I_Cons] is never used here. *)
      else ss in

  let handleVar pos vid ss mx :=
      mkint vid ss pos mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i I) in

  blocks <<- iget SSError ;;
  (fun bs =>
     let regs := vmap (fun mr =>
           if mr is Some (exist r _)
           then Some (packInterval (I_Sing 0 Whole r.2))
           else None) (bsRegs bs) in

     let s0 := ScanState_nil in
     let s1 := ScanState_setFixedIntervals s0 regs in
     let s2 := packScanState s1 in
     let s3 := foldl_with_index (handleVar (bsPos bs)) s2 (bsVars bs) in
     let s4 := ScanState_finalize s3.2 in
     let s5 := packScanState s4 in
     return_ s5)
  (processOperations blocks).

Definition resolveDataFlow : BlockState unit := return_ tt.

(* Definition mapOps (f : opType -> opType) : BlockList -> BlockList := *)
(*   NE_map (fun blk => setBlockOps binfo blk (map f (blockOps binfo blk))). *)

Definition assignRegNum `(st : ScanState InUse sd) :
  BlockState (NonEmpty blockType2) :=
  let ints := handled sd ++ active sd ++ inactive sd in
  let f n op :=
    let k v :=
      let h acc x :=
        let: (xid, reg) := x in
        (* This strange use of a lambda is so that the generated code
           evaluates [getInterval] only once, and shares the resulting [int]
           at each use point; otherwise, if we use [let] or [match], Coq's
           extractor inlines each use of [int], resulting in no sharing of
           values. *)
        (fun vid int =>
           if (ivar int == vid) &&
              (ibeg int <= n < iend int)
           then let isFirst := firstUsePos int == n in
                let isLast  := nextUseAfter int n == None in
             (vid,
              {| allocReg    := reg
               ; allocAction :=
                   match iknd int, isFirst, isLast with
                   | Middle,    true,  true  => Some RestoreAndSpill
                   | Middle,    false, true  => Some Spill
                   | Middle,    true,  false => Some Restore
                   | LeftMost,  _,     true  => Some Spill
                   | RightMost, true,  _     => Some Restore
                   | _,         _,     _     => None
                   end
               |}) :: acc
           else acc)
        (varId vinfo v) (getInterval xid) in
      foldl h [::] ints in
    let vars := flatten (map k (fst (opRefs oinfo op))) in
    (n.+2, applyAllocs oinfo op vars) in
  blocks <<- iget SSError ;;
  return_ (snd (mapAccumLOps f 1 blocks)).

End Blocks.

End MBlocks.