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

Definition VarId := nat.

Inductive VarKind := Input | Temp | Output.

Inductive Allocation := Unallocated | Register of PhysReg | Spill.

(* [VarInfo] abstracts information about the caller's notion of variables
   associated with an operation. *)
Record VarInfo := {
  varId       : VarId;          (* from 0 to highest var index *)
  varKind     : VarKind;
  varAlloc    : Allocation;
  regRequired : bool
}.

Definition VarList := (seq VarInfo).

Definition OpId := nat.

Inductive OpKind := Normal | LoopBegin | LoopEnd | Call.

(* The [OpInfo] structure is a collection of functions that allow us to
   determine information about each operation coming from the caller's
   side. *)
Record OpInfo := {
  opId    : OpId;
  opKind  : OpKind;
  varRefs : VarList;
  regRefs : seq PhysReg
}.

Definition OpList := (NonEmpty OpInfo).

Definition BlockId := nat.

Record BlockInfo := {
  blockId     : BlockId;
  blockOps    : NonEmpty OpInfo
}.

Definition BlockList := (NonEmpty BlockInfo).

Record BuildState := {
  bsVars    : seq (seq nat);
  bsNextPos : nat;
  bsLoopBeg : option nat;
  bsLoopEnd : option nat
}.

Definition buildIntervals (blocks : BlockList) : ScanStateSig :=
  (* Create a vector from variables to lists of use positions *)
  let bst :=
    foldl (fun bacc blk =>
      foldl (fun oacc op =>
        {| bsVars    :=
             foldl (fun vacc var =>
               apply_nth [::] vacc (varId var)
                         (fun xs => bsNextPos oacc :: xs))
               (bsVars oacc) (varRefs op)
         ; bsNextPos := (bsNextPos oacc).+2
         ; bsLoopBeg :=
             if (bsLoopBeg oacc, opKind op) is (None, LoopBegin)
             then Some (bsNextPos oacc)
             else bsLoopBeg oacc
         ; bsLoopEnd :=
             if (bsLoopEnd oacc, opKind op) is (None, LoopEnd)
             then Some (bsNextPos oacc)
             else bsLoopEnd oacc
         |}) bacc (blockOps blk))
      {| bsVars    := [::]
       ; bsNextPos := 1
       ; bsLoopBeg := None
       ; bsLoopEnd := None
       |} blocks in
  (* Walk through all the operations, adding an address to each vector *)
  undefined.

Definition boundedRange (pos : nat) :=
  { rd : RangeDesc | Range rd & pos <= NE_head (ups rd) }.

Definition boundedTriple (pos : nat) :=
  (option nat * option nat * option (boundedRange pos))%type.

Record boundedRangeVec (pos : nat) := {
  vars : seq (boundedTriple pos);
  regs : Vec (boundedTriple pos) maxReg
}.

Definition transportTriple {pos : nat} `(Hlt : pos < n)
  (x : boundedTriple n) : boundedTriple pos :=
  let: (o1, o2, mo) := x in match mo with
    | Some o => let: exist2 rd r H := o in
      (o1, o2, Some (exist2 Range _ rd r (ltnW (leq_trans Hlt H))))
    | None => (o1, o2, None)
    end.

Definition transportBounds (pos : nat) `(Hlt : pos < n) :
  seq (boundedTriple n) -> seq (boundedTriple pos) :=
  map (@transportTriple pos n Hlt).

Definition transportVecBounds (pos m : nat) `(Hlt : pos < n) :
  Vec (boundedTriple n) m -> Vec (boundedTriple pos) m :=
  vmap (@transportTriple pos n Hlt).

Definition boundedTransport (pos : nat) `(Hlt : pos < n)
  (xs : boundedRangeVec n) : boundedRangeVec pos :=
  {| vars := transportBounds    Hlt (vars xs)
   ; regs := transportVecBounds Hlt (regs xs)
   |}.

Definition boundedSing (upos : UsePos) (Hodd : odd upos) : boundedRange upos :=
  let r := R_Sing Hodd in exist2 Range _ r r (leqnn upos).

Definition boundedCons (upos : UsePos) (Hodd : odd upos)
  `(Hlt : upos < n) (xs : boundedRange n) : boundedRange upos :=
  let: exist2 rd r H := xs in
  let r' := R_Cons Hodd r (ltn_leq_trans Hlt H) in
  exist2 Range _ r' r' (leqnn upos).

Lemma withRanges (pos : nat) (Hodd : odd pos) (req : bool)
  (upos : UsePos) (Heqe : upos = Build_UsePos pos req)
  `(Hlt : upos < n) : boundedTriple n -> boundedTriple (uloc upos).
Proof.
  move=> [p [[rd r Hr]| ]]; last first.
    split. exact: p.
    apply/Some/boundedSing.
    by rewrite Heqe /=.
  split. exact: p.
  apply/Some/(@boundedCons upos).
  - by rewrite Heqe /=.
  - exact: n.
  - exact: Hlt.
  - by exists rd.
Defined.

Definition emptyBoundedRangeVec (n : nat) : boundedRangeVec n.+2 :=
  {| vars := nil
   ; regs := vconst (None, None, None)
   |}.

(* jww (2014-11-04): Still to be done:

   Register constraints at method calls are also modeled using fixed
   intervals: Because all registers are destroyed when the call is executed,
   ranges of length 1 are added to all fixed intervals at the call
   site. Therefore, the allocation pass cannot assign a register to any
   interval there, and all intervals are spilled before the call. *)

Definition handleOp (op : OpData) (rest : boundedRangeVec (opId op).+2) :
  boundedRangeVec (opId op) :=
  let pos := opId op in
  let Hodd := opIdOdd op in

  let liftOr f mx y :=
      Some (match mx with Some x => f x y | None => y end) in

  (** If the instruction at this position begins or ends a loop, extend the
      current range so that it starts at, or end at, this boundary. *)
  let savingBound x :=
      if (isLoopBegin (opInfo op) (baseOp op)) ||
         (isLoopEnd (opInfo op) (baseOp op))
      then let: (mb, me, r) := x in
           (liftOr minn mb pos, liftOr maxn me pos, r)
      else x in

  (** Add a new use position to the beginning of the current range. *)
  let consr (x : boundedTriple pos.+2) req : boundedTriple pos :=
      let upos := Build_UsePos pos req in
      @withRanges pos Hodd _ upos refl_equal pos.+2 (ltnSSn _) x in

  let restVars' := map savingBound (vars rest) in
  let restRegs' := vmap savingBound (regs rest) in
  let unchanged :=
      boundedTransport (ltnSSn _)
                       {| vars := restVars'; regs := restRegs' |} in

  let rest2 :=
      let k acc v :=
          let x := consr (nth (None, None, None) restVars' (varId v))
                         (regRequired v) in
          {| vars := set_nth (None, None, None) (vars acc) (varId v) x
           ; regs := regs acc
           |} in
      foldl k unchanged (varRefs (opInfo op) (baseOp op)) in

  let k acc r :=
      let x := consr (vnth restRegs' r) false in
      {| vars := vars acc
       ; regs := vreplace (regs acc) r x
       |} in
  foldl k rest2 (regRefs (opInfo op) (baseOp op)).

Definition extractRange {n} (x : boundedTriple n) : option RangeSig :=
  let: (mb, me, mr) := x in
  match mr with
  | None => None
  | Some (exist2 rd r _) =>
    let mres := match (mb, me) with
      | (None, None)     => None
      | (Some b, None)   => Some (b, rend rd)
      | (None, Some e)   => Some (rbeg rd, e)
      | (Some b, Some e) => Some (b, e)
      end in
    Some (match mres with
            | None        => packRange r
            | Some (b, e) => packRange (R_Extend b e r)
            end)
  end.

Definition applyList (opInfo : OpInfo) (op : opType) (ops : seq opType)
  (base : forall l, boundedRangeVec l.+2)
  (f : forall op : OpData,
         boundedRangeVec (opId op).+2 -> boundedRangeVec (opId op))
   : seq OpData * boundedRangeVec 1 :=
  let fix go i Hoddi x xs : seq OpData * boundedRangeVec i :=
      let newop := {| baseOp  := x
                    ; opInfo  := opInfo
                    ; opId    := i
                    ; opIdOdd := Hoddi
                    ; opAlloc := nil |} in
      match xs with
      | nil => ([:: newop], f newop (base i))
      | y :: ys =>
          let: (ops', next) := go i.+2 (odd_add_2 Hoddi) y ys in
          (newop :: ops', f newop next)
      end in
  go 1 odd_1 op ops.

(** The list of operations is processed in reverse, so that the resulting
    sub-lists are also in order. *)
Definition processOperations (opInfo : OpInfo) (ops : seq opType) :
  seq OpData * seq (option RangeSig) * Vec (option RangeSig) maxReg :=
  match ops with
  | nil => (nil, nil, vconst None)
  | x :: xs =>
      let: (ops', {| vars := vars'; regs := regs' |}) :=
           @applyList opInfo x xs emptyBoundedRangeVec handleOp in
      (ops', map extractRange vars', vmap extractRange regs')
  end.

(* jww (2014-11-19): Note that we are currently not computing the block order
   in any intelligent way. This is covered in quite some depth in Christian
   Wimmer's thesis.  At the moment we're simply accepting whatever block order
   is passed to us by the caller.  However, implementing this function
   properly is a strong means of improving the accuracy and efficiency of this
   algorithm. *)
Definition computeBlockOrder :
  IState SSError (seq blockType) (seq blockType) unit := return_ tt.

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations :
  IState SSError (seq blockType) (seq BlockData) unit :=
  imodify SSError blocksToBlockList.

Definition BlockState := IState SSError (seq BlockData) (seq BlockData).

(* jww (2014-12-01): The following two functions are used for computing
   accurate live ranges. they constitute a dataflow analysis which determines
   the true live range for variables referenced from loops.  At the moment
   these are being left unimplemented, but this is very likely something that
   will need to be done for the sake of the correctness of the algorithm. *)
Definition computeLocalLiveSets : BlockState unit := return_ tt.
Definition computeGlobalLiveSets : BlockState unit := return_ tt.

Definition buildIntervals (blocks : seq BlockData) : ScanStateSig :=
  let mkint (vid : nat)
            (ss : ScanStateSig)
            (mx : option RangeSig)
            (f : forall sd, ScanState sd -> forall d, Interval d
                   -> ScanStateSig) :=
      let: (exist sd st) := ss in match mx with
           | Some (exist _ r) => f _ st _ (I_Sing vid r)
           | None => ss
           end in

  let handleVar vid ss mx := mkint vid ss mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i) in

  let ops := flatten (map (blockToOpList binfo \o baseBlock) blocks) in
  let: (ops', varRanges, regRanges) := processOperations oinfo ops in
  let regs := vmap (fun mr =>
                      if mr is Some r
                      then Some (packInterval (I_Sing 0 r.2))
                      else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  (ops', foldl_with_index handleVar s2 varRanges).

Definition resolveDataFlow : BlockState unit := return_ tt.

Definition assignRegNum (ops : seq (OpData opType)) `(st : ScanState sd) :
  BlockState unit :=
  let ints := handled sd ++ active sd ++ inactive sd in
  let f op :=
      let o := baseOp op in
      let vars := varRefs (opInfo op) o in
      let k op' v :=
          let vid := varId v in
          let h acc x :=
              let: (xid, reg) := x in
              (* This strange use of a lambda is so that the generated code
                 evaluates [getInterval] only once, and shares the resulting
                 [int] at each use point; otherwise, if we use [let] or
                 [match], Coq's extractor inlines each use of [int], resulting
                 in no sharing of values. *)
              (fun int =>
                 if (ivar int == vid) &&
                    (ibeg int <= opId op < iend int)
                 then (vid, Register reg) :: acc
                 else acc) (getInterval xid) in
          {| baseOp  := o
           ; opInfo  := opInfo op'
           ; opId    := opId op'
           ; opIdOdd := opIdOdd op'
           ; opAlloc := foldl h nil ints ++ opAlloc op'
           |} in
      foldl k op vars in
  map f ops.

End Blocks.

Arguments computeBlockOrder {blockType}.
Arguments numberOperations {opType blockType} oinfo binfo.
Arguments computeLocalLiveSets {opType blockType}.
Arguments computeGlobalLiveSets {opType blockType}.
Arguments buildIntervals {opType blockType} oinfo binfo blocks.
Arguments resolveDataFlow {opType blockType}.
Arguments assignRegNum {opType} ops {sd} st.

End MBlocks.