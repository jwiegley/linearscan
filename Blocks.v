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

Variables accType    : Set.
Variables blockType1 : Set.
Variables blockType2 : Set.
Variables opType1    : Set.
Variables opType2    : Set.
Variables varType    : Set.

Inductive VarKind : Set := Input | Temp | Output.

Definition VarId := nat.

(* [VarInfo] abstracts information about the caller's notion of variables
   associated with an operation. *)
Record VarInfo (varType : Set) := {
  varId       : varType -> VarId;     (* from 0 to highest var index *)
  varKind     : varType -> VarKind;
  regRequired : varType -> bool
}.

Variable vinfo : VarInfo varType.

Inductive OpKind : Set :=
  IsNormal | IsCall | IsBranch | IsLoopBegin | IsLoopEnd.

(* The [OpInfo] structure is a collection of functions that allow us to
   determine information about each operation coming from the caller's
   side. *)
Record OpInfo (accType opType1 opType2 varType : Set) := {
  opKind      : opType1 -> OpKind;
  opRefs      : opType1 -> seq varType * seq PhysReg;
  saveOp      : VarId -> opType2;
  restoreOp   : VarId -> opType2;
  applyAllocs : opType1 -> accType -> seq (VarId * PhysReg)
                  -> accType * opType2
}.

Variable oinfo : OpInfo accType opType1 opType2 varType.

Definition BlockId := nat.

Record BlockInfo (blockType1 blockType2 opType1 opType2 : Set) := {
  blockId         : blockType1 -> BlockId;
  blockSuccessors : blockType1 -> seq BlockId;
  blockOps        : blockType1 -> seq opType1;
  setBlockOps     : blockType1 -> seq opType2 -> blockType2
}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.

Definition BlockList := seq blockType1.

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
  foldl (fun bacc blk => foldl f bacc (blockOps binfo blk)) z.

Definition countOps : BlockList -> nat := foldOps (fun acc _ => acc.+1) 0.

Definition foldOpsRev {a} (f : a -> opType1 -> a) (z : a)
  (blocks : BlockList) : a :=
  foldl (fun bacc blk => foldl f bacc (rev (blockOps binfo blk)))
        z (rev blocks).

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

Definition OpId := nat.

Record BlockLiveSets := {
  blockLiveGen   : seq VarId;
  blockLiveKill  : seq VarId;
  blockLiveIn    : seq VarId;
  blockLiveOut   : seq VarId;
  blockFirstOpId : OpId;
  blockLastOpId  : OpId
}.

Section IntMap.

Variable a : Type.

Inductive IntMap :=
  | emptyIntMap
  | getIntMap of seq (nat * a).

Definition IntMap_lookup (key : nat) (m : IntMap) : option a.
Admitted.

Definition IntMap_insert (key : nat) (value : a) (m : IntMap) : IntMap.
Admitted.

Definition IntMap_alter (f : option a -> option a) (key : nat) (m : IntMap) :
  IntMap.
Admitted.

End IntMap.

Definition union (a : eqType) (m1 m2 : seq a) : seq a := undup (m1 ++ m2).

Definition relative_complement (a : eqType) (m1 m2 : seq a) : seq a :=
  [seq i <- m1 | i \notin m2].

Arguments emptyIntMap [a].
Arguments getIntMap [a] _.

Definition forFold {A B : Type} (b : B) (v : seq A) (f : B -> A -> B) : B :=
  foldl f b v.

Definition computeLocalLiveSets (blocks : BlockList) : IntMap BlockLiveSets :=
  (* for each block b in blocks do
       b.live_gen  = { }
       b.live_kill = { }

       for each operation op in b.operations do
         visitor.visit(op)

         for each virtual register opr in visitor.input_oprs do
           if opr ∉ block.live_kill then
             b.live_gen = b.live_gen ∪ { opr }
         end for

         for each virtual register opr in visitor.temp_oprs do
           b.live_kill = b.live_kill ∪ { opr }
         end for

         for each virtual register opr in visitor.output_oprs do
           b.live_kill = b.live_kill ∪ { opr }
         end for
       end for
     end for *)
  @snd _ _ $
  forFold (1, emptyIntMap) blocks $ fun acc b => let: (idx, m) := acc in
    let liveSet :=
        {| blockLiveGen   := [::]
         ; blockLiveKill  := [::]
         ; blockLiveIn    := [::]
         ; blockLiveOut   := [::]
         ; blockFirstOpId := idx
         ; blockLastOpId  := idx
         |} in
    let: (lastIdx', liveSet3) :=
      forFold (idx, liveSet) (blockOps binfo b) $ fun acc o =>
        let: (lastIdx, liveSet1) := acc in
        (lastIdx.+2,
         forFold liveSet1 (fst (opRefs oinfo o)) $ fun liveSet2 v =>
           let vid := varId vinfo v in
           if varKind vinfo v is Input
           then
             if vid \notin blockLiveKill liveSet2
             then {| blockLiveGen   := vid :: blockLiveGen liveSet2
                   ; blockLiveKill  := blockLiveKill liveSet2
                   ; blockLiveIn    := blockLiveIn liveSet2
                   ; blockLiveOut   := blockLiveOut liveSet2
                   ; blockFirstOpId := blockFirstOpId liveSet2
                   ; blockLastOpId  := lastIdx
                   |}
             else liveSet2
           else
             {| blockLiveGen   := blockLiveGen liveSet2
              ; blockLiveKill  := vid :: blockLiveKill liveSet2
              ; blockLiveIn    := blockLiveIn liveSet2
              ; blockLiveOut   := blockLiveOut liveSet2
              ; blockFirstOpId := blockFirstOpId liveSet2
              ; blockLastOpId  := lastIdx
              |})
      in
    (lastIdx', IntMap_insert (blockId binfo b) liveSet3 m).

Definition computeGlobalLiveSets (blocks : BlockList)
  (liveSets : IntMap BlockLiveSets) : IntMap BlockLiveSets :=
  (* do
       for each block b in blocks in reverse order do
         b.live_out = { }
         for each successor sux of b do
           b.live_out = b.live_out ∪ sux.live_in
         end for

         b.live_in = (b.live_out – b.live_kill) ∪ b.live_gen
       end for
     while change occurred in any live set *)
  forFold liveSets (rev blocks) $ fun liveSets1 b =>
    let bid := blockId binfo b in
    match IntMap_lookup bid liveSets1 with
    | None => liveSets1         (* should never happen *)
    | Some liveSet =>
      let liveSet2 :=
        forFold liveSet (blockSuccessors binfo b) $ fun liveSet1 s_bid =>
          match IntMap_lookup s_bid liveSets1 with
          | None => liveSet1  (* should never happen *)
          | Some sux =>
            {| blockLiveGen   := blockLiveGen liveSet1
             ; blockLiveKill  := blockLiveKill liveSet1
             ; blockLiveIn    := blockLiveIn liveSet1
             ; blockLiveOut   := union (blockLiveOut liveSet1)
                                       (blockLiveIn sux)
             ; blockFirstOpId := blockFirstOpId liveSet1
             ; blockLastOpId  := blockLastOpId liveSet1
             |}
          end
        in
      IntMap_insert bid
        {| blockLiveGen   := blockLiveGen liveSet2
         ; blockLiveKill  := blockLiveKill liveSet2
         ; blockLiveIn    :=
             union (relative_complement (blockLiveOut liveSet2)
                                        (blockLiveKill liveSet2))
                   (blockLiveGen liveSet2)
         ; blockLiveOut   := blockLiveOut liveSet2
         ; blockFirstOpId := blockFirstOpId liveSet2
         ; blockLastOpId  := blockLastOpId liveSet2
         |} liveSets1
    end.

Definition buildIntervals : BlockState (ScanStateSig InUse) :=
  (* jww (2015-01-27): NYI: Still need to insert length-1 fixed intervals at
     call points. *)
  let mkint (vid : VarId)
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

Inductive InsertPos : Set := AtBegin of VarId | AtEnd of VarId.

Section EqInsertPos.

Definition eqact v1 v2 :=
  match v1, v2 with
  | AtBegin r1, AtBegin r2 => r1 == r2
  | AtEnd r1,   AtEnd r2   => r1 == r2
  | _, _ => false
  end.

Lemma eqactP : Equality.axiom eqact.
Proof.
  move.
  case=> [r1|r1];
  case=> [r2|r2];
  case: (r1 =P r2) => [<-|/eqP /negbTE neqx] //=;
    do [ rewrite eq_refl;
         by constructor
       | rewrite neqx;
         constructor;
         move/eqP in neqx;
         move=> H;
         contradiction neqx;
         congruence
       | constructor;
         discriminate
       | idtac ].
Qed.

Canonical act_eqMixin := EqMixin eqactP.
Canonical act_eqType := Eval hnf in EqType InsertPos act_eqMixin.

Lemma eqactE : eqact = eq_op. Proof. by []. Qed.

Definition InsertPos_eqType (A : eqType) :=
  Equality.Pack act_eqMixin InsertPos.

End EqInsertPos.

Definition resolveDataFlow `(st : ScanState InUse sd)
  (blocks : BlockList) (liveSets : IntMap BlockLiveSets) :
  IntMap (seq InsertPos) :=
  (* for each block from in blocks do
       for each successor to of from do
         // collect all resolving moves necessary between the blocks from
         // and to
         for each operand opr in to.live_in do
           Interval parent_interval = intervals[opr]

           Interval from_interval = parent_interval.child_at(from.last_op.id)
           Interval to_interval = parent_interval.child_at(to.first_op.id)

           if from_interval ≠ to_interval then
             // interval was split at the edge between the blocks from and to
             resolver.add_mapping(from_interval, to_interval)
           end if
         end for

         // the moves are inserted either at the end of block from or at the
         // beginning of block to, depending on the control flow
         resolver.find_insert_position(from, to)

         // insert all moves in correct order (without overwriting registers
         // that are used later)
         resolver.resolve_mappings()
       end for
     end for *)
  forFold emptyIntMap blocks $ fun mappings b =>
    let bid := blockId binfo b in
    match IntMap_lookup bid liveSets with
    | None => mappings
    | Some from =>
      (fun successors =>
        forFold mappings successors $ fun ms s_bid =>
          match IntMap_lookup s_bid liveSets with
          | None => ms
          | Some to =>
            forFold ms (blockLiveIn to) $ fun ms' vid =>
              if lookupInterval st vid (blockLastOpId from)
                 is Some from_interval
              then
                if lookupInterval st vid (blockFirstOpId to)
                   is Some to_interval
                then
                  if from_interval != to_interval
                  then
                    let in_from := size successors <= 1 in
                    let ins     := if in_from
                                   then AtEnd vid
                                   else AtBegin vid in
                    let f mxs   := if mxs is Some xs
                                   then if ins \notin xs
                                        then Some (ins :: xs)
                                        else Some xs
                                   else Some [:: ins] in
                    let key     := if in_from
                                   then bid
                                   else s_bid in
                    IntMap_alter f key ms'
                  else ms'    (* should be impossible *)
                else ms'      (* should be impossible *)
              else ms'        (* should be impossible *)
          end)
      (blockSuccessors binfo b)
    end.

Section Allocation.

Record AssnStateInfo := {
  assnOpId : OpId;
  assnAcc  : accType
}.

Definition AssnState :=
  IState SSError AssnStateInfo AssnStateInfo.

Definition savesAndRestores (opid : OpId) (vid : VarId)
  (int : IntervalDesc) : (seq opType2 * seq opType2) :=
  let isFirst := firstUsePos int == opid in
  let isLast  := nextUseAfter int opid == None in
  let save := [:: saveOp oinfo vid] in
  let restore := [:: restoreOp oinfo vid] in
  match iknd int, isFirst, isLast with
  | Middle,    true,  true  => (restore, save)
  | Middle,    false, true  => ([::], save)
  | Middle,    true,  false => (restore, [::])
  | LeftMost,  _,     true  => ([::], save)
  | RightMost, true,  _     => (restore, [::])
  | _,         _,     _     => ([::], [::])
  end.

Definition doAllocations (ints : seq (IntervalDesc * PhysReg))
  (op : opType1) : AssnState (seq opType2) :=
  assn <<- iget SSError ;;
  let opid := assnOpId assn in
  let vars := fst (opRefs oinfo op) in
  let: (allocs, restores, saves) :=
    forFold ([::], [::], [::]) vars $ fun acc v =>
      let vid := varId vinfo v in
      let v_ints :=
          [seq x <- ints | isWithin (fst x) vid (assnOpId assn)] in
      forFold acc v_ints $ fun acc' ir =>
        let: (int, reg) := ir in
        let: (allocs', restores', saves') := acc' in
        let: (ss, rs) := savesAndRestores opid vid int in
        ((vid, reg) :: allocs', rs ++ restores', ss ++ saves') in
  let: (acc', op') := applyAllocs oinfo op (assnAcc assn) allocs in
  (* With lenses, this would just be: assnOpId += 2 *)
  iput SSError {| assnOpId := (assnOpId assn).+2
                ; assnAcc  := acc' |} ;;;
  return_ $ restores ++ op' :: saves.

Definition considerOps (f : opType1 -> AssnState (seq opType2))
  (mappings : IntMap (seq InsertPos)) :=
  mapM $ fun blk =>
    (* First apply all allocations *)
    let ops := blockOps binfo blk in
    ops' <<- concatMapM f ops ;;
    (* Insert resolving moves based on the mappings *)
    let bid := blockId binfo blk in
    let ops'' :=
        if IntMap_lookup bid mappings is Some inss
        then forFold ops' inss $ fun ops'' ins =>
          (* jww (2015-01-27): NYI: When multiple moves must be inserted at
             one edge, then the order of the moves is important because the
             same register can occur as the source of one move and the
             destination of another move. The moves must be ordered such that
             a register is saved first before it is overwritten. *)
          match ins with
          | AtBegin vid => restoreOp oinfo vid :: ops''
          | AtEnd   vid =>
            (fun sop =>
              if ops is o :: os
              then
                if ops'' is o'' :: os''
                then
                  if opKind oinfo (last o os) is IsBranch
                  then belast o'' os'' ++ [:: sop; last o'' os'']
                  else ops' ++ [:: sop]
                else [:: sop]
              else [:: sop])
            (saveOp oinfo vid)
          end
        else ops' in
    return_ $ setBlockOps binfo blk ops''.

Definition assignRegNum `(st : ScanState InUse sd)
  (mappings : IntMap (seq InsertPos)) (acc : accType) :
  IState SSError (seq blockType1) (seq blockType2) accType :=
  let ints :=
      map (fun x => (getIntervalDesc (getInterval (fst x)), snd x))
          (handled sd ++ active sd ++ inactive sd) in
  blocks <<- iget SSError ;;
  match (considerOps (doAllocations ints) mappings blocks)
        {| assnOpId := 1
         ; assnAcc := acc |} with
  | inl err => ierr SSError err
  | inr (blocks', assn) =>
      iput SSError blocks' ;;;
      return_ $ assnAcc assn
  end.

End Allocation.

End Blocks.

End MBlocks.