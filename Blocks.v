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
  moveOp      : PhysReg -> PhysReg -> accType -> opType2 * accType;
  (* swapOp      : PhysReg -> PhysReg -> accType -> opType2 * accType; *)
  saveOp      : VarId   -> PhysReg -> accType -> opType2 * accType;
  restoreOp   : VarId   -> PhysReg -> accType -> opType2 * accType;
  applyAllocs : opType1 -> seq (VarId * PhysReg) -> opType2
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
  seq blockType1 -> a :=
  foldl (fun bacc blk => foldl f bacc (blockOps binfo blk)) z.

Definition countOps : seq blockType1 -> nat := foldOps (fun acc _ => acc.+1) 0.

Definition foldOpsRev {a} (f : a -> opType1 -> a) (z : a)
  (blocks : seq blockType1) : a :=
  foldl (fun bacc blk => foldl f bacc (rev (blockOps binfo blk)))
        z (rev blocks).

Definition processOperations (blocks : seq blockType1) : BuildState.
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

(* jww (2014-11-19): Note that we are currently not computing the block order
   in any intelligent way. This is covered in quite some depth in Christian
   Wimmer's thesis.  At the moment we're simply accepting whatever block order
   is passed to us by the caller.  However, implementing this function
   properly is a strong means of improving the accuracy and efficiency of this
   algorithm. *)
Definition computeBlockOrder (blocks : seq blockType1) : seq blockType1 :=
  blocks.

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations (blocks : seq blockType1) : seq blockType1 :=
  blocks.
  (* let f n op := *)
  (*   (n.+2, {| opId    := n *)
  (*           ; opMeta  := opMeta op *)
  (*           ; opKind  := opKind op *)
  (*           ; varRefs := varRefs op *)
  (*           ; regRefs := regRefs op |}) in *)
  (* imodify SSError (@snd _ _ \o mapAccumLOps f 1). *)

Inductive IntMap (a : Type) :=
  | emptyIntMap
  | getIntMap of seq (nat * a).

Arguments emptyIntMap [a].
Arguments getIntMap [a] _.

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntMap_lookup : forall a, nat -> IntMap a -> option a :=
  fun _ _ _ => None.
Definition IntMap_insert : forall a, nat -> a -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.
Definition IntMap_alter : forall a,
  (option a -> option a) -> nat -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.

Definition IntMap_toList {a} (m : IntMap a) : seq (nat * a) :=
  match m with
    | emptyIntMap => nil
    | getIntMap xs => xs
  end.

Definition prepend (a : eqType) (x : a) mxs :=
  if mxs is Some xs
  then if x \notin xs
       then Some (x :: xs)
       else Some xs
  else Some [:: x].

Inductive IntSet :=
  | emptyIntSet
  | getIntSet of seq nat.

Arguments emptyIntSet.
Arguments getIntSet _.

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntSet_member     : nat -> IntSet -> bool      := fun _ _ => false.
Definition IntSet_insert     : nat -> IntSet -> IntSet    := fun _ x => x.
Definition IntSet_union      : IntSet -> IntSet -> IntSet := fun _ x => x.
Definition IntSet_difference : IntSet -> IntSet -> IntSet := fun _ x => x.

Definition IntSet_foldl : forall a, (a -> nat -> a) -> a -> IntSet -> a :=
  fun _ _ z _ => z.

Definition IntSet_forFold {a} (z : a) (m : IntSet) (f: a -> nat -> a) : a :=
  IntSet_foldl f z m.

Definition OpId := nat.

Record BlockLiveSets := {
  blockLiveGen   : IntSet;
  blockLiveKill  : IntSet;
  blockLiveIn    : IntSet;
  blockLiveOut   : IntSet;
  blockFirstOpId : OpId;
  blockLastOpId  : OpId
}.

Definition computeLocalLiveSets (blocks : seq blockType1) :
  IntMap BlockLiveSets :=
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
  forFold (1, emptyIntMap) blocks $ fun acc b =>
    let: (idx, m) := acc in
    let liveSet :=
        {| blockLiveGen   := emptyIntSet
         ; blockLiveKill  := emptyIntSet
         ; blockLiveIn    := emptyIntSet
         ; blockLiveOut   := emptyIntSet
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
             if ~~ (IntSet_member vid (blockLiveKill liveSet2))
             then {| blockLiveGen   := IntSet_insert vid (blockLiveGen liveSet2)
                   ; blockLiveKill  := blockLiveKill liveSet2
                   ; blockLiveIn    := blockLiveIn liveSet2
                   ; blockLiveOut   := blockLiveOut liveSet2
                   ; blockFirstOpId := blockFirstOpId liveSet2
                   ; blockLastOpId  := lastIdx
                   |}
             else liveSet2
           else
             {| blockLiveGen   := blockLiveGen liveSet2
              ; blockLiveKill  := IntSet_insert vid (blockLiveKill liveSet2)
              ; blockLiveIn    := blockLiveIn liveSet2
              ; blockLiveOut   := blockLiveOut liveSet2
              ; blockFirstOpId := blockFirstOpId liveSet2
              ; blockLastOpId  := lastIdx
              |})
      in
    (lastIdx', IntMap_insert (blockId binfo b) liveSet3 m).

Definition computeGlobalLiveSets (blocks : seq blockType1)
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
             ; blockLiveOut   := IntSet_union (blockLiveOut liveSet1)
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
             IntSet_union (IntSet_difference (blockLiveOut liveSet2)
                                             (blockLiveKill liveSet2))
                          (blockLiveGen liveSet2)
         ; blockLiveOut   := blockLiveOut liveSet2
         ; blockFirstOpId := blockFirstOpId liveSet2
         ; blockLastOpId  := blockLastOpId liveSet2
         |} liveSets1
    end.

Definition buildIntervals (blocks : seq blockType1) : ScanStateSig InUse :=
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
     packScanState s4)
  (processOperations blocks).

Inductive InsertPos : Set := AtBegin | AtEnd.

Inductive MoveAction : Type :=
  | MoveOp of PhysReg & PhysReg
  | SaveOp of PhysReg
  | RestoreOp of PhysReg.

Record Move := {
  movePos    : InsertPos;
  moveVarId  : VarId;
  moveAction : MoveAction
}.

Section EqMove.

Definition eqipos v1 v2 :=
  match v1, v2 with
  | AtBegin, AtBegin => true
  | AtEnd,   AtEnd   => true
  | _, _ => false
  end.

Lemma eqiposP : Equality.axiom eqipos.
Proof. move; case; case => /=; constructor => //. Qed.

Canonical ipos_eqMixin := EqMixin eqiposP.
Canonical ipos_eqType := Eval hnf in EqType InsertPos ipos_eqMixin.

Lemma eqiposE : eqipos = eq_op. Proof. by []. Qed.

Definition InsertPos_eqType (A : eqType) :=
  Equality.Pack ipos_eqMixin InsertPos.

Definition eqmoveAct m1 m2 :=
  match m1, m2 with
  | MoveOp s1 d1, MoveOp s2 d2 => (s1 == s2) && (d1 == d2)
  | SaveOp r1,    SaveOp r2    => r1 == r2
  | RestoreOp r1, RestoreOp r2 => r1 == r2
  | _, _ => false
  end.

Lemma eqmoveActP : Equality.axiom eqmoveAct.
Proof.
  move.
  case=> [s1 d1|r1|r1];
  case=> [s2 d2|r2|r2];
  rewrite /eqmoveAct /=;
  do ?[ case: (s1 =P s2) => [<- /=|/eqP /negbTE /eqP neqx_s] /=
      | case: (d1 =P d2) => [<- /=|/eqP /negbTE /eqP neqx_d] /=
      | case: (r1 =P r2) => [<- /=|/eqP /negbTE /eqP neqx_r] /= ];
  constructor => //;
  move=> H;
  do [ contradiction neqx_s
     | contradiction neqx_d
     | contradiction neqx_r ];
  inversion H; auto.
Qed.

Canonical moveAct_eqMixin := EqMixin eqmoveActP.
Canonical moveAct_eqType := Eval hnf in EqType MoveAction moveAct_eqMixin.

Lemma eqmoveActE : eqmoveAct = eq_op. Proof. by []. Qed.

Definition MoveAction_eqType (A : eqType) :=
  Equality.Pack moveAct_eqMixin MoveAction.

Definition eqmove m1 m2 :=
  (movePos    m1 == movePos    m2) &&
  (moveVarId  m1 == moveVarId  m2) &&
  (moveAction m1 == moveAction m2).

Lemma eqmoveP : Equality.axiom eqmove.
Proof.
  move.
  case=> [p1 v1 m1];
  case=> [p2 v2 m2];
  rewrite /eqmove /=;
  case: (p1 =P p2) => [<- /=|/eqP /negbTE /eqP neqx_p];
  case: (v1 =P v2) => [<- /=|/eqP /negbTE /eqP neqx_v];
  case: (m1 =P m2) => [<- /=|/eqP /negbTE /eqP neqx_m];
  constructor => //;
  move=> H;
  do [ contradiction neqx_p
     | contradiction neqx_v
     | contradiction neqx_m ];
  inversion H; auto.
Qed.

Canonical move_eqMixin := EqMixin eqmoveP.
Canonical move_eqType := Eval hnf in EqType Move move_eqMixin.

Lemma eqmoveE : eqmove = eq_op. Proof. by []. Qed.

Definition Move_eqType (A : eqType) :=
  Equality.Pack move_eqMixin Move.

End EqMove.

Definition checkIntervalBoundary `(st : ScanState InUse sd)
  key in_from from to mappings vid :=

  let mfrom_int := lookupInterval st vid (blockLastOpId from) in
  if mfrom_int isn't Some from_interval then mappings else
    (* jww (2015-01-28): the failing case should be provably impossible *)

  let mto_int := lookupInterval st vid (blockFirstOpId to) in
  if mto_int isn't Some to_interval then mappings else
    (* jww (2015-01-28): the failing case should be provably impossible *)

  (* If the interval match, no move resolution is necessary. *)
  if from_interval == to_interval then mappings else

  let msreg := lookupRegister st from_interval in
  let mdreg := lookupRegister st to_interval in

  let maction := match msreg, mdreg with
        (* jww (2015-01-28): should be impossible *)
      | None,      None      => None
      | Some sreg, None      => Some (SaveOp sreg)
      | None,      Some dreg => Some (RestoreOp dreg)
      | Some sreg, Some dreg => Some (MoveOp sreg dreg)
      end in

  if maction isn't Some action then mappings else

  let mv :=
      {| movePos    := if in_from then AtEnd else AtBegin
       ; moveVarId  := vid
       ; moveAction := action
       |} in

  IntMap_alter (prepend mv) key mappings.

Definition resolveDataFlow `(st : ScanState InUse sd)
  (blocks : seq blockType1) (liveSets : IntMap BlockLiveSets) :
  IntMap (seq Move) :=
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
    | None => mappings          (* jww (2015-01-28): should be impossible *)
    | Some from =>
      (fun successors =>
        let in_from := size successors <= 1 in
        forFold mappings successors $ fun ms s_bid =>
          match IntMap_lookup s_bid liveSets with
          | None => ms          (* jww (2015-01-28): should be impossible *)
          | Some to =>
              let key := if in_from then bid else s_bid in
              IntSet_forFold ms (blockLiveIn to) $
                checkIntervalBoundary st key in_from from to
          end)
      (blockSuccessors binfo b)
    end.

Section Allocation.

Require Import LinearScan.State.

Record AssnStateInfo := {
  assnOpId : OpId;
  assnAcc  : accType
}.

Definition AssnState := State AssnStateInfo.

Definition moveOpM sreg dreg : AssnState opType2 :=
  assn <-- get ;;
  let: (mop, acc') := moveOp oinfo sreg dreg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure mop.

Definition saveOpM vid reg : AssnState opType2 :=
  assn <-- get ;;
  let: (sop, acc') := saveOp oinfo vid reg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure sop.

Definition restoreOpM vid reg : AssnState opType2 :=
  assn <-- get ;;
  let: (rop, acc') := restoreOp oinfo vid reg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure rop.

Definition pairM {A B : Type} (x : AssnState A) (y : AssnState B) :
  AssnState (A * B)%type :=
  x' <-- x ;;
  y' <-- y ;;
  pure (x', y').

Definition savesAndRestores opid vid reg int :
  AssnState (seq opType2 * seq opType2) :=
  let isFirst := firstUsePos int == opid in
  let isLast  := nextUseAfter int opid == None in
  let save    := sop <-- saveOpM vid reg ;; pure [:: sop] in
  let restore := rop <-- restoreOpM vid reg ;; pure [:: rop] in
  match iknd int, isFirst, isLast with
    | Middle,    true,  true  => pairM restore save
    | Middle,    false, true  => pairM (pure [::]) save
    | Middle,    true,  false => pairM restore (pure [::])
    | LeftMost,  _,     true  => pairM (pure [::]) save
    | RightMost, true,  _     => pairM restore (pure [::])
    | _,         _,     _     => pure ([::], [::])
    end.

Definition collectAllocs opid ints acc v :=
  let vid := varId vinfo v in
  let v_ints := [seq x <- ints | isWithin (fst x) vid opid] in
  if v_ints is (int, reg) :: _
  return AssnState (seq (VarId * PhysReg) *
                    seq opType2 * seq opType2)
  then
    let: (allocs', restores', saves') := acc in
    res <-- savesAndRestores opid vid reg int ;;
    let: (rs, ss) := res in
    pure ((vid, reg) :: allocs', rs ++ restores', ss ++ saves')
  else pure acc.

Definition doAllocations ints op : AssnState (seq opType2) :=
  assn <-- get ;;
  let opid := assnOpId assn in
  let vars := fst (opRefs oinfo op) in
  res <-- forFoldM ([::], [::], [::]) vars $ collectAllocs opid ints ;;
  let: (allocs, restores, saves) := res in
  let op' := applyAllocs oinfo op allocs in
  (* With lenses, this would just be: assnOpId += 2 *)
  modify (fun assn' => {| assnOpId := opid.+2
                        ; assnAcc  := assnAcc assn' |}) ;;
  pure $ restores ++ op' :: saves.

Section Topsort.

Record NatGraph := {
  vertices : seq PhysReg;
  edges    : seq (PhysReg * PhysReg)
}.

Definition emptyGraph :=
  {| vertices := [::]
   ; edges    := [::] |}.

Definition removeEdge (x : PhysReg * PhysReg) g :=
  {| vertices := vertices g
   ; edges    := filter (fun y => y != x) (edges g) |}.

Definition connections (f : (PhysReg * PhysReg) -> PhysReg) (x : PhysReg) g :=
  filter ((fun y => y == x) \o f) (edges g).

Definition outbound := connections (@fst _ _).
Definition inbound  := connections (@snd _ _).

Fixpoint tsort' fuel l roots g :=
  (* The fuel represents the fact that we must only call tsort' once for
     each vertex in the graph. *)
  if fuel isn't S fuel then inr (rev l) else
  match roots, edges g with
  | [::],   [::] => inr (rev l)
  | [::],   _    => inl (edges g)
  | n :: s, _    =>
    let outEdges := outbound n g in
    let g' := foldr removeEdge g outEdges in
    let outNodes := map (@snd _ _) outEdges in
    let s' := s ++ filter (@nilp _ \o inbound ^~ g') outNodes in
    tsort' fuel (n :: l) s' g'
  end.

Definition topsort g : seq (PhysReg * PhysReg) + seq PhysReg :=
  let noInbound :=
      (fun xs => [seq x <- vertices g | x \notin xs])
      (map (@snd _ _) (edges g)) in
  tsort' (size (vertices g)) [::] noInbound g.

End Topsort.

(* Compute topsort *)
(*   {| vertices := *)
(*        [:: 1; 3; 4; 5; 9; 7; 6; 2] *)
(*    ; edges := *)
(*        [:: (1, 3) *)
(*          ; (4, 5) *)
(*          ; (9, 7) *)
(*          ; (7, 1) *)
(*          ; (6, 2) *)
(*          ; (2, 4) *)
(*          ; (5, 6) *)
(*        ] *)
(*    |}. *)

Definition addVertex (v : PhysReg) (g : NatGraph) : NatGraph :=
  (fun vg =>
    {| vertices := if v \in vg then vg else v :: vg
     ; edges := edges g
     |})
  (vertices g).

Definition addEdge (e : PhysReg * PhysReg) (g : NatGraph) : NatGraph :=
  let g' :=
    (fun eg =>
      {| vertices := vertices g
       ; edges := if e \in eg then eg else e :: eg
       |})
    (edges g) in
  addVertex (fst e) $ addVertex (snd e) $ g'.

Definition resolveMappings bid ops ops' mappings :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some inss then pure ops' else

  let g := forFold emptyGraph inss $ fun g mv =>
    match moveAction mv with
    | MoveOp sreg dreg => addEdge (sreg, dreg) g
    | SaveOp sreg      => addVertex sreg g
    | RestoreOp dreg   => addVertex dreg g
    end in
  let order := topsort g in

  (* Do all saves first.

     Then moves in proper order (degrading them to save/restore to break
     cycles; or if there is a restore pending, use its register).

     Then all restores.

     This function should break into several parts:

     1. Compute the instructions, producing ordered operations that go to
        either the beginning or end of the block.

     2. Insert the instruction at the correct place. *)

  forFoldM ops' inss $ fun ops'' mv =>
    let: {| movePos    := pos
          ; moveVarId  := vid
          ; moveAction := action
          |} := mv in

    (* jww (2015-01-27): NYI: When multiple moves must be inserted at
       one edge, then the order of the moves is important because the
       same register can occur as the source of one move and the
       destination of another move. The moves must be ordered such that
       a register is saved first before it is overwritten. *)
    op <--
       match action with
       | MoveOp sreg dreg => moveOpM sreg dreg
       | SaveOp sreg      => saveOpM vid sreg
       | RestoreOp dreg   => restoreOpM vid dreg
       end ;;

    pure $ match pos with
      | AtBegin => op :: ops''
      | AtEnd =>
          match ops, ops'' with
          | o :: os, o'' :: os'' =>
              if opKind oinfo (last o os) is IsBranch
              then belast o'' os'' ++ [:: op; last o'' os'']
              else ops' ++ [:: op]
          | _, _ => [:: op]
          end
      end.

Definition considerOps (f : opType1 -> AssnState (seq opType2))
  (mappings : IntMap (seq Move)) :=
  mapM $ fun blk =>
    (* First apply all allocations *)
    let ops := blockOps binfo blk in
    ops' <-- concatMapM f ops ;;
    (* Insert resolving moves based on the mappings *)
    let bid := blockId binfo blk in
    ops'' <-- resolveMappings bid ops ops' mappings ;;
    pure $ setBlockOps binfo blk ops''.

Definition assignRegNum `(st : ScanState InUse sd)
  (mappings : IntMap (seq Move)) (blocks : seq blockType1)
  (acc : accType) : seq blockType2 * accType :=
  let: (blocks', assn) :=
    considerOps
      (doAllocations
         [seq (getIntervalDesc (getInterval (fst x)), snd x)
         | x <- handled sd ++ active sd ++ inactive sd])
      mappings
      blocks
      {| assnOpId := 1
       ; assnAcc := acc |} in
  (blocks', assnAcc assn).

End Allocation.

End Blocks.

End MBlocks.