Require Import LinearScan.Lib.
Require Import LinearScan.Blocks.
Require Import LinearScan.Graph.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.IntMap.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Resolve.
Require Import LinearScan.ScanState.
Require Import LinearScan.Allocate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Assign.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg opType1 opType2.

Record AllocState := {
  (* Indicate which variables (not intervals) are currently allocated. *)
  registers   : Vec (option nat) maxReg;

  (* Indicate whether a variable is currently known to be in either a register
     or a variable spill slot. If not present, the variable is not known at
     this point and is not available in either register or memory. *)
  allocations : IntMap (option PhysReg)
}.

Definition newAllocState : AllocState :=
   {| registers   := vconst None
    ; allocations := emptyIntMap |}.

(* An allocation error occurs if the source and destination for a register are
   different, because this should have been accounted for. *)
Record AllocError := {
  aeVarId     : nat;
  aeVarSrcReg : option PhysReg;
  aeVarDstReg : option PhysReg;
  aeBlockId   : BlockId
}.

Record AssnStateInfo := {
  assnOpId             : OpId;
  assnBlockBeg         : OpId;
  assnBlockEnd         : OpId;
  assnAllocState       : AllocState;
  assnBlockEntryAllocs : IntMap AllocState;
  assnBlockExitAllocs  : IntMap AllocState;
  assnErrors           : seq AllocError
}.

Definition newAssnStateInfo :=
  {| assnOpId             := 1
   ; assnBlockBeg         := 1
   ; assnBlockEnd         := 1
   ; assnAllocState       := newAllocState
   ; assnBlockEntryAllocs := emptyIntMap
   ; assnBlockExitAllocs  := emptyIntMap
   ; assnErrors           := [::]
   |}.

Definition _assnOpId : Lens' AssnStateInfo OpId := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId             := x
     ; assnBlockBeg         := assnBlockBeg s
     ; assnBlockEnd         := assnBlockEnd s
     ; assnAllocState       := assnAllocState s
     ; assnBlockEntryAllocs := assnBlockEntryAllocs s
     ; assnBlockExitAllocs  := assnBlockExitAllocs s
     ; assnErrors           := assnErrors s
     |}) (f (assnOpId s)).
Program Instance Lens__assnOpId : CorrectLens _assnOpId.
Obligation 2. by case: x. Qed.

Definition _assnBlockBeg : Lens' AssnStateInfo OpId := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId             := assnOpId s
     ; assnBlockBeg         := x
     ; assnBlockEnd         := assnBlockEnd s
     ; assnAllocState       := assnAllocState s
     ; assnBlockEntryAllocs := assnBlockEntryAllocs s
     ; assnBlockExitAllocs  := assnBlockExitAllocs s
     ; assnErrors           := assnErrors s
     |}) (f (assnBlockBeg s)).
Program Instance Lens__assnBlockBeg : CorrectLens _assnBlockBeg.
Obligation 2. by case: x. Qed.

Definition _assnBlockEnd : Lens' AssnStateInfo OpId := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId             := assnOpId s
     ; assnBlockBeg         := assnBlockBeg s
     ; assnBlockEnd         := x
     ; assnAllocState       := assnAllocState s
     ; assnBlockEntryAllocs := assnBlockEntryAllocs s
     ; assnBlockExitAllocs  := assnBlockExitAllocs s
     ; assnErrors           := assnErrors s
     |}) (f (assnBlockEnd s)).
Program Instance Lens__assnBlockEnd : CorrectLens _assnBlockEnd.
Obligation 2. by case: x. Qed.

Definition _assnAllocState : Lens' AssnStateInfo AllocState := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId             := assnOpId s
     ; assnBlockBeg         := assnBlockBeg s
     ; assnBlockEnd         := assnBlockEnd s
     ; assnAllocState       := x
     ; assnBlockEntryAllocs := assnBlockEntryAllocs s
     ; assnBlockExitAllocs  := assnBlockExitAllocs s
     ; assnErrors           := assnErrors s
     |}) (f (assnAllocState s)).
Program Instance Lens__assnAllocState : CorrectLens _assnAllocState.
Obligation 2. by case: x. Qed.

Definition _assnBlockEntryAllocs : Lens' AssnStateInfo (IntMap AllocState) :=
  fun _ _ f s => fmap (fun x =>
    {| assnOpId             := assnOpId s
     ; assnBlockBeg         := assnBlockBeg s
     ; assnBlockEnd         := assnBlockEnd s
     ; assnAllocState       := assnAllocState s
     ; assnBlockEntryAllocs := x
     ; assnBlockExitAllocs  := assnBlockExitAllocs s
     ; assnErrors           := assnErrors s
     |}) (f (assnBlockEntryAllocs s)).
Program Instance Lens__assnBlockEntryAllocs : CorrectLens _assnBlockEntryAllocs.
Obligation 2. by case: x. Qed.

Definition _assnBlockExitAllocs : Lens' AssnStateInfo (IntMap AllocState) :=
  fun _ _ f s => fmap (fun x =>
    {| assnOpId             := assnOpId s
     ; assnBlockBeg         := assnBlockBeg s
     ; assnBlockEnd         := assnBlockEnd s
     ; assnAllocState       := assnAllocState s
     ; assnBlockEntryAllocs := assnBlockEntryAllocs s
     ; assnBlockExitAllocs  := x
     ; assnErrors           := assnErrors s
     |}) (f (assnBlockExitAllocs s)).
Program Instance Lens__assnBlockExitAllocs : CorrectLens _assnBlockExitAllocs.
Obligation 2. by case: x. Qed.

Definition _assnErrors : Lens' AssnStateInfo (seq AllocError) := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId             := assnOpId s
     ; assnBlockBeg         := assnBlockBeg s
     ; assnBlockEnd         := assnBlockEnd s
     ; assnAllocState       := assnAllocState s
     ; assnBlockEntryAllocs := assnBlockEntryAllocs s
     ; assnBlockExitAllocs  := assnBlockExitAllocs s
     ; assnErrors           := x
     |}) (f (assnErrors s)).
Program Instance Lens__assnErrors : CorrectLens _assnErrors.
Obligation 2. by case: x. Qed.

Definition AssnState := StateT AssnStateInfo mType.

Definition use `(l : Lens' s a) `{Monad m} : StateT s m a := view l <$> getT.

Definition plusStateT `(l : Lens' s nat) (n : nat) `{Monad m} :
  StateT s m unit := modifyT (l %~ plus n).

Notation "l += n" := (plusStateT l n) (at level 71).

Definition generateMoves (moves : seq (ResolvingMove maxReg)) :
  mType (seq opType2) :=
  forFoldrM [::] moves $ fun mv acc =>
    (* The [iso_to] is due to the fact that swapOp returns [Yoneda m a],
       rather than [m a]. This is necessary to work around a limitation with
       type formers and extraction:
       https://coq.inria.fr/bugs/show_bug.cgi?id=4227. *)
    let k := fmap (@Some _) \o iso_to in
    mops <-- match mv with
      | Swap    sreg dreg => k $ swapOp oinfo sreg dreg
      | Move    sreg dreg => k $ moveOp oinfo sreg dreg
      | Spill   sreg vid  => k $ saveOp oinfo sreg (Some vid)
      | Restore vid  dreg => k $ restoreOp oinfo (Some vid) dreg
      | Nop               => pure None
      end ;;
    pure $ if mops is Some ops then ops ++ acc else acc.

Definition varAllocs opid (allocs : seq (Allocation maxReg)) v :
  seq (VarId * PhysReg) :=
  if @varId maxReg v isn't inr vid then [::] else
  map (fun x => (vid, x)) $ catMaybes
    [seq intReg i | i <- allocs
    & let int := intVal i in
      [&& ivar int == vid
      ,   ibeg int <= opid
      &   if varKind v is Input
          then opid <= iend int
          else opid <  iend int]].

Definition setAllocations (allocs : seq (Allocation maxReg)) op :
  AssnState (seq opType2) :=
  assn <-- getT ;;
  let opid  := assnOpId assn in
  let vars  := opRefs oinfo op in
  let regs  := concat $ map (varAllocs opid allocs) vars in
  let ops   := applyAllocs oinfo op regs in

  transitions <--
    (if assnBlockBeg assn <= opid < assnBlockEnd assn
     then lift $ generateMoves
                   (determineMoves
                      (resolvingMoves allocs opid opid.+2))
     else pure [::]) ;;

  modifyT (_assnOpId .~ opid.+2) ;;

  pure $ ops ++ transitions.

Definition resolveMappings bid opsm mappings : mType (seq opType2) :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some graphs then pure opsm else
  let: (gbeg, gend) := graphs in
  bmoves <-- generateMoves (map (@moveFromGraph maxReg) (topsort gbeg)) ;;
  emoves <-- generateMoves (map (@moveFromGraph maxReg) (topsort gend)) ;;
  pure $ bmoves ++ opsm ++ emoves.

Definition considerOps
  (allocs : seq (Allocation maxReg))
  (liveSets : IntMap BlockLiveSets)
  (mappings : IntMap (BlockMoves maxReg)) :
  seq blockType1 -> AssnState (seq blockType2) :=
  mapM $ fun blk =>
    let: (opsb, opsm, opse) := blockOps binfo blk in

    modifyT (fun assn =>
      let opid := assn ^_ _assnOpId in
      assn &+ _assnBlockBeg .~ opid + (size opsb).*2
           &+ _assnBlockEnd .~ opid + (size opsb + size opsm).*2) ;;

    let k := setAllocations allocs in
    opsb' <-- concatMapM k opsb ;;
    opsm' <-- concatMapM k opsm ;;
    opse' <-- concatMapM k opse ;;

    (* Insert resolving moves at the beginning or end of [opsm'] based on the
       mappings. *)
    bid    <-- lift $ iso_to $ blockId binfo blk ;;
    opsm'' <-- lift $ resolveMappings bid opsm' mappings ;;

    match opsb', opse' with
    | b :: bs, e :: es =>
        pure $ setBlockOps binfo blk
          [:: b] (bs ++ opsm'' ++ belast e es) [:: last e es]
    | b :: bs, [::] =>
        pure $ setBlockOps binfo blk
          [:: b] (bs ++ opsm'') [::]
    | [::], e :: es =>
        pure $ setBlockOps binfo blk
          [::] (opsm'' ++ belast e es) [:: last e es]
    | [::], [::] =>
        pure $ setBlockOps binfo blk [::] opsm'' [::]
    end.

Definition compatibleAllocStates (bb be : BlockId) (x y : AllocState) :
  seq AllocError :=
  let f errs varId reg :=
      if IntMap_lookup varId (allocations y) is Some r
      then if r != reg
           then {| aeVarId     := varId
                 ; aeVarSrcReg := reg
                 ; aeVarDstReg := r
                 ; aeBlockId   := bb
                 |} :: errs
           else errs
      else {| aeVarId     := varId
            ; aeVarSrcReg := reg
            ; aeVarDstReg := None
            ; aeBlockId   := bb
            |} :: errs in
  let errs := IntMap_foldlWithKey f [::] (allocations x) in
  let g errs varId reg :=
      if IntMap_lookup varId (allocations x) is None
      then {| aeVarId     := varId
            ; aeVarSrcReg := None
            ; aeVarDstReg := reg
            ; aeBlockId   := be
            |} :: errs
      else errs in
  IntMap_foldlWithKey g errs (allocations y).

(* Given a set of allocations, which associate intervals with optional
   register assignments; the set of live variables at the beginning and ending
   of each block; the set of resolving moves between each two connected
   blocks; and the list of blocks themselves, assign the allocated registers
   in the instruction stream itself, returning a new list of blocks. *)
Definition assignRegNum
  (allocs   : seq (Allocation maxReg))
  (liveSets : IntMap BlockLiveSets)
  (mappings : IntMap (BlockMoves maxReg))
  (blocks   : seq blockType1) : mType (seq blockType2) :=
  fst <$> considerOps allocs liveSets mappings blocks newAssnStateInfo.

End Assign.
