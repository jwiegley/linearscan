Require Import LinearScan.Lib.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Trans.State.
Require Import LinearScan.Blocks.
Require Import LinearScan.Graph.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Resolve.
Require Import LinearScan.ScanState.
Require Import LinearScan.Allocate.
Require Import LinearScan.Verify.

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

Record AssnStateDesc := {
  assnOpId     : OpId;
  assnBlockBeg : OpId;
  assnBlockEnd : OpId
}.

Definition newAssnStateDesc :=
  {| assnOpId     := 1
   ; assnBlockBeg := 1
   ; assnBlockEnd := 1
   |}.

Definition _assnOpId : Lens' AssnStateDesc OpId := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId     := x
     ; assnBlockBeg := assnBlockBeg s
     ; assnBlockEnd := assnBlockEnd s
     |}) (f (assnOpId s)).

Definition _assnBlockBeg : Lens' AssnStateDesc OpId := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId     := assnOpId s
     ; assnBlockBeg := x
     ; assnBlockEnd := assnBlockEnd s
     |}) (f (assnBlockBeg s)).

Definition _assnBlockEnd : Lens' AssnStateDesc OpId := fun _ _ f s =>
  fmap (fun x =>
    {| assnOpId     := assnOpId s
     ; assnBlockBeg := assnBlockBeg s
     ; assnBlockEnd := x
     |}) (f (assnBlockEnd s)).

Definition generateMoves (moves : seq (ResolvingMove maxReg)) :
  mType (seq opType2) :=
  forFoldrM [::] moves $ fun mv acc =>
    let k := fmap (@Some _) in
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

Definition _aside {a b : Type} {P : a -> Prop} :
  Lens' { x : a * b | P (fst x) } b :=
  fun _ _ f s =>
    let: exist (x, y) H := s in
    fmap (fun z => exist _ (x, z) H) (f y).

Definition Verified (maxVar : nat) :=
  Verified maxReg maxVar mType AssnStateDesc.

Definition setAllocations (maxVar : nat) (allocs : seq (Allocation maxReg)) op :
  Verified maxVar (seq opType2) :=
  assn <-- lift $ use _aside ;;
  let opid  := assnOpId assn in
  let vars  := opRefs oinfo op in
  let regs  := concat $ map (varAllocs opid allocs) vars in
  ops <-- verifyApplyAllocs oinfo op regs ;;

  transitions <--
    (if assnBlockBeg assn <= opid < assnBlockEnd assn
     then lift $ lift $ generateMoves
       (determineMoves
          (resolvingMoves allocs opid opid.+2))
     else pure [::]) ;;

  lift $ modifyT ((_aside \o+ _assnOpId) .~ opid.+2) ;;

  pure $ ops ++ transitions.

Definition resolveMappings {maxVar : nat} bid opsm mappings :
  Verified maxVar (seq opType2) :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some graphs then pure opsm else
  let: (gbeg, gend) := graphs in

  let begMoves := map (@moveFromGraph maxReg) (topsort gbeg) in
  verifyResolutions begMoves ;;
  bmoves <-- lift $ lift $ generateMoves begMoves ;;

  let endMoves := map (@moveFromGraph maxReg) (topsort gend) in
  verifyResolutions endMoves ;;
  emoves <-- lift $ lift $ generateMoves endMoves ;;

  pure $ bmoves ++ opsm ++ emoves.

Definition considerOps (maxVar : nat)
  (allocs   : seq (Allocation maxReg))
  (liveSets : IntMap BlockLiveSets)
  (mappings : IntMap (BlockMoves maxReg)) :
  seq blockType1 -> Verified maxVar (seq blockType2) :=
  mapM $ fun blk =>
    let: (opsb, opsm, opse) := blockOps binfo blk in

    lift $ modifyT (fun s =>
      let opid := s ^_ stepdown (_aside \o+ _assnOpId) in
      s &+ (_aside \o+ _assnBlockBeg) .~ opid + (size opsb).*2
        &+ (_aside \o+ _assnBlockEnd) .~ opid + (size opsb + size opsm).*2) ;;

    bid <-- lift $ lift $ blockId binfo blk ;;
    let: (liveIn, liveOut) :=
       if IntMap_lookup bid liveSets is Some bls
       then (blockLiveIn bls, blockLiveOut bls)
       else (emptyIntSet, emptyIntSet) in

    verifyBlockBegin liveIn ;;

    let k := setAllocations allocs in
    opsb' <-- concatMapM k opsb ;;
    opsm' <-- concatMapM k opsm ;;
    opse' <-- concatMapM k opse ;;

    (* Insert resolving moves at the beginning or end of [opsm'] based on the
       mappings. *)
    opsm'' <-- resolveMappings bid opsm' mappings ;;

    verifyBlockEnd liveOut ;;

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

(* Given a set of allocations, which associate intervals with optional
   register assignments; the set of live variables at the beginning and ending
   of each block; the set of resolving moves between each two connected
   blocks; and the list of blocks themselves, assign the allocated registers
   in the instruction stream itself, returning a new list of blocks. *)
Definition assignRegNum
  (allocs   : seq (Allocation maxReg))
  (liveSets : IntMap BlockLiveSets)
  (mappings : IntMap (BlockMoves maxReg))
  (blocks   : seq blockType1) : mType (AllocError + seq blockType2) :=
  let maxVar := forFold 0 allocs $ fun acc x =>
    maxn acc (ivar (intVal x)) in
  fmap fst <$> considerOps allocs liveSets mappings blocks
    (exist _ (newRegStateDesc maxReg maxVar, newAssnStateDesc)
             (StartState maxReg maxVar)).

End Assign.

Module AssnLensLaws.

Include LensLaws.

Program Instance Lens__assnOpId : LensLaws _assnOpId.
Obligation 2. by case: x. Qed.
Program Instance Lens__assnBlockBeg : LensLaws _assnBlockBeg.
Obligation 2. by case: x. Qed.
Program Instance Lens__assnBlockEnd : LensLaws _assnBlockEnd.
Obligation 2. by case: x. Qed.

End AssnLensLaws.
