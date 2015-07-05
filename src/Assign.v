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

Definition varAllocs opid (allocs : seq (Allocation maxReg)) kind vid :
  seq (VarId * PhysReg) :=
  map (fun x => (vid, x)) $ catMaybes
    [seq intReg i | i <- allocs
    & let int := intVal i in
      [&& ivar int == vid
      ,   ibeg int <= opid
      &   if kind is Input
          then opid <= iend int
          else opid <  iend int]].

Definition varInfoAllocs opid (allocs : seq (Allocation maxReg)) v :
  seq (VarId * PhysReg) :=
  if @varId maxReg v isn't inr vid then [::] else
  varAllocs opid allocs (varKind v) vid.

Definition Verified (maxVar : nat) :=
  Verified maxReg maxVar mType AssnStateDesc.

Definition _verExt {maxVar : nat} := @_verExt maxReg maxVar AssnStateDesc.

Definition setAllocations (maxVar : nat) (allocs : seq (Allocation maxReg)) op :
  Verified maxVar (seq opType2) :=
  assn <-- use _verExt ;;
  let opid  := assnOpId assn in
  let vars  := opRefs oinfo op in
  let regs  := concat $ map (varInfoAllocs opid allocs) vars in
  ops <-- verifyApplyAllocs oinfo opid op regs ;;

  transitions <--
    (if assnBlockBeg assn <= opid < assnBlockEnd assn
     then
       let moves := determineMoves (resolvingMoves allocs opid opid.+2) in
       verifyResolutions opid moves ;;
       lift $ lift $ generateMoves moves
     else pure [::]) ;;

  _verExt \o+ _assnOpId .= opid.+2 ;;

  pure $ ops ++ transitions.

Definition considerOps (maxVar : nat)
  (allocs   : seq (Allocation maxReg))
  (liveSets : IntMap BlockLiveSets)
  (mappings : IntMap (BlockMoves maxReg)) :
  seq blockType1 -> Verified maxVar (seq blockType2) :=
  mapM $ fun blk =>
    let: (opsb, opsm, opse) := blockOps binfo blk in

    opid <-- use (stepdownl' (_verExt \o+ _assnOpId)) ;;
    let opid_firstOp := opid + (size opsb).*2 in

    _verExt \o+ _assnBlockBeg .= opid + (size opsb).*2 ;;
    _verExt \o+ _assnBlockEnd .= opid + (size opsb + size opsm).*2 ;;

    bid <-- lift $ lift $ blockId binfo blk ;;
    let: (liveIns, liveOuts) :=
       if IntMap_lookup bid liveSets is Some bls
       then (blockLiveIn bls, blockLiveOut bls)
       else (emptyIntSet, emptyIntSet) in

    let startRegs :=
        concat $ map (varAllocs opid_firstOp allocs Input)
                     (IntSet_toList liveIns) in

    verifyBlockBegin opid liveIns startRegs ;;

    let: (gbeg, gend) :=
       if IntMap_lookup bid mappings is Some graphs
       then graphs
       else (emptyGraph, emptyGraph) in

    let begMoves := map (@moveFromGraph maxReg) (topsort gbeg) in
    (* jww (2015-07-04): We don't currently have enough information to verify
       the incoming resolutions at the beginning of each block. *)
    (* verifyResolutions opid begMoves ;; *)
    bmoves <-- lift $ lift $ generateMoves begMoves ;;

    let k := setAllocations allocs in
    opsb' <-- concatMapM k opsb ;;
    opsm' <-- concatMapM k opsm ;;
    opse' <-- concatMapM k opse ;;

    opid <-- use (stepdownl' (_verExt \o+ _assnOpId)) ;;

    let endMoves := map (@moveFromGraph maxReg) (topsort gend) in
    verifyResolutions opid endMoves ;;
    emoves <-- lift $ lift $ generateMoves endMoves ;;

    verifyBlockEnd opid liveOuts ;;

    let opsm'' := bmoves ++ opsm' ++ emoves in
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
  (blocks   : seq blockType1) :
  mType ((OpId * seq AllocError) + seq blockType2) :=
  let maxVar := forFold 0 allocs $ fun acc x =>
    maxn acc (ivar (intVal x)) in
  runVerified (maxVar:=maxVar.+1)
    (considerOps allocs liveSets mappings blocks) newAssnStateDesc.

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
