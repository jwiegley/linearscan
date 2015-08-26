Require Import LinearScan.Lib.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Trans.State.
Require Import LinearScan.Blocks.
Require Import LinearScan.Graph.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Loops.
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
  forFoldM [::] moves $ fun acc mv =>
    let k := fmap (@Some _) in
    mops <-- match mv with
      | Move    sreg svid dreg => k $ moveOp oinfo sreg svid dreg
      | Spill   sreg svid      => k $ saveOp oinfo sreg svid
      | Restore dvid dreg      => k $ restoreOp oinfo dvid dreg
      | _ => pure None
      end ;;
    pure $ if mops is Some ops then acc ++ ops else acc.

Definition varAllocs pos (allocs : seq (Allocation maxReg)) vid v :
  seq ((VarId * VarKind) * PhysReg) :=
  map (fun x => ((vid, @varKind maxReg v), x)) $ catMaybes
    [seq intReg i | i <- allocs
    & let int := intVal i in
      [&& ivar int == vid
      ,   pos < iend int & ibeg int < pos.+2 ]].

Definition varInfoAllocs pos (allocs : seq (Allocation maxReg)) v :
  seq ((VarId * VarKind) * PhysReg) :=
  if @varId maxReg v isn't inr vid then [::] else
  varAllocs pos allocs vid v.

Definition Verified := Verified maxReg mType AssnStateDesc.

Definition _verExt := @_verExt maxReg AssnStateDesc.

Variable useVerifier : UseVerifier.

Definition setAllocations (allocs : seq (Allocation maxReg))
  (injector : Verified (seq opType2)) op :
  Verified (seq opType2) :=
  assn <-- use _verExt ;;
  let opid := assnOpId assn in
  let vars := opRefs oinfo op in
  let regs := concat $ map (varInfoAllocs opid allocs) vars in

  let transitions b e :=
    if assnBlockBeg assn <= b < assnBlockEnd assn
    then let moves := determineMoves allocs None b e in
         moves' <-- verifyResolutions e useVerifier moves ;;
         lift $ generateMoves moves'
    else pure [::] in

  inputTransitions  <-- transitions opid.-1 opid ;;
  outputTransitions <-- transitions opid opid.+1 ;;

  injected <-- injector ;;

  (* opid.+2 is used here so that verification action appear to have happened
     after the current instruction, since they represent the "effect" of the
     instruction. *)
  verifyAllocs oinfo opid.+2 useVerifier op regs ;;
  ops <-- lift $ applyAllocs oinfo op regs ;;

  _verExt \o+ _assnOpId += 2 ;;

  pure $ inputTransitions ++ outputTransitions ++ injected ++ ops.

Definition considerOps
  (allocs   : seq (Allocation maxReg))
  (liveSets : IntMap BlockLiveSets)
  (mappings : IntMap (BlockMoves maxReg))
  (loops    : LoopState) :
  seq blockType1 -> Verified (seq blockType2) :=
  mapM $ fun blk =>
    let: (opsb, opsm, opse) := blockOps binfo blk in

    opid <-- use (stepdownl' (_verExt \o+ _assnOpId)) ;;
    _verExt \o+ _assnBlockBeg .= opid + (size opsb).*2 ;;
    _verExt \o+ _assnBlockEnd .= opid + (size opsb + size opsm).*2 ;;

    bid <-- lift $ blockId binfo blk ;;
    let: (liveIns, liveOuts) :=
      if IntMap_lookup bid liveSets is Some bls
      then (blockLiveIn bls, blockLiveOut bls)
      else (emptyIntSet, emptyIntSet) in
    let: (begMoves, endMoves) :=
      fromMaybe ([::], [::]) (IntMap_lookup bid mappings) in
    let k := setAllocations allocs in

    let resolutions pos moves :=
      opid   <-- use (stepdownl' (_verExt \o+ _assnOpId)) ;;
      moves' <-- verifyResolutions pos useVerifier moves ;;
      lift $ generateMoves moves' in

    verifyBlockBegin opid useVerifier bid liveIns loops ;;

    opsb'  <-- concatMapM (k (pure [::])) opsb ;;
    bmoves <-- resolutions opid.-1 begMoves ;;
    opsm'  <-- concatMapM (k (pure [::])) opsm ;;

    opse'  <-- match opse with
      | e :: es =>
          xs <-- concatMapM (k (pure [::])) (belast e es) ;;
          x  <-- k (resolutions opid endMoves) (last e es) ;;
          pure (xs ++ x)
      | [::] =>
          pure [::]
      end ;;

    verifyBlockEnd opid useVerifier bid liveOuts ;;

    let opsm'' := bmoves ++ opsm' in
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
  (loops    : LoopState)
  (blocks   : seq blockType1) :
  mType (IntMap (seq ResolvingMoveSet) *
         (VerifiedSig maxReg AssnStateDesc + seq blockType2)) :=
  res <-- considerOps allocs liveSets mappings loops blocks
                      (newVerifiedSig maxReg newAssnStateDesc) ;;
  let: (bs, st) := res in
  pure (verMoves st,
        if IntMap_toList (verErrors st) is [::]
        then inr bs
        else inl st).

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
