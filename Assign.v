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
Require Import LinearScan.State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Assign.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

Record AssnStateInfo := {
  assnOpId     : OpId;
  assnBlockBeg : OpId;
  assnBlockEnd : OpId;
  assnAcc      : accType
}.

Definition AssnState := State AssnStateInfo.

Definition swapOpM sreg dreg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (mop, acc') := swapOp oinfo sreg dreg (assnAcc assn) in
  put {| assnOpId     := assnOpId assn
       ; assnBlockBeg := assnBlockBeg assn
       ; assnBlockEnd := assnBlockEnd assn
       ; assnAcc      := acc' |} ;;
  pure mop.

Definition moveOpM sreg dreg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (mop, acc') := moveOp oinfo sreg dreg (assnAcc assn) in
  put {| assnOpId     := assnOpId assn
       ; assnBlockBeg := assnBlockBeg assn
       ; assnBlockEnd := assnBlockEnd assn
       ; assnAcc      := acc' |} ;;
  pure mop.

Definition saveOpM vid reg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (sop, acc') := saveOp oinfo vid reg (assnAcc assn) in
  put {| assnOpId     := assnOpId assn
       ; assnBlockBeg := assnBlockBeg assn
       ; assnBlockEnd := assnBlockEnd assn
       ; assnAcc      := acc' |} ;;
  pure sop.

Definition restoreOpM vid reg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (rop, acc') := restoreOp oinfo vid reg (assnAcc assn) in
  put {| assnOpId     := assnOpId assn
       ; assnBlockBeg := assnBlockBeg assn
       ; assnBlockEnd := assnBlockEnd assn
       ; assnAcc      := acc' |} ;;
  pure rop.

Definition pairM {A B : Type} (x : AssnState A) (y : AssnState B) :
  AssnState (A * B)%type :=
  x' <-- x ;;
  y' <-- y ;;
  pure (x', y').

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

Definition generateMoves (moves : seq (ResolvingMove maxReg)) :
  AssnState (seq opType2) :=
  forFoldrM [::] moves $ fun mv acc =>
    mops <-- match mv with
      | Swap    sreg dreg => fmap (@Some _) $ swapOpM sreg dreg
      | Move    sreg dreg => fmap (@Some _) $ moveOpM sreg dreg
      | Spill   sreg vid  => fmap (@Some _) $ saveOpM sreg (Some vid)
      | Restore vid  dreg => fmap (@Some _) $ restoreOpM (Some vid) dreg
      | Nop => pure None
      end ;;
    pure $ if mops is Some ops then ops ++ acc else acc.

Definition doAllocations (allocs : seq (Allocation maxReg)) op :
  AssnState (seq opType2) :=
  assn <-- get ;;
  let opid  := assnOpId assn in
  let vars  := opRefs oinfo op in
  let regs  := concat $ map (varAllocs opid allocs) vars in
  let ops   := applyAllocs oinfo op regs in

  transitions <--
    (if assnBlockBeg assn < opid < assnBlockEnd assn
     then generateMoves
            (determineMoves (resolvingMoves allocs opid opid.+2 false))
     else pure [::]) ;;

  (* With lenses, this would just be: assnOpId += 2 *)
  modify (fun assn' =>
            {| assnOpId     := opid.+2
             ; assnBlockBeg := assnBlockBeg assn'
             ; assnBlockEnd := assnBlockEnd assn'
             ; assnAcc      := assnAcc assn' |}) ;;

  pure $ ops ++ transitions.

Definition resolveMappings bid opsm mappings : AssnState (seq opType2) :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some graphs then pure opsm else

  let: (gbeg, gend) := graphs in

  bmoves <-- generateMoves (map (@moveFromGraph maxReg) (topsort gbeg)) ;;
  let opsm' := bmoves ++ opsm in

  emoves <-- generateMoves (map (@moveFromGraph maxReg) (topsort gend)) ;;
  let opsm'' := opsm' ++ emoves in
  pure opsm''.

Definition considerOps (f : opType1 -> AssnState (seq opType2))
  (liveSets : IntMap BlockLiveSets) mappings :=
  mapM $ fun blk =>
    (* First apply all allocations *)
    let ops := blockOps binfo blk in
    let bid := blockId binfo blk in

    let outs := if IntMap_lookup bid liveSets is Some ls
                then blockLiveOut ls
                else emptyIntSet in

    let: (opsb, opsm, opse) := ops in
    modify (fun assn =>
              {| assnOpId     := assnOpId assn
               ; assnBlockBeg := assnOpId assn + (size opsb).*2
               ; assnBlockEnd := assnOpId assn + (size opsb + size opsm).*2
               ; assnAcc      := assnAcc assn |}) ;;
    opsb' <-- concatMapM f opsb ;;
    opsm' <-- concatMapM f opsm ;;
    opse' <-- concatMapM f opse ;;
    (* Insert resolving moves based on the mappings *)
    opsm'' <-- resolveMappings bid opsm' mappings ;;
    match opsb', opse' with
    | b :: bs, e :: es =>
        pure $ setBlockOps binfo blk
          [:: b] (bs ++ opsm'' ++ belast e es) [:: last e es]
    | _, _ => pure $ setBlockOps binfo blk opsb' opsm'' opse'
    end.

Definition assignRegNum (allocs : seq (Allocation maxReg))
  (liveSets : IntMap BlockLiveSets) (mappings : IntMap (BlockMoves maxReg))
  (blocks : seq blockType1) (acc : accType) : seq blockType2 * accType :=
  let: (blocks', assn) :=
    considerOps
      (doAllocations allocs)
      liveSets
      mappings
      blocks
      {| assnOpId     := 1
       ; assnBlockBeg := 1
       ; assnBlockEnd := 1
       ; assnAcc      := acc |} in
  (blocks', assnAcc assn).

End Assign.
