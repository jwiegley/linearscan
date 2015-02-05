Require Import LinearScan.Lib.
Require Import LinearScan.Blocks.
Require Import LinearScan.Graph.
Require Import LinearScan.Interval.
Require Import LinearScan.IntMap.
Require Import LinearScan.Resolve.
Require Import LinearScan.ScanState.
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
  assnOpId : OpId;
  assnAcc  : accType
}.

Definition AssnState := State AssnStateInfo.

Definition moveOpM sreg dreg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (mop, acc') := moveOp oinfo sreg dreg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure mop.

Definition saveOpM vid reg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (sop, acc') := saveOp oinfo vid reg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure sop.

Definition restoreOpM vid reg : AssnState (seq opType2) :=
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

Definition savesAndRestores (opid : OpId) vid reg int :
  AssnState (seq opType2 * seq opType2) :=
  let isFirst := firstUsePos int == Some opid in
  let isLast  := nextUseAfter int opid == None in
  let save    := saveOpM reg (Some vid) in
  let restore := restoreOpM (Some vid) reg in
  match iknd int, isFirst, isLast with
    | Middle,    true,  true  => pairM restore save
    | Middle,    false, true  => pairM (pure [::]) save
    | Middle,    true,  false => pairM restore (pure [::])
    | LeftMost,  _,     true  => pairM (pure [::]) save
    | RightMost, true,  _     => pairM restore (pure [::])
    | _,         _,     _     => pure ([::], [::])
    end.

Definition collectAllocs opid ints acc v :=
  let vid := varId v in
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
  pure $ restores ++ op' ++ saves.


Definition generateMoves (moves : seq (option PhysReg * option PhysReg)) :
  AssnState (seq opType2) :=
  forFoldM [::] moves $ fun acc mv =>
    mops <-- match mv with
      | (Some sreg, Some dreg) => fmap (@Some _) $ moveOpM sreg dreg
      | (Some sreg, None)      => fmap (@Some _) $ saveOpM sreg None
      | (None, Some dreg)      => fmap (@Some _) $ restoreOpM None dreg
      | (None, None)           => pure None
      end ;;
    pure $ if mops is Some ops then ops ++ acc else acc.

Definition resolveMappings bid ops ops' mappings :
  AssnState (seq opType2) :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some graphs then pure ops' else

  let: (gbeg, gend) := graphs in

  bmoves <-- generateMoves (topsort gbeg) ;;
  let ops'' := bmoves ++ ops' in

  emoves <-- generateMoves (topsort gend) ;;
  pure $ match ops, ops'' with
    | o :: os, o'' :: os'' =>
        if opKind oinfo (last o os) is IsBranch
        then belast o'' os'' ++ emoves ++ [:: last o'' os'']
        else ops'' ++ emoves
    | _, _ => ops'' ++ emoves
  end.

Definition considerOps (f : opType1 -> AssnState (seq opType2)) mappings :=
  mapM $ fun blk =>
    (* First apply all allocations *)
    let ops := blockOps binfo blk in
    ops' <-- concatMapM f ops ;;
    (* Insert resolving moves based on the mappings *)
    let bid := blockId binfo blk in
    ops'' <-- resolveMappings bid ops ops' mappings ;;
    pure $ setBlockOps binfo blk ops''.

Definition assignRegNum `(st : ScanState InUse sd)
  (mappings : IntMap (BlockMoves maxReg)) (blocks : seq blockType1)
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

End Assign.
