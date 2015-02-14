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
  assnOpId     : OpId;
  assnBlockBeg : OpId;
  assnBlockEnd : OpId;
  assnAcc      : accType
}.

Definition AssnState := State AssnStateInfo.

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

Definition savesAndRestores (opid : OpId) v reg int :
  AssnState (seq opType2 * seq opType2) :=
  if @varId maxReg v isn't inr vid then pure ([::], [::]) else

  (* Wimmer: "If a split position is moved to a block boundary, the algorithm
     for resolving the data flow takes care of inserting the move. It is also
     possible that no move is necessary at all because of the control flow." *)
  assn <-- get ;;
  (* We increment by two before checking the beginning in order to skip past
     the label. *)
  let knd := varKind v in
  let atBoundary :=
      ((knd == Input)  && (assnBlockBeg assn == opid)) ||
      ((knd == Output) && (opid.+2 == assnBlockEnd assn)) in
  if atBoundary then pure ([::], [::]) else

  let isFirst := firstUsePos int == Some opid in
  let isLast  := nextUseAfter int opid == None in
  let save    := saveOpM reg (Some vid) in
  let restore := restoreOpM (Some vid) reg in
  match knd, iknd int, isFirst, isLast with
    | Input,  LeftMost,  _,     true  => pairM (pure [::]) save
    | Input,  Middle,    true,  true  => pairM restore save
    | Input,  Middle,    true,  _     => pairM restore (pure [::])
    | Input,  Middle,    _,     true  => pairM (pure [::]) save
    | Input,  RightMost, true,  _     => pairM restore (pure [::])
    | Output, LeftMost,  _,     true  => pairM (pure [::]) save
    | Output, Middle,    _,     true  => pairM (pure [::]) save
    | _,      _,         _,     _     => pure ([::], [::])
    end.

Definition collectAllocs opid ints acc v :=
  if @varId maxReg v isn't inr vid then pure acc else
  let v_ints := [seq x <- ints | isWithin (fst x) vid opid] in
  forFoldM acc v_ints $ fun acc' x =>
    match x
    return AssnState (seq (VarId * PhysReg) *
                      seq opType2 * seq opType2) with
    | (int, reg) =>
      let: (allocs', restores', saves') := acc' in
      res <-- savesAndRestores opid v reg int ;;
      let: (rs, ss) := res in
      pure ((vid, reg) :: allocs', rs ++ restores', ss ++ saves')
    end.

Definition doAllocations ints op : AssnState (seq opType2) :=
  assn <-- get ;;
  let opid := assnOpId assn in
  let vars := opRefs oinfo op in
  res <-- forFoldM ([::], [::], [::]) vars $ collectAllocs opid ints ;;
  let: (allocs, restores, saves) := res in
  let op' := applyAllocs oinfo op allocs in
  (* With lenses, this would just be: assnOpId += 2 *)
  modify (fun assn' =>
            {| assnOpId     := opid.+2
             ; assnBlockBeg := assnBlockBeg assn'
             ; assnBlockEnd := assnBlockEnd assn'
             ; assnAcc      := assnAcc assn' |}) ;;
  pure $ restores ++ op' ++ saves.


Definition generateMoves
  (moves : seq (option (PhysReg + nat) * option (PhysReg + nat))) :
  AssnState (seq opType2) :=
  forFoldM [::] moves $ fun acc mv =>
    mops <-- match mv with
      | (Some (inl sreg), Some (inl dreg)) =>
          fmap (@Some _) $ moveOpM sreg dreg
      | (Some (inl sreg), Some (inr vid)) =>
          fmap (@Some _) $ saveOpM sreg (Some vid)
      | (Some (inl sreg), None) => fmap (@Some _) $ saveOpM sreg None
      | (Some (inr vid), Some (inl dreg)) =>
          fmap (@Some _) $ restoreOpM (Some vid) dreg
      | (None, Some (inl dreg)) => fmap (@Some _) $ restoreOpM None dreg
        (* jww (2015-02-14): There are possibilities, like Some (inr sv), Some
           (inr dv), which should be provably impossible, since no resolving
           move for the same variable would ever both to copy from and to the
           same stack location. *)
      | (_, _) => pure None
      end ;;
    pure $ if mops is Some ops then ops ++ acc else acc.

Definition resolveMappings bid opsm mappings :
  AssnState (seq opType2) :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some graphs then pure opsm else

  let: (gbeg, gend) := graphs in

  bmoves <-- generateMoves (topsort gbeg) ;;
  let opsm' := bmoves ++ opsm in

  emoves <-- generateMoves (topsort gend) ;;
  let opsm'' := opsm' ++ emoves in
  pure opsm''.

Definition considerOps (f : opType1 -> AssnState (seq opType2)) mappings :=
  mapM $ fun blk =>
    (* First apply all allocations *)
    let ops := blockOps binfo blk in
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
    let bid := blockId binfo blk in
    opsm'' <-- resolveMappings bid opsm' mappings ;;
    pure $ setBlockOps binfo blk opsb' opsm'' opse'.

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
      {| assnOpId     := 1
       ; assnBlockBeg := 1
       ; assnBlockEnd := 1
       ; assnAcc      := acc |} in
  (blocks', assnAcc assn).

End Assign.
