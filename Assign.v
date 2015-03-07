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
  if lookupInterval vid (varKind v) opid allocs is Some alloc
  then if intReg alloc is Some reg
       then [:: (vid, reg)]
       else [::]
  else [::].

Definition generateMoves
  (moves : seq (option (PhysReg + nat) * option (PhysReg + nat))) :
  AssnState (seq opType2) :=
  forFoldrM [::] moves $ fun mv acc =>
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

Definition doAllocations (allocs : seq (Allocation maxReg)) op :
  AssnState (seq opType2) :=
  assn <-- get ;;
  let opid := assnOpId assn in

  let findIntervals b p f :=
      if b then [::] else
      [seq (let vid := ivar (intVal j) in f vid j)
      | j <- [seq i <- allocs
             | p i & if intReg i is Some _ then true else false ]] in

  (* Find all intervals for which this is the final operation, then pair them
     intervals beginning at the next operation for the same variable.  This is
     only done if we are not at the beginning or end of a block. *)
  let endingTransitions :=
      findIntervals (opid <= assnBlockBeg assn)
        (fun i => iend (intVal i) == opid)
        (fun vid j =>
           if getBy (fun x => (ibeg (intVal x) == opid) &&
                              (ivar (intVal x) == vid)) allocs
             is Some to_int
           then checkIntervalBoundary j to_int vid true
           else None) in
  let edgeTransitions :=
      findIntervals (opid <= assnBlockBeg assn)
        (fun i => (ibeg (intVal i) == opid) &&
                  (iend (intVal i) == opid))
        (fun vid j =>
           (Some (inr vid,
            if intReg j is Some reg
            then inl reg
            else inr vid))) in
  let startingTransitions :=
      findIntervals (assnBlockEnd assn <= opid)
        (fun i => ibeg (intVal i) == opid)
        (fun vid j =>
           if getBy (fun x => (iend (intVal x) == opid) &&
                               (ivar (intVal x) == vid)) allocs
             is Some from_int
           then checkIntervalBoundary from_int j vid true
           else None) in

  let generator k :=
      forFoldrM [::] k $ fun mx acc =>
        if mx is Some x
        then moves <-- generateMoves [:: (Some (fst x), Some (snd x))] ;;
             pure $ moves ++ acc
        else pure acc in

  closing <-- generator endingTransitions ;;
  edges   <-- generator edgeTransitions ;;
  opening <-- generator startingTransitions ;;

  let vars := opRefs oinfo op in
  let hereAllocs := concat $ map (varAllocs opid allocs) vars in
  let op' := applyAllocs oinfo op hereAllocs in

  (* With lenses, this would just be: assnOpId += 2 *)
  modify (fun assn' =>
            {| assnOpId     := opid.+2
             ; assnBlockBeg := assnBlockBeg assn'
             ; assnBlockEnd := assnBlockEnd assn'
             ; assnAcc      := assnAcc assn' |}) ;;

  pure $ closing ++ edges ++ opening ++ op'.

Definition resolveMappings bid opsm mappings : AssnState (seq opType2) :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some graphs then pure opsm else

  let: (gbeg, gend) := graphs in

  bmoves <-- generateMoves (topsort gbeg) ;;
  let opsm' := bmoves ++ opsm in

  emoves <-- generateMoves (topsort gend) ;;
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
