Require Import LinearScan.Lib.
Require Import Hask.Control.Monad.State.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Trans.State.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Resolve.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg opType1 opType2.

Record LoopState : Set := {
  activeBlocks     : IntSet;
  visitedBlocks    : IntSet;
  loopHeaderBlocks : seq BlockId;   (* loop index -> block id *)
  loopEndBlocks    : IntSet;
  forwardBranches  : IntMap IntSet; (* block id -> block ids *)
  backwardBranches : IntMap IntSet; (* block id -> block ids *)
  loopIndices      : IntMap IntSet;
  loopDepths       : IntMap (nat * nat)
}.

Definition emptyLoopState :=
  {| activeBlocks     := emptyIntSet
   ; visitedBlocks    := emptyIntSet
   ; loopHeaderBlocks := [::]
   ; loopEndBlocks    := emptyIntSet
   ; forwardBranches  := emptyIntMap
   ; backwardBranches := emptyIntMap
   ; loopIndices      := emptyIntMap
   ; loopDepths       := emptyIntMap |}.

Definition modifyActiveBlocks (f : IntSet -> IntSet) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := f (activeBlocks st)
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopIndices      := loopIndices st
   ; loopDepths       := loopDepths st |}.

Definition modifyVisitedBlocks (f : IntSet -> IntSet) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := f (visitedBlocks st)
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopIndices      := loopIndices st
   ; loopDepths       := loopDepths st |}.

Definition modifyLoopHeaderBlocks (f : seq BlockId -> seq BlockId) :
  State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := f (loopHeaderBlocks st)
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopIndices      := loopIndices st
   ; loopDepths       := loopDepths st |}.

Definition modifyLoopEndBlocks (f : IntSet -> IntSet) :
  State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := f (loopEndBlocks st)
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopIndices      := loopIndices st
   ; loopDepths       := loopDepths st |}.

Definition modifyForwardBranches
  (f : IntMap (IntSet) -> IntMap (IntSet)) :
  State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := f (forwardBranches st)
   ; backwardBranches := backwardBranches st
   ; loopIndices      := loopIndices st
   ; loopDepths       := loopDepths st |}.

Definition modifyBackwardBranches
  (f : IntMap (IntSet) -> IntMap (IntSet)) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := f (backwardBranches st)
   ; loopIndices      := loopIndices st
   ; loopDepths       := loopDepths st |}.

Definition setLoopIndices (indices : IntMap IntSet) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopIndices      := indices
   ; loopDepths       := loopDepths st |}.

Definition setLoopDepths (depths : IntMap (nat * nat)) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopIndices      := loopIndices st
   ; loopDepths       := depths |}.

Definition addReference (i x : nat) :
  IntMap IntSet -> IntMap IntSet :=
  IntMap_alter (fun macc => if macc is Some acc
                            then Some (IntSet_insert x acc)
                            else Some (IntSet_singleton x)) i.

Definition pathToLoopHeader  (blk : BlockId) (header : nat) (st : LoopState) :
  option IntSet :=
  let fix go fuel visited b :=
    if fuel isn't S n then (visited, None) else
    let visited' := IntSet_insert b visited in
    let forwardPreds :=
      if IntMap_lookup b (forwardBranches st) is Some preds
      then IntSet_toList preds
      else [::] in
    let backwardPreds :=
      if IntMap_lookup b (backwardBranches st) is Some preds
      then IntSet_toList preds
      else [::] in
    let preds := forwardPreds ++ backwardPreds in
    forFold (visited', Some (IntSet_singleton b)) preds $ fun mxs pred =>
      if mxs isn't (vis, Some xs) then mxs else
      if pred == header
      then
        (vis, Some (IntSet_union xs (IntSet_singleton pred)))
      else
        if IntSet_member pred vis then (vis, Some xs) else
        if go n vis pred is (vis', Some ys)
        then (vis', Some (IntSet_union xs ys))
        else (vis, None) in
  snd (go (IntSet_size (visitedBlocks st)) emptyIntSet blk).

(* Compute lowest loop index and the loop depth for each block.  If the block
   is not part of a loop, it will not be in the resulting [IntMap]. *)
Definition computeLoopDepths (bs : IntMap blockType1) :
  StateT LoopState mType unit :=
  st <-- getT ;;
  m <-- lift $ forFoldM emptyIntMap (IntSet_toList (loopEndBlocks st))
    (fun m endBlock =>
      if IntMap_lookup endBlock bs isn't Some b
      then pure m
      else
        suxs <-- blockSuccessors binfo b ;;
        pure $ forFold m suxs $ fun m' sux =>
          let headers   := loopHeaderBlocks st in
          let loopIndex := find (fun x => x == sux) headers in
          if loopIndex == size headers then m' else

          let mres := pathToLoopHeader endBlock sux st in
          if mres isn't Some path then m' else

          forFold m' (IntSet_toList path) $ fun m'' blk =>
            addReference loopIndex blk m'') ;;
  let f acc loopIndex refs :=
    IntSet_forFold acc refs $ fun m' blk =>
        let f mx :=
          if mx is Some (idx, depth)
          then Some (minn idx loopIndex, depth.+1)
          else Some (loopIndex, 1) in
        IntMap_alter f blk m' in
  liftStateT
    (setLoopIndices m ;;
     setLoopDepths (IntMap_foldlWithKey f emptyIntMap m)).

(* Determine all of the variables which are referenced within any loop, and
   collect them into sets associated with each loop end block, since they will
   be inserted as zero-length ranges making reference to each of those
   variables. *)
Definition computeVarReferences (bs : seq blockType1) (st : LoopState) :
  mType (IntMap IntSet) :=
  forFoldM emptyIntMap bs $ fun acc b =>
    bid <-- blockId binfo b ;;
    let g acc1 loopIndex blks :=
      if ~~ IntSet_member bid blks then acc1 else
      let: (xs, ys, zs) := blockOps binfo b in
      forFold acc1 (xs ++ ys ++ zs) $ fun acc2 op =>
        forFold acc2 (opRefs oinfo op) $ fun acc3 v =>
          if varId v isn't inr vid then acc3 else
          addReference loopIndex vid acc3 in
    pure $ IntMap_foldlWithKey g acc (loopIndices st).

Definition findLoopEnds (bs : IntMap blockType1) :
  StateT LoopState mType unit :=
  let fix go n b :=
    if n isn't S n then pure tt else
    bid <-- lift $ blockId binfo b ;;
    liftStateT
      (modifyVisitedBlocks (IntSet_insert bid) ;;
       modifyActiveBlocks (IntSet_insert bid)) ;;
    suxs <-- lift $ blockSuccessors binfo b ;;
    (forM_ suxs $ fun sux =>
      active <-- getsT activeBlocks ;;
      liftStateT
        (if IntSet_member sux active
         then
           modifyLoopHeaderBlocks
             (fun l => if sux \notin l then sux :: l else l) ;;
           modifyLoopEndBlocks (IntSet_insert bid) ;;
           modifyBackwardBranches (addReference sux bid)
         else
           modifyForwardBranches (addReference sux bid)) ;;
      visited <-- getsT visitedBlocks ;;
      (if IntSet_member sux visited
       then pure tt
       else if IntMap_lookup sux bs is Some x
            then go n x
            else pure tt)) ;;
    liftStateT (modifyActiveBlocks (IntSet_delete bid)) in
  if IntMap_toList bs is (_, b) :: _
  then go (IntMap_size bs) b
  else pure tt.

Definition computeBlockOrder (blocks : seq blockType1) :
  mType (LoopState * seq blockType1) :=
  if blocks isn't b :: bs then pure (emptyLoopState, [::]) else

  keys <-- mapM (fun x => bid <-- blockId binfo x ;;
                          pure (bid, x)) blocks ;;
  let blockMap := IntMap_fromList keys in
  z <-- findLoopEnds blockMap emptyLoopState ;;
  let: (_, st0) := z in

  (* Every branch from a block with multiple successors to a block with *)
  (* multiple predecessors is a "critical edge".  We insert a new, anonymous *)
  (* block at this edge to hold the resolving moves for the critical edge. *)
  blocks' <--
    forFoldrM [::] blocks (fun b rest =>
      suxs <-- blockSuccessors binfo b ;;
      if size suxs <= 1
      then pure $ b :: rest
      else (fun x => let: (b', rest') := x in b' :: rest') <$>
        forFoldrM (b, rest) suxs (fun sux x =>
          let: (b', rest') := x in
          let fsz := if IntMap_lookup sux (forwardBranches st0) is Some fwds
                     then IntSet_size fwds else 0 in
          let bsz := if IntMap_lookup sux (backwardBranches st0) is Some bwds
                     then IntSet_size bwds else 0 in
          if fsz + bsz <= 1
          then pure (b', rest')
          else
            if IntMap_lookup sux blockMap is Some sux'
            then z <-- splitCriticalEdge binfo b' sux' ;;
                 let: (b'', sux'') := z in
                 pure (b'', sux'' :: rest')
            else pure (b', rest'))) ;;
  keys' <-- mapM (fun x => bid <-- blockId binfo x ;;
                           pure (bid, x)) blocks' ;;
  let blockMap' := IntMap_fromList keys' in
  z' <-- findLoopEnds blockMap' emptyLoopState ;;
  let: (_, st1) := z' in
  if blocks' isn't b' :: bs' then pure (emptyLoopState, [::]) else
  w <-- computeLoopDepths blockMap st1 ;;
  let: (_, st2) := w in

  (* jww (2015-03-08): This is a somewhat simplistic computation of weighting *)
  (*    for each block. *)
  let isHeavier x y :=
    x_id <-- blockId binfo x ;;
    y_id <-- blockId binfo y ;;
    let x_depth := if IntMap_lookup x_id (loopDepths st2) is Some (idx, depth)
                   then depth else 0 in
    let y_depth := if IntMap_lookup y_id (loopDepths st2) is Some (idx, depth)
                   then depth else 0 in
    pure (x_depth > y_depth) in

  let fix go n branches work_list :=
    if n isn't S n then pure [::] else
    if work_list isn't w :: ws then pure [::] else
    bid  <-- blockId binfo w ;;
    suxs <-- blockSuccessors binfo w ;;
    x <--
      forFoldM (branches, ws) suxs (fun acc sux =>
        let: (branches', ws') := acc in
        insertion <--
          (if IntMap_lookup sux blockMap' is Some s
           then insertM isHeavier s ws'
           else pure ws') ;;
        pure
          (if IntMap_lookup sux branches' is Some incs
           then (IntMap_insert sux (IntSet_delete bid incs) branches',
                 if IntSet_size incs == 1 then insertion else ws')
           else (branches', insertion))) ;;
    let: (branches', ws') := x in
    cons w <$> go n branches' ws' in
  res <-- go (size blocks') (forwardBranches st2) [:: b'] ;;
  pure (st2, res).

End Resolve.