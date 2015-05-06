Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Resolve.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Set -> Set.
Context `{mDict : Monad mType}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg opType1 opType2.

Record LoopState := {
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

Definition remainingBlocks (bs : IntMap blockType1) (st : LoopState) : nat :=
  IntMap_size bs - IntSet_size (visitedBlocks st).

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
Definition computeLoopDepths (bs : IntMap blockType1) : State LoopState unit :=
  st <-- get ;;
  let m :=
    forFold emptyIntMap (IntSet_toList (loopEndBlocks st)) $ fun m endBlock =>
      if IntMap_lookup endBlock bs isn't Some b then m else
      forFold m (blockSuccessors binfo b) $ fun m' sux =>
        let headers := loopHeaderBlocks st in
        let loopIndex := find (fun x => x == sux) headers in
        if loopIndex == size headers then m' else

        let mres := pathToLoopHeader endBlock sux st in
        if mres isn't Some path then m' else

        forFold m' (IntSet_toList path) $ fun m'' blk =>
          addReference loopIndex blk m'' in
  let f acc loopIndex refs :=
    IntSet_forFold acc refs $ fun m' blk =>
        let f mx :=
          if mx is Some (idx, depth)
          then Some (minn idx loopIndex, depth.+1)
          else Some (loopIndex, 1) in
        IntMap_alter f blk m' in
  setLoopIndices m ;;
  setLoopDepths (IntMap_foldlWithKey f emptyIntMap m).

(* Determine all of the variables which are referenced within any loop, and
   collect them into sets associated with each loop end block, since they will
   be inserted as zero-length ranges making reference to each of those
   variables. *)
Definition computeVarReferences (bs : seq blockType1) (st : LoopState) :
  IntMap IntSet :=
  forFold emptyIntMap bs $ fun acc b =>
    let bid := blockId binfo b in
    let g acc1 loopIndex blks :=
      if ~~ IntSet_member bid blks then acc1 else
      let: (xs, ys, zs) := blockOps binfo b in
      forFold acc1 (xs ++ ys ++ zs) $ fun acc2 op =>
        forFold acc2 (opRefs oinfo op) $ fun acc3 v =>
          if varId v isn't inr vid then acc3 else
          addReference loopIndex vid acc3 in
    IntMap_foldlWithKey g acc (loopIndices st).

Definition findLoopEnds (bs : IntMap blockType1) : State LoopState unit :=
  let fix go n b :=
    if n isn't S n then pure tt else
    let bid := blockId binfo b in
    modifyVisitedBlocks (IntSet_insert bid) ;;
    modifyActiveBlocks (IntSet_insert bid) ;;
    (forM_ (blockSuccessors binfo b) $ fun sux =>
      active <-- gets activeBlocks ;;
      (if IntSet_member sux active
       then
         modifyLoopHeaderBlocks (fun l => if sux \notin l
                                          then sux :: l
                                          else l) ;;
         modifyLoopEndBlocks (IntSet_insert bid) ;;
         modifyBackwardBranches (addReference sux bid)
       else
         modifyForwardBranches (addReference sux bid)) ;;
      visited <-- gets visitedBlocks ;;
      (if IntSet_member sux visited
       then pure tt
       else if IntMap_lookup sux bs is Some x
            then go n x
            else pure tt)) ;;
    modifyActiveBlocks (IntSet_delete bid) in
  if IntMap_toList bs is (_, b) :: _
  then go (IntMap_size bs) b
  else pure tt.

Definition computeBlockOrder (blocks : seq blockType1) :
  mType (LoopState * seq blockType1) :=
  if blocks isn't b :: bs then pure (emptyLoopState, [::]) else

  let blockMap :=
    IntMap_fromList (map (fun x => (blockId binfo x, x)) blocks) in
  let: (_, st0) := findLoopEnds blockMap emptyLoopState in

  (* Every branch from a block with multiple successors to a block with *)
  (* multiple predecessors is a "critical edge".  We insert a new, anonymous *)
  (* block at this edge to hold the resolving moves for the critical edge. *)
  blocks' <--
    forFoldrM [::] blocks (fun b rest =>
      let suxs := blockSuccessors binfo b in
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
  let blockMap' :=
    IntMap_fromList (map (fun x => (blockId binfo x, x)) blocks') in
  let: (_, st1) := findLoopEnds blockMap' emptyLoopState in
  if blocks' isn't b' :: bs' then pure (emptyLoopState, [::]) else
  let: (_, st2)  := computeLoopDepths blockMap st1 in

  (* jww (2015-03-08): This is a somewhat simplistic computation of weighting *)
  (*    for each block. *)
  let isHeavier x y :=
    let x_id := blockId binfo x in
    let y_id := blockId binfo y in
    let x_depth := if IntMap_lookup x_id (loopDepths st2) is Some (idx, depth)
                   then depth else 0 in
    let y_depth := if IntMap_lookup y_id (loopDepths st2) is Some (idx, depth)
                   then depth else 0 in
    x_depth > y_depth in

  let fix go n branches work_list :=
    if n isn't S n then [::] else
    if work_list isn't w :: ws then [::] else
    let: (branches', ws') :=
      let bid := blockId binfo w in
      let suxs := blockSuccessors binfo w in
      forFold (branches, ws) suxs $ fun acc sux =>
        let: (branches', ws') := acc in
        let insertion := if IntMap_lookup sux blockMap' is Some s
                         then insert isHeavier s ws'
                         else ws' in
        if IntMap_lookup sux branches' is Some incs
        then (IntMap_insert sux (IntSet_delete bid incs) branches',
              if IntSet_size incs == 1 then insertion else ws')
        else (branches', insertion) in
    w :: go n branches' ws' in
  pure (st2, go (size blocks') (forwardBranches st2) [:: b']).

End Resolve.