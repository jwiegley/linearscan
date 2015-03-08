Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Resolve.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

Record LoopState := {
  activeBlocks     : IntSet;
  visitedBlocks    : IntSet;
  loopHeaderBlocks : seq BlockId;   (* loop index -> block id *)
  loopEndBlocks    : IntSet;
  forwardBranches  : IntMap IntSet; (* block id -> block ids *)
  backwardBranches : IntMap IntSet  (* block id -> block ids *)
}.

Definition emptyLoopState :=
  {| activeBlocks     := emptyIntSet
   ; visitedBlocks    := emptyIntSet
   ; loopHeaderBlocks := [::]
   ; loopEndBlocks    := emptyIntSet
   ; forwardBranches  := emptyIntMap
   ; backwardBranches := emptyIntMap |}.

Definition modifyActiveBlocks (f : IntSet -> IntSet) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := f (activeBlocks st)
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st |}.

Definition modifyVisitedBlocks (f : IntSet -> IntSet) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := f (visitedBlocks st)
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st |}.

Definition modifyLoopHeaderBlocks (f : seq BlockId -> seq BlockId) :
  State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := f (loopHeaderBlocks st)
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st |}.

Definition modifyLoopEndBlocks (f : IntSet -> IntSet) :
  State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := f (loopEndBlocks st)
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st |}.

Definition modifyForwardBranches
  (f : IntMap (IntSet) -> IntMap (IntSet)) :
  State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := f (forwardBranches st)
   ; backwardBranches := backwardBranches st |}.

Definition modifyBackwardBranches
  (f : IntMap (IntSet) -> IntMap (IntSet)) : State LoopState unit :=
  modify $ fun st =>
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := f (backwardBranches st) |}.

Definition remainingBlocks (bs : IntMap blockType1) (st : LoopState) : nat :=
  IntMap_size bs - IntSet_size (visitedBlocks st).

Definition addReference (i x : nat) :
  IntMap (IntSet) -> IntMap (IntSet) :=
  IntMap_alter (fun macc => if macc is Some acc
                            then Some (IntSet_insert x acc)
                            else Some (IntSet_singleton x)) i.

Definition findLoopEnds (bs : IntMap blockType1) : State LoopState unit :=
  let fix go n b :=
    if n isn't S n then pure tt else
    let bid := blockId binfo b in
    modifyVisitedBlocks (IntSet_insert bid) ;;
    modifyActiveBlocks (IntSet_insert bid) ;;
    forM_ (blockSuccessors binfo b) $ fun sux =>
      active <-- gets activeBlocks ;;
      (if IntSet_member sux active
       then
         modifyLoopHeaderBlocks (cons sux) ;;
         modifyLoopEndBlocks (IntSet_insert bid) ;;
         modifyBackwardBranches (addReference sux bid)
       else
         modifyForwardBranches (addReference sux bid)) ;;
      visited <-- gets visitedBlocks ;;
      (if IntSet_member sux visited
       then pure tt
       else if IntMap_lookup sux bs is Some x
            then go n x
            else pure tt) ;;
    modifyActiveBlocks (IntSet_delete bid) in
  if IntMap_toList bs is (_, b) :: _
  then go (IntMap_size bs) b
  else pure tt.

Fixpoint pathToLoopHeader  (b : BlockId) (st : LoopState) :
  option nat * IntSet :=
  let fix go fuel b :=
    if fuel isn't S n then (None, emptyIntSet) else
    let idx := find (fun x => x == b) (loopHeaderBlocks st) in
    if idx == size (loopHeaderBlocks st)
    then
      let preds :=
        if IntMap_lookup b (forwardBranches st) is Some predecessors
        then predecessors
        else emptyIntSet in
      forFold (None, IntSet_singleton b) (IntSet_toList preds) $ fun z pred =>
        let: (mx, xs) := z in
        let: (my, ys) := go n pred in
        (option_choose mx my, IntSet_union xs ys)
    else (Some idx, IntSet_singleton b) in
  go (IntSet_size (visitedBlocks st)) b.

(* Compute lowest loop index and the loop depth for each block.  If the block
   is not part of a loop, it will not be in the resulting [IntMap]. *)
Definition computeLoopDepths (st : LoopState) : IntMap (nat * nat) :=
  forFold emptyIntMap (IntSet_toList (loopEndBlocks st)) $ fun m endBlock =>
    let: (mloopIndex, path) := pathToLoopHeader endBlock st in
    if mloopIndex isn't Some loopIndex then m else
    forFold m (IntSet_toList path) $ fun m' blk =>
      let f mx :=
        if mx is Some (idx, depth)
        then Some (minn idx loopIndex, depth.+1)
        else Some (loopIndex, 1) in
      IntMap_alter f blk m'.

(* jww (2015-03-08): For every block I need to know the list of loop end
   blocks, for those loops of which it is a member.  This way I can accumulate
   a list of all the variables used in each loop, and create zero-length
   ranges with use positions that force these variables to be live at the end
   of the loop. *)

(* jww (2015-03-08): After loops have been computed, artificial use positions
   should be place at the end of the loop end blocks for any variables used
   within those loops. *)

Definition computeBlockOrder (blocks : seq blockType1) : seq blockType1 :=
  if blocks isn't b :: bs then [::] else

  let blockMap :=
    IntMap_fromList (map (fun x => (blockId binfo x, x)) blocks) in
  let: (_, st) := findLoopEnds blockMap emptyLoopState in
  let depths := computeLoopDepths st in

  (* jww (2015-03-08): This is a somewhat simplistic computation of weighting
     for each block. *)
  let lighter x y :=
    let x_id := blockId binfo x in
    let y_id := blockId binfo y in
    let x_depth := if IntMap_lookup x_id depths is Some (idx, depth)
                   then depth else 0 in
    let y_depth := if IntMap_lookup y_id depths is Some (idx, depth)
                   then depth else 0 in
    x_depth < y_depth in

  blocks.
  (* let fix go n branches blocks' work_list := *)
  (*   if n isn't S n then blocks' else *)
  (*   if work_list isn't w :: ws then blocks' else *)
  (*   let: (branches', ws') := *)
  (*     let bid := blockId binfo w in *)
  (*     let suxs := blockSuccessors binfo w in *)
  (*     forFold (branches, ws) suxs $ fun acc sux => *)
  (*       let: (branches', ws') := acc in *)
  (*       let insertion := if IntMap_lookup sux blockMap is Some s *)
  (*                        then insert lighter s ws' *)
  (*                        else ws' in *)
  (*       if IntMap_lookup sux branches' is Some incs *)
  (*       then (IntMap_insert sux (IntSet_delete bid incs) branches', *)
  (*             if IntSet_size incs == 1 then insertion else ws') *)
  (*       else (branches', insertion) in *)
  (*   go n branches' (w :: blocks') ws' in *)
  (* go (size blocks) (forwardBranches st) [::] [:: b]. *)

End Resolve.