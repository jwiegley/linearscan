Require Import LinearScan.Lib.
Require Import LinearScan.Blocks.
Require Import LinearScan.Graph.
Require Import LinearScan.Interval.
Require Import LinearScan.IntMap.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Resolve.
Require Import LinearScan.ScanState.
Require Import LinearScan.State.
Require Import String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Trace.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

Close Scope string_scope.

Definition showOps1 (sd : ScanStateDesc maxReg) (startPos : nat)
  (ops : seq opType1) : string :=
  let fix go pos os :=
    if os isn't o :: os then EmptyString else
    let refs := opRefs oinfo o in
    let collectVarRefs p :=
      concat $ map (fun v =>
        let vid := varId v in
        if vid isn't inr vid then [::] else
        let k idx acc i :=
          if p vid i
          then (nat_of_ord idx, inr vid) :: acc
          else acc in
        vfoldl_with_index k [::] (intervals sd)) refs in
    let collectRegRefs p :=
      concat $ map (fun v =>
        let vid := varId v in
        if vid isn't inl vid then [::] else
        let k idx acc i :=
          if p vid i
          then (nat_of_ord idx, inl vid) :: acc
          else acc in
        vfoldl_with_index k [::] (fixedIntervals sd)) refs in
    let startingP vid i   := (ivar i.1 == vid) && (ibeg i.1 == pos.*2.+1) in
    let endingP vid i     := (ivar i.1 == vid) && (iend i.1 == pos.*2.+1) in
    let checkReg p vid mi := if mi isn't Some i then false else p vid i in
    let startingAtPos := collectVarRefs startingP ++
                         collectRegRefs (checkReg startingP) in
    let endingAtPos   := collectVarRefs endingP ++
                         collectRegRefs (checkReg endingP) in
    String.append
      (showOp1 oinfo pos.*2.+1 startingAtPos endingAtPos o)
      (go pos.+1 os) in
  go startPos ops.

Definition showBlocks1 (sd : ScanStateDesc maxReg)
  (liveSets : IntMap BlockLiveSets) (blocks : seq blockType1) :
  string :=
  let fix go pos bs :=
    if bs isn't b :: bs then EmptyString else
    let bid := blockId binfo b in
    let: (liveIn, liveOut) :=
       if IntMap_lookup bid liveSets isn't Some ls
       then (emptyIntSet, emptyIntSet)
       else (blockLiveIn ls, blockLiveOut ls) in
    String.append
      (showBlock1 binfo bid pos liveIn liveOut (showOps1 sd) b)
      (go (pos + blockSize binfo b) bs) in
  go 0 blocks.

Definition traceBlocksHere (sd : ScanStateDesc maxReg)
  (liveSets : IntMap BlockLiveSets) (blocks : seq blockType1) :
  seq blockType1 :=
  traceBlocks binfo (showBlocks1 sd liveSets blocks) blocks.

End Trace.
