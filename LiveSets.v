Require Import LinearScan.Lib.
Require Import LinearScan.Blocks.
Require Import LinearScan.IntMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Record BlockLiveSets := {
  blockLiveGen   : IntSet;
  blockLiveKill  : IntSet;
  blockLiveIn    : IntSet;
  blockLiveOut   : IntSet;
  blockFirstOpId : OpId;
  blockLastOpId  : OpId
}.

Section LiveSets.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

Definition computeLocalLiveSets (blocks : seq blockType1) :
  IntMap BlockLiveSets :=
  (* for each block b in blocks do
       b.live_gen  = { }
       b.live_kill = { }

       for each operation op in b.operations do
         visitor.visit(op)

         for each virtual register opr in visitor.input_oprs do
           if opr ∉ block.live_kill then
             b.live_gen = b.live_gen ∪ { opr }
         end for

         for each virtual register opr in visitor.temp_oprs do
           b.live_kill = b.live_kill ∪ { opr }
         end for

         for each virtual register opr in visitor.output_oprs do
           b.live_kill = b.live_kill ∪ { opr }
         end for
       end for
     end for *)
  @snd _ _ $
  forFold (1, emptyIntMap) blocks $ fun acc b =>
    let: (idx, m) := acc in
    let liveSet :=
        {| blockLiveGen   := emptyIntSet
         ; blockLiveKill  := emptyIntSet
         ; blockLiveIn    := emptyIntSet
         ; blockLiveOut   := emptyIntSet
         ; blockFirstOpId := idx
         ; blockLastOpId  := idx
         |} in
    let: (lastIdx', liveSet3) :=
      forFold (idx, liveSet) (blockOps binfo b) $ fun acc o =>
        let: (lastIdx, liveSet1) := acc in
        (lastIdx.+2,
         forFold liveSet1 (opRefs oinfo o) $ fun liveSet2 v =>
           let vid := varId v in
           if varKind v is Input
           then
             if ~~ (IntSet_member vid (blockLiveKill liveSet2))
             then {| blockLiveGen   := IntSet_insert vid (blockLiveGen liveSet2)
                   ; blockLiveKill  := blockLiveKill liveSet2
                   ; blockLiveIn    := blockLiveIn liveSet2
                   ; blockLiveOut   := blockLiveOut liveSet2
                   ; blockFirstOpId := blockFirstOpId liveSet2
                   ; blockLastOpId  := lastIdx
                   |}
             else liveSet2
           else
             {| blockLiveGen   := blockLiveGen liveSet2
              ; blockLiveKill  := IntSet_insert vid (blockLiveKill liveSet2)
              ; blockLiveIn    := blockLiveIn liveSet2
              ; blockLiveOut   := blockLiveOut liveSet2
              ; blockFirstOpId := blockFirstOpId liveSet2
              ; blockLastOpId  := lastIdx
              |})
      in
    (lastIdx', IntMap_insert (blockId binfo b) liveSet3 m).

Definition computeGlobalLiveSets (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : IntMap BlockLiveSets :=
  (* do
       for each block b in blocks in reverse order do
         b.live_out = { }
         for each successor sux of b do
           b.live_out = b.live_out ∪ sux.live_in
         end for

         b.live_in = (b.live_out – b.live_kill) ∪ b.live_gen
       end for
     while change occurred in any live set *)
  forFold liveSets (rev blocks) $ fun liveSets1 b =>
    let bid := blockId binfo b in
    match IntMap_lookup bid liveSets1 with
    | None => liveSets1         (* should never happen *)
    | Some liveSet =>
      let liveSet2 :=
        forFold liveSet (blockSuccessors binfo b) $ fun liveSet1 s_bid =>
          match IntMap_lookup s_bid liveSets1 with
          | None => liveSet1  (* should never happen *)
          | Some sux =>
            {| blockLiveGen   := blockLiveGen liveSet1
             ; blockLiveKill  := blockLiveKill liveSet1
             ; blockLiveIn    := blockLiveIn liveSet1
             ; blockLiveOut   := IntSet_union (blockLiveOut liveSet1)
                                              (blockLiveIn sux)
             ; blockFirstOpId := blockFirstOpId liveSet1
             ; blockLastOpId  := blockLastOpId liveSet1
             |}
          end
        in
      IntMap_insert bid
        {| blockLiveGen   := blockLiveGen liveSet2
         ; blockLiveKill  := blockLiveKill liveSet2
         ; blockLiveIn    :=
             IntSet_union (IntSet_difference (blockLiveOut liveSet2)
                                             (blockLiveKill liveSet2))
                          (blockLiveGen liveSet2)
         ; blockLiveOut   := blockLiveOut liveSet2
         ; blockFirstOpId := blockFirstOpId liveSet2
         ; blockLastOpId  := blockLastOpId liveSet2
         |} liveSets1
    end.

End LiveSets.