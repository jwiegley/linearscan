Require Import LinearScan.Lib.
Require Import LinearScan.UsePos.
Require Import LinearScan.Blocks.

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

Section EqBlockLiveSets.

Variable a : eqType.

Definition eqBlockLiveSets (s1 s2 : BlockLiveSets) :=
  match s1, s2 with
  | {| blockLiveGen   := lg1
     ; blockLiveKill  := lk1
     ; blockLiveIn    := li1
     ; blockLiveOut   := lo1
     ; blockFirstOpId := fi1
     ; blockLastOpId  := la1
     |},
    {| blockLiveGen   := lg2
     ; blockLiveKill  := lk2
     ; blockLiveIn    := li2
     ; blockLiveOut   := lo2
     ; blockFirstOpId := fi2
     ; blockLastOpId  := la2
     |} =>
    [&& lg1 == lg2
    ,   lk1 == lk2
    ,   li1 == li2
    ,   lo1 == lo2
    ,   fi1 == fi2
    &   la1 == la2 ]
  end.

Lemma eqBlockLiveSetsP : Equality.axiom eqBlockLiveSets.
Proof.
  move.
  case=> [lg1 lk1 li1 lo1 fi1 la1].
  case=> [lg2 lk2 li2 lo2 fi2 la2] /=.
  case: (lg1 =P lg2) => [<-|neqx]; last by right; case.
  case: (lk1 =P lk2) => [<-|neqx]; last by right; case.
  case: (li1 =P li2) => [<-|neqx]; last by right; case.
  case: (lo1 =P lo2) => [<-|neqx]; last by right; case.
  case: (fi1 =P fi2) => [<-|neqx]; last by right; case.
  case: (la1 =P la2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical BlockLiveSets_eqMixin := EqMixin eqBlockLiveSetsP.
Canonical BlockLiveSets_eqType :=
  Eval hnf in EqType BlockLiveSets BlockLiveSets_eqMixin.

End EqBlockLiveSets.

Section LiveSets.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg opType1 opType2.

Definition computeLocalLiveSets (blocks : seq blockType1) :
  mType (IntMap BlockLiveSets) :=
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
  @snd _ _ <$> forFoldM (1, emptyIntMap) blocks (fun acc b =>
    let: (idx, m) := acc in
    let: (opsb, opsm, opse) := blockOps binfo b in
    let liveSet :=
        {| blockLiveGen   := emptyIntSet
         ; blockLiveKill  := emptyIntSet
         ; blockLiveIn    := emptyIntSet
         ; blockLiveOut   := emptyIntSet
         ; blockFirstOpId := idx + (size opsb).*2
         ; blockLastOpId  := idx
         |} in
    let: (lastIdx', liveSet3) :=
      forFold (idx, liveSet) (opsb ++ opsm ++ opse) $ fun acc o =>
        let: (lastIdx, liveSet1) := acc in
        (lastIdx.+2,
         let: (inputs, others) :=
            partition (fun v => varKind v == Input) (opRefs oinfo o) in
         let liveSet2 :=
           forFold liveSet1 inputs $ fun liveSet2 v =>
             if @varId maxReg v isn't inr vid then liveSet2 else
             if ~~ (IntSet_member vid (blockLiveKill liveSet2))
             then {| blockLiveGen   := IntSet_insert vid (blockLiveGen liveSet2)
                   ; blockLiveKill  := blockLiveKill liveSet2
                   ; blockLiveIn    := blockLiveIn liveSet2
                   ; blockLiveOut   := blockLiveOut liveSet2
                   ; blockFirstOpId := blockFirstOpId liveSet2
                   ; blockLastOpId  := lastIdx
                   |}
             else liveSet2 in
         let liveSet3 :=
           forFold liveSet2 others $ fun liveSet3 v =>
             if @varId maxReg v isn't inr vid then liveSet3 else
             {| blockLiveGen   := blockLiveGen liveSet3
              ; blockLiveKill  := IntSet_insert vid (blockLiveKill liveSet3)
              ; blockLiveIn    := blockLiveIn liveSet3
              ; blockLiveOut   := blockLiveOut liveSet3
              ; blockFirstOpId := blockFirstOpId liveSet3
              ; blockLastOpId  := lastIdx
              |} in
         {| blockLiveGen   := blockLiveGen liveSet3
          ; blockLiveKill  := blockLiveKill liveSet3
          ; blockLiveIn    := blockLiveIn liveSet3
          ; blockLiveOut   := blockLiveOut liveSet3
          ; blockFirstOpId := blockFirstOpId liveSet3
          ; blockLastOpId  := lastIdx
          |})
      in
    k <-- blockId binfo b ;;
    pure (lastIdx', IntMap_insert k liveSet3 m)).

Definition computeGlobalLiveSets (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : mType (IntMap BlockLiveSets) :=
  (* do
       for each block b in blocks in reverse order do
         b.live_out = { }
         for each successor sux of b do
           b.live_out = b.live_out ∪ sux.live_in
         end for

         b.live_in = (b.live_out – b.live_kill) ∪ b.live_gen
       end for
     while change occurred in any live set *)
  forFoldrM liveSets blocks $ fun b liveSets1 =>
    bid <-- blockId binfo b ;;
    match IntMap_lookup bid liveSets1 with
    | None => pure liveSets1    (* jww (2015-02-14): should never happen *)
    | Some liveSet =>
      suxs <-- blockSuccessors binfo b ;;
      let liveSet1' :=
          {| blockLiveGen   := blockLiveGen liveSet
           ; blockLiveKill  := blockLiveKill liveSet
           ; blockLiveIn    := blockLiveIn liveSet
           ; blockLiveOut   := emptyIntSet
           ; blockFirstOpId := blockFirstOpId liveSet
           ; blockLastOpId  := blockLastOpId liveSet
           |} in
      let liveSet2 := forFold liveSet1' suxs $ fun liveSet2 s_bid =>
          match IntMap_lookup s_bid liveSets1 with
          | None => liveSet2  (* jww (2015-02-14): should never happen *)
          | Some sux =>
            {| blockLiveGen   := blockLiveGen liveSet2
             ; blockLiveKill  := blockLiveKill liveSet2
             ; blockLiveIn    := blockLiveIn liveSet2
             ; blockLiveOut   := IntSet_union (blockLiveOut liveSet2)
                                              (blockLiveIn sux)
             ; blockFirstOpId := blockFirstOpId liveSet2
             ; blockLastOpId  := blockLastOpId liveSet2
             |}
          end
        in
      pure $ IntMap_insert bid
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

Definition computeGlobalLiveSetsRecursively (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : mType (IntMap BlockLiveSets) :=
  let fix go n previous :=
    if n isn't S n
    then pure previous
    else
      computed <-- computeGlobalLiveSets blocks previous ;;
      if previous == computed
      then pure computed
      else go n computed in
  go (size blocks) liveSets.

End LiveSets.