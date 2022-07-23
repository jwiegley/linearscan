Set Warnings "-notation-overridden".

Require Import LinearScan.Lib.
Require Import LinearScan.UsePos.
Require Import LinearScan.Blocks.
Require Import Hask.Control.Monad.State.
Require Import Hask.Control.Monad.

Open Scope seq_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.
Set Universe Polymorphism.

Record BlockLiveSets := {
  blockLiveGen   : IntSet;
  blockLiveKill  : IntSet;
  blockLiveIn    : IntSet;
  blockLiveOut   : IntSet;
  blockFirstOpId : OpId;
  blockLastOpId  : OpId
}.

Definition emptyBlockLiveSets : BlockLiveSets :=
  {| blockLiveGen   := emptyIntSet
   ; blockLiveKill  := emptyIntSet
   ; blockLiveIn    := emptyIntSet
   ; blockLiveOut   := emptyIntSet
   ; blockFirstOpId := 1
   ; blockLastOpId  := 1
   |}.

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

Definition _blockLiveGen :
  Lens' BlockLiveSets IntSet := fun _ _ f s =>
  fmap (fun x =>
    {| blockLiveGen   := x
     ; blockLiveKill  := blockLiveKill  s
     ; blockLiveIn    := blockLiveIn    s
     ; blockLiveOut   := blockLiveOut   s
     ; blockFirstOpId := blockFirstOpId s
     ; blockLastOpId  := blockLastOpId  s
     |}) (f (blockLiveGen s)).

Definition _blockLiveKill :
  Lens' BlockLiveSets IntSet := fun _ _ f s =>
  fmap (fun x =>
    {| blockLiveGen   := blockLiveGen   s
     ; blockLiveKill  := x
     ; blockLiveIn    := blockLiveIn    s
     ; blockLiveOut   := blockLiveOut   s
     ; blockFirstOpId := blockFirstOpId s
     ; blockLastOpId  := blockLastOpId  s
     |}) (f (blockLiveKill s)).

Definition _blockLiveIn :
  Lens' BlockLiveSets IntSet := fun _ _ f s =>
  fmap (fun x =>
    {| blockLiveGen   := blockLiveGen   s
     ; blockLiveKill  := blockLiveKill  s
     ; blockLiveIn    := x
     ; blockLiveOut   := blockLiveOut   s
     ; blockFirstOpId := blockFirstOpId s
     ; blockLastOpId  := blockLastOpId  s
     |}) (f (blockLiveIn s)).

Definition _blockLiveOut :
  Lens' BlockLiveSets IntSet := fun _ _ f s =>
  fmap (fun x =>
    {| blockLiveGen   := blockLiveGen   s
     ; blockLiveKill  := blockLiveKill  s
     ; blockLiveIn    := blockLiveIn    s
     ; blockLiveOut   := x
     ; blockFirstOpId := blockFirstOpId s
     ; blockLastOpId  := blockLastOpId  s
     |}) (f (blockLiveOut s)).

Definition _blockFirstOpId :
  Lens' BlockLiveSets OpId := fun _ _ f s =>
  fmap (fun x =>
    {| blockLiveGen   := blockLiveGen   s
     ; blockLiveKill  := blockLiveKill  s
     ; blockLiveIn    := blockLiveIn    s
     ; blockLiveOut   := blockLiveOut   s
     ; blockFirstOpId := x
     ; blockLastOpId  := blockLastOpId  s
     |}) (f (blockFirstOpId s)).

Definition _blockLastOpId :
  Lens' BlockLiveSets OpId := fun _ _ f s =>
  fmap (fun x =>
    {| blockLiveGen   := blockLiveGen   s
     ; blockLiveKill  := blockLiveKill  s
     ; blockLiveIn    := blockLiveIn    s
     ; blockLiveOut   := blockLiveOut   s
     ; blockFirstOpId := blockFirstOpId s
     ; blockLastOpId  := x
     |}) (f (blockLastOpId s)).

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg opType1 opType2.

Definition computeLiveSets b idx : State BlockLiveSets nat :=
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
  let: (opsb, opsm, opse) := blockOps binfo b in

  _blockFirstOpId .= (idx + (size opsb).*2) ;;
  _blockLastOpId  .= idx ;;

  forFoldM (H:=State_Monad) idx (opsb ++ opsm ++ opse) $ fun next o =>
    let: (inputs, others) :=
      partition (fun v => varKind v == Input) (opRefs oinfo o) in

    forM_ inputs (fun v =>
      if @varId maxReg v isn't inr vid then pure tt else
      liveKill <- use _blockLiveKill ;
      unless (IntSet_member vid liveKill)
        (_blockLiveGen %= IntSet_insert vid)) ;;

    forM_ others (fun v =>
      if @varId maxReg v isn't inr vid then pure tt else
      _blockLiveKill %= IntSet_insert vid) ;;

    _blockLastOpId .= next ;;

    pure next.+2.

Definition computeLocalLiveSets (blocks : seq blockType1) :
  IntMap BlockLiveSets :=
  @snd _ _ $ forFold (1, emptyIntMap) blocks $ fun acc b =>
    let: (idx, m) := acc in
    let (idx', liveSets) := computeLiveSets b idx emptyBlockLiveSets in
    let k := blockId binfo b in
    (idx', IntMap_insert k liveSets m).

Definition updateLiveSets (blockLiveSets : IntMap BlockLiveSets)
  (suxs : seq BlockId) : State BlockLiveSets unit :=
  (* do
       for each block b in blocks in reverse order do
         b.live_out = { }
         for each successor sux of b do
           b.live_out = b.live_out ∪ sux.live_in
         end for

         b.live_in = (b.live_out – b.live_kill) ∪ b.live_gen
       end for
     while change occurred in any live set *)
  _blockLiveOut .= emptyIntSet ;;

  forM_ suxs (fun s_bid =>
    if IntMap_lookup s_bid blockLiveSets is Some sux
    then _blockLiveOut %= flip IntSet_union (blockLiveIn sux)
    else pure tt) ;;

  (ls <- get ;
  _blockLiveIn .=
    IntSet_union (IntSet_difference (blockLiveOut ls)
                                    (blockLiveKill ls))
                 (blockLiveGen ls)).

Definition computeGlobalLiveSets (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : IntMap BlockLiveSets :=
  forFoldr liveSets blocks $ fun b liveSets1 =>
    let bid := blockId binfo b in
    match IntMap_lookup bid liveSets1 with
    | None => liveSets1
    | Some liveSet =>
        let suxs := blockSuccessors binfo b in
        let (_, liveSet') := updateLiveSets liveSets suxs liveSet in
        IntMap_insert bid liveSet' liveSets1
    end.

Definition computeGlobalLiveSetsRecursively (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : IntMap BlockLiveSets :=
  let fix go n previous :=
    if n isn't S n
    then pure previous
    else
      let computed := computeGlobalLiveSets blocks previous in
      if previous == computed
      then computed
      else go n computed in
  go (size blocks) liveSets.

End LiveSets.

Module VerifyLensLaws.

Include LensLaws.

#[export]
Program Instance Lens__blockLiveGen : LensLaws _blockLiveGen.
Obligation 2. by case: x. Qed.
#[export]
Program Instance Lens__blockLiveKill : LensLaws _blockLiveKill.
Obligation 2. by case: x. Qed.
#[export]
Program Instance Lens__blockLiveIn : LensLaws _blockLiveIn.
Obligation 2. by case: x. Qed.
#[export]
Program Instance Lens__blockLiveOut : LensLaws _blockLiveOut.
Obligation 2. by case: x. Qed.
#[export]
Program Instance Lens__blockFirstOpId : LensLaws _blockFirstOpId.
Obligation 2. by case: x. Qed.
#[export]
Program Instance Lens__blockLastOpId : LensLaws _blockLastOpId.
Obligation 2. by case: x. Qed.

End VerifyLensLaws.
