Require Import LinearScan.Lib.
Require Import LinearScan.Context.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Morph.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Open Scope nat_scope.

Inductive SSTrace : Set :=
  | ESplitAssignedIntervalForReg of nat    (* register *)
  | ESplitActiveOrInactiveInterval of bool (* true for active *)
  | EIntervalHasUsePosReqReg of nat
  | EIntervalBeginsAtSplitPosition
  | EMoveUnhandledToActive of nat          (* register *)
  | ESplitActiveIntervalForReg of nat      (* register *)
  | ESplitAnyInactiveIntervalForReg of nat (* register *)
  | ESpillInterval
  | ESpillCurrentInterval
  | ESplitUnhandledInterval
  | ESplitCurrentInterval of nat           (* split pos *)
  | ETryAllocateFreeReg of nat             (* interval id *)
  | EAllocateBlockedReg of nat             (* interval id *)
  | ERemoveUnhandledInterval of nat        (* interval id *)
  | ECannotInsertUnhandled
  | EIntervalBeginsBeforeUnhandled of nat
  | ENoValidSplitPosition of nat
  | ECannotSplitSingleton of nat
  | ERegisterAlreadyAssigned of nat
  | ERegisterAssignmentsOverlap of nat
  | EUnexpectedNoMoreUnhandled
  | ECannotSpillIfRegisterRequired of nat
  | EFuelExhausted
  | ENotYetImplemented of nat.

(** ** SSMorph *)

(** A [SSMorph] is a relation describe a lawful transition between two
    states.  It is a [PreOrder] relation. *)

Record SSMorph (sd1 sd2 : ScanStateDesc maxReg) : Prop := {
    next_interval_increases : nextInterval sd1 <= nextInterval sd2
}.

Arguments next_interval_increases [sd1 sd2] _.

Global Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  - exact: (leq_trans next_interval_increases0).
Qed.

Record SSMorphLen (sd1 sd2 : ScanStateDesc maxReg) : Prop := {
    len_is_SSMorph :> SSMorph sd1 sd2;

    unhandled_nonempty :
      size (unhandled sd1) > 0 -> size (unhandled sd2) > 0
}.

Global Program Instance SSMorphLen_PO : PreOrder SSMorphLen.
Obligation 1.
  unfold Reflexive. intros.
  constructor; auto; constructor; auto.
Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity y; assumption. auto.
Qed.

Definition newSSMorphLen (s : ScanStateDesc maxReg) : SSMorphLen s s.
Proof. intros. constructor; auto. constructor; auto. Defined.

Record SSMorphHasLen (sd1 sd2 : ScanStateDesc maxReg) : Prop := {
    haslen_is_SSMorphLen :> SSMorphLen sd1 sd2;

    first_nonempty : size (unhandled sd2) > 0
}.

Definition newSSMorphHasLen (sd : ScanStateDesc maxReg)
  (H : size (unhandled sd) > 0) : SSMorphHasLen sd sd.
Proof. repeat (constructor; auto). Defined.

Record SSInfo (startDesc : ScanStateDesc maxReg) P := {
    thisDesc  : ScanStateDesc maxReg;
    thisHolds : P startDesc thisDesc;
    thisState : ScanState InUse thisDesc
}.

Arguments thisDesc  {_ P} _.
Arguments thisHolds {_ P} _.
Arguments thisState {_ P} _.

Definition SState (sd : ScanStateDesc maxReg) P Q :=
  Context SSTrace (SSInfo sd P) (SSInfo sd Q).

Definition error_ {sd P Q a} err : SState sd P Q a := fun _ _ => inl err.

Definition conseqSState `(x : SState sd P2 Q2 a)
  `(f : forall a b, P1 a b -> P2 a b) `(g : forall a b, Q2 a b -> Q1 a b) :
  SState sd P1 Q1 a :=
  conseq x
    (fun p => match p with
       {| thisDesc  := desc
        ; thisHolds := holds
        ; thisState := state |} =>
       {| thisDesc  := desc
        ; thisHolds := f sd desc holds
        ; thisState := state |}
       end)
    (fun q => match q with
       {| thisDesc  := desc
        ; thisHolds := holds
        ; thisState := state |} =>
       {| thisDesc  := desc
        ; thisHolds := g sd desc holds
        ; thisState := state |}
       end).

Definition strengthenSState `(x : SState sd P2 Q a)
  `(f : forall a b, P1 a b -> P2 a b) : SState sd P1 Q a :=
  conseqSState x f (fun _ _ => id).

Definition weakenSState `(x : SState sd P Q2 a)
  `(g : forall a b, Q2 a b -> Q1 a b) : SState sd P Q1 a :=
  conseqSState x (fun _ _ => id) g.

Definition withScanState {a pre} {P Q}
  (f : forall sd : ScanStateDesc maxReg, ScanState InUse sd
         -> SState pre P Q a) : SState pre P Q a :=
  ibind (fun i => f (thisDesc i) (thisState i)) iget.

Arguments withScanState {a pre P Q} f _ _.

Definition withScanStatePO {a pre P} `{PO : PreOrder _ P}
  (f : forall sd : ScanStateDesc maxReg, ScanState InUse sd
         -> SState sd P P a) : SState pre P P a.
Proof.
  intros e i.
  destruct i.
  specialize (f thisDesc0 thisState0).
  assert (SSInfo thisDesc0 P).
    eapply {| thisDesc  := _
            ; thisHolds := _ |}.
  apply (f e) in X.
  destruct X as [err|p].
    apply (inl err).
  apply inr.
  destruct p.
  split. apply a0.
  destruct s.
  eexists.
  apply (transitivity thisHolds0 thisHolds1).
  assumption.
  Grab Existential Variables.
  apply thisState0.
  reflexivity.
Defined.

Arguments withScanStatePO {a pre P _} f _ _.

Definition liftLen {pre a} :
  (forall sd : ScanStateDesc maxReg, SState sd SSMorphLen SSMorphLen a)
    -> SState pre SSMorphHasLen SSMorphHasLen a.
Proof.
  move=> f.
  move=> e [sd [morphlen Hempty] st].
  pose ss := {| thisDesc  := sd
              ; thisHolds := newSSMorphLen sd
              ; thisState := st
              |}.
  case: (f sd e ss) => [err|[x [sd' morphlen' st']]].
    exact: inl err.
  apply: inr.
  split; first exact: x.
  apply: {| thisDesc  := sd'
          ; thisHolds := _
          ; thisState := st'
          |}.
  apply: Build_SSMorphHasLen.
    exact: (transitivity morphlen morphlen').
  case: morphlen' => [_ (* _ *) H].
  exact: H.
Defined.

Definition weakenHasLen {pre} : forall sd,
  SSMorphHasLen pre sd -> SSMorph pre sd.
Proof. by move=> ? [[?]]. Defined.

Definition weakenHasLen_ {pre} : SState pre SSMorphHasLen SSMorph unit.
Proof.
  intros e HS.
  apply inr.
  split. apply tt.
  destruct HS.
  apply: Build_SSInfo.
  - exact: thisHolds0.
  - by [].
Defined.

Definition strengthenHasLen {pre} : forall sd,
  SSMorph pre sd -> option (SSMorphHasLen pre sd).
Proof.
  move=> sd H.
  case E: (unhandled sd).
    exact: None.
  apply: Some _.
  constructor.
    constructor. exact.
    rewrite E /=. by [].
  rewrite E /=. by [].
Defined.

Definition moveUnhandledToHandled {pre} : SState pre SSMorphHasLen SSMorph unit.
Proof.
  intros e X.
  destruct X.
  destruct thisDesc0.
  destruct thisHolds0.
  destruct haslen_is_SSMorphLen0.
  destruct len_is_SSMorph0.
  destruct unhandled; first by [].
  destruct p.
  case E: (firstUseReqReg (vnth intervals i).2 == None);
    last exact: inl (ECannotSpillIfRegisterRequired i :: e).
  apply inr.
  split. apply tt.
  pose (ScanState_moveUnhandledToHandled thisState0 E).
  eapply {| thisState := s |}.
  Grab Existential Variables.
  apply Build_SSMorph; intuition.
Defined.

Definition moveUnhandledToActive {pre} (reg : PhysReg) :
  SState pre SSMorphHasLen SSMorph unit.
Proof.
  intros e X.
  destruct X.
  destruct thisDesc0.
  destruct thisHolds0.
  destruct haslen_is_SSMorphLen0.
  destruct len_is_SSMorph0.
  destruct unhandled; first by [].
  destruct p.
  case H: (reg \notin [seq snd i | i <- active]);
    last exact: inl (ERegisterAlreadyAssigned reg :: e).
  apply inr.
  split. apply tt.
  pose (ScanState_moveUnhandledToActive thisState0 H).
  eapply {| thisState := s |}.
  Grab Existential Variables.
  apply Build_SSMorph; intuition.
Defined.

Definition transportUnhandled (sd sd' : ScanStateDesc maxReg)
  (unh : seq (IntervalId sd * nat))
  (Heqe : nextInterval sd' = nextInterval sd) :
  seq (IntervalId sd' * nat).
Proof.
  elim: unh => [|[uid beg] us IHus].
    exact: [::].
  apply: cons.
    split.
      rewrite /IntervalId in uid *.
      by rewrite Heqe.
    exact: beg.
  exact: IHus.
Defined.

Definition moveActiveToHandled
  `(st : ScanState InUse sd) (spilled : bool) `(H: x \in active sd)
  (Hreq : if spilled
          then firstUseReqReg (getInterval (fst x)) == None
          else true) :
  { sd' : ScanStateDesc maxReg
  | ScanState InUse sd'
  & SSMorphLen sd sd' /\
    { H : nextInterval sd = nextInterval sd'
    | unhandled sd = transportUnhandled (unhandled sd') H } }.
Proof.
  pose (ScanState_moveActiveToHandled st H Hreq).
  eexists. apply s. simpl.
  split.
    apply Build_SSMorphLen; auto.
    apply Build_SSMorph; auto.
  exists refl_equal.
  elim: (unhandled sd) => //= [[uid beg] us IHus].
  by f_equal.
Defined.

Arguments moveActiveToHandled {sd} st spilled {x} H Hreq.

Definition moveActiveToInactive
  `(st : ScanState InUse sd) `(H: x \in active sd) :
  { sd' : ScanStateDesc maxReg | ScanState InUse sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Definition moveInactiveToActive
  `(st : ScanState InUse sd) `(H : x \in inactive sd)
  (Hreg : snd x \notin [seq snd i | i <- active sd]) :
  { sd' : ScanStateDesc maxReg | ScanState InUse sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToActive st H Hreg).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Lemma moveInactiveToActive_spec
  `(st : ScanState InUse sd) `(H : x \in inactive sd)
  (Hreg : snd x \notin [seq snd i | i <- active sd]) :
  let: exist2 sd' st' sslen' := moveInactiveToActive st H Hreg in
  nextInterval sd = nextInterval sd'.
Proof. reflexivity. Qed.

Definition moveInactiveToHandled `(st : ScanState InUse sd)
  (spilled : bool) `(H : x \in inactive sd)
  (Hreq : if spilled
          then firstUseReqReg (getInterval (fst x)) == None
          else true) :
  { sd' : ScanStateDesc maxReg
  | ScanState InUse sd'
  & SSMorphLen sd sd' /\
    { H : nextInterval sd = nextInterval sd'
    | unhandled sd = transportUnhandled (unhandled sd') H } }.
Proof.
  pose (ScanState_moveInactiveToHandled st H Hreq).
  eexists. apply s. simpl.
  split.
    apply Build_SSMorphLen; auto.
    apply Build_SSMorph; auto.
  exists refl_equal.
  elim: (unhandled sd) => //= [[uid beg] us IHus].
  by f_equal.
Defined.

Arguments moveInactiveToHandled {sd} st spilled {x} H Hreq.

End Morph.
