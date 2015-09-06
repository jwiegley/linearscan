Require Import LinearScan.Lib.
Require Import LinearScan.Context.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.
Require Export LinearScan.Trace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Morph.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Open Scope nat_scope.

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

Record SSInfo P := {
    thisDesc  : ScanStateDesc maxReg;
    thisHolds : P thisDesc;
    thisState : ScanState InUse thisDesc
}.

Arguments thisDesc  {P} _.
Arguments thisHolds {P} _.
Arguments thisState {P} _.

Definition SState (sd : ScanStateDesc maxReg) P Q :=
  Context SSTrace (SSInfo (P sd)) (SSInfo (Q sd)).

Definition error_ {sd P Q a} err : SState sd P Q a := fun _ _ => inl err.

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
  assert (SSInfo (P thisDesc0)).
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
  case E: (firstUseReqReg (vnth intervals i).2 == None); last first.
    exact: inl (ECannotSpillIfRegisterRequired i :: e).
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
  (Hreq : let int := vnth (intervals sd) (fst x) in
          if spilled
          then firstUseReqReg int.2 == Nothing
          else verifyNewHandled sd int.1 (snd x)) :
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

Theorem moveInactiveToActive_spec
  `(st : ScanState InUse sd) `(H : x \in inactive sd)
  (Hreg : snd x \notin [seq snd i | i <- active sd]) :
  let: exist2 sd' st' sslen' := moveInactiveToActive st H Hreg in
  nextInterval sd = nextInterval sd'.
Proof. reflexivity. Qed.

Definition moveInactiveToHandled `(st : ScanState InUse sd)
  (spilled : bool) `(H : x \in inactive sd)
  (Hreq : let int := vnth (intervals sd) (fst x) in
          if spilled
          then firstUseReqReg int.2 == Nothing
          else verifyNewHandled sd int.1 (snd x)) :
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
