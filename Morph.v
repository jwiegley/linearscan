Require Import LinearScan.Lib.
Require Import LinearScan.IState.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Morph.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Open Scope nat_scope.

Inductive SSError : Set :=
  | ERegistersExhausted : nat -> SSError
  | ENoValidSplitPosition : nat -> SSError
  | ECannotSplitSingleton2 : nat -> IntervalDesc -> nat -> SSError
  | ECannotSplitSingleton3 : nat -> SSError
  | ECannotSplitSingleton4 : nat -> SSError
  | ECannotSplitSingleton5 : nat -> SSError
  | ECannotSplitSingleton6 : nat -> SSError
  | ECannotSplitSingleton7 : nat -> SSError
  | ECannotSplitSingleton8 : nat -> SSError
  | ENoIntervalsToSplit
  | ERegisterAlreadyAssigned : nat -> SSError
  | ERegisterAssignmentsOverlap : nat -> SSError
  | EFuelExhausted : SSError
  | EUnexpectedNoMoreUnhandled : SSError.

Definition stbind {P Q R a b}
  (f : (a -> IState SSError Q R b)) (x : IState SSError P Q a) :
  IState SSError P R b := @ijoin _ P Q R b (@imap _ P Q _ _ f x).

Definition error_ {I O X} err : IState SSError I O X :=
  fun (_ : I) => inl err.
Definition return_ {I O X} := @ipure I O X.

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
  IState SSError (SSInfo sd P) (SSInfo sd Q).

Definition withScanState {a pre} {P Q}
  (f : forall sd : ScanStateDesc maxReg, ScanState InUse sd
         -> SState pre P Q a) : SState pre P Q a :=
  stbind (fun i => f (thisDesc i) (thisState i)) (iget SSError).

Arguments withScanState {a pre P Q} f _.

Definition withScanStatePO {a pre P} `{PO : PreOrder _ P}
  (f : forall sd : ScanStateDesc maxReg, ScanState InUse sd
         -> SState sd P P a) : SState pre P P a.
Proof.
  intros i.
  destruct i.
  specialize (f thisDesc0 thisState0).
  assert (SSInfo thisDesc0 P).
    eapply {| thisDesc  := _
            ; thisHolds := _ |}.
  apply f in X.
  destruct X.
    apply (inl s).
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

Arguments withScanStatePO {a pre P _} f _.

Definition liftLen {pre a} :
  (forall sd : ScanStateDesc maxReg, SState sd SSMorphLen SSMorphLen a)
    -> SState pre SSMorphHasLen SSMorphHasLen a.
Proof.
  move=> f.
  move=> [sd [morphlen Hempty] st].
  pose ss := {| thisDesc  := sd
              ; thisHolds := newSSMorphLen sd
              ; thisState := st
              |}.
  case: (f sd ss) => [err|[x [sd' morphlen' st']]].
    exact: (inl err).
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

Definition weakenHasLen {pre} :
  forall sd, SSMorphHasLen pre sd -> SSMorph pre sd.
Proof. by move=> ? [[?]]. Defined.

Definition weakenHasLen_ {pre} :
  SState pre SSMorphHasLen SSMorph unit.
Proof.
  intros HS.
  apply inr.
  split. apply tt.
  destruct HS.
  apply: Build_SSInfo.
  - exact: thisDesc0.
  - exact: thisHolds0.
  - by [].
Defined.

Definition strengthenHasLen {pre} :
  forall sd, SSMorph pre sd -> option (SSMorphHasLen pre sd).
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
  intros.
  intro X.
  destruct X.
  destruct thisDesc0.
  destruct thisHolds0.
  destruct haslen_is_SSMorphLen0.
  destruct len_is_SSMorph0.
  destruct unhandled; first by [].
  destruct p.
  apply inr.
  split. apply tt.
  pose (ScanState_moveUnhandledToHandled thisState0).
  eapply {| thisState := s |}.
  Grab Existential Variables.
  apply Build_SSMorph; intuition.
Defined.

Definition moveUnhandledToActive {pre} (reg : PhysReg) :
  SState pre SSMorphHasLen SSMorph unit.
Proof.
  intros.
  intro X.
  destruct X.
  destruct thisDesc0.
  destruct thisHolds0.
  destruct haslen_is_SSMorphLen0.
  destruct len_is_SSMorph0.
  destruct unhandled; first by [].
  destruct p.
  case H: (reg \notin [seq snd i | i <- active]);
    last exact: (inl (ERegisterAlreadyAssigned reg)).
  apply inr.
  split. apply tt.
  pose (ScanState_moveUnhandledToActive thisState0 H).
  eapply {| thisState := s |}.
  Grab Existential Variables.
  apply Build_SSMorph; intuition.
Defined.

Definition moveActiveToHandled
  `(st : ScanState InUse sd) `(H: x \in active sd) :
  { sd' : ScanStateDesc maxReg | ScanState InUse sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToHandled st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

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
  `(H : x \in inactive sd) :
  { sd' : ScanStateDesc maxReg | ScanState InUse sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToHandled st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

End Morph.

Notation "m >>>= f" := (stbind f m) (at level 25, left associativity).

Notation "X <<- A ;; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

Notation "A ;;; B" := (_ <<- A ;; B)
  (right associativity, at level 84, A1 at next level).
