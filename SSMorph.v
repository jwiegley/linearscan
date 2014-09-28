Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import Fin.
Require Import Interval.
Require Import Lib.
Require Import ScanState.

Generalizable All Variables.

Module MSSMorph (M : Machine).
Include MScanState M.

(** ** SSMorph *)

(** A [SSMorph] is a relation describe a lawful transition between two
    states.  It is a [PreOrder] relation. *)

Record SSMorph (sd1 sd2 : ScanStateDesc) : Prop := {
    next_interval_increases : nextInterval sd1     <= nextInterval sd2;
    total_extent_decreases  : unhandledExtent sd2  <= unhandledExtent sd1;
    handled_count_increases : length (handled sd1) <= length (handled sd2)
}.

Arguments next_interval_increases [sd1 sd2] _.
Arguments total_extent_decreases  [sd1 sd2] _.
Arguments handled_count_increases [sd1 sd2] _.

Definition newSSMorph (s : ScanStateDesc) : SSMorph s s.
Proof. constructor; auto. Defined.

Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Defined.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity (nextInterval y); auto.
  transitivity (unhandledExtent y); auto.
  transitivity (length (handled y)); auto.
Defined.

Record SSMorphLen (sd1 sd2 : ScanStateDesc) : Prop := {
    len_is_SSMorph :> SSMorph sd1 sd2;

    unhandled_nonempty :
      length (unhandled sd1) > 0 -> length (unhandled sd2) > 0
}.

Definition newSSMorphLen (s : ScanStateDesc) : SSMorphLen s s.
Proof. intros. constructor; auto. constructor; auto. Defined.

Record SSMorphSt (sd1 sd2 : ScanStateDesc) : Prop := {
    st_is_SSMorph :> SSMorph sd1 sd2;

    total_extent_measurably_decreases :
      unhandledExtent sd2 < unhandledExtent sd1
}.

Program Instance SSMorphSt_Trans : Transitive SSMorphSt.
Obligation 1.
  constructor.
    destruct H. destruct H0.
    transitivity y; assumption.
  inversion H. inversion H0.
  destruct total_extent_measurably_decreases1. omega.
  destruct total_extent_measurably_decreases0. omega.
  right. omega.
Qed.

Record SSMorphStLen (sd1 sd2 : ScanStateDesc) : Prop := {
    stlen_is_SSMorphLen :> SSMorphLen sd1 sd2;
    stlen_is_SSMorphSt  :> SSMorphSt sd1 sd2
}.

Lemma ScanState_unhandledExtent_nonzero `(st : ScanState sd) :
  length (unhandled sd) > 0 <-> unhandledExtent sd > 0.
Proof.
  intros.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil".
    split; intros; inversion H.
  - Case "ScanState_newUnhandled".
    pose (Interval_extent_nonzero i).
    destruct unh eqn:Heqe;
    unfold unhandledExtent; simpl.
      split; intros; try cmp_reflexive; auto.
    destruct l eqn:Heqe2; simpl.
      split; intros; try cmp_reflexive; auto. omega.
    split; intros.
      apply fold_gt.
      cmp_reflexive. omega.
    apply Gt.gt_Sn_O.
  - Case "ScanState_moveUnhandledToActive".
    apply ScanState_unhandledExtent in st.
    rename st into i. simpl in *.
    destruct unh eqn:Heqe.
      split; intros. inversion H. auto.
    unfold unhandledExtent; simpl.
    destruct l eqn:Heqe2; simpl.
      split; intros.
      apply Interval_extent_nonzero.
      auto.
    split; intros.
      apply fold_gt.
      pose (Interval_extent_nonzero (proj2_sig (geti f))).
      omega.
    omega.
  - Case "ScanState_moveActiveToInactive".  apply IHst.
  - Case "ScanState_moveActiveToHandled".   apply IHst.
  - Case "ScanState_moveInactiveToActive".  apply IHst.
  - Case "ScanState_moveInactiveToHandled". apply IHst.
Qed.

Definition moveActiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (active sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveActiveToInactive sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveActiveToInactive `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (active sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveActiveToInactive sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveInactiveToActive `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveInactiveToActive sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveInactiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveInactiveToHandled sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
  apply Le.le_n_Sn.
Defined.

Definition moveUnhandledToActive `(cur : ScanStateCursor sd) (reg : PhysReg)
  : NextState cur SSMorphSt.
Proof.
  destruct cur. destruct sd.
  destruct unhandled0; simpl in *. omega.
  pose (ScanState_moveUnhandledToActive nextInterval0 unhandled0
          (* unhsort *)
          active0 inactive0 handled0 getInterval0 assignments0
          getFixedInterval0 i reg lists_are_unique0).
  eexists. apply s. apply curState0.
  pose (unhandledExtent_cons nextInterval0 i unhandled0 getInterval0
         (fun i0 : fin nextInterval0 =>
            if cmp_eq_dec i0 i
            then Some reg
            else assignments0 i0) assignments0 getFixedInterval0
         (i :: active0) active0 inactive0 inactive0 handled0 handled0
         (move_unhandled_to_active _ i unhandled0 active0 inactive0 handled0
            lists_are_unique0) lists_are_unique0)
    as ue_cons.
  rapply Build_SSMorphSt; auto.
  rapply Build_SSMorph; auto.
  apply (Lt.lt_le_weak _ _ ue_cons).
Defined.

End MSSMorph.