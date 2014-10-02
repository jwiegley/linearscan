Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import Fin.
Require Import Interval.
Require Import Lib.
Require Import ScanState.
Require Import Hask.IEndo.
Require Import Hask.IApplicative.
Require Import Hask.IMonad.
Require Import Hask.IState.

Generalizable All Variables.

Open Scope nat_scope.
Open Scope program_scope.

Module MSSMorph (M : Machine).
Include MScanState M.

Record SSInfo (H : ScanStateDesc -> Prop) (P : relation ScanStateDesc) := {
    startDesc  : ScanStateDesc;
    startHolds : H startDesc;
    thisDesc   : ScanStateDesc;
    thisHolds  : P startDesc thisDesc;
    thisState  : ScanState thisDesc
}.

Arguments startDesc {H P} _.
Arguments thisDesc  {H P} _.
Arguments thisHolds {H P} _.
Arguments thisState {H P} _.

Definition SState (J K : ScanStateDesc -> Prop) (P Q : relation ScanStateDesc) :=
  IState (SSInfo J P) (SSInfo K Q).

(* Definition withCursor {P Q a} `{PreOrder _ P} *)
(*   (f : forall sd : ScanStateDesc, ScanStateCursor sd -> SState P Q a) : SState P Q a := *)
(*   rgets (fun s => exist _ (thisDesc s) (thisCursor s)) *)
(*     >>= uncurry_sig f. *)

Definition withScanState {J K P Q a}
  (f : forall sd : ScanStateDesc, ScanState sd -> SState J K P Q a)
  : SState J K P Q a :=
  iget >>>= fun i => f (thisDesc i) (thisState i).

(** Given an non-monadic function that returns a [NextScanState], absorb it
    into the indexed monad appropriately. *)

(*
Definition step {H P} `{Transitive _ P} `(st : ScanState sd)
  (n : NextScanState (P sd)) : SState H H P P unit.
Proof.
  constructor. intros i.
  split. apply tt.
  destruct i.
  destruct n.
  subst.
  rapply Build_SSInfo.
  apply startHolds0.
  transitivity thisDesc0.
    assumption.
  apply morphProof0.
  assumption.
Defined.
*)

(* Arguments cursor {P a} f. *)
Arguments withScanState {J K P Q a} f.
(* Arguments step {H P _} f. *)

Definition stbind {P Q R a b}
  (f : (a -> IState Q R b)) (x : IState P Q a) : IState P R b :=
  @ijoin IState _ P Q R b (@imap _ _ P Q _ _ f x).

Notation "m >>>= f" := (stbind f m) (at level 25, left associativity).

(* Notation "x <- c1 ;; c2" := (@ibind _ _ _ _ _ c1 (fun x => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "X <<- A ; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

(* Notation "x : a <== c1 ;; c2" := (@ibind _ _ _ _ _ c1 (fun x : a => c2)) *)
(*   (at level 100, c1 at next level, right associativity). *)

Notation "A ;;; B" := (_ <<- A ; B)
  (right associativity, at level 84, A1 at next level).

Definition return_ {I X} := @ipure IState _ I X.

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
Obligation 1. constructor; auto. Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity (nextInterval y); auto.
  transitivity (unhandledExtent y); auto.
  transitivity (length (handled y)); auto.
Qed.

Record > SSMorphSt (sd1 sd2 : ScanStateDesc) : Prop := {
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

Program Instance SSMorphSt_SO : StrictOrder SSMorphSt.
Obligation 1.
  unfold Irreflexive. reduce_goal. inversion H. omega.
Qed.

Record SSMorphLen (sd1 sd2 : ScanStateDesc) : Prop := {
    len_is_SSMorph :> SSMorph sd1 sd2;

    unhandled_nonempty :
      length (unhandled sd1) > 0 -> length (unhandled sd2) > 0
}.

Program Instance SSMorphLen_Trans : Transitive SSMorphLen.
Obligation 1.
  constructor.
    destruct H. destruct H0.
    transitivity y; assumption.
  inversion H. inversion H0.
  intros. auto.
Qed.

Program Instance SSMorphLen_PO : PreOrder SSMorphLen.
Obligation 1.
  unfold Reflexive. intros.
  constructor. reflexivity.
  intuition.
Qed.

Definition newSSMorphLen (s : ScanStateDesc) : SSMorphLen s s.
Proof. intros. constructor; auto. constructor; auto. Defined.

Record > SSMorphStLen (sd1 sd2 : ScanStateDesc) : Prop := {
    stlen_is_SSMorphLen :> SSMorphLen sd1 sd2;
    stlen_is_SSMorphSt  :> SSMorphSt sd1 sd2
}.

Lemma SSMorphStLen_Len_StLen_transitivity
  `(i : SSMorphLen sd0 sd1)
  `(j : SSMorphStLen  sd1 sd2) : SSMorphStLen sd0 sd2.
Proof. destruct i; destruct j; intuition. Qed.

Lemma NS_SSMorphStLen_Len_StLen_transitivity
  `(cur : ScanStateCursor sd)
  `(i : @NextState sd cur SSMorphLen)
  `(j : @NextState (nextDesc i) cur' SSMorphStLen)
  : @NextState sd cur SSMorphStLen.
Proof.
  destruct i. destruct j.
  rapply Build_NextScanState. apply nextState1.
  apply (SSMorphStLen_Len_StLen_transitivity morphProof0 morphProof1).
Qed.

Lemma SSMorphSt_Len_St_transitivity
  `(i : SSMorphLen sd0 sd1)
  `(j : SSMorphSt sd1 sd2)
  : SSMorphSt sd0 sd2.
Proof. destruct i; destruct j; intuition. Qed.

Definition NS_SSMorphSt_Len_StLen_transitivity
  `(cur : ScanStateCursor sd)
  `(i : @NextState sd cur SSMorphLen)
  `(j : @NextState (nextDesc i) cur' SSMorphStLen)
  : @NextState sd cur SSMorphSt :=
  NSS_transport SSMorphStLen SSMorphSt
    (NS_SSMorphStLen_Len_StLen_transitivity cur i j)
    (stlen_is_SSMorphSt _ _).

Lemma SSMorphSt_StLen_St_transitivity
  `(i : SSMorphStLen sd0 sd1)
  `(j : SSMorphSt sd1 sd2) : SSMorphSt sd0 sd2.
Proof. destruct i; destruct j; intuition. Qed.

Lemma NS_SSMorphSt_StLen_St_transitivity
  `(cur : ScanStateCursor sd)
  `(i : @NextState sd cur SSMorphStLen)
  `(j : @NextState (nextDesc i) cur' SSMorphSt)
  : @NextState sd cur SSMorphSt.
Proof.
  destruct i. destruct j.
  rapply Build_NextScanState. apply nextState1.
  apply (SSMorphSt_StLen_St_transitivity morphProof0 morphProof1).
Qed.

Lemma SSMorphSt_Len_Len_St_transitivity
  `(i : SSMorphLen sd0 sd1)
  `(j : SSMorphLen sd1 sd2)
  `(k : SSMorphSt  sd2 sd3) : SSMorphSt sd0 sd3.
Proof. destruct i; destruct j; destruct k; intuition. Qed.

Lemma NS_SSMorphSt_Len_Len_St_transitivity
  `(cur : ScanStateCursor sd)
  `(i : @NextState sd cur SSMorphLen)
  `(j : @NextState (nextDesc i) cur' SSMorphLen)
  `(k : @NextState (nextDesc j) cur'' SSMorphSt)
  : @NextState sd cur SSMorphSt.
Proof.
  destruct i. destruct j. destruct k.
  rapply Build_NextScanState. apply nextState2.
  apply (SSMorphSt_Len_Len_St_transitivity
           morphProof0 morphProof1 morphProof2).
Qed.

Lemma SSMorphStLen_Len_Len_StLen_transitivity
  `(i : SSMorphLen sd0 sd1)
  `(j : SSMorphLen sd1 sd2)
  `(k : SSMorphStLen sd2 sd3) : SSMorphStLen sd0 sd3.
Proof. destruct i; destruct j; destruct k; intuition. Qed.

Lemma NS_SSMorphStLen_Len_Len_StLen_transitivity
  `(cur : ScanStateCursor sd)
  `(i : @NextState sd cur SSMorphLen)
  `(j : @NextState (nextDesc i) cur' SSMorphLen)
  `(k : @NextState (nextDesc j) cur'' SSMorphStLen)
  : @NextState sd cur SSMorphStLen.
Proof.
  destruct i. destruct j. destruct k.
  rapply Build_NextScanState. apply nextState2.
  apply (SSMorphStLen_Len_Len_StLen_transitivity
           morphProof0 morphProof1 morphProof2).
Qed.

Lemma SSMorphStLen_Len_StLen_StLen_transitivity
  `(i : SSMorphLen   sd0 sd1)
  `(j : SSMorphStLen sd1 sd2)
  `(k : SSMorphStLen sd2 sd3) : SSMorphStLen sd0 sd3.
Proof. destruct i; destruct j; destruct k; intuition. Qed.

Lemma NS_SSMorphStLen_Len_StLen_StLen_transitivity
  `(cur : ScanStateCursor sd)
  `(i : @NextState sd cur SSMorphLen)
  `(j : @NextState (nextDesc i) cur' SSMorphStLen)
  `(k : @NextState (nextDesc j) cur'' SSMorphStLen)
  : @NextState sd cur SSMorphStLen.
Proof.
  destruct i. destruct j. destruct k.
  rapply Build_NextScanState. apply nextState2.
  apply (SSMorphStLen_Len_StLen_StLen_transitivity
           morphProof0 morphProof1 morphProof2).
Qed.

Lemma SSMorphSt_Len_StLen_StLen_transitivity
  `(i : SSMorphLen   sd0 sd1)
  `(j : SSMorphStLen sd1 sd2)
  `(k : SSMorphStLen sd2 sd3) : SSMorphSt sd0 sd3.
Proof. destruct i; destruct j; destruct k; intuition. Qed.

Definition NS_SSMorphSt_Len_StLen_StLen_transitivity
  `(cur : ScanStateCursor sd)
  `(i : @NextState sd cur SSMorphLen)
  `(j : @NextState (nextDesc i) cur' SSMorphStLen)
  `(k : @NextState (nextDesc j) cur'' SSMorphStLen)
  : @NextState sd cur SSMorphSt :=
  NSS_transport SSMorphStLen SSMorphSt
    (NS_SSMorphStLen_Len_StLen_StLen_transitivity cur i j k)
    (stlen_is_SSMorphSt _ _).

Definition cursorFromMorphLen `(cur : ScanStateCursor sd)
  `(n : NextState cur SSMorphLen) : ScanStateCursor (nextDesc n).
Proof.
  destruct sd. destruct cur. simpl in *.
  rapply Build_ScanStateCursor;
  destruct n; simpl in *.
    apply nextState0.
  destruct morphProof0.
  destruct nextDesc0.
  simpl in *. omega.
Defined.

Definition cursorFromMorphStLen `(cur : ScanStateCursor sd)
  `(n : NextState cur SSMorphStLen) : ScanStateCursor (nextDesc n) :=
  cursorFromMorphLen cur (NSS_transport _ _ n (stlen_is_SSMorphLen _ _)).

Definition HasUnhandled := fun sd => length (unhandled sd) > 0.
Definition MaybeHasUnhandled := fun sd => length (unhandled sd) >= 0.

Definition withLenCursor {H Q a}
  (f : forall sd : ScanStateDesc, ScanStateCursor sd
         -> SState HasUnhandled H SSMorphLen Q a)
  : SState HasUnhandled H SSMorphLen Q a.
Proof.
  constructor. intros i.
  destruct i.
  unfold HasUnhandled in startHolds0.
  destruct thisHolds0.
  pose proof startHolds0.
  apply unhandled_nonempty0 in H0.
  pose {| curState  := thisState0
        ; curExists := H0 |} as p.
  specialize (f thisDesc0 p).
  destruct f as [res].
  apply res.
  rapply Build_SSInfo.
  apply startHolds0.
  rapply Build_SSMorphLen; auto.
  apply len_is_SSMorph0.
  apply thisState0.
Defined.

Definition weakenStLenToSt {H} : SState H H SSMorphStLen SSMorphSt unit.
Proof.
  constructor. intros HS.
  split. constructor.
  destruct HS.
  rapply Build_SSInfo.
  - apply startHolds0.
  - destruct thisHolds0.
    apply stlen_is_SSMorphSt0.
  - assumption.
Defined.

(*
Definition withStLenCursor {Q a}
  (f : forall sd : ScanStateDesc, ScanStateCursor sd
         -> SState HasUnhandled SSMorphStLen Q a)
  : SState HasUnhandled SSMorphStLen Q a.
Proof.
  constructor. intros i.
  destruct i.
  pose (@withLenCursor Q a).
  unfold HasUnhandled in startHolds0.
  destruct thisHolds0.
  pose proof startHolds0.
  apply unhandled_nonempty0 in H.
  pose {| curState  := thisState0
        ; curExists := H |} as p.
  specialize (f thisDesc0 p).
  destruct f as [res].
  apply res.
  rapply Build_SSInfo.
  apply startHolds0.
  rapply Build_SSMorphLen; auto.
  apply len_is_SSMorph0.
  apply thisState0.
Defined.
*)

(*
Definition weakenStLenToSt H : SState SSMorphStLen SSMorphSt unit.
Proof.
  constructor. intros.
  split. constructor.
  destruct H.
  rapply @Build_SState'.
    destruct bridgeState0.
    destruct morphProof0.
    rapply Build_NextScanState.
    apply nextState0.
    apply stlen_is_SSMorphSt0.
  destruct resultState0.
  destruct morphProof0.
  rapply Build_NextScanState.
  apply nextState0.
  apply stlen_is_SSMorphSt0.
  Grab Existential Variables.
  apply thisCursor0.
  apply startCursor0.
Defined.
*)

(*
Definition weakenStLenToLen : SState SSMorphStLen SSMorphLen unit.
Proof.
  constructor. intros.
  split. constructor.
  destruct H as [sd s].
  destruct s as [cur n].
  unfold SState'.
  exists sd.
  exists cur.
  destruct n.
  eexists.
  apply nextState0.
  destruct morphProof0.
  apply stlen_is_SSMorphLen0.
Defined.
*)

Definition weakenStLenToLen {H} : SState H H SSMorphStLen SSMorphLen unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - apply startHolds0.
  - destruct thisHolds0.
    apply stlen_is_SSMorphLen0.
  - assumption.
Defined.

Definition weakenHasUnhandled {P}
  : SState HasUnhandled MaybeHasUnhandled P P unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - unfold HasUnhandled in startHolds0.
    unfold MaybeHasUnhandled. omega.
  - apply thisHolds0.
  - assumption.
Defined.

(*
Definition weakenStLenToLen : SState SSMorphStLen SSMorphLen unit.
Proof.
  constructor. intros.
  split. constructor.
  destruct H.
  rapply @Build_SState'.
    destruct bridgeState0.
    destruct morphProof0.
    rapply Build_NextScanState.
    apply nextState0.
    apply stlen_is_SSMorphLen0.
  destruct resultState0.
  destruct morphProof0.
  rapply Build_NextScanState.
  apply nextState0.
  apply stlen_is_SSMorphLen0.
  Grab Existential Variables.
  apply thisCursor0.
  apply startCursor0.
Defined.
*)

(*
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
*)

Definition moveUnhandledToActive (reg : PhysReg)
  : SState HasUnhandled MaybeHasUnhandled SSMorphLen SSMorphSt unit.
Proof.
Admitted.
(*
  constructor. intros.
  split. constructor.
  destruct H.
  destruct resultState0.
  destruct morphProof0.
  destruct nextDesc0.
  destruct unhandled0; simpl in *.
    destruct thisCursor0. omega.
  pose (ScanState_moveUnhandledToActive nextInterval0 unhandled0
          (* unhsort *)
          active0 inactive0 handled0 intervals0 assignments0
          fixedIntervals0 i reg lists_are_unique0).
  eapply {| startDesc   := startDesc0
          ; startCursor := startCursor0
          ; thisDesc    :=
            {| nextInterval     := nextInterval0
             ; unhandled        := i :: unhandled0
             ; active           := active0
             ; inactive         := inactive0
             ; handled          := handled0
             ; intervals        := intervals0
             ; assignments      := assignments0
             ; fixedIntervals   := fixedIntervals0
             ; lists_are_unique := lists_are_unique0
             |}
          ; resultState := {| nextState := s nextState0 |}
          |}.
  Grab Existential Variables.
  pose (NoDup_unhandledExtent_cons nextInterval0 i unhandled0 intervals0
         (V.replace assignments0 i (Some reg)) assignments0 fixedIntervals0
         (i :: active0) active0 inactive0 inactive0 handled0 handled0
         (move_unhandled_to_active _ i unhandled0 active0 inactive0 handled0
            lists_are_unique0) lists_are_unique0)
      as ue_cons.
  - rapply Build_SSMorphSt; auto.
    rapply Build_SSMorph; auto.
    intuition.
  - admit.
  - admit.
Defined.
*)

(*
Definition moveUnhandledToActive (reg : PhysReg)
  : SState SSMorphLen SSMorphSt unit.
Proof.
  constructor. intros.
  split. constructor.
  destruct H as [sd p].
  destruct p as [cur n].
  destruct n.
  destruct morphProof0.
  destruct nextDesc0.
  destruct unhandled0; simpl in *.
    destruct cur. omega.
  pose (ScanState_moveUnhandledToActive nextInterval0 unhandled0
          (* unhsort *)
          active0 inactive0 handled0 intervals0 assignments0
          fixedIntervals0 i reg lists_are_unique0).
  unfold SState'.
  eexists         {|
        nextInterval := nextInterval0;
        unhandled := i :: unhandled0;
        active := active0;
        inactive := inactive0;
        handled := handled0;
        intervals := intervals0;
        assignments := assignments0;
        fixedIntervals := fixedIntervals0;
        lists_are_unique := lists_are_unique0 |}.
  eexists.
  eexists. apply (s nextState0).
  pose (NoDup_unhandledExtent_cons nextInterval0 i unhandled0 intervals0
         (V.replace assignments0 i (Some reg)) assignments0 fixedIntervals0
         (i :: active0) active0 inactive0 inactive0 handled0 handled0
         (move_unhandled_to_active _ i unhandled0 active0 inactive0 handled0
            lists_are_unique0) lists_are_unique0)
    as ue_cons.
  rapply Build_SSMorphSt; auto.
  rapply Build_SSMorph; auto.
  intuition.
  Grab Existential Variables.
  rapply Build_ScanStateCursor.
    apply nextState0.
  simpl in *.
  intuition.
Defined.
*)

Definition moveActiveToHandled {H} `(x : IntervalId sd)
  : SState (fun sd' => sd = sd' /\ In x (active sd)) H SSMorphLen SSMorphLen unit.
Proof.
  constructor. intros i.
  split. apply tt.
  destruct i.
  intuition.
  pose (ScanState_moveActiveToInactive thisDesc0 x thisState0 H1). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

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

End MSSMorph.