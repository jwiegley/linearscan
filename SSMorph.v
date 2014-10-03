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

(* Inductive tlist {a : Type} : list a -> Type := *)
(*   | tnil : tlist nil *)
(*   | tcons x xs : tlist xs -> tlist (x :: xs). *)

(* Definition Has {a} (x : a) {xs : list a} (T : tlist xs) := *)

(* Notation " '[ ] " := (tlist nil) (at level 100) : type_scope. *)
(* Notation "x ':: y" := (tlist (x :: y)) (at level 100) : type_scope. *)
(* Notation " '[ x ] " := (tlist (x :: nil)) : type_scope. *)
(* Notation " '[ x ; .. ; y ] " := (tlist (cons x .. (cons y nil) ..)) : type_scope. *)

(* Goal '[true ; false ; true]. *)

Module MSSMorph (M : Machine).
Include MScanState M.

Record SSInfo (startDesc : ScanStateDesc) (P : relation ScanStateDesc) := {
    thisDesc  : ScanStateDesc;
    thisHolds : P startDesc thisDesc;
    thisState : ScanState thisDesc
}.

(* Arguments startDesc {P} _. *)
Arguments thisDesc  {_ P} _.
Arguments thisHolds {_ P} _.
Arguments thisState {_ P} _.

Definition SState (sd : ScanStateDesc) (P Q : relation ScanStateDesc) :=
  IState (SSInfo sd P) (SSInfo sd Q).

(* Definition withCursor {P Q a} `{PreOrder _ P} *)
(*   (f : forall sd : ScanStateDesc, ScanStateCursor sd -> SState P Q a) : SState P Q a := *)
(*   rgets (fun s => exist _ (thisDesc s) (thisCursor s)) *)
(*     >>= uncurry_sig f. *)

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

(*
Definition ssput {P : relation ScanStateDesc} `(st : ScanState sd)
  (H : forall start this : ScanStateDesc, P start this) : SState P P unit.
Proof.
  eexists. intros.
  split. apply tt.
  destruct H0.
  specialize (H startDesc0 sd).
  rapply Build_SSInfo.
  apply H.
  assumption.
Defined.
*)

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

Definition withSSInfo {P Q : relation ScanStateDesc} {a pre}
  (f : forall (i : SSInfo pre P), SState pre P Q a)
  : SState pre P Q a := iget >>>= f.

Arguments withSSInfo {P Q a pre} f.

(*
Definition slift {pre} `{st : ScanState sub} {a}
  {P : relation ScanStateDesc} `{T : Transitive _ P}
  : P pre sub -> SState sub P P a -> SState pre P P a.
Proof.
  intros Hp i. destruct i.
  eexists. intros.
  destruct H.
  assert (SSInfo sub P).
    eapply {| thisDesc  := _
            ; thisHolds := _
            |}.
  pose proof H.
  destruct H0.
  apply p in H.
  destruct H.
  split. apply a0.
  destruct s.
  eexists.
  apply (transitivity Hp thisHolds2).
  assumption.
  Grab Existential Variables.
  assumption.
  
Defined.
*)

Definition withScanState {P Q : relation ScanStateDesc} {a pre}
  (f : forall sd : ScanStateDesc, ScanState sd -> SState pre P Q a)
  : SState pre P Q a :=
  iget >>>= fun i => f (thisDesc i) (thisState i).

Arguments withScanState {P Q a pre} f.

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

    transportation (x : IntervalId sd1) : IntervalId sd2 :=
      transportId (next_interval_increases len_is_SSMorph) x;

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
    stlen_is_SSMorph    :> SSMorph sd1 sd2;
    stlen_is_SSMorphLen :> SSMorphLen sd1 sd2;
    stlen_is_SSMorphSt  :> SSMorphSt sd1 sd2
}.

Definition withScanStatePO {P a pre} `{PO : PreOrder _ P}
  (f : forall sd : ScanStateDesc, ScanState sd
         -> SState sd P P a)
  : SState pre P P a.
Proof.
  exists. intros i.
  destruct i.
  specialize (f thisDesc0 thisState0).
  destruct f.
  assert (SSInfo thisDesc0 P).
    eapply {| thisDesc  := _
            ; thisHolds := _
            |}.
  apply p in H.
  destruct H.
  split. apply a0.
  destruct s.
  eexists.
  apply (transitivity thisHolds0 thisHolds1).
  assumption.
  Grab Existential Variables.
  apply thisState0.
  reflexivity.
Defined.

Arguments withScanStatePO {P a pre _} f.

Record SSMorphHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    haslen_is_SSMorph    :> SSMorph sd1 sd2;
    haslen_is_SSMorphLen :> SSMorphLen sd1 sd2;

    first_nonempty : length (unhandled sd1) > 0
}.

Definition newSSMorphHasLen (sd : ScanStateDesc)
  (H : length (unhandled sd) > 0) : SSMorphHasLen sd sd.
Proof. repeat (constructor; auto). Defined.

Definition liftLen {pre a}
  : SState pre SSMorphLen SSMorphLen a
      -> SState pre SSMorphHasLen SSMorphHasLen a.
Proof.
  intros.
  destruct X.
  exists. intros.
  destruct H.
  destruct thisHolds0.
  specialize (p
    {| thisDesc  := thisDesc0
     ; thisHolds := haslen_is_SSMorphLen0
     ; thisState := thisState0
     |}).
  destruct p.
  split. apply a0.
  eexists.
  rapply Build_SSMorphHasLen.
  apply haslen_is_SSMorph0.
  apply haslen_is_SSMorphLen0.
  apply first_nonempty0.
  assumption.
Defined.

(*
Record SSMorphLenEq (sd0 sd1 sd2 : ScanStateDesc) : Prop := {
    hasleneq_is_SSMorph    :> SSMorph sd1 sd2;
    hasleneq_is_SSMorphLen :> SSMorphLen sd1 sd2;

    is_unchanged : sd0 = sd2
}.

Definition weakenHasLenEqToHasLen {sd}
  : SState (SSMorphHasLenEq sd) SSMorphHasLen unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - destruct thisHolds0.
    apply hasleneq_is_SSMorphHasLen0.
  - assumption.
Defined.

Definition withScanStateEq {a}
  (f : forall sd : ScanStateDesc, ScanState sd
         -> SState SSMorphHasLen (SSMorphHasLenEq sd) a)
  : SState SSMorphLen SSMorphLen a :=
  i <<- iget ;
  x <<- f (thisDesc i) (thisState i) ;
  weakenHasLenEqToHasLen ;;;
  return_ x.

Definition promoteHasLenToEq `(st : ScanState sd) (H : forall sd', sd = sd')
  : SState SSMorphHasLen (SSMorphHasLenEq sd) unit.
Proof.
  exists. intros.
  split. apply tt.
  destruct H0.
  specialize (H thisDesc0). subst.
  destruct thisHolds0.
  eexists.
  rapply Build_SSMorphHasLenEq; auto.
  apply haslen_is_SSMorph0.
  assumption.
  rapply Build_SSMorphHasLen; auto.
  apply st.
Defined.
*)

Program Instance SSMorphHasLen_Trans : Transitive SSMorphHasLen.
Obligation 1.
  constructor; destruct H; destruct H0.
  transitivity y; assumption.
  transitivity y; assumption.
  omega.
Qed.

Record SSMorphStHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    sthaslen_is_SSMorph       :> SSMorph sd1 sd2;
    sthaslen_is_SSMorphLen    :> SSMorphLen sd1 sd2;
    sthaslen_is_SSMorphSt     :> SSMorphSt sd1 sd2;
    sthaslen_is_SSMorphHasLen :> SSMorphHasLen sd1 sd2
}.

Program Instance SSMorphStHasLen_Trans : Transitive SSMorphStHasLen.
Obligation 1.
  constructor; destruct H; destruct H0;
  transitivity y; assumption.
Qed.

(*
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
*)

Definition withLenCursor {Q a pre}
  (f : forall sd : ScanStateDesc, ScanStateCursor sd
         -> SState pre SSMorphHasLen Q a)
  : SState pre SSMorphHasLen Q a.
Proof.
  constructor. intros i.
  destruct i.
  pose proof thisHolds0.
  destruct thisHolds0.
  destruct haslen_is_SSMorphLen0.
  pose proof first_nonempty0.
  apply unhandled_nonempty0 in H0.
  pose {| curState  := thisState0
        ; curExists := H0 |} as p.
  specialize (f thisDesc0 p).
  destruct f as [res].
  apply res.
  rapply Build_SSInfo.
  apply H.
  assumption.
Defined.

Definition weakenStLenToSt {pre} : SState pre SSMorphStLen SSMorphSt unit.
Proof.
  constructor. intros HS.
  split. constructor.
  destruct HS.
  rapply Build_SSInfo.
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

Definition weakenStLenToLen {pre} : SState pre SSMorphStLen SSMorphLen unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - destruct thisHolds0.
    apply stlen_is_SSMorphLen0.
  - assumption.
Defined.

Definition weakenHasLenToLen {pre} : SState pre SSMorphHasLen SSMorphLen unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - apply thisHolds0.
  - assumption.
Defined.

Definition weakenStHasLenToHasLen {pre}
  : SState pre SSMorphStHasLen SSMorphHasLen unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - apply thisHolds0.
  - assumption.
Defined.

Definition weakenStHasLenToSt {pre}
  : SState pre SSMorphStHasLen SSMorphSt unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
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

Definition moveUnhandledToActive {pre} (reg : PhysReg)
  : SState pre SSMorphHasLen SSMorphSt unit.
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

Definition moveActiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (active sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

(*
Definition moveActiveToHandled' `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (active sd)) : SState sd SSMorphLen SSMorphLen unit.
Proof.
  constructor. intros.
  split. apply tt.
  destruct H0.
  pose proof thisHolds0 as TH.
  destruct thisHolds0.
  destruct len_is_SSMorph0.
  pose (moveActiveToHandled thisState0 (transportation0 x)).
  destruct s.
  eapply {| thisDesc  := x0
          ; thisState := s
          |}.
  Grab Existential Variables.
  transitivity thisDesc0; auto.
Defined.
*)

Definition moveActiveToInactive `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (active sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

(*
Definition moveActiveToInactive' `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (active sd)) : SState sd SSMorphLen SSMorphLen unit.
Proof.
  constructor. intros.
  split. apply tt.
  destruct H0.
  pose proof thisHolds0 as TH.
  destruct thisHolds0.
  destruct len_is_SSMorph0.
  pose (moveActiveToHandled thisState0
          (transportId next_interval_increases0 x)
          (In_transportId _ H)).
  destruct s.
  eapply {| thisDesc  := x0
          ; thisState := s
          |}.
  Grab Existential Variables.
  transitivity thisDesc0; auto.
Defined.
*)

(* Definition moveActiveToInactive `(st : ScanState sd) (x : IntervalId sd) *)
(*   (H : In x (active sd)) : { sd' : ScanStateDesc | ScanState sd' }. *)
(* Proof. *)
(*   pose (ScanState_moveActiveToInactive sd x st H). *)
(*   eexists. apply s. *)
(* Defined. *)

Definition moveInactiveToActive `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToActive sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

(*
Definition moveInactiveToActive' `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (inactive sd)) : SState sd SSMorphLen SSMorphLen unit.
Proof.
  constructor. intros.
  split. apply tt.
  destruct H0.
  pose proof thisHolds0 as TH.
  destruct thisHolds0.
  destruct len_is_SSMorph0.
  pose (moveInactiveToActive thisState0
          (transportId next_interval_increases0 x)
          (In_transportId _ H)).
  destruct s.
  eapply {| thisDesc  := x0
          ; thisState := s
          |}.
  Grab Existential Variables.
  transitivity thisDesc0; auto.
Defined.
*)

Definition moveInactiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToHandled sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
  apply Le.le_n_Sn.
Defined.

(*
Definition moveInactiveToHandled' `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (inactive sd)) : SState sd SSMorphLen SSMorphLen unit.
Proof.
  constructor. intros.
  split. apply tt.
  destruct H0.
  pose proof thisHolds0 as TH.
  destruct thisHolds0.
  destruct len_is_SSMorph0.
  pose (moveInactiveToHandled thisState0
          (transportId next_interval_increases0 x)
          (In_transportId _ H)).
  destruct s.
  eapply {| thisDesc  := x0
          ; thisState := s
          |}.
  Grab Existential Variables.
  transitivity thisDesc0; auto.
Defined.
*)

End MSSMorph.