Require Import Coq.Classes.RelationClasses.

Require Import Lib.
Require Import NonEmpty.
Require Import Hask.IEndo.
Require Import Hask.IApplicative.
Require Import Hask.IMonad.
Require Import Hask.IState.

Require Export ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MSSMorph (M : Machine).
Include MScanState M.

(** ** SSMorph *)

(** A [SSMorph] is a relation describe a lawful transition between two
    states.  It is a [PreOrder] relation. *)

Record SSMorph (sd1 sd2 : ScanStateDesc) : Prop := {
    next_interval_increases : nextInterval sd1    <= nextInterval sd2;
    total_extent_decreases  : unhandledExtent sd2 <= unhandledExtent sd1;
    handled_count_increases : size (handled sd1)  <= size (handled sd2)
}.

Arguments next_interval_increases [sd1 sd2] _.
Arguments total_extent_decreases  [sd1 sd2] _.
Arguments handled_count_increases [sd1 sd2] _.

Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  - exact: (leq_trans next_interval_increases0).
  - exact: (leq_trans total_extent_decreases1).
  - exact: (leq_trans handled_count_increases0).
Qed.

Record > SSMorphSt (sd1 sd2 : ScanStateDesc) : Prop := {
    st_is_SSMorph :> SSMorph sd1 sd2;

    total_extent_measurably_decreases :
      unhandledExtent sd2 < unhandledExtent sd1
}.

Record SSMorphLen (sd1 sd2 : ScanStateDesc) : Prop := {
    len_is_SSMorph :> SSMorph sd1 sd2;

    transportation (x : IntervalId sd1) : IntervalId sd2 :=
      widen_ord (next_interval_increases len_is_SSMorph) x;

    unhandled_nonempty : size (unhandled sd1) > 0 -> size (unhandled sd2) > 0
}.

Program Instance SSMorphLen_PO : PreOrder SSMorphLen.
Obligation 1.
  unfold Reflexive. intros.
  constructor; auto; constructor; auto.
Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity y; assumption. auto.
Qed.

Definition newSSMorphLen (s : ScanStateDesc) : SSMorphLen s s.
Proof. intros. constructor; auto. constructor; auto. Defined.

Record > SSMorphStLen (sd1 sd2 : ScanStateDesc) : Prop := {
    stlen_is_SSMorph    :> SSMorph sd1 sd2;
    stlen_is_SSMorphLen :> SSMorphLen sd1 sd2;
    stlen_is_SSMorphSt  :> SSMorphSt sd1 sd2
}.

Record SSMorphHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    haslen_is_SSMorph    :> SSMorph sd1 sd2;
    haslen_is_SSMorphLen :> SSMorphLen sd1 sd2;

    first_nonempty : size (unhandled sd1) > 0
}.

Definition newSSMorphHasLen (sd : ScanStateDesc)
  (H : size (unhandled sd) > 0) : SSMorphHasLen sd sd.
Proof. repeat (constructor; auto). Defined.

Class HasWork P := {
    ssMorphHasLen : forall sd1 sd2, P sd1 sd2 -> SSMorphHasLen sd1 sd2
}.

Program Instance SSMorphHasLen_HasWork : HasWork SSMorphHasLen.

Record SSMorphStHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    sthaslen_is_SSMorph       :> SSMorph sd1 sd2;
    sthaslen_is_SSMorphLen    :> SSMorphLen sd1 sd2;
    sthaslen_is_SSMorphSt     :> SSMorphSt sd1 sd2;
    sthaslen_is_SSMorphHasLen :> SSMorphHasLen sd1 sd2
}.

Program Instance SSMorphStHasLen_HasWork : HasWork SSMorphStHasLen.
Obligation 1. destruct H. auto. Defined.

Record SSMorphSplit (sd1 sd2 : ScanStateDesc) : Prop := {
    split_is_SSMorph       :> SSMorph sd1 sd2;
    split_is_SSMorphLen    :> SSMorphLen sd1 sd2;
    split_is_SSMorphHasLen :> SSMorphHasLen sd1 sd2;

    next_unhandled_splittable :
      ~~ Interval_is_singleton (getInterval
        (fst (safe_hd _ (first_nonempty split_is_SSMorphHasLen))))
}.

(* Definition newSSMorphSplit (sd : ScanStateDesc) *)
(*   (H : size (unhandled sd) > 0) : SSMorphSplit sd sd. *)
(* Proof. repeat (constructor; auto). Defined. *)

Class IsSplittable P := {
    ssMorphSplittable : forall sd1 sd2, P sd1 sd2 -> SSMorphSplit sd1 sd2
}.

(* Program Instance SSMorphSplit_HasWork : HasWork SSMorphSplit | 10. *)
(* Obligation 1. destruct H. auto. Defined. *)
Program Instance SSMorphSplit_IsSplittable : IsSplittable SSMorphSplit.

Record SSMorphStSplit (sd1 sd2 : ScanStateDesc) : Prop := {
    stsplit_is_SSMorph         :> SSMorph sd1 sd2;
    stsplit_is_SSMorphLen      :> SSMorphLen sd1 sd2;
    stsplit_is_SSMorphSt       :> SSMorphSt sd1 sd2;
    stsplit_is_SSMorphHasLen   :> SSMorphHasLen sd1 sd2;
    stsplit_is_SSMorphStHasLen :> SSMorphStHasLen sd1 sd2;
    stsplit_is_SSMorphSplit    :> SSMorphSplit sd1 sd2
}.

(* Program Instance SSMorphStSplit_HasWork : HasWork SSMorphStSplit | 10. *)
(* Obligation 1. destruct H. auto. Defined. *)
Program Instance SSMorphStSplit_IsSplittable : IsSplittable SSMorphStSplit.
Obligation 1. destruct H. auto. Defined.

Record SSInfo (startDesc : ScanStateDesc) P := {
    thisDesc  : ScanStateDesc;
    thisHolds : P startDesc thisDesc;
    thisState : ScanState thisDesc
}.

Arguments thisDesc  {_ P} _.
Arguments thisHolds {_ P} _.
Arguments thisState {_ P} _.

Definition SState (sd : ScanStateDesc) P Q :=
  IState (SSInfo sd P) (SSInfo sd Q).

Definition withScanState {a pre} {P Q}
  (f : forall sd : ScanStateDesc, ScanState sd -> SState pre P Q a) :
  SState pre P Q a := iget >>>= fun i => f (thisDesc i) (thisState i).

Arguments withScanState {a pre P Q} f.

Definition withScanStatePO {a pre P} `{PO : PreOrder _ P}
  (f : forall sd : ScanStateDesc, ScanState sd
         -> SState sd P P a) : SState pre P P a.
Proof.
  exists. intros i.
  destruct i.
  specialize (f thisDesc0 thisState0).
  destruct f.
  assert (SSInfo thisDesc0 P).
    eapply {| thisDesc  := _
            ; thisHolds := _ |}.
  apply p in X.
  destruct X.
  split. apply a0.
  destruct s.
  eexists.
  apply (transitivity thisHolds0 thisHolds1).
  assumption.
  Grab Existential Variables.
  apply thisState0.
  reflexivity.
Defined.

Arguments withScanStatePO {a pre P _} f.

Definition liftLen {pre a} :
  SState pre SSMorphLen SSMorphLen a
    -> SState pre SSMorphHasLen SSMorphHasLen a.
Proof.
  intros.
  destruct X.
  exists. intros.
  destruct X.
  destruct thisHolds0.
  specialize (p
    {| thisDesc  := thisDesc0
     ; thisHolds := haslen_is_SSMorphLen0
     ; thisState := thisState0
     |}).
  destruct p.
  split. apply a0.
  eexists.
  apply Build_SSMorphHasLen.
  apply haslen_is_SSMorph0.
  apply haslen_is_SSMorphLen0.
  apply first_nonempty0.
  assumption.
Defined.

Definition stbind {P Q R a b}
  (f : (a -> IState Q R b)) (x : IState P Q a) : IState P R b :=
  @ijoin IState _ P Q R b (@imap _ _ P Q _ _ f x).

Notation "m >>>= f" := (stbind f m) (at level 25, left associativity).

Notation "X <<- A ;; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

Notation "A ;;; B" := (_ <<- A ;; B)
  (right associativity, at level 84, A1 at next level).

Definition return_ {I X} := @ipure IState _ I X.

Definition weakenStHasLenToSt {pre} :
  SState pre SSMorphStHasLen SSMorphSt unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  apply: Build_SSInfo.
  - exact: thisDesc0.
  - exact: thisHolds0.
  - by [].
Defined.

Definition withCursor {P Q a pre} `{HasWork P}
  (f : forall sd : ScanStateDesc, ScanStateCursor sd -> SState pre P Q a) :
  SState pre P Q a.
Proof.
  constructor. intros i.
  destruct i.
  destruct H.
  specialize (ssMorphHasLen0 pre thisDesc0 thisHolds0).
  pose proof ssMorphHasLen0.
  destruct ssMorphHasLen0.
  destruct haslen_is_SSMorphLen0.
  pose proof first_nonempty0.
  apply unhandled_nonempty0 in H0.
  pose {| curState  := thisState0
        ; curExists := H0 |} as p.
  specialize (f thisDesc0 p).
  destruct f as [res].
  apply res.
  exact: Build_SSInfo.
Defined.

Lemma unhandledExtent_cons :
  forall ni i (unh : list (fin ni * nat)) ints fixints
    act act' inact inact' hnd hnd',
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := unh
     ; active           := act
     ; inactive         := inact
     ; handled          := hnd
     ; intervals        := ints
     ; fixedIntervals   := fixints
     |} <
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := i :: unh
     ; active           := act'
     ; inactive         := inact'
     ; handled          := hnd'
     ; intervals        := ints
     ; fixedIntervals   := fixints
     |}.
Proof.
  intros.
  induction unh;
  unfold unhandledExtent;
  simpl; destruct i as [i beg];
  pose (Interval_extent_nonzero (vnth ints i).2);
    first by [].
  rewrite /IntervalId /= !sumf_cons.
  exact: ltn_plus.
Qed.

Definition moveUnhandledToActive {pre P} `{HasWork P} (reg : PhysReg) :
  SState pre P SSMorphSt unit.
Proof.
  constructor. intros.
  split. apply tt.
  destruct H.
  destruct X.
  specialize (ssMorphHasLen0 pre thisDesc0 thisHolds0).
  destruct thisDesc0.
  destruct ssMorphHasLen0.
  destruct haslen_is_SSMorphLen0.
  destruct unhandled0; simpl in *.
    by specialize (unhandled_nonempty0 first_nonempty0).
  destruct p.
  pose (ScanState_moveUnhandledToActive reg thisState0).
  eapply {| thisState := s |}.
  Grab Existential Variables.
  pose (unhandledExtent_cons (i, n) unhandled0 intervals0
         fixedIntervals0
         ((i, reg) :: active0) active0 inactive0 inactive0 handled0 handled0)
      as ue_cons.
  apply Build_SSMorphSt; auto;
  unfold lt in *; intuition;
  [ apply le_Sn_le in ue_cons | ];
  exact: (leq_trans ue_cons).
Defined.

Definition moveActiveToHandled `(st : ScanState sd) `(H: x \in active sd) :
  { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Definition moveActiveToInactive `(st : ScanState sd) `(H: x \in active sd) :
  { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Definition moveInactiveToActive `(st : ScanState sd) `(H : x \in inactive sd) :
  { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToActive st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Definition moveInactiveToHandled `(st : ScanState sd) `(H : x \in inactive sd) :
  { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToHandled st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Definition distance (n m : nat) : nat := if n < m then m - n else n - m.

Lemma unhandledExtent_zero :
  forall ni i (unh : list (fin ni * nat)) ints fixints act inact hnd,
  0 <
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := i :: unh
     ; active           := act
     ; inactive         := inact
     ; handled          := hnd
     ; intervals        := ints
     ; fixedIntervals   := fixints
     |}.
Proof.
  intros.
  induction unh;
  unfold unhandledExtent;
  simpl; destruct i as [i beg];
  pose (Interval_extent_nonzero (vnth ints i).2);
    first by [].
  rewrite /IntervalId /= !sumf_cons /= addn_gt0.
  by apply/orP; left.
Qed.

Definition splitCurrentInterval {pre P} `{W : HasWork P}
  (before : option nat) : SState pre P SSMorphStHasLen unit.
Proof.
  rewrite /SState.
  apply: mkIState => ssi.
  apply: (tt, _).

  case: ssi => desc holds.
  case: W => /(_ pre desc holds).
  case=> H; case; case: H holds.
  case: desc => /= ? intervals0 ? unhandled0 ? ? ?.

  case E: unhandled0 => //= [|[uid beg] us];
    first abstract by intuition.
  set desc := Build_ScanStateDesc _ _ _ _ _ _; simpl in desc.
  move=> ? extent_decreases ? holds _ H unhandled_nonempty0.
  move: H (unhandled_nonempty0) => H /H {H} ? state.

  set int := vnth intervals0 uid.
  have Hnotsing : ~~ Interval_is_singleton int.2.
    (* jww (2014-11-06): This information must come from the input state,
       which would be something along the lines of SSMorphSplit, above. *)
    admit.
  have Hlt := Interval_rds_size_bounded Hnotsing.

  move: (@splitPosition _ int.2 before Hlt) => [pos Hmid].
  move: (splitInterval_spec Hmid).
  case: (splitInterval Hmid)
    => [[[id0 i0] [id1 i1]] [/= H1 H2 /eqP H3 /eqP H4 H5]] Hdim.

  move: (Hdim) => /ltn_add1l /= H6.
  move: H3 => /eqP H3.
  rewrite eq_sym in H3.

  have Hmem: uid \in unhandledIds desc.
    rewrite /desc /unhandledIds /=.
    exact: mem_head.
  have := @ScanState_hasInterval_spec _ state uid Hmem.

  have := ScanState_setInterval state H6 H3.
  have := ScanState_setInterval_spec state H6 H3.
  rewrite /= -[vnth _ _]/int => {state}.
  set set_int_desc := Build_ScanStateDesc _ _ _ _ _ _.
  simpl in set_int_desc.
  move=> Hintdesc state Hcontent.

  have := ScanState_newUnhandled state i1.
  have := ScanState_newUnhandled_spec state i1.
  rewrite /= => {state}.
  set new_unhandled_added := Build_ScanStateDesc _ _ _ _ _ _.
  simpl in new_unhandled_added.
  move=> Hunhandled state.

  apply: (Build_SSInfo _ state).

  have is_productive :
      unhandledExtent new_unhandled_added < unhandledExtent pre.
    apply: (leq_trans _ extent_decreases).
    move: Hunhandled => /eqP ->.
    move: Hintdesc => /eqP ->.
    by rewrite -addnA -ltn_subRL subKn.

  abstract
    (apply Build_SSMorphStHasLen;
     try apply Build_SSMorphHasLen;
     try apply Build_SSMorphLen;
     try apply Build_SSMorphSt;
     try apply Build_SSMorph;
     rewrite ?size_insert ?size_map //;
     by apply/ltnW).
Defined.

End MSSMorph.