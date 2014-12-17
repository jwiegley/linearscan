Require Import LinearScan.Lib.
Require Import LinearScan.Spec.

Require Export LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MSSMorph (Mach : Machine).

Include MLinearSpec Mach.

Open Scope nat_scope.

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

Record SSMorphSt (sd1 sd2 : ScanStateDesc) : Prop := {
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

Class HasBase P := {
    ssMorphLen : forall sd1 sd2, P sd1 sd2 -> SSMorphLen sd1 sd2
}.

Program Instance SSMorphLen_HasWork : HasBase SSMorphLen.

Record SSMorphStLen (sd1 sd2 : ScanStateDesc) : Prop := {
    stlen_is_SSMorphLen :> SSMorphLen sd1 sd2;
    stlen_is_SSMorphSt  :> SSMorphSt sd1 sd2
}.

Record SSMorphHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    haslen_is_SSMorphLen :> SSMorphLen sd1 sd2;

    first_nonempty : size (unhandled sd2) > 0
}.

Definition newSSMorphHasLen (sd : ScanStateDesc)
  (H : size (unhandled sd) > 0) : SSMorphHasLen sd sd.
Proof. repeat (constructor; auto). Defined.

Class HasWork P := {
    ssMorphHasLen : forall sd1 sd2, P sd1 sd2 -> SSMorphHasLen sd1 sd2
}.

Program Instance SSMorphHasLen_HasWork : HasWork SSMorphHasLen.

Record SSMorphStHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    sthaslen_is_SSMorphSt     :> SSMorphSt sd1 sd2;
    sthaslen_is_SSMorphHasLen :> SSMorphHasLen sd1 sd2
}.

Program Instance SSMorphStHasLen_HasWork : HasWork SSMorphStHasLen.
Obligation 1. destruct H. auto. Defined.

Record SSMorphSplit (sd1 sd2 : ScanStateDesc) : Prop := {
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
    stsplit_is_SSMorphSt       :> SSMorphSt sd1 sd2;
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
  IState SSError (SSInfo sd P) (SSInfo sd Q).

Definition withScanState {a pre} {P Q}
  (f : forall sd : ScanStateDesc, ScanState sd -> SState pre P Q a) :
  SState pre P Q a := iget SSError >>>= fun i => f (thisDesc i) (thisState i).

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
  apply s in X.
  destruct X.
    apply (inl s0).
  apply inr.
  destruct p.
  split. apply a0.
  destruct s0.
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
  specialize (s
    {| thisDesc  := thisDesc0
     ; thisHolds := haslen_is_SSMorphLen0
     ; thisState := thisState0
     |}).
  destruct s.
    apply (inl s).
  apply inr.
  destruct p.
  split. apply a0.
  eexists.
  apply Build_SSMorphHasLen.
  apply haslen_is_SSMorphLen0.
  apply first_nonempty0.
  assumption.
Defined.

Definition weakenStHasLenToSt {pre} :
  SState pre SSMorphStHasLen SSMorphSt unit.
Proof.
  constructor. intros HS.
  apply inr.
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
  constructor.
  destruct 1.
  destruct H.
  specialize (ssMorphHasLen0 pre thisDesc0 thisHolds0).
  pose proof ssMorphHasLen0.
  destruct ssMorphHasLen0.
  destruct haslen_is_SSMorphLen0.
  pose {| curState  := thisState0
        ; curExists := first_nonempty0 |} as p.
  specialize (f thisDesc0 p).
  destruct f as [res].
  apply res.
  exact: Build_SSInfo.
Defined.

Lemma unhandledExtent_cons :
  forall ni i (unh : list ('I_ni * nat)) ints fixints
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
  rewrite !sumlist_cons.
  exact: ltn_plus.
Qed.

Definition moveUnhandledToActive {pre P} `{HasWork P} (reg : PhysReg) :
  SState pre P SSMorphSt unit.
Proof.
  constructor. intros.
  apply inr.
  split. apply tt.
  destruct H.
  destruct X.
  specialize (ssMorphHasLen0 pre thisDesc0 thisHolds0).
  destruct thisDesc0.
  destruct ssMorphHasLen0.
  destruct haslen_is_SSMorphLen0.
  destruct len_is_SSMorph0.
  destruct unhandled0; simpl in *; first by [].
  destruct p.
  pose (ScanState_moveUnhandledToActive reg thisState0).
  eapply {| thisState := s |}.
  Grab Existential Variables.
  pose (unhandledExtent_cons (i, n) unhandled0 intervals0
         fixedIntervals0
         ((i, reg) :: active0) active0 inactive0 inactive0 handled0 handled0)
      as ue_cons.
  apply Build_SSMorphSt; intuition.
    apply le_Sn_le in ue_cons;
    exact: (leq_trans ue_cons).
  exact: (leq_trans ue_cons).
Defined.

Definition moveActiveToHandled `(st : ScanState sd) `(H: x \in active sd) :
  { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToHandled st H).
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

Definition splitCurrentInterval {pre P} `{W : HasWork P}
  (before : option nat) : SState pre P SSMorphStHasLen unit.
Proof.
  rewrite /SState.
  apply: mkIState => ssi.

  case: ssi => desc holds.
  case: W => /(_ pre desc holds).
  case=> H. case: H holds => /=; case.
  case: desc => /= ? intervals0 ? unhandled0 ? ? ?.

  case E: unhandled0 => //= [[uid beg] us].
  set desc := Build_ScanStateDesc _ _ _ _ _ _; simpl in desc.
  move=> ? extent_decreases ? ? holds unhandled_nonempty0 state.

  set int := vnth intervals0 uid.
  (* jww (2014-11-06): This could come from the input state, along the lines
     of SSMorphSplit, above. *)
  case Hnotsing: (Interval_is_singleton int.2).
    apply (inl ECurrentIsSingleton). (* ERROR *)
  apply: (inr (tt, _)).
  move/negbT in Hnotsing.
  have Hlt := Interval_rds_size_bounded Hnotsing.

  move: (@splitPosition _ int.2 before true Hlt) => [pos Hmid].
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
  move/(_ Hmem).
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
    move/eqP: Hunhandled => ->.
    move/eqP: Hintdesc => ->.
    rewrite -ltn_subRL subKn.
      by rewrite ltn_subRL.
    rewrite -[_ desc]subn0.
    by apply leq_sub.

  abstract
    (apply Build_SSMorphStHasLen;
     try apply Build_SSMorphHasLen;
     try apply Build_SSMorphLen;
     try apply Build_SSMorphSt;
     try apply Build_SSMorph;
     rewrite ?insert_size ?size_map //;
     by apply/ltnW).
Defined.

(** If [pos] is None, it means "split at the end of its lifetime hole". *)
Definition splitAssignedIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) (pos : option nat) (trueForActives : bool) :
  SState pre P SSMorphHasLen unit.
Proof.
  rewrite /SState.
  apply: mkIState => ssi.

  case: ssi => desc holds st.
  (* There is an opportunity here for optimization: finding the best inactive
     interval to split, for example one with a large lifetime hole, or one
     that does not cover loops. *)
  have intids := intervals_for_reg (if trueForActives
                                    then active desc
                                    else inactive desc) reg.
  case: W => /(_ pre desc holds).
  case=> /=; case.
  case: desc => /= ni intervals0 ? unh active0 ? ? in holds intids st *.

  case: intids
    => //= [|aid _] len_is_SSMorph0 unhandled_nonempty first_nonempty.
    apply (inl ENoIntervalsToSplit). (* ERROR *)

  set int := vnth intervals0 aid.
  (* jww (2014-11-06): This could come from the input state, along the lines
     of SSMorphSplit, above. *)
  case Hnotsing: (Interval_is_singleton int.2).
    apply (inl ECurrentIsSingleton). (* ERROR *)
  apply: (inr (tt, _)).
  move/negbT in Hnotsing.
  have Hlt := Interval_rds_size_bounded Hnotsing.

  move: (@splitPosition _ int.2 pos false Hlt)
    => [pos' Hmid].
  move: (splitInterval_spec Hmid).
  case: (splitInterval Hmid)
    => [[[id0 i0] [id1 i1]] [/= H1 H2 /eqP H3 /eqP H4 H5]] Hdim.

  move: (Hdim) => /ltn_add1l /= H6.
  move: H3 => /eqP H3.
  rewrite eq_sym in H3.

  have := ScanState_setInterval st H6 H3.
  set set_int_desc := Build_ScanStateDesc _ _ _ _ _ _.
  simpl in set_int_desc.
  move=> state.

  have := ScanState_newInactive reg state i1.
  rewrite /= => {state}.
  set new_inactive_added := Build_ScanStateDesc _ _ _ _ _ _.
  simpl in new_inactive_added.
  move=> state.

  apply: (Build_SSInfo _ state).

  case: len_is_SSMorph0
    => /= next_interval_increases
          total_extent_decreases
          handled_count_increases.
  have ?: unhandledExtent new_inactive_added <= unhandledExtent pre.
    move: (lists_are_unique st).
    move: (lists_are_unique state).
    rewrite /all_state_lists /new_inactive_added.
    rewrite /unhandledIds cat_uniq => /and3P [/= Huniq_state _ _].
    rewrite /unhandledIds cat_uniq /= => /and3P [Huniq_st _ _].
    apply: (leq_trans _ total_extent_decreases).
    rewrite /unhandledExtent /=
            {holds state st new_inactive_added set_int_desc
             unhandled_nonempty total_extent_decreases}.
    elim: unh => // [u us IHus] in first_nonempty Huniq_state Huniq_st *.
    case: us => /= [|y ys] in IHus first_nonempty Huniq_state Huniq_st *.
      simpl.
      rewrite !sumlist_cons /sumlist !addn0 /=.
      case H: (aid == fst u).
        move/eqP in H.
        move: H6.
        rewrite H !vnth_vshiftin vnth_vreplace /int H.
        by move/ltnW.
      rewrite vnth_vshiftin vnth_vreplace_neq; first by [].
      by move/negbT in H.
    rewrite sumlist_cons [sumlist [:: _, _ & _]]sumlist_cons.
    apply/leq_add.
      case H: (aid == fst u).
        move/eqP in H.
        move: H6.
        rewrite H !vnth_vshiftin vnth_vreplace /int H /=.
        by move/ltnW.
      rewrite vnth_vshiftin vnth_vreplace_neq; first by [].
      by move/negbT in H.
    apply IHus; first by [].
      rewrite !map_widen_fst -cons_uniq -map_cons.
      rewrite map_inj_uniq; last by exact: widen_ord_inj.
      move: Huniq_st.
      by rewrite -cons_uniq -map_cons cons_uniq => /andP [_ ?].
    move/and3P: Huniq_st => [? ? ?].
    by apply/andP.

  apply: Build_SSMorphHasLen;
  try apply: Build_SSMorphLen;
  try apply: Build_SSMorph;
  rewrite ?insert_size ?size_map; auto.
Defined.

Definition splitActiveIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) (pos : nat) : SState pre P SSMorphHasLen unit :=
  splitAssignedIntervalForReg reg (Some pos) true.

Definition splitAnyInactiveIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) : SState pre P SSMorphHasLen unit :=
  splitAssignedIntervalForReg reg None false.

End MSSMorph.