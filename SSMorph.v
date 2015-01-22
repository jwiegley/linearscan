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
    next_interval_increases :
      nextInterval sd1 <= nextInterval sd2;
    (* work_left_decreases : *)
    (*   work_left_for_sd sd2 <=, work_left_for_sd sd1; *)
    handled_count_increases :
      size (handled sd1) <= size (handled sd2)
}.

Arguments next_interval_increases [sd1 sd2] _.
(* Arguments work_left_decreases     [sd1 sd2] _. *)
Arguments handled_count_increases [sd1 sd2] _.

Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  - exact: (leq_trans next_interval_increases0).
  (* - exact: (dist_leq_trans work_left_decreases1). *)
  - exact: (leq_trans handled_count_increases0).
Qed.

Record SSMorphSt (sd1 sd2 : ScanStateDesc) : Prop := {
    st_is_SSMorph :> SSMorph sd1 sd2(* ; *)

    (* work_left_did_decrease : *)
    (*   work_left_for_sd sd2 <, work_left_for_sd sd1 *)
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

(*
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
*)

Record SSInfo (startDesc : ScanStateDesc) P := {
    thisDesc  : ScanStateDesc;
    thisHolds : P startDesc thisDesc;
    thisState : ScanState InUse thisDesc
}.

Arguments thisDesc  {_ P} _.
Arguments thisHolds {_ P} _.
Arguments thisState {_ P} _.

Definition SState (sd : ScanStateDesc) P Q :=
  IState SSError (SSInfo sd P) (SSInfo sd Q).

Definition withScanState {a pre} {P Q}
  (f : forall sd : ScanStateDesc, ScanState InUse sd
         -> SState pre P Q a) : SState pre P Q a :=
  iget SSError >>>= fun i => f (thisDesc i) (thisState i).

Arguments withScanState {a pre P Q} f.

Definition withScanStatePO {a pre P} `{PO : PreOrder _ P}
  (f : forall sd : ScanStateDesc, ScanState InUse sd
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
  (forall sd : ScanStateDesc, SState sd SSMorphLen SSMorphLen a)
    -> SState pre SSMorphHasLen SSMorphHasLen a.
Proof.
  move=> f.
  exists=> [] [sd [morphlen Hempty] st].
  pose ss := {| thisDesc  := sd
              ; thisHolds := newSSMorphLen sd
              ; thisState := st
              |}.
  case: (f sd) => /(_ ss) [err|[x [sd' morphlen' st']]].
    exact: (inl err).
  apply: inr.
  split; first exact: x.
  apply: {| thisDesc  := sd'
          ; thisHolds := _
          ; thisState := st'
          |}.
  apply: Build_SSMorphHasLen.
    exact: (transitivity morphlen morphlen').
  case: morphlen' => [_ _ H].
  exact: H.
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

(*
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
*)

Definition moveUnhandledToActive {pre P} `{HasWork P} (reg : PhysReg) :
  SState pre P SSMorphSt unit.
Proof.
  constructor. intros.
  destruct H.
  destruct X.
  specialize (ssMorphHasLen0 pre thisDesc0 thisHolds0).
  destruct thisDesc0.
  destruct ssMorphHasLen0.
  destruct haslen_is_SSMorphLen0.
  destruct len_is_SSMorph0.
  destruct unhandled0; first by [].
  destruct p.
  case H: (reg \notin [seq snd i | i <- active0]);
    last exact: (inl (ERegisterAlreadyAssigned reg)).
  apply inr.
  split. apply tt.
  pose (ScanState_moveUnhandledToActive thisState0 H).
  eapply {| thisState := s |}.
  Grab Existential Variables.
  (* pose (unhandledExtent_cons (i, n) unhandled0 intervals0 *)
  (*        fixedIntervals0 *)
  (*        ((i, reg) :: active0) active0 inactive0 inactive0 handled0 handled0) *)
  (*     as ue_cons. *)
  apply Build_SSMorphSt; intuition.
  (*   apply le_Sn_le in ue_cons; *)
  (*   exact: (leq_trans ue_cons). *)
  (* exact: (leq_trans ue_cons). *)
Defined.

Definition moveActiveToHandled
  `(st : ScanState InUse sd) `(H: x \in active sd) :
  { sd' : ScanStateDesc | ScanState InUse sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToHandled st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Definition moveActiveToInactive
  `(st : ScanState InUse sd) `(H: x \in active sd) :
  { sd' : ScanStateDesc | ScanState InUse sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive st H).
  eexists. apply s.
  apply Build_SSMorphLen; auto.
  apply Build_SSMorph; auto.
Defined.

Definition moveInactiveToActive
  `(st : ScanState InUse sd) `(H : x \in inactive sd)
  (Hreg : snd x \notin [seq snd i | i <- active sd]) :
  { sd' : ScanStateDesc | ScanState InUse sd' & SSMorphLen sd sd' }.
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
  { sd' : ScanStateDesc | ScanState InUse sd' & SSMorphLen sd sd' }.
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
  move=> ? (* extent_decreases *) ? ? holds unhandled_nonempty0 state.

  set int := vnth intervals0 uid.
  case: (option_choose before (firstUseReqReg int.2)) => [splitPos |];
    last first.
    exact: (inl (ECannotSplitSingleton uid)). (* ERROR *)

  case Hmid: (ibeg int.1 < splitPos < iend int.1); last first.
    exact: (inl (ECannotSplitSingleton uid)). (* ERROR *)

  move/andP: Hmid => [Hmid1 Hmid2].

  have Hset := (ScanState_setInterval state).
  case Hint: int => [d i] in Hmid1 Hmid2 *.
  case: d => iv ib ie rds in i Hint Hmid1 Hmid2 *.
  rewrite /= in Hset.

  case: (intervalSpan splitPos i) => [[[[id0 i0] |] [[id1 i1] |]]].
  (* We have two intervals, one occurring at the current position, and the
     second which must be inserted back into the unhandled list. *)
  - Case "(Some, Some)".
    move=> [/= H1 H2 /eqP H3].

    apply: (inr (tt, _)).

    rewrite eq_sym in H2.
    move: Hset.
    move/(_ uid id0 i0).
    rewrite /int in Hint.
    rewrite Hint.
    move/(_ H2).
    rewrite /= => {state}.
    set set_int_desc := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in set_int_desc.
    move=> state.

    have Hincr: beg < ibeg id1.
      have H0: (uid, beg) \in unhandled set_int_desc
        by exact: mem_head.
      have /eqP <- := (@beginnings InUse _ state uid beg H0).
      simpl.
      rewrite vnth_vreplace /=.
      move: (Interval_bounded i0) => Hbound.
      apply leq_leq in H1.
      exact: (ltn_leq_trans _ H1).

    have := ScanState_newUnhandled state i1.
    rewrite /= => {state}.
    set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in new_unhandled.
    move/(_ Hincr).
    move=> state.

    apply: (Build_SSInfo _ state).

    abstract
      (apply Build_SSMorphStHasLen;
       try apply Build_SSMorphHasLen;
       try apply Build_SSMorphLen;
       try apply Build_SSMorphSt;
       try apply Build_SSMorph;
       rewrite ?insert_size ?size_map //;
       by apply/ltnW).

  (* Splitting discarded the latter part of the current interval having no use
     positions, so we only need to set the new interval. *)
  - Case "(Some, None)".
    move=> [/= H2 H3 H4].

    apply: (inr (tt, _)).

    rewrite eq_sym in H2.
    move: Hset.
    move/(_ uid id0 i0).
    rewrite /int in Hint.
    rewrite Hint.
    move/(_ H2).
    rewrite /= => {state}.
    set set_int_desc := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in set_int_desc.
    move=> state.

    apply: (Build_SSInfo _ state).

    abstract
      (apply Build_SSMorphStHasLen;
       try apply Build_SSMorphHasLen;
       try apply Build_SSMorphLen;
       try apply Build_SSMorphSt;
       try apply Build_SSMorph;
       rewrite ?insert_size ?size_map //;
       by apply/ltnW).

  (* Splitting discarded the beginning of the current interval having no use
     positions, so we need to re-inject the interval onto the unhandled list. *)
  - Case "(None, Some)".
    move=> [/= H2 H3 H4].

    apply: (inr (tt, _)).

    clear Hset.
    have Hincr: beg < ibeg id1.
      simpl in *.
      have H0: (uid, beg) \in unhandled desc
        by exact: mem_head.
      have /eqP <- := (@beginnings InUse _ state uid beg H0).
      simpl.
      rewrite /int in Hint.
      rewrite Hint /=.
      exact: (ltn_leq_trans _ H4).

    have := ScanState_newUnhandled state i1.
    rewrite /= => {state}.
    set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in new_unhandled.
    move/(_ Hincr).
    move=> state.

    apply: (Build_SSInfo _ state).

    abstract
      (apply Build_SSMorphStHasLen;
       try apply Build_SSMorphHasLen;
       try apply Build_SSMorphLen;
       try apply Build_SSMorphSt;
       try apply Build_SSMorph;
       rewrite ?insert_size ?size_map //;
       by apply/ltnW).

  - Case "(None, None)".
    contradiction.
Defined.

Definition create_ssinfo
  (ni : nat)
  (intervals0 : Vec IntervalSig ni)
  (fixedIntervals0 : fixedIntervalsType)
  (unh : seq ('I_ni * nat))
  (active0 inactive0 handled0 : seq ('I_ni * PhysReg))

  (sd := {| nextInterval   := ni
          ; intervals      := intervals0
          ; fixedIntervals := fixedIntervals0
          ; unhandled      := unh
          ; active         := active0
          ; inactive       := inactive0
          ; handled        := handled0
          |} : ScanStateDesc)
  (st : ScanState InUse sd)

  (pre : ScanStateDesc)
  (len_is_SSMorph0    : SSMorph pre sd)
  (unhandled_nonempty : 0 < size (unhandled pre) -> 0 < size unh)
  (first_nonempty     : 0 < size unh)

  (aid  : 'I_ni)
  (int  := vnth intervals0 aid : IntervalSig)
  (Hlt  : firstUsePos int.2 < lastUsePos int.2)
  (pos' : nat)
  (Hmid : firstUsePos int.2 < pos' <= lastUsePos int.2)
  (id0  : IntervalDesc)
  (i0   : Interval id0)
  (id1  : IntervalDesc)
  (i1   : Interval id1)
  (H1   : NE_all_true (fun u : UsePos => u < pos')
                      (ups (NE_head (rds id0)).1))
  (H2   : ~~ (NE_head (ups (NE_head (rds id1)).1) < pos'))
  (H4   : iend int.1 = iend id1)
  (H5   : iend id0 < ibeg id1)
  (* (Hdim : intervalExtent i0 + intervalExtent i1 < intervalExtent int.2) *)
  (* (H6   : intervalExtent i0 < intervalExtent int.2) *)
  (H3   : ibeg id0 == ibeg int.1)

  (unhandled1 : seq ('I_ni.+1 * nat))
  (active1 inactive1 : seq ('I_ni.+1 * PhysReg))
  (new_unhandled :=
     {| nextInterval   := ni.+1
      ; intervals      := vshiftin (vreplace intervals0 aid (id0; i0))
                                   (id1; i1)
      ; fixedIntervals := fixedIntervals0
      ; unhandled      := unhandled1
      ; active         := active1
      ; inactive       := inactive1
      ; handled        := [seq widen_fst i | i <- handled0]
      |} : ScanStateDesc)

  (state : ScanState InUse new_unhandled) : SSInfo pre SSMorphHasLen.
Proof.
  unfold sd in *. clear sd.
  apply: (Build_SSInfo _ state).

  case: len_is_SSMorph0
    => /= next_interval_increases
          handled_count_increases.

(*
  have ?: unhandledExtent new_unhandled <= unhandledExtent pre.
    move: (lists_are_unique st).
    move: (lists_are_unique state).
    rewrite /all_state_lists /new_unhandled.
    rewrite /unhandledIds cat_uniq => /and3P [/= Huniq_state _ _].
    rewrite /unhandledIds cat_uniq /= => /and3P [Huniq_st _ _].
    apply: (leq_trans _ total_extent_decreases).
    rewrite /unhandledExtent /=
            {state st new_unhandled
             unhandled_nonempty total_extent_decreases}.
    elim: unh => // [u us IHus] in first_nonempty Huniq_state Huniq_st *.
    case: us => /= [|y ys] in IHus first_nonempty Huniq_state Huniq_st *.
      rewrite /= !sumlist_cons /sumlist !addn0 /=.
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
*)

  apply: Build_SSMorphHasLen;
  try apply: Build_SSMorphLen;
  try apply: Build_SSMorph;
  rewrite ?insert_size ?size_map; auto.
  admit.
  admit.
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
  pose intlist := if trueForActives then active desc else inactive desc.
  have Hintlist:
    intlist = if trueForActives then active desc else inactive desc by [].
  set intids := [seq fst i | i <- intlist & snd i == reg].
  have /allP /= Hin: all (fun x => (x, reg) \in intlist) intids
    by exact: map_fst_filter_snd.
  move: intlist Hintlist intids Hin.

  case: W => /(_ pre desc holds).
  case=> /=; case.
  case: desc => /= ni intervals0 ? unh active0 ? ? in holds st *.
  set sd := Build_ScanStateDesc _ _ _ _ _ _ in holds st *.
  simpl in sd.

  move=> len_is_SSMorph0 unhandled_nonempty first_nonempty
         intlist Hintlist intids Hin.

  elim Hintids: intids => /= [|aid aids IHaids] in Hin *.
    exact: (inl ENoIntervalsToSplit). (* ERROR *)

  set int := vnth intervals0 aid.
  admit.
(*
  (* jww (2014-11-06): This could come from the input state, along the lines
     of SSMorphSplit, above. *)
  case Hnotsing: (Interval_is_singleton int.2).
    apply: IHaids.
    move=> x H.
    apply: Hin.
    rewrite in_cons.
    by apply/orP; right.

  move/negbT in Hnotsing.
  have Hlt := Interval_rds_size_bounded Hnotsing.

  move: (@splitPosition _ int.2 pos false Hlt) => [pos' Hmid].
  case: (pos == Some pos'.-1).
    apply: IHaids.
    move=> x H.
    apply: Hin.
    rewrite in_cons.
    by apply/orP; right.

  apply: (inr (tt, _)).

  (* move: (splitInterval_spec Hmid). *)
  case: (splitInterval Hmid)
    => [[[id0 i0] [id1 i1]] [/= H1 H2 /eqP H3 /eqP H4 H5]].

  (* move: (Hdim) => /ltn_add1l /= H6. *)
  move: H3 => /eqP H3.
  rewrite eq_sym in H3.

  (* have := ScanState_setInterval st H6 H3. *)
  have := ScanState_setInterval st H3.
  move/(_ i0).
  set set_int_desc := Build_ScanStateDesc _ _ _ _ _ _.
  simpl in set_int_desc.
  move=> state.

  specialize (Hin aid (mem_head _ _)).
  case: trueForActives in Hin Hintlist *;
    first
      (have /= := ScanState_moveActiveToInactive state;
       rewrite -Hintlist;
       move=> /(_ _ Hin) {state};
       set act_to_inact := Build_ScanStateDesc _ _ _ _ _ _;
       simpl in act_to_inact;
       move=> state);

  have := ScanState_newUnhandled state i1;
  rewrite /= => {state};
  set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _;
  simpl in new_unhandled;
  [clear act_to_inact|];

  case: unh => [//|[? u] uu] /=
    in sd st holds len_is_SSMorph0 unhandled_nonempty
          first_nonempty set_int_desc new_unhandled *;
  have Hincr: u < ibeg id1 by admit.

    move/(_ Hincr);
    move=> state.
    exact: (create_ssinfo st len_is_SSMorph0
                          unhandled_nonempty first_nonempty
                          Hlt Hmid H1 H2 H4 H5 H3 state).

  move/(_ Hincr);
  move=> state.
  exact: (create_ssinfo st len_is_SSMorph0
                        unhandled_nonempty first_nonempty
                        Hlt Hmid H1 H2 H4 H5 H3 state).
*)
Defined.

Definition splitActiveIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) (pos : nat) : SState pre P SSMorphHasLen unit :=
  splitAssignedIntervalForReg reg (Some pos) true.

Definition splitAnyInactiveIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) : SState pre P SSMorphHasLen unit.
Proof.
  exists=> [] ss.
  have := splitAssignedIntervalForReg reg None false.
  move=> /(_ pre P W); case; move=> /(_ ss).
  case=> [err|[_ ss']]; right; split; try constructor.
    case: W => /(_ pre (thisDesc ss) (thisHolds ss))
            => sshaslen.
    exact: {| thisDesc  := thisDesc ss
            ; thisHolds := sshaslen
            ; thisState := thisState ss |}.
  exact: ss'.
Defined.

End MSSMorph.