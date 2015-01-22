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
    next_interval_increases : nextInterval sd1 <= nextInterval sd2
}.

Arguments next_interval_increases [sd1 sd2] _.

Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  - exact: (leq_trans next_interval_increases0).
Qed.

Record SSMorphLen (sd1 sd2 : ScanStateDesc) : Prop := {
    len_is_SSMorph :> SSMorph sd1 sd2;

    unhandled_nonempty :
      size (unhandled sd1) > 0 -> size (unhandled sd2) > 0
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
  case: morphlen' => [_ (* _ *) H].
  exact: H.
Defined.

Definition weakenHasLen {pre} :
  forall sd, SSMorphHasLen pre sd -> SSMorph pre sd.
Proof. by move=> ? [[?]]. Defined.

Definition weakenHasLen_ {pre} :
  SState pre SSMorphHasLen SSMorph unit.
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

Definition moveUnhandledToActive {pre P} `{HasWork P} (reg : PhysReg) :
  SState pre P SSMorph unit.
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
  apply Build_SSMorph; intuition.
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

Definition splitInterval `(st : ScanState InUse sd)
  `(uid : IntervalId sd) (pos : SplitPosition) (forCurrent : bool) :
  SSError + option { ss : ScanStateSig InUse | SSMorphLen sd ss.1 }.
Proof.
  case: sd => /= ? ints ? unh ? ? ? in st uid *.
  set int := vnth ints uid.

  (* Splitting is not possible if we have nothing to process.  jww
     (2015-01-22): This should be provably unreachable code. *)
  case: unh => [|[u beg] us] in st *.
    exact: inl (ECannotSplitSingleton uid). (* ERROR *)

  case: (splitPosition int.2 pos) => [splitPos |]; last first.
    exact: inr None.            (* could not split, but benign *)

  (* Ensure that the [splitPos] falls within the interval, otherwise our
     action can have no effect.  jww (2015-01-22): This should be proven
     impossible, or differentiated somehow. *)
  case Hmid: (ibeg int.1 < splitPos < iend int.1); last first.
    exact: inl (ECannotSplitSingleton uid). (* ERROR *)
  move/andP: Hmid => [Hmid1 Hmid2].

  have Hset := ScanState_setInterval st.
  case Hint: int => [d i] in Hmid1 Hmid2 *.
  case: d => iv ib ie rds in i Hint Hmid1 Hmid2 *.
  rewrite /= in Hset.

  case: (intervalSpan splitPos i) => /= [[[[id0 i0] |] [[id1 i1] |]]].
  (* The interval was split into two parts, each containing use positions.
     The second part always goes back onto the unhandled list for processing
     later. *)
  - Case "(Some, Some)".
    move=> [/= H1 H2 /eqP H3].

    case Hincr: (beg < ibeg id1); last first.
      (* It is not allowable to inject new unhandled intervals for the current
         position.  jww (2015-01-22): This should be provably impossible. *)
      exact: inl (ECannotSplitSingleton uid). (* ERROR *)

    rewrite eq_sym in H2.
    move: Hset.
    move/(_ uid id0 i0).
    rewrite /int in Hint.
    rewrite Hint.
    move/(_ H2).
    rewrite /= => {st}.
    set set_int_desc := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in set_int_desc.
    move=> st.

    have := ScanState_newUnhandled st i1.
    rewrite /= => {st}.
    set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in new_unhandled.
    move/(_ Hincr).
    move=> st.

    apply: inr (Some (exist _ (packScanState st) _)).
    apply Build_SSMorphLen.
    apply Build_SSMorph => //=.
    by rewrite insert_size.

  (* This generally means the interval was shrunk, and should only happen when
     we are splitting active or inactive intervals, not the current interval. *)
  - Case "(Some, None)".
    move=> [/= H2 H3 H4].

    (* jww (2015-01-22): This should be provably impossible. *)
    case: forCurrent.
      exact: inl (ECannotSplitSingleton uid). (* ERROR *)

    rewrite eq_sym in H2.
    move: Hset.
    move/(_ uid id0 i0).
    rewrite /int in Hint.
    rewrite Hint.
    move/(_ H2).
    rewrite /= => {st}.
    set set_int_desc := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in set_int_desc.
    move=> st.

    apply: inr (Some (exist _ (packScanState st) _)).
    apply Build_SSMorphLen.
    apply Build_SSMorph => //=.
    exact.

  (* This means the interval was shrunk by moving its beginning position
     forward.  This is acceptable for the current interval, since it makes
     progress. *)
  - Case "(None, Some)".
    move=> [/= H2 H3 H4].

    case Hincr: (beg < ibeg id1); last first.
      (* It is not allowable to inject new unhandled intervals for the current
         position.  jww (2015-01-22): This should be provably impossible. *)
      exact: inl (ECannotSplitSingleton uid). (* ERROR *)

    have := ScanState_newUnhandled st i1.
    rewrite /= => {st}.
    set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in new_unhandled.
    move/(_ Hincr).
    move=> st.

    apply: inr (Some (exist _ (packScanState st) _)).
    apply Build_SSMorphLen.
    apply Build_SSMorph => //=.
    by rewrite insert_size.

  - Case "(None, None)".
    contradiction.
Defined.

(** If [pos] is [None], it means "split before first use pos requiring a
    register". *)
Definition splitCurrentInterval {pre P} `{W : HasWork P}
  (pos : SplitPosition) : SState pre P SSMorphHasLen unit.
Proof.
  apply: mkIState => ssi.
  case: ssi => desc holds.
  case: W => /(_ pre desc holds).
  case=> H. case: H holds => /=; case.
  case: desc => /= ? intervals0 ? unhandled0 ? ? ?.

  case E: unhandled0 => //= [[uid beg] us].
  set desc := Build_ScanStateDesc _ _ _ _ _ _; simpl in desc.
  move=> next_interval_increases0 unhandled_nonempty0 ? first_nonempty0.

  move/splitInterval/(_ uid pos true).
  case=> [err|[[[sd st] [[/= ? H]]] |]]; last first.
  - exact: inl (ECannotSplitSingleton uid). (* ERROR *)
  - apply: (inr (tt, _)).
    apply: (Build_SSInfo _ st).
    apply Build_SSMorphHasLen;
    try apply Build_SSMorphHasLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorph;
    rewrite ?insert_size ?size_map //;
    try move=> Hpre;
    try exact: (leq_trans next_interval_increases0 _);
    exact: H first_nonempty0.
  - exact: inl err.
Defined.

(** If [pos] is [None], it means "split at the end of its lifetime hole". *)
Definition splitAssignedIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) (pos : SplitPosition) (trueForActives : bool) :
  SState pre P SSMorphHasLen unit.
Proof.
  apply: mkIState => ssi.
  case: ssi => desc holds.
  case: W => /(_ pre desc holds).
  case=> H. case: H holds => /=; case.

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

  case: desc => /= ? intervals0 ? ? active0 inactive0 ?.
  move=> intlist Hintlist intids Hin.

  set desc := Build_ScanStateDesc _ _ _ _ _ _.
  simpl in desc.
  move=> next_interval_increases0 unhandled_nonempty0 holds
         first_nonempty0 st.

  elim Hintids: intids => /= [|aid aids IHaids] in Hin *.
    exact: inl ENoIntervalsToSplit. (* ERROR *)

  move: st.
  move/splitInterval/(_ aid pos false).
  case=> [err|[[[sd st] [[/= ? H]]] |]]; last first.
  - exact: inl (ECannotSplitSingleton aid). (* ERROR *)
  - apply: (inr (tt, _)).

    (* (* When splitting an active interval, we must move the first half over to *)
    (*    the inactive list, since it no longer intersects with the current *)
    (*    position. *) *)
    (* case: trueForActives in Hin Hintlist *; *)
    (*   first *)
    (*     (have /= := ScanState_moveActiveToInactive st; *)
    (*      rewrite -Hintlist; *)
    (*      move=> /(_ _ Hin) {st}; *)
    (*      set act_to_inact := Build_ScanStateDesc _ _ _ _ _ _; *)
    (*      simpl in act_to_inact; *)
    (*      move=> st); *)
    (* admit. *)

    apply: (Build_SSInfo _ st);
    apply Build_SSMorphHasLen;
    try apply Build_SSMorphHasLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorph;
    rewrite ?insert_size ?size_map //;
    try move=> Hpre;
    try exact: (leq_trans next_interval_increases0 _);
    exact: (H first_nonempty0).
  - exact: inl err.
Defined.

Definition splitActiveIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) (pos : nat) : SState pre P SSMorphHasLen unit :=
  splitAssignedIntervalForReg reg (BeforePos pos) true.

Definition splitAnyInactiveIntervalForReg {pre P} `{W : HasWork P}
  (reg : PhysReg) : SState pre P SSMorphHasLen unit.
Proof.
  exists=> [] ss.
  have := splitAssignedIntervalForReg reg EndOfLifetimeHole false.
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