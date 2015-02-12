Require Import LinearScan.Lib.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.
Require Import LinearScan.Morph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Split.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Definition splitInterval `(st : ScanState InUse sd)
  `(uid : IntervalId sd) (pos : SplitPosition) (forCurrent : bool) :
  SSError + option { ss : ScanStateSig maxReg InUse | SSMorphLen sd ss.1 }.
Proof.
  case: sd => /= ? ints ? unh ? ? ? in st uid *.
  set int := vnth ints uid.

  (* Splitting is not possible if we have nothing to process.
     jww (2015-01-22): This should be provably unreachable code. *)
  case: unh => [|[u beg] us] in st uid int *.
    exact: inl (ECannotSplitSingleton1 uid). (* ERROR *)

  case: (splitPosition int.2 pos) => [[splitPos Hodd] |]; last first.
    exact: inr None.            (* could not split, but benign *)

  (* Ensure that the [splitPos] falls within the interval, otherwise our
     action can have no effect.
     jww (2015-01-22): This should be provably impossible. *)
  case Hmid: (ibeg int.1 < splitPos < iend int.1); last first.
    exact: inl (ECannotSplitSingleton2 uid). (* ERROR *)
  move/andP: Hmid => [Hmid1 Hmid2].

  have Hset := ScanState_setInterval st.
  case Hint: int => [d i] in Hmid1 Hmid2 *.
  case: d => iv ib ie ? rds in i Hint Hmid1 Hmid2 *.
  rewrite /= in Hset.

  case: (intervalSpan Hodd i) => /= [[[[id0 i0] |] [[id1 i1] |]]].
  (* The interval was split into two parts, each containing use positions.
     The second part always goes back onto the unhandled list for processing
     later. *)
  - Case "(Some, Some)".
    move=> [/= H1 H2 /eqP H3].

    case Hincr: (beg < ibeg id1); last first.
      (* It is not allowable to inject new unhandled intervals for the current
         position.
         jww (2015-01-22): This should be provably impossible. *)
      exact: inl (ECannotSplitSingleton3 uid). (* ERROR *)

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
      exact: inl (ECannotSplitSingleton4 uid). (* ERROR *)

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
         position.
         jww (2015-01-22): This should be provably impossible. *)
      exact: inl (ECannotSplitSingleton5 uid). (* ERROR *)

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
Definition splitCurrentInterval {pre} (pos : SplitPosition) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> ssi.
  case: ssi => desc.
  case=> H. case: H => /=; case.
  case: desc => /= ? intervals0 ? unhandled0 ? ? ?.

  case E: unhandled0 => //= [[uid beg] us].
  set desc := Build_ScanStateDesc _ _ _ _ _ _; simpl in desc.
  move=> next_interval_increases0 unhandled_nonempty0 first_nonempty0.

  move/splitInterval/(_ uid pos true).
  case=> [err|[[[sd st] [[/= ? H]]] |]]; last first.
  - exact: inl (ECannotSplitSingleton6 uid). (* ERROR *)
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
Definition splitAssignedIntervalForReg {pre}
  (reg : PhysReg) (pos : SplitPosition) (trueForActives : bool) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> ssi.
  case: ssi => desc.
  case=> H. case: H => /=; case.

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
  move=> next_interval_increases0 unhandled_nonempty0 first_nonempty0 st.

  elim Hintids: intids => /= [|aid aids IHaids] in Hin *.
    exact: inl ENoIntervalsToSplit. (* ERROR *)

  move: st.
  move/splitInterval/(_ aid pos false).
  case=> [err|[[[sd st] [[/= Hincr H]]] |]]; last first.
  - exact: inl (ECannotSplitSingleton7 aid). (* ERROR *)
  - apply: (inr (tt, _)).

    (* When splitting an active interval, we must move the first half over to
       the inactive list, since it no longer intersects with the current
       position.  This is only valid when [trueForActives] is [true], and only
       if [splitInterval] does not modify the actives list.  It doesn't hurt
       to always check whether it's a member, though we should prove that
       [splitInterval] has the right behavior. *)
    case E: ((widen_ord Hincr aid, reg) \in active sd) => //;
      first
        (have /= := ScanState_moveActiveToInactive st E;
         move=> {st};
         set act_to_inact := Build_ScanStateDesc _ _ _ _ _ _;
         simpl in act_to_inact;
         move=> st);

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

Definition splitActiveIntervalForReg {pre} (reg : PhysReg) (pos : oddnum) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit :=
  splitAssignedIntervalForReg reg (BeforePos pos) true.

Definition splitAnyInactiveIntervalForReg {pre} (reg : PhysReg) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> ss.
  have := splitAssignedIntervalForReg reg EndOfLifetimeHole false.
  move=> /(_ pre ss).
  case=> [err|[_ ss']]; right; split; try constructor.
    exact: ss.
  exact: ss'.
Defined.

End Split.