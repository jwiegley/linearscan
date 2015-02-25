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

Inductive SplitPosition :=
  | BeforePos of oddnum
  | BeforeFirstUsePosReqReg
  | EndOfLifetimeHole.

(* Given an interval, determine its optimal split position.  If no split
   position can be found, it means the interval may be safely spilled, and all
   further variable references should be accessed directly from memory. *)
Program Definition splitPosition `(i : Interval d) (pos : SplitPosition) :
  option oddnum :=
  match pos with
  | BeforePos x             => Some x
  | BeforeFirstUsePosReqReg => firstUseReqReg i
  | EndOfLifetimeHole       => None (* jww (2015-01-22): NYI *)
    (* This should be the same thing as splitting at the current position. *)
  end.

Definition splitPosWithin `(i : Interval d) (pos : SplitPosition) :=
  match pos with
  | BeforePos (exist x _) => ibeg d < x < iend d
  | BeforeFirstUsePosReqReg => true
  | EndOfLifetimeHole => true
  end.

Definition splitInterval `(st : ScanState InUse sd)
  `(Hunh : unhandled sd = (u, beg) :: us) (pos : SplitPosition)
  (uid : IntervalId sd) (forCurrent : bool) :
  SSError + option { ss : ScanStateSig maxReg InUse | SSMorphLen sd ss.1 }.
Proof.
  case: sd => /= ? ints ? unh ? ? ? in st u us Hunh uid *.
  set int := vnth ints uid.

  case: (splitPosition int.2 pos) => [[splitPos Hodd] |]; last first.
    exact: inr None.            (* could not split, but maybe benign *)

  (* Ensure that the [splitPos] falls within the interval, otherwise our
     action can have no effect. *)
  case Hmid: (ibeg int.1 < splitPos <= iend int.1); last first.
    exact: inl (ERegistersExhausted uid). (* ERROR *)
  move/andP: Hmid => [Hmid1 Hmid2].

  have Hset := ScanState_setInterval st.
  case Hint: int => [d i] in Hmid1 Hmid2 *.
  case: d => iv ib ie ? rds in i Hint Hmid1 Hmid2 *.
  rewrite /= in Hset.

  case: (intervalSpan Hodd i) => /= [[[[id0 i0] |] [[id1 i1] |]]].
  (* The interval was split into two parts.  The second part goes back onto
     the unhandled list for processing later if it contains use positions that
     require a register. *)
  - Case "(Some, Some)".
    move=> [/= H1 H2 /eqP H3].

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

    case Hincr: (beg < ibeg id1); last first.
      (* Wimmer: "All active and inactive intervals for this register
         intersecting with current are split before the start of current and
         spilled to the stack.  These split children are not considered during
         allocation any more because they do not have a register assigned.  If
         they have a use positions requiring a register, however, they must be
         reloaded again to a register later on.  Therefore, they are split a
         second time before these use positions, and the second split children
         are sorted into the unhandled list.  They get a register assigned
         when the allocator advances to the start position of these
         intervals." *)
      case: (splitPosition i1 BeforeFirstUsePosReqReg)
        => [[splitPos2 Hodd2] |]; last first.
        apply: inr (Some (exist _ (packScanState st) _)).
        apply Build_SSMorphLen.
        apply Build_SSMorph => //=.
        exact.

      case Hmid': (ibeg id1 < splitPos2 < iend id1); last first.
        exact: inl (ECannotSplitSingleton2 uid). (* ERROR *)
      move/andP: Hmid' => [Hmid1' Hmid2'].

      case: id1 => iv1 ib1 ie1 ? rds1 in i1 H1 H3 Hincr Hmid1' Hmid2' *.
      case: (intervalSpan Hodd2 i1) => [[[[id1_0 i1_0] |] [[id1_1 i1_1] |]]].
      - SCase "(Some, Some)".
        move=> [/= H1_1 H2_1 /eqP H3_1].
        have := ScanState_newUnhandled st i1_1.
        rewrite /= => {st}.
        set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
        simpl in new_unhandled.
        case Hincr2: (beg < ibeg id1_1); last first.
          (* It is not allowable to inject new unhandled intervals for the
             current position.
             jww (2015-01-22): This should be provably impossible. *)
          move=> _.
          exact: inl (ECannotSplitSingleton3 uid). (* ERROR *)
        rewrite Hunh.
        move/(_ Hincr2).
        move=> st.

        apply: inr (Some (exist _ (packScanState st) _)).
        apply Build_SSMorphLen.
        apply Build_SSMorph => //=.
        by rewrite insert_size.

      - SCase "(Some, None)".
        move=> [/= H2_1 H3_1 H4_1].
        apply: inr (Some (exist _ (packScanState st) _)).
        apply Build_SSMorphLen.
        apply Build_SSMorph => //=.
        exact.

      - SCase "(None, Some)".
        move=> [/= H2_1 H3_1 H4_1].
        have := ScanState_newUnhandled st i1_1.
        rewrite /= => {st}.
        set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
        simpl in new_unhandled.
        case Hincr2: (beg < ibeg id1_1); last first.
          (* It is not allowable to inject new unhandled intervals for the
             current position.
             jww (2015-01-22): This should be provably impossible. *)
          move=> _.
          exact: inl (ECannotSplitSingleton4 uid). (* ERROR *)
        rewrite Hunh.
        move/(_ Hincr2).
        move=> st.

        apply: inr (Some (exist _ (packScanState st) _)).
        apply Build_SSMorphLen.
        apply Build_SSMorph => //=.
        by rewrite insert_size.

      - SCase "(None, None)".
        contradiction.

    have := ScanState_newUnhandled st i1.
    rewrite /= => {st}.
    set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in new_unhandled.
    rewrite Hunh.
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
      exact: inl (ECannotSplitSingleton5 uid). (* ERROR *)

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
      exact: inl (ECannotSplitSingleton6 uid). (* ERROR *)

    have := ScanState_newUnhandled st i1.
    rewrite /= => {st}.
    set new_unhandled := Build_ScanStateDesc _ _ _ _ _ _.
    simpl in new_unhandled.
    rewrite Hunh.
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
  case Hunh: (unhandled desc) => //= [[uid beg] us].
  move=> H1 H2 H3.
  move/splitInterval/(_ uid beg us Hunh pos uid true).
  case: desc => /= ? intervals0 ? unhandled0 ? ? ? in uid us Hunh H1 H2 H3 *.
  case=> [err|[[[sd st] [[/= ? H]]] |]]; last first.
  - exact: inl (ECannotSplitSingleton7 uid). (* ERROR *)
  - apply: (inr (tt, _)).
    apply: (Build_SSInfo _ st).
    rewrite Hunh /= in H.
    specialize (H (ltn0Sn _)).
    apply Build_SSMorphHasLen;
    try apply Build_SSMorphHasLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorph;
    rewrite ?insert_size ?size_map //;
    try move=> Hpre;
    exact: (leq_trans H1 _).
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

  case Hunh: (unhandled desc) => //= [[uid beg] us].
  case: desc => /= ? intervals0 ? ? active0 inactive0 ? in uid us Hunh *.
  move=> intlist Hintlist intids Hin H1 H2 H3 st.

  elim Hintids: intids => /= [|aid aids IHaids] in Hin *.
    exact: inl ENoIntervalsToSplit. (* ERROR *)

  move: st.
  move/splitInterval/(_ uid beg us Hunh pos aid false).
  case=> [err|[[[sd st] [[/= Hincr H]]] |]]; last first.
  - exact: inl (ECannotSplitSingleton8 aid). (* ERROR *)
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

    rewrite Hunh /= in H;
    specialize (H (ltn0Sn _));
    apply: (Build_SSInfo _ st);
    apply Build_SSMorphHasLen;
    try apply Build_SSMorphHasLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorph;
    rewrite ?insert_size ?size_map //;
    try move=> Hpre;
    exact: (leq_trans H1 _).
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