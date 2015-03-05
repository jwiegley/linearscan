Require Import LinearScan.Lib.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.
Require Import LinearScan.Spec.
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
  | EndOfLifetimeHole of oddnum.

(* Given an interval, determine its optimal split position.  If no split
   position can be found, it means the interval may be safely spilled, and all
   further variable references should be accessed directly from memory. *)
Program Definition splitPosition `(i : Interval d) (pos : SplitPosition) :
  oddnum :=
  match pos with
  | BeforePos n             => n
  | BeforeFirstUsePosReqReg => if firstUseReqReg i is Some n
                               then n
                               else if odd (iend i)
                                    then iend i
                                    else (iend i).-1
  | EndOfLifetimeHole n     => afterLifetimeHole i n
  end.
Obligation 1.
  case E: (odd (iend d)) => //.
  move: (Interval_exact_beg i) => Hbeg.
  move: (Interval_bounded i) => Hbound.
  move: (Range_beg_odd (NE_head (rds d)).2) => Hodd.
  rewrite -{}Hbeg in Hodd.
  case: (iend d) => [|n] /= in E Hbound *.
    move/odd_gt1 in Hodd.
    by ordered.
  by move/negbT/negbNE in E.
Qed.

Definition splitUnhandledInterval `(st : ScanState InUse sd)
  `(Hunh : unhandled sd = (uid, beg) :: us) (pos : SplitPosition) :
  SSError + option { ss : ScanStateSig maxReg InUse | SSMorphLen sd ss.1 }.
Proof.
  case: sd => /= [? ints ? unh ? ? ?] in st uid us Hunh *.
  set int := vnth ints uid.

  case: (splitPosition int.2 pos) => [splitPos Hodd].

  (* Ensure that the [splitPos] falls within the interval, otherwise our
     action can have no effect. *)
  case Hmid: (ibeg int.1 < splitPos <= iend int.1); last first.
    exact: inl (ENoValidSplitPosition uid). (* ERROR *)

  case Hint: int => [d i] in Hmid *.
  case: d => [iv ib ie ? rds] /= in i Hint Hmid *.

  case: (splitInterval i Hodd Hmid) => [[i0 i1] [/= H1 H2 H3]] //.

  (* The interval was split into two parts.  The first part gets spilled by
     adding it to the handled list without a register assignment; the second
     part goes back onto the unhandled list for processing later, unless it is
     empty (i.e., ibeg i == iend i, *and* there are no use positions). *)

  (* Update the state with the new dimensions of the first interval. *)
  move: (ScanState_setInterval st) => /= /(_ uid i0.1 i0.2).
  move: Hint; rewrite /int => ->.
  move/eqP in H2; rewrite eq_sym in H2; move/(_ H2).
  rewrite /= => {st} st.

  (* Establish that beg == ibeg i0.1. *)
  clear int.
  case U: unh => // [x xs] in uid st us Hunh *.
  have Hin : (uid, beg) \in unh.
    rewrite U Hunh.
    exact: mem_head.
  rewrite -U in st *.
  move/eqP: (beginnings (maxReg:=maxReg) st Hin) => Heqe.

  (* The second interval goes back on the unhandled list, to be processed in a
     later iteration.  Note that this does not change the head of the list. *)
  have := ScanState_newUnhandled st i1.2.
  rewrite U Hunh => /=.
  have Hincr: (beg < ibeg i1.1).
    clear -Hmid H1 H2 H3 x Hunh Heqe.
    inversion Hunh.
    rewrite -Heqe /= vnth_vreplace /=.
    move/andP: Hmid => [? ?].
    by ordered.
  move/(_ Hincr).
  rewrite /= => {st} st.

  (* The first interval goes onto the handled list, with no register assigned
     to indicate the spill. *)
  case E: (insert _ _ _) => [|y ys] in st *.
    clear -E.
    rewrite /insert /= -/insert in E.
    by case: (lebf _ _) in E; discriminate.
  move: (ScanState_moveUnhandledToHandled st).
  rewrite /= => {st} st.

  apply: inr (Some (packScanState st; _)).
  apply Build_SSMorphLen.
  apply Build_SSMorph => //=.
  rewrite /=.

  have /=: (1 < (size ((uid, beg) :: us)).+1 -> 1 < size (y :: ys))
    by rewrite -E insert_size.
  move=> H5 H6.
  move/ltn_addn1 in H6.
  by move/H5 in H6.
Defined.

(*
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
        apply: inr (Some (packScanState st; _)).
        apply Build_SSMorphLen.
        apply Build_SSMorph => //=.
        exact.

      case Hmid': (ibeg id1 < splitPos2 <= iend id1); last first.
        exact: inl (ECannotSplitSingleton2 uid i1 splitPos2). (* ERROR *)
      move/andP: Hmid' => [Hmid1' Hmid2'].

      case: id1 => iv1 ib1 ie1 ? rds1 in i1 H1 H3 Hincr Hmid1' Hmid2' *.
      case: (intervalSpan Hodd2 i1) => [[[[id1_0 i1_0] |] [[id1_1 i1_1] |]]].
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

        apply: inr (Some (packScanState st; _)).
        apply Build_SSMorphLen.
        apply Build_SSMorph => //=.
        by rewrite insert_size.
*)

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
  move/splitUnhandledInterval/(_ uid beg us Hunh pos).
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

  exact: inl ENoIntervalsToSplit. (* ERROR *)
  (* move: st. *)
  (* admit. *)
(*
  move/splitAtInterval/(_ uid beg us Hunh pos aid false).
  case=> [err|[[[sd st] [[/= Hincr H]]] |]]; last first.
  - exact: inl (ECannotSplitSingleton8 aid). (* ERROR *)
  - apply: (inr (tt, _)).

    (* When splitting an active interval, we must move the first half over to
       the inactive list, since it no longer intersects with the current
       position.  This is only valid when [trueForActives] is [true], and only
       if [splitAtInterval] does not modify the actives list.  It doesn't hurt
       to always check whether it's a member, though we should prove that
       [splitAtInterval] has the right behavior. *)
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
*)
Defined.

Definition splitActiveIntervalForReg {pre} (reg : PhysReg) (pos : oddnum) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit :=
  splitAssignedIntervalForReg reg (BeforePos pos) true.

Definition splitAnyInactiveIntervalForReg {pre} (reg : PhysReg) (pos : oddnum) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> ss.
  have := splitAssignedIntervalForReg reg (EndOfLifetimeHole pos) false.
  move=> /(_ pre ss).
  case=> [err|[_ ss']]; right; split; try constructor.
    exact: ss.
  exact: ss'.
Defined.

End Split.