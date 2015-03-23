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

(* Given an interval, determine its optimal split position.  If no split
   position can be found, it means the interval may be safely spilled, and all
   further variable references should be accessed directly from memory. *)
Program Definition splitPosition `(i : Interval d) (pos : SplitPosition) :
  oddnum :=
  match pos with
  | BeforePos n _       => n
  | EndOfLifetimeHole n => afterLifetimeHole i n
  end.

Inductive SpillCondition (sd : ScanStateDesc maxReg) :=
  | NewToHandled : SpillCondition sd
  | UnhandledToHandled : SpillCondition sd
  | ActiveToHandled xid reg :
      (xid, reg) \in active sd -> SpillCondition sd
  | InactiveToHandled xid reg :
      (xid, reg) \in inactive sd -> SpillCondition sd.

Definition spillConditionToDetails `(spill : SpillCondition sd) :
  SpillDetails :=
  match spill with
  | NewToHandled                => SD_NewToHandled
  | UnhandledToHandled          => SD_UnhandledToHandled
  | ActiveToHandled xid reg _   => SD_ActiveToHandled xid reg
  | InactiveToHandled xid reg _ => SD_InactiveToHandled xid reg
  end.

Definition spillInterval `(st : ScanState InUse sd)
  (i1 : IntervalSig) `(Hunh : unhandled sd = (uid, beg) :: us)
  (xid : IntervalId sd) (Hbeg : beg <= ibeg i1.1)
  (spill : SpillCondition sd) :
  SSError + { ss : ScanStateSig maxReg InUse
            | if spill is UnhandledToHandled
              then SSMorph sd ss.1
              else SSMorphHasLen sd ss.1 }.
Proof.
  (* Is there a use position requiring a register in the interval?  If yes,
     then split it again; otherwise, spill it. *)
  case: (firstUseReqReg i1.2) => [[[splitPos2 Hodd2] /= Hmid2] |]; last first.
    case: spill => [||? ? Hin|? ? Hin].
    - move: (ScanState_newHandled st i1.2) => st'.
      apply: inr _.
      exists (_; st').
      apply Build_SSMorphHasLen => //=;
      try apply Build_SSMorphLen => //=;
      try apply Build_SSMorph => //=;
      by rewrite size_map Hunh.
    - destruct sd; simpl in *.
      rewrite Hunh in st.
      move: (ScanState_moveUnhandledToHandled st) => st'.
      apply: inr _.
      exists (_; st').
      exact: Build_SSMorph.
    - move: (moveActiveToHandled st Hin) => [sd' st' [[[?] H] [Heqe Heqe2]]].
      apply: inr _.
      exists (sd'; st').
      apply Build_SSMorphHasLen => //=.
      apply H.
      by rewrite Hunh.
    - move: (moveInactiveToHandled st Hin) => [sd' st' [[[?] H] [Heqe Heqe2]]].
      apply: inr _.
      exists (sd'; st').
      apply Build_SSMorphHasLen => //=.
      apply H.
      by rewrite Hunh.

  case E: (ibeg i1.1 == splitPos2).
    (* The second interval goes back on the unhandled list, to be processed in a
       later iteration.  Note: this cannot change the head of the unhandled
       list. *)
    case Hincr: (beg < ibeg i1.1); last first.
      move=> *.
      set det := spillConditionToDetails spill.
      exact: inl (ECannotInsertUnhAtCurPos det xid). (* ERROR *)

    have := ScanState_newUnhandled st i1.2.
    rewrite Hunh => /=.
    move/(_ Hincr).
    rewrite /= => {st} st.

    apply: inr (packScanState st; _).
    case: spill => [||*|*];
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=;
    by rewrite /= insert_size /=.

  have Hmid3 : ibeg i1.1 < splitPos2 <= iend i1.1.
    move/andP: Hmid2 => [Hmid2 ?].
    move/(leq_eqF E) in Hmid2.
    by ordered.

  (* Wimmer: "All active and inactive intervals for this register intersecting
     with current are split before the start of current and spilled to the
     stack.  These split children are not considered during allocation any
     more because they do not have a register assigned.  If they have a use
     positions requiring a register, however, they must be reloaded again to a
     register later on.  Therefore, they are split a second time before these
     use positions, and the second split children are sorted into the
     unhandled list.  They get a register assigned when the allocator advances
     to the start position of these intervals." *)
  case: (splitInterval i1.2 Hodd2 Hmid3)
    => [[i1_0 i1_1] [/= H1_1 H2_1 H3_1]] //.

  (* The second interval goes back on the unhandled list, to be processed in a
     later iteration.  Note: this cannot change the head of the unhandled
     list. *)
  have := ScanState_newUnhandled st i1_1.2.
  rewrite Hunh => /=.
  have Hincr: (beg < ibeg i1_1.1) by ordered.
  move/(_ Hincr).
  rewrite /= => {st} st.

  move: st.
  set unh' := insert _ _ _.
  set sd' := (X in ScanState _ X).
  rewrite /= in sd' *.
  move=> st.

  have Hle : nextInterval sd <= nextInterval sd' by ordered.

  (* The first interval goes onto the handled list, with no register assigned
     to indicate a spill. *)
  case: spill => [||xid' reg' Hin|xid' reg' Hin].
  - move: (ScanState_newHandled st i1.2) => st'.
    apply: inr _.
    exists (_; st').
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=;
    try by rewrite size_map insert_size.
    by ordered.
  - rewrite /sd' in st.
    case U: unh' => [|u' us'] in sd' Hle st.
      move: U.
      rewrite /unh'.
      clear.
      rewrite /insert /= -/insert.
      set b := lebf _ _ _.
      by case: b; discriminate.
    move: (ScanState_moveUnhandledToHandled st) => st'.
    apply: inr _.
    exists (_; st').
    apply Build_SSMorph => //=;
    try by rewrite size_map insert_size.
  - have Hin' : widen_fst (xid', reg') \in active sd'.
      rewrite /sd' /= mem_map //=.
      exact: widen_fst_inj.
    move: (moveActiveToHandled st Hin') => [sd'' st'' [[[?] H] [Heqe Heqe2]]].
    apply: inr _.
    exists (sd''; st'').
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=.
    + by ordered.
    + admit.
    + admit.
  - have Hin' : widen_fst (xid', reg') \in inactive sd'.
      rewrite /sd' /= mem_map //=.
      exact: widen_fst_inj.
    move: (moveInactiveToHandled st Hin') => [sd'' st'' [[[?] H] [Heqe Heqe2]]].
    apply: inr _.
    exists (sd''; st'').
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=.
    + by ordered.
    + admit.
    + admit.
Defined.

Definition spillCurrentInterval {pre} :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> ssi.
  case: ssi => sd.
  case=> H. case: H => /=; case.
  case Hunh: (unhandled sd) => //= [[uid beg] us].
  move=> H1 H2 H3.
  have := getInterval uid.
  set d := (X in Interval X).
  move=> i st.
  case Hbeg2: (beg <= ibeg d); last first.
    exact: inl (EIntervalBeginsBeforeUnhandled uid). (* ERROR *)
  case: (spillInterval st Hunh uid Hbeg2
           (UnhandledToHandled sd)) => [err|[ss [/= ?]]].
    exact: inl err.
  apply: inr (tt, _).
  apply: (Build_SSInfo _ st).
  apply Build_SSMorphHasLen => //=;
  try apply Build_SSMorphHasLen => //=;
  try apply Build_SSMorphLen => //=;
  try apply Build_SSMorph => //=;
  by rewrite Hunh.
Defined.

Definition splitUnhandledInterval `(st : ScanState InUse sd)
  `(Hunh : unhandled sd = (uid, beg) :: us) (pos : SplitPosition) :
  SSError + { ss : ScanStateSig maxReg InUse | SSMorphLen sd ss.1 }.
Proof.
  case: sd => /= [? ints ? unh ? ? ?] in st uid us Hunh *.
  set int := vnth ints uid.

  case: (splitPosition int.2 pos) => [splitPos Hodd].

  (* Ensure that the [splitPos] falls within the interval, otherwise our
     action can have no effect.

     jww (2015-03-05): Evidence should be given so we do not need this
     check. *)
  case Hmid: (ibeg int.1 < splitPos <= iend int.1); last first.
    case Hbeg2: (beg <= ibeg int.1); last first.
      exact: inl (ENoValidSplitPositionUnh pos uid). (* ERROR *)

    move: st.
    set sd := (X in ScanState _ X).
    move=> st.

    case: (spillInterval st Hunh uid Hbeg2
             (UnhandledToHandled sd)) => [err|[ss [/= ?]]].
      exact: inl err.
    apply: inr (ss; _).
    apply Build_SSMorphLen => //=.
    admit.

  case Hint: int => [d i] in Hmid *.
  case: d => [iv ib ie rds] /= in i Hint Hmid *.

  case: (splitInterval i Hodd Hmid) => [[i0 i1] [/= H1 H2 H3]] //.

  (* The interval was split into two parts.  The first part will be dealt with
     by the caller (either moved to the active list to represent a register
     assignment, or move to the handled list to indicate a spill to the
     stack); the second goes back onto the unhandled list for processing
     later, unless it is empty (i.e., ibeg i == iend i, *and* there are no use
     positions). *)

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
     later iteration.  Note: this cannot change the head of the unhandled
     list. *)
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

  apply: inr (packScanState st; _).
  apply Build_SSMorphLen.
  apply Build_SSMorph => //=.
  by rewrite insert_size.
Defined.

(** If [reg] is some value, it means we allocate the first part of the split
   interval to that register; otherwise, we spill it. *)
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
  case=> [err|[[sd st] [[/= ? H]]]].
    exact: inl err.
  apply: (inr (tt, _)).
  apply: (Build_SSInfo _ st).
  rewrite Hunh /= in H.
  specialize (H (ltn0Sn _)).
  apply Build_SSMorphHasLen;
  try apply Build_SSMorphLen;
  try apply Build_SSMorph;
  rewrite ?insert_size ?size_map //;
  try move=> Hpre;
  exact: (leq_trans H1 _).
Defined.

Definition splitActiveOrInactiveInterval `(st : ScanState InUse sd)
  `(Hunh : unhandled sd = (uid, beg) :: us)
  (xid : IntervalId sd) (pos : SplitPosition) (reg : PhysReg)
  (Hbeg : beg <= (splitPosition (getInterval xid) pos).1)
  (Hin : ((xid, reg) \in active sd) + ((xid, reg) \in inactive sd)) :
  SSError + { ss : ScanStateSig maxReg InUse | SSMorphHasLen sd ss.1 }.
Proof.
  case: sd => /= [ni ints ? unh ? ? ?] in st uid us xid Hunh Hbeg Hin *.
  set int := vnth ints xid.

  case: (splitPosition int.2 pos) => [splitPos Hodd] in Hbeg *.

  move: st.
  set sd := (X in ScanState _ X).
  move=> st.

  have Hsize : 0 < size (unhandled sd).
    rewrite /= in sd st *.
    by rewrite /sd /= Hunh.

  have inactiveToHandled :
    (forall sd : ScanStateDesc maxReg, ScanState InUse sd
       -> 0 < size (unhandled sd)
       -> forall (xid : IntervalId sd) (reg : PhysReg),
          (xid, reg) \in inactive sd
       -> { ss : ScanStateSig maxReg InUse
          | SSMorphHasLen sd ss.1 }).
    move=> sd' st' H xid' reg' Hin'.
    apply: exist _ _ _.
      have /= := (ScanState_moveInactiveToHandled st' Hin').
      set sd'' := (X in ScanState _ X).
      move=> st''.
      exact: (exist _ sd'' st'').
    rewrite /=.
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=;
    by rewrite size_map.

  (* Ensure that the [splitPos] falls within the interval. *)
  case Hmid: (ibeg int.1 < splitPos <= iend int.1); last first.
    (* If the [splitPos] is before the beginning, there's really nothing we
       can do except fail.  But if our interval begins at or after [beg], then
       we can try to spill the first part of the interval (or all of it, if
       there are no use positions requiring registers). *)
    case Hbeg2: (beg <= ibeg int.1); last first.
      exact: inl (ENoValidSplitPosition pos xid). (* ERROR *)

    case: Hin => [Hin|Hin].
      case: (spillInterval st Hunh xid Hbeg2 (ActiveToHandled Hin))
        => [err|[ss [[[/= ?] ?] ?]]].
        exact: inl err.
      exact: inr (ss; _).
    case: (spillInterval st Hunh xid Hbeg2 (InactiveToHandled Hin))
      => [err|[ss [[[/= ?] ?] ?]]].
      exact: inl err.
    exact: inr (ss; _).

  case Hint: int => [d i] in Hmid *.
  case: d => [iv ib ie rds] /= in i Hint Hmid *.

  case: (splitInterval i Hodd Hmid) => [[i0 i1] [/= H1 H2 H3]] //.

  (* The interval was split into two parts.  The first part is left where it
     was (it is simply shorter now, but it's beginning has not changed), while
     the second part is spilled -- unless the second part contains a use
     position that requires a register, in which case we split at that point,
     and the first part of that split child is spilled, and the second part is
     put on the unhandled list. *)

  (* Update the state with the new dimensions of the first interval. *)
  move: (ScanState_setInterval st) => /= /(_ xid i0.1 i0.2).
  move: Hint; rewrite /int => ->.
  move/eqP in H2; rewrite eq_sym in H2; move/(_ H2).
  rewrite /= => {Hsize sd st} st.

  move: st.
  set sd := (X in ScanState _ X).
  move=> st.

  have Hbeg2 : beg <= ibeg i1.1
    by clear -H1 Hbeg; rewrite /= in Hbeg; ordered.

  have Hsize2 : 0 < size (unhandled sd).
    rewrite /= in sd st *.
    by rewrite /sd /= Hunh.

  have Hle : ni <= nextInterval sd by [].

  (* Spill the second interval, unless it has a use position that requires a
     register, in which case we spill the first place and add the second part
     back onto the unhandled list for processing later. *)
  case: Hin => [Hin|Hin].
    have Hin' : (widen_ord Hle xid, reg) \in active sd.
      rewrite /sd /= in Hle *.
      by rewrite widen_ord_spec.
    case: (spillInterval st Hunh xid Hbeg2 (ActiveToHandled Hin'))
      => [err|[ss [[[/= ?] ?] ?]]].
      exact: inl err.
    exact: inr (ss; _).
  have Hin' : (widen_ord Hle xid, reg) \in inactive sd.
    rewrite /sd /= in Hle *.
    by rewrite widen_ord_spec.
  case: (spillInterval st Hunh xid Hbeg2 (InactiveToHandled Hin'))
    => [err|[ss [[[/= ?] ?] ?]]].
    exact: inl err.
  exact: inr (ss; _).
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
    apply: (inr (tt, (Build_SSInfo _ st))).
    apply Build_SSMorphHasLen;
    try apply Build_SSMorphHasLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorph => //=;
    by rewrite Hunh.

  case Hbeg: (beg <= (splitPosition (getInterval aid) pos).1); last first.
    exact: inl (ECannotSplitSingleton pos aid). (* ERROR *)

  move/splitActiveOrInactiveInterval: st
    => /(_ uid beg us Hunh aid pos reg Hbeg) /=.

  have Hin' : (((aid, reg) \in active0) + ((aid, reg) \in inactive0))%type.
    case: trueForActives in Hintlist;
    pose H := (Hin aid _);
    specialize (H (mem_head _ _));
    rewrite Hintlist in H.
      exact: inl _.
    exact: inr _.
  move=> /(_ Hin') {Hin'}.

  case=> [err|[[sd st] [[/= [Hincr] H ?]]]].
    exact: inl err.
  apply: (inr (tt, _)).

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
Defined.

Definition splitActiveIntervalForReg {pre} (reg : PhysReg) (pos : oddnum) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit :=
  splitAssignedIntervalForReg reg (BeforePos pos (SplittingActive reg)) true.

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
