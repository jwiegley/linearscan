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

Section Spill.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Inductive SpillCondition (sd : ScanStateDesc maxReg) (uid : IntervalId sd)
  (i : IntervalSig) :=
  | NewToHandled : SpillCondition uid i
  | UnhandledToHandled :
      vnth (intervals sd) uid = i -> SpillCondition uid i
  | ActiveToHandled xid reg   :
      vnth (intervals sd) xid = i ->
      (xid, reg) \in active sd    -> SpillCondition uid i
  | InactiveToHandled xid reg :
      vnth (intervals sd) xid = i ->
      (xid, reg) \in inactive sd -> SpillCondition uid i.

Definition SpillConditionToT `(x : @SpillCondition sd uid i) :=
  match x with
  | NewToHandled                  => NewToHandledT uid
  | UnhandledToHandled _          => UnhandledToHandledT uid
  | ActiveToHandled xid reg _ _   => ActiveToHandledT xid reg
  | InactiveToHandled xid reg _ _ => InactiveToHandledT xid reg
  end.

Tactic Notation "SpillCondition_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "NewToHandled"
  | Case_aux c "UnhandledToHandled"
  | Case_aux c "ActiveToHandled"
  | Case_aux c "InactiveToHandled"
  ].

Definition spillInterval `(st : ScanState InUse sd)
  (i1 : IntervalSig) `(Hunh : unhandled sd = (uid, beg) :: us)
  (Hbeg : beg <= ibeg i1.1) (spill : SpillCondition uid i1) (e : seq SSTrace) :
  seq SSTrace +
    { ss : ScanStateSig maxReg InUse
    | if spill is UnhandledToHandled _
      then if firstUseReqReg i1.2 is Some _
           then SSMorphLen sd ss.1
           else SSMorph sd ss.1
      else SSMorphHasLen sd ss.1 }.
Proof.
  have e2 := ESpillInterval (SpillConditionToT spill) :: e.

  (* Is there a use position requiring a register in the interval?  If yes,
     then split it again; otherwise, spill it. *)
  case S: (firstUseReqReg i1.2) => [[[splitPos2 Hodd2] /= Hmid2] |]; last first.
    move/eqP in S.
    SpillCondition_cases
      (case: spill => [|Heqe|xid reg Heqe Hin|xid reg Heqe Hin]) Case.
    - Case "NewToHandled".
      move: (ScanState_newHandled st S) => st'.
      apply: inr _.
      exists (_; st').
      apply Build_SSMorphHasLen => //=;
      try apply Build_SSMorphLen => //=;
      try apply Build_SSMorph => //=;
      by rewrite size_map Hunh.

    - Case "UnhandledToHandled".
      rewrite [firstUseReqReg]lock in S.
      destruct sd; simpl in *.
      rewrite Hunh in st.
      have Hreq: firstUseReqReg (vnth intervals uid).2 == None.
        rewrite -lock in S.
        by rewrite Heqe S.
      move: (ScanState_moveUnhandledToHandled st Hreq) => st'.
      apply: inr _.
      exists (_; st').
      exact: Build_SSMorph.

    - Case "ActiveToHandled".
      have Hreq : (firstUseReqReg (getInterval xid) == None)
        by rewrite /getInterval Heqe.
      move: (moveActiveToHandled st Hin (spilled:=true) Hreq)
        => [sd' st' [[[? ?] H] _]].
      apply: inr _.
      exists (sd'; st').
      apply Build_SSMorphHasLen => //=.
      apply H.
      by rewrite Hunh.

    - Case "InactiveToHandled".
      have Hreq : (firstUseReqReg (getInterval xid) == None)
        by rewrite /getInterval Heqe.
      move: (moveInactiveToHandled st Hin (spilled:=true) Hreq)
        => [sd' st' [[[? ?] H] _]].
      apply: inr _.
      exists (sd'; st').
      apply Build_SSMorphHasLen => //=.
      apply H.
      by rewrite Hunh.

  have e3 := EIntervalHasUsePosReqReg splitPos2 :: e2.

  case E: (ibeg i1.1 == splitPos2).
    (* This interval goes back on the unhandled list, to be processed in a
       later iteration. Note: this cannot change the head of the unhandled
       list. *)
    case Hincr: (beg < ibeg i1.1); last first.
      move=> *.
      exact: inl (ECannotInsertUnhandled ::
                  EIntervalBeginsAtSplitPosition :: e3).

    have := ScanState_newUnhandled st i1.2.
    rewrite Hunh => /=.
    move/(_ Hincr).
    rewrite /= => {st} st.

    apply: inr (packScanState st; _).
    case: spill => [|*|*|*];
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=;
    by rewrite /= insert_size /=.

  have Hmid3 : ibeg i1.1 < splitPos2 <= iend i1.1.
    clear S.
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

  (* jww (2015-05-21): This should be [None] by definition, but I lack the
     evidence for now, from the first use of [firstUseReqReg] and then
     [splitInterval] at the returned position. *)
  case Hreq: (firstUseReqReg i1_0.2) => [[pos ?]|].
    exact: inl (ECannotSpillIfRegisterRequired pos.1 :: e3).
  rewrite [firstUseReqReg]lock in Hreq.
  move/eqP in Hreq.

  (* The second interval will go back on the unhandled list, to be processed
     in a later iteration. Note: By definition of [insert] and
     [ScanState_newUnhandled], it cannot become the new first element.
     jww (2015-05-22): This should be proven. *)
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
  SpillCondition_cases
    (case: spill => [|Heqe|xid reg Heqe Hin|xid reg Heqe Hin]) Case.
  - Case "NewToHandled".
    rewrite -lock in Hreq.
    move: (ScanState_newHandled st Hreq) => {st} st.
    apply: inr _.
    exists (_; st).
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=;
    try by rewrite size_map insert_size;
    by ordered.
    by ordered.

  - Case "UnhandledToHandled".
    (* Update the state with the new dimensions of the first interval. *)
    move: (ScanState_setInterval st)
      => /= /(_ (widen_ord Hle uid) i1_0.1 i1_0.2).

    have Hint : ibeg i1_0.1 ==
                ibeg (vnth (vshiftin (intervals sd) (i1_1.1; i1_1.2))
                           (widen_ord Hle uid)).1.
      have ->: widen_ord Hle uid = widen_id uid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      by rewrite vnth_vshiftin Heqe -H2_1.

    have Hend : iend i1_0.1 <=
                iend (vnth (vshiftin (intervals sd) (i1_1.1; i1_1.2))
                           (widen_ord Hle uid)).1.
      have ->: widen_ord Hle uid = widen_id uid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      rewrite vnth_vshiftin Heqe.
      by ordered.

    case Hnot: (widen_ord Hle uid \notin handledIds sd'); last first.
      move=> *.
      exact: inl (ECannotModifyHandledInterval uid :: e3).

    move/(_ Hint Hend is_true_true).
    rewrite /= => {Hint Hend Hnot st} st.

    rewrite /sd' in st.
    case U: unh' => [|u' us'] in sd' Hle st.
      move: U.
      rewrite /unh'.
      clear.
      rewrite /insert /= -/insert.
      set b := lebf _ _ _.
      by case: b; discriminate.
    rewrite /unh' /insert /= -/insert /widen_fst in U.

    have Hreq' : firstUseReqReg
                   (vnth (vreplace (vshiftin (intervals sd) (i1_1.1; i1_1.2))
                                   (widen_ord Hle uid)
                                   (i1_0.1; i1_0.2)) (fst u')).2 == None.
      case F: (lebf snd (widen_fst (uid, beg)) (ord_max, ibeg i1_1.1)) in U;
      inversion U.
        have ->: widen_id uid = widen_ord Hle uid.
          rewrite /widen_id.
          f_equal.
          exact: eq_irrelevance.
        rewrite -lock in Hreq.
        by rewrite vnth_vreplace.
      rewrite /lebf /= in F.
      by ordered.

    move: (ScanState_moveUnhandledToHandled st Hreq') => {Hreq' st} st.

    apply: inr _.
    exists (_; st).

    apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=;
    case F: (lebf snd (widen_fst (uid, beg)) (ord_max, ibeg i1_1.1)) in U;
    inversion U => //;
    by rewrite insert_size.

  - Case "ActiveToHandled".
    move: (ScanState_setInterval st)
      => /= /(_ (widen_ord Hle xid) i1_0.1 i1_0.2).

    have Hint : ibeg i1_0.1 ==
                ibeg (vnth (vshiftin (intervals sd) (i1_1.1; i1_1.2))
                           (widen_ord Hle xid)).1.
      have ->: widen_ord Hle xid = widen_id xid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      by rewrite vnth_vshiftin Heqe -H2_1.

    have Hend : iend i1_0.1 <=
                iend (vnth (vshiftin (intervals sd) (i1_1.1; i1_1.2))
                           (widen_ord Hle xid)).1.
      have ->: widen_ord Hle xid = widen_id xid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      rewrite vnth_vshiftin Heqe.
      by ordered.

    case Hnot: (widen_ord Hle xid \notin handledIds sd'); last first.
      move=> *.
      exact: inl (ECannotModifyHandledInterval xid :: e3).

    move/(_ Hint Hend is_true_true).
    rewrite /= => {Hint Hend Hnot st} st.

    move: st.
    set sd'' := (X in ScanState _ X).
    rewrite /= in sd'' *.
    move=> st.

    pose elem := widen_fst (xid, reg).
    have Hin' : elem \in active sd'.
      rewrite /sd' /= mem_map //=.
      exact: widen_fst_inj.
    case Helem: elem => [a b] in Hin'.

    have Hreq' : if true
                 then firstUseReqReg (vnth (intervals sd'') a).2 == None
                 else true.
      rewrite /elem /widen_fst in Helem.
      inversion Helem.
      rewrite -lock in Hreq.
      have ->: widen_id xid = widen_ord Hle xid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      by rewrite /sd'' [vnth _]/= vnth_vreplace.

    move: (moveActiveToHandled st Hin' (spilled:=true) Hreq')
      => [sd3 st3 [[[? ?] H] _]].
    apply: inr _.
    exists (sd3; st3).
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=.
    + by ordered.
    + replace (unhandled sd') with unh' in H; last by auto.
      rewrite /unh' insert_size /= in H.
      by auto.
    + replace (unhandled sd') with unh' in H; last by auto.
      rewrite /unh' insert_size /= in H.
      by auto.

  - Case "InactiveToHandled".
    move: (ScanState_setInterval st)
      => /= /(_ (widen_ord Hle xid) i1_0.1 i1_0.2).

    have Hint : ibeg i1_0.1 ==
                ibeg (vnth (vshiftin (intervals sd) (i1_1.1; i1_1.2))
                           (widen_ord Hle xid)).1.
      have ->: widen_ord Hle xid = widen_id xid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      by rewrite vnth_vshiftin Heqe -H2_1.

    have Hend : iend i1_0.1 <=
                iend (vnth (vshiftin (intervals sd) (i1_1.1; i1_1.2))
                           (widen_ord Hle xid)).1.
      have ->: widen_ord Hle xid = widen_id xid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      rewrite vnth_vshiftin Heqe.
      by ordered.

    case Hnot: (widen_ord Hle xid \notin handledIds sd'); last first.
      move=> *.
      exact: inl (ECannotModifyHandledInterval xid :: e3).

    move/(_ Hint Hend is_true_true).
    rewrite /= => {Hint Hend Hnot st} st.

    move: st.
    set sd'' := (X in ScanState _ X).
    rewrite /= in sd'' *.
    move=> st.

    pose elem := widen_fst (xid, reg).
    have Hin' : elem \in inactive sd'.
      rewrite /sd' /= mem_map //=.
      exact: widen_fst_inj.
    case Helem: elem => [a b] in Hin'.

    have Hreq' : if true
                 then firstUseReqReg (vnth (intervals sd'') a).2 == None
                 else true.
      rewrite /elem /widen_fst in Helem.
      inversion Helem.
      rewrite -lock in Hreq.
      have ->: widen_id xid = widen_ord Hle xid.
        rewrite /widen_id.
        f_equal.
        exact: eq_irrelevance.
      by rewrite /sd'' [vnth _]/= vnth_vreplace.

    move: (moveInactiveToHandled st Hin' (spilled:=true) Hreq')
      => [sd3 st3 [[[? ?] H] _]].
    apply: inr _.
    exists (sd3; st3).
    apply Build_SSMorphHasLen => //=;
    try apply Build_SSMorphLen => //=;
    try apply Build_SSMorph => //=.
    + by ordered.
    + replace (unhandled sd') with unh' in H; last by auto.
      rewrite /unh' insert_size /= in H.
      by auto.
    + replace (unhandled sd') with unh' in H; last by auto.
      rewrite /unh' insert_size /= in H.
      by auto.
Defined.

Definition spillCurrentInterval {pre} :
  SState pre (@SSMorphHasLen maxReg) (@SSMorph maxReg) unit.
Proof.
  move=> e ssi.
  have e2 := ESpillCurrentInterval :: e.
  case: ssi => sd.
  case=> H. case: H => /=; case.
  case Hunh: (unhandled sd) => //= [[uid beg] us].
  move=> H1 H2 H3 H4.
  have := getInterval uid.
  set d := (X in Interval X).
  move=> i st.
  case Hbeg2: (beg <= ibeg d); last first.
    exact: inl (EIntervalBeginsBeforeUnhandled uid :: e).
  case: (spillInterval st Hunh Hbeg2 (UnhandledToHandled (refl_equal _)) e)
    => [err|[[sd' st'] H]].
    exact: inl err.
  apply: inr (tt, _).
  apply: (Build_SSInfo _ st').
  case: (firstUseReqReg (vnth (intervals sd) uid).2) => [[pos /= ?]|] in H.
  case: H => [[/= ? ?] _].
  apply Build_SSMorph => //=; try ordered.
    by (transitivity (fixedIntervals sd)).
  case: H => [/= ? ?].
  apply Build_SSMorph => //=; try ordered.
    by (transitivity (fixedIntervals sd)).
Defined.

End Spill.
