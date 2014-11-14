Require Import Lib.
Require Import NonEmpty3.

Require Export Range2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** * IntervalDesc *)

(** A lifetime interval defines the lifetime of a variable.  It is defined as
    a list of ranges "covered" by that variable in the low-level intermediate
    representation (LIR).  Gaps in the list of ranges are called "lifetime
    holes".  By summing the extent of a list of ranges, we have an idea of how
    much ground is left to cover, and this gives us a notion of well-founded
    recursion for iterating over intervals that may split as we examine them
    -- i.e., whose total extent must decrease after each pass.

    A lifetime is not necessarily only the distance that a variable is first
    and last used.  The lifetime of a variable used in a loop extends to the
    whole loop, for example, even if it is only used at the very end.  In this
    sense, coverage takes into account code flow, or what ranges would map to
    if all loops were unrolled, and then rolled back keeping track of
    coverage.

    Use positions are actual instructions where a variable is read from or
    written to, and whether it is required to be in a register at that
    point. *)

(** If for some reason we cannot assign a single register for all ranges, then
    the interval is split into two or more intervals, so each interval can be
    assigned its own register. *)

Record IntervalDesc : Set := {
    ibeg : nat;
    iend : nat;
    rds  : NonEmpty RangeSig
}.

(** * Interval *)

Inductive Interval : IntervalDesc -> Prop :=
  | I_Sing : forall x (r : Range x),
      Interval {| ibeg := rbeg x
                ; iend := rend x
                ; rds  := [::: (x; r)]
                |}

  | I_Cons : forall xs,
      Interval {| ibeg := rbeg (NE_head xs).1
                ; iend := rend (NE_last xs).1
                ; rds  := xs
                |}
        -> forall r (H : rend r.1 < rbeg (NE_head xs).1),
      Interval {| ibeg := rbeg r.1
                ; iend := rend (NE_last xs).1
                ; rds  := [::: r & xs]
                |}.

Tactic Notation "Interval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "I_Sing"
  | Case_aux c "I_Cons"
  ].

Definition getIntervalDesc `(i : Interval d) := d.
Arguments getIntervalDesc [d] i /.

Coercion getIntervalDesc : Interval >-> IntervalDesc.

Definition packInterval `(i : Interval d) := exist Interval d i.
Arguments packInterval [d] i /.

Definition intervalStart `(Interval i) : nat := ibeg i.
Definition intervalEnd   `(Interval i) : nat := iend i.

Arguments intervalStart [i] _ /.
Arguments intervalEnd [i] _ /.

Definition intervalCoversPos `(i : Interval d) (pos : nat) : bool :=
  (intervalStart i <= pos) && (pos < intervalEnd i).
Arguments intervalCoversPos [d] i pos /.

Definition intervalExtent `(i : Interval d) := intervalEnd i - intervalStart i.

Definition Interval_is_singleton `(i : Interval d) :=
  (NE_length (rds d) == 1)
    && (NE_length (ups (NE_head (rds d)).1) == 1).
Arguments Interval_is_singleton [d] i /.

Lemma intervalConnected
  `(i : Interval {| ibeg := ib
                  ; iend := ie
                  ; rds  := NE_append [::: r] xs |}) :
  rend r.1 < rbeg (NE_head xs).1.
Proof. move: i. invert as [ [rd0 r0] i [rd1 r1] | ] => //=. Admitted.

Lemma Interval_exact_end `(i : Interval d) :
  iend d = rend (NE_last (rds d)).1.
Proof. move: i. invert as [ [rd0 r0] i [rd1 r1] | ] => //=. Admitted.

Definition intervalUncons
  `(i : Interval {| ibeg := ib
                  ; iend := ie
                  ; rds := NE_append [::: r] xs |}) :
  [ /\ Interval {| ibeg := ib
                 ; iend := rend r.1
                 ; rds := [::: r] |}
  &    Interval {| ibeg := rbeg (NE_head xs).1
                 ; iend := ie
                 ; rds := xs |}
  ].
Admitted.
(* Proof. *)
(*   inversion i as [rd0 r0|rd1 r1 H1 H2 H3]. *)
(*   elim: i => rd1 r1 //=. *)
(*   case: xs => [u us] /=. *)
(*   case: r => rd r * /=. *)
(*   split. *)
(*   admit. *)
(*     apply (I_Sing r). *)
(* Defined. *)

Definition intervalsIntersect `(Interval i) `(Interval j) : bool :=
  let f (x y : RangeSig) : bool := rangesIntersect x.2 y.2 in
  has (fun (x : RangeSig) => has (f x) (list_of_ne (rds j)))
      (list_of_ne (rds i)).

Definition intervalIntersectionPoint `(Interval i) `(Interval j) : option nat :=
  NE_fold_left
    (fun acc rd =>
       match acc with
       | Some x => Some x
       | None =>
         NE_fold_left
           (fun acc' rd' =>
              match acc' with
              | Some x => Some x
              | None => rangeIntersectionPoint rd.2 rd'.2
              end) (rds j) None
       end) (rds i) None.

Definition findIntervalUsePos `(Interval i) (f : UsePos -> bool) :
  option (RangeSig * UsePos).
  Admitted.
(*
  :=
  let f r := match r with
      | exist rd r' => match findRangeUsePos r' f with
          | Some pos => Some (r, pos)
          | None => None
          end
      end in
  let fix go rs := match rs with
      | NE r nil => f r
      | NE r (r' :: rs') => option_choose (f r) (go (NE r' rs'))
      end in
  go (rds i).
*)

Definition nextUseAfter `(i : Interval d) (pos : nat) : option nat :=
  option_map (uloc \o @snd _ _) (findIntervalUsePos i (fun u => pos < uloc u)).
Arguments nextUseAfter [d] i pos /.

Definition firstUsePos `(i : Interval d) : nat :=
  uloc (NE_head (ups (NE_head (rds d)).1)).
Arguments firstUsePos [d] i /.

Definition firstUseReqReg `(i : Interval d) : option nat :=
  option_map (uloc \o @snd _ _) (findIntervalUsePos i regReq).
Arguments firstUseReqReg [d] i /.

Definition lastUsePos `(i : Interval d) : nat :=
  uloc (NE_last (ups (NE_last (rds d)).1)).
Arguments lastUsePos [d] i /.

Lemma Interval_nonempty : forall `(i : Interval d),
  intervalStart i < intervalEnd i.
Proof.
  rewrite /intervalStart /intervalEnd.
  move=> d. elim=> [rd r|rs i H [rd r] Hend] * /=;
    first exact: Range_bounded.
  move: (Range_bounded r).
  move=> H0.
  exact/(ltn_trans H0)/(ltn_trans Hend).
Qed.

Lemma Interval_extent_nonzero : forall `(i : Interval d), intervalExtent i > 0.
Proof. move=> d i; move: subn_gt0 (Interval_nonempty i) => -> //. Qed.

Notation IntervalSig := { d : IntervalDesc | Interval d }.

Record DividedInterval `(i : Interval d) (f : UsePos -> bool)
  `(i1 : Interval d1) `(i2 : Interval d2) : Prop := {
    _ : all f (ups (NE_head (rds i1)).1);
    _ : ~~ f (NE_head (ups (NE_head (rds i2)).1));
    _ : ibeg i == ibeg i1;
    _ : iend i == iend i2;
    _ : iend i1 < ibeg i2
}.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition SubIntervalsOf (before : nat) `(i : Interval d)
  (p : option IntervalSig * option IntervalSig) :=
  let f u := uloc u < before in
  match p with
  | (Some i1, Some i2) => DividedInterval i f i1.2 i2.2
  | (Some i1, None) =>
      rds d = rds i1.1 /\ all f (ups (NE_last (rds i1.1)).1)
  | (None, Some i2) =>
      rds d = rds i2.1 /\ ~~ f (NE_head (ups (NE_head (rds i2.1)).1))
  | (None, None) => False
  end.

Program Definition splitPosition `(i : Interval d) (before : option nat)
  (H : firstUsePos i < lastUsePos i) :
  { n : nat | firstUsePos i < n <= lastUsePos i } :=
  let initial := firstUsePos i in
  let final := lastUsePos i in
  maxn initial.+1
    (minn final (fromMaybe final (option_choose before (firstUseReqReg i)))).
Obligation 1.
  apply/andP; split.
    rewrite leq_max.
    by apply/orP; left.
  rewrite geq_max.
  apply/andP; split. by [].
  rewrite geq_min.
  by apply/orP; left.
Qed.

Lemma Interval_beg_bounded `(i : Interval d) : ibeg d <= firstUsePos i.
Proof.
  rewrite /firstUsePos.
  elim: i => [rd r|rs i H [rd r]] * /=;
    first exact: (Range_beg_bounded r).
  pose (Range_beg_bounded r). simpl in *. auto.
Qed.

Lemma Interval_beg_of_rds `(i : Interval d) :
  ibeg d == rbeg (NE_head (rds d)).2.
Proof. by elim: i => * //=. Qed.

Lemma Interval_end_of_rds `(i : Interval d) :
  iend d == rend (NE_last (rds d)).2.
Proof. elim: i => [|[? ?]] //. Qed.

Fixpoint Interval_end_bounded `(i : Interval d) : lastUsePos i < iend d.
Admitted.
(*
Proof.
  case: d i => ib ie rds /=.
  invert as [rd r| ] => /=;
    first apply: (Range_end_bounded r);
  rename H1 into i;
  exact: (Interval_end_bounded i).
Qed.
*)

Fixpoint Interval_rds_bounded `(i : Interval d) :
  firstUsePos i <= lastUsePos i.
Proof.
  Interval_cases (inversion i) Case; simpl in *.
  - Case "I_Sing".
    rewrite -{}H /=.
    exact: (Range_ups_bounded r).
  - Case "I_Cons".
    rewrite -{}H1 /=.
    move: (Interval_rds_bounded _ H) => /= {H} H1.
    move: (Range_ups_bounded r.2) => H2.
    move: (Range_end_bounded r.2) => H3.
    move: (Range_beg_bounded (NE_head xs).2) => H4.
    apply (leq_trans H2).
    apply ltnW in H3.
    apply (leq_trans H3).
    apply ltnW in H0.
    apply (leq_trans H0).
    move: xs => [x xs] in H0 H1 H4 *.
    by apply (leq_trans H4).
Qed.

Definition Interval_rds_size_bounded `(i : Interval d) :
  ~~ Interval_is_singleton i -> firstUsePos i < lastUsePos i.
Proof.
  Interval_cases (inversion i) Case; simpl in *.
  - Case "I_Sing".
    rewrite -{}H => /= H.
    move: (Range_sorted r).
    case: (ups x) H => //= [u us] H H1.
    admit.
    (* by apply NE_Forall_last in H1. *)
  - Case "I_Cons".
    rewrite -{}H1 => /= H2.
    move: (Interval_rds_bounded H) => /= {H} H1.
    move: (Range_ups_bounded r.2) => H3.
    move: (Range_end_bounded r.2) => H4.
    move: (Range_beg_bounded (NE_head xs).2) => H5.
    apply (leq_ltn_trans H3).
    apply (ltn_trans H4).
    apply (ltn_leq_trans H0).
    move: xs => [x xs] in H0 H1 H4 H5 *.
    by apply (leq_trans H5).
Qed.

Lemma Interval_bounded `(i : Interval d) : ibeg d < iend d.
Proof.
  case: d i => ib ie rds /= i.
  move: (Interval_beg_bounded i) => /= H1.
  move: (Interval_end_bounded i) => /= H2.
  move: (Interval_rds_bounded i) => /= H3.
  apply (leq_ltn_trans H1).
  by apply (leq_ltn_trans H3).
Qed.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Fixpoint intervalSpan (rs : NonEmpty RangeSig) (before : nat)
  `(i : Interval {| ibeg := ib
                  ; iend := ie
                  ; rds  := rs |}) {struct rs} :
  { p : option IntervalSig * option IntervalSig | SubIntervalsOf before i p }.
Proof.
  set f := (fun u => (uloc u < before)).
  destruct rs as [r|r rs] using ne_ind;
  case: (@rangeSpan f _ r.2) => [[[r0| ] [r1| ]]].

  - Case "rs = R_Sing r; (o, o0) = (Some, Some)".
    move=> [? ? ? /eqP H2 /eqP H3 *].
    move: (Interval_beg_of_rds i) (Interval_end_of_rds i).
    rewrite H2 H3.
    by eexists (Some (exist _ _ (I_Sing r0.2)),
                Some (exist _ _ (I_Sing r1.2))).

  - Case "rs = R_Sing r; (o, o0) = (Some, None)".
    move=> [<- H0].
    by exists (Some (exist _ _ i), None).

  - Case "rs = R_Sing r; (o, o0) = (None, Some)".
    move=> [<- H0].
    by exists (None, Some (exist _ _ i)).

  - Case "rs = R_Sing r; (o, o0) = (None, None)".
    contradiction.

  - Case "rs = R_Cons r rs'; (o, o0) = (Some, Some)".
    move=> [? ? ? /eqP H2 /eqP H3 *].

    move: (intervalUncons i) => [? i1].
    move: (intervalConnected i) => *.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_beg_of_rds i) (Interval_end_of_rds i).
    rewrite H2.
    move=> /= Hb He.
    have Hi: rend r1.1 < rbeg (NE_head rs).1 by rewrite -H3.

    by exists (Some (exist _ _ (I_Sing r0.2)),
               Some (exist _ _ (I_Cons i1 Hi))).

  - Case "rs = R_Cons r rs'; (o, o0) = (Some, None)".
    move=> [<- H0].

    (* In this branch, we know that all of [r] is < before, and that the point
       to split may be one of the ranges in [rs].  So we divide the current
       interval into two: [i0] covering the range that is < before, and [i1]
       covering the remainder. *)
    move: (intervalUncons i) => [i0 i1].
    move: (intervalConnected i) => Hi0.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_beg_of_rds i) (Interval_end_of_rds i).

    (* After splitting [i1], the result we finally return will effectively be
      (i0 :: i1_1, i1_2). *)
    move: (intervalSpan rs before _ _ i1) => /= [] [[i1_1| ] [i1_2| ]].
    + SCase "(Some, Some)".
      move=> [? ? /eqP H2 /eqP H3 ? H4].
      destruct i1_1 as [i1_1d i1_1i] eqn:Heqe.
      destruct i1_1d as [? ? ?].
      move: (Interval_beg_of_rds i1_1i)
            (Interval_end_of_rds i1_1i) => /eqP Hb /eqP He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_1i H4.
      rewrite Hb in H2.
      rewrite H2 in Hi0.
      rewrite H3.
      have i1_1i' := I_Cons i1_1i Hi0.
      rewrite -He in i1_1i'.
      by exists (Some (exist _ _ i1_1i'), Some i1_2).

    + SCase "(Some, None)".
      move=> [<- /= Ht].
      by exists (Some (exist _ _ (I_Cons i1 Hi0)), None).

    + SCase "(None, Some)".
      move=> [<- /= Hf].
      by exists (Some (exist _ _ i0), Some (exist _ _ i1)).

    + SCase "(None, None)".
      contradiction.

  - Case "rs = R_Cons r rs'; (o, o0) = (None, Some)".
    move=> [<- H0].
    by exists (None, Some (exist _ _ i)).

  - Case "rs = R_Cons r rs'; (o, o0) = (None, None)".
    contradiction.
Defined.

Definition DefiniteSubIntervalsOf (before : nat) `(i : Interval d)
  (p : IntervalSig * IntervalSig) :=
  let f u := uloc u < before in
  let: (i1, i2) := p in DividedInterval i f i1.2 i2.2.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Definition splitInterval (before : nat) `(i : Interval d)
  (H : firstUsePos i < before <= lastUsePos i) :
  { p : IntervalSig * IntervalSig | DefiniteSubIntervalsOf before i p }.
Proof.
  case: d => ib ie rds in i H *.
  case: (intervalSpan before i) => // [] [[i0| ] [i1| ]].
  - Case "(Some, Some)".
    move=> [Ht Hf H1 H2 H3].
    by exists (i0, i1).
  - Case "(Some, None)".
    move: H => /andP [Hb He].
    move=> [<- /= H]; exfalso.
    apply NE_Forall_last in H.
    rewrite /lastUsePos /= leqNgt H in He.
    by move: He => /negbTE.
  - Case "(None, Some)".
    move: H => /andP [Hb He].
    move=> [<- /= /negbTE H]; exfalso.
    by rewrite /firstUsePos /= H in Hb.
  - Case "(None, None)".
    contradiction.
Defined.

Definition splitInterval_spec (before : nat) `(i : Interval d)
  (H : firstUsePos i < before <= lastUsePos i) :
  let: exist (i1, i2) Hdi := splitInterval H in
  intervalExtent i1.2 + intervalExtent i2.2 < intervalExtent i.
Proof.
  case: (splitInterval H) => [[i1 i2] [_ _ /eqP H1 /eqP H2 ?]] /=.
  rewrite /intervalExtent /=.
  rewrite {}H1 {}H2 {H i d}.
  apply four_points.
  apply/andP; split.
    apply/andP; split.
      by move: (Interval_bounded i1.2).
    by [].
  by move: (Interval_bounded i2.2).
Qed.

(** * Fixed Intervals *)

(** Effectively these are just pre-allocated registers.

    Some machine instructions require their operands in fixed registers. Such
    constraints are already considered during the construction of the LIR by
    emitting physical register operands instead of virtual register
    operands. Although the register allocator must leave these operands
    unchanged, they must be considered during register allocation because they
    limit the number of available registers. Information about physical
    registers is collected in fixed intervals.

    For each physical register, one fixed interval stores where the register
    is not available for allocation. Use positions are not needed for fixed
    intervals because they are never split and spilled. Register constraints
    at method calls are also modeled using fixed intervals: Because all
    registers are destroyed when the call is executed, ranges of length 1 are
    added to all fixed intervals at the call site. Therefore, the allocation
    pass cannot assign a register to any interval there, and all intervals are
    spilled before the call.

    Note that we do not distinguish between the two types of intervals in this
    code, and in fact make use of the use positions to track the locations of
    fixity (such as call sites) within the code. *)

Definition FixedInterval := Interval.
