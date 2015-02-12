Require Import LinearScan.Lib.
Require Import LinearScan.Range.
Require Import LinearScan.UsePos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** * IntervalDesc *)

(** A lifetime interval defines the lifetime of a variable.  It is defined as
    a list of ranges "covered" by that variable in the low-level intermediate
    representation (LIR).  Gaps in the list of ranges are called "lifetime
    holes".

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

Inductive IntervalKind := Whole | LeftMost | Middle | RightMost.

Definition splitKind (k : IntervalKind) : IntervalKind * IntervalKind :=
  match k with
  | Whole     => (LeftMost, RightMost)
  | LeftMost  => (LeftMost, Middle)
  | Middle    => (Middle, Middle)
  | RightMost => (Middle, RightMost)
  end.

Record IntervalDesc : Set := {
    (* The [varId] is simply a number that refers to the variable for which
       this interval was created.  This number must be maintained by the
       caller, and has no meaning at this point in the code.  Note that
       multiple intervals can all relate to the same [varId]. *)
    ivar : nat;
    ibeg : nat;
    iend : nat;
    (* [ispl] is true if this interval is the left half of a split block,
       where isplit was [false] for that block; otherwise, isplit is
       inherited. *)
    iknd : IntervalKind;
    rds  : NonEmpty RangeSig
}.

(** * Interval *)

Inductive Interval : IntervalDesc -> Prop :=
  | I_Sing : forall i knd x (r : Range x),
      Interval {| ivar := i
                ; ibeg := rbeg x
                ; iend := rend x
                ; iknd := knd
                ; rds  := NE_Sing (x; r)
                |}

  | I_Cons : forall i knd xs,
      Interval {| ivar := i
                ; ibeg := rbeg (NE_head xs).1
                ; iend := rend (NE_last xs).1
                ; iknd := knd
                ; rds  := xs
                |}
        -> forall r (H : rend r.1 < rbeg (NE_head xs).1),
      Interval {| ivar := i
                ; ibeg := rbeg r.1
                ; iend := rend (NE_last xs).1
                ; iknd := knd
                ; rds  := NE_Cons r xs (* cons_range H *)
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
  intervalStart i <= pos < intervalEnd i.
Arguments intervalCoversPos [d] i pos /.

(* This lemma proves that if an [Interval] is formed from the list of ranges,
   where that list is at least a cons cell, then the end of the first element
   of the list occurs before the beginning of the head of the rest of the
   list. *)
Lemma intervalConnected
  `(i : Interval {| ivar := iv
                  ; ibeg := ib
                  ; iend := ie
                  ; iknd := z
                  ; rds := NE_Cons r xs |}) :
  rend r.1 < rbeg (NE_head xs).1.
Proof. move: i. invert => //. Qed.

Lemma Interval_exact_beg `(i : Interval d) :
  ibeg d = rbeg (NE_head (rds d)).1.
Proof. move: i. invert => //. Qed.

Lemma Interval_exact_end `(i : Interval d) :
  iend d = rend (NE_last (rds d)).1.
Proof. move: i. invert => //. Qed.

Definition intervalUncons
  `(i : Interval {| ivar := iv
                  ; ibeg := ib
                  ; iend := ie
                  ; iknd := z
                  ; rds := NE_Cons r xs |}) :
  [ /\ Interval {| ivar := iv
                 ; ibeg := ib
                 ; iend := rend r.1
                 ; iknd := z
                 ; rds := NE_Sing r |}
  &    Interval {| ivar := iv
                 ; ibeg := rbeg (NE_head xs).1
                 ; iend := ie
                 ; iknd := z
                 ; rds := xs |} ].
Proof.
  move: i. invert => //=.
  split; auto. subst.
  case: r H6 => [rd r] *.
  exact: (I_Sing iv z r).
Defined.

Definition intervalsIntersect `(Interval i) `(Interval j) : bool :=
  let f (x y : RangeSig) : bool := rangesIntersect x.2 y.2 in
  has (fun (x : RangeSig) => has (f x) (NE_to_list (rds j)))
      (NE_to_list (rds i)).

Definition intervalIntersectionPoint `(Interval i) `(Interval j) : option nat :=
  NE_foldl
    (fun acc rd =>
       match acc with
       | Some x => Some x
       | None =>
         NE_foldl
           (fun acc' rd' =>
              match acc' with
              | Some x => Some x
              | None => rangeIntersectionPoint rd.2 rd'.2
              end) None (rds j)
       end) None (rds i).

Definition findIntervalUsePos (d : IntervalDesc) (f : UsePos -> bool) :
  option (RangeSig * UsePos) :=
  let f r := match r with
      | exist rd r' => match findRangeUsePos r' f with
          | Some pos => Some (r, pos)
          | None => None
          end
      end in
  let fix go rs := match rs with
      | NE_Sing r     => f r
      | NE_Cons r rs' => option_choose (f r) (go rs')
      end in
  go (rds d).

Definition nextUseAfter (d : IntervalDesc) (pos : nat) : option nat :=
  option_map (uloc \o @snd _ _) (findIntervalUsePos d (fun u => pos < uloc u)).
Arguments nextUseAfter d pos /.

Definition firstUsePos (d : IntervalDesc) : option nat :=
  if ups (NE_head (rds d)).1 is u :: _
  then Some (uloc u)
  else None.
Arguments firstUsePos d /.

Definition firstUseReqReg (d : IntervalDesc) : option nat :=
  option_map (uloc \o @snd _ _) (findIntervalUsePos d regReq).
Arguments firstUseReqReg d /.

Lemma Interval_nonempty : forall `(i : Interval d),
  intervalStart i < intervalEnd i.
Proof.
  rewrite /intervalStart /intervalEnd.
  move=> d. elim=> [rd r|iv ? rs i H [rd r] Hend] * /=;
    first exact: Range_bounded.
  move: (Range_bounded r).
  move=> H0.
  exact/(ltn_trans H0)/(ltn_trans Hend).
Qed.

Lemma Interval_beg_of_rds `(i : Interval d) :
  ibeg d == rbeg (NE_head (rds d)).2.
Proof. by elim: i => * //=. Qed.

Lemma Interval_end_of_rds `(i : Interval d) :
  iend d == rend (NE_last (rds d)).2.
Proof. by elim: i => * //=. Qed.

Notation IntervalSig := { d : IntervalDesc | Interval d }.

Record DividedInterval `(i : Interval d) (before : nat)
  `(i1 : Interval d1) `(i2 : Interval d2) : Prop := {
  _ : iend i1 <= before <= ibeg i2;
  _ : ibeg i == ibeg i1;
  _ : iend i == iend i2
}.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition SubIntervalsOf (before : nat) `(i : Interval d)
  (p : option IntervalSig * option IntervalSig) :=
  let f u := u < before in
  match p with
  | (Some i1, Some i2) => DividedInterval i before i1.2 i2.2
  | (Some i1, None)    => [/\ ibeg d == ibeg i1.1
                          ,   iend i1.1 <= iend d
                          &   iend i1.1 <= before ]
  | (None, Some i2)    => [/\ iend d == iend i2.1
                          ,   ibeg d <= ibeg i2.1
                          &   before <= ibeg i2.1]
  | (None, None)       => False
  end.

Definition BoundedInterval (pos : nat) :=
  { i : IntervalSig | pos <= rbeg (NE_head (rds i.1)).1 }.

Definition transportBoundedInterval {base : nat} `(Hlt : base <= prev)
  (x : BoundedInterval prev) : BoundedInterval base.
  case: x => [i H].
  apply: exist.
  apply: i.
  exact/(leq_trans _ H).
Defined.

Definition Interval_fromRanges (vid : nat)
  `(sr : SortedRanges b) :
  forall r rs, sr.1 = r :: rs ->
  let rs' := NE_from_list r rs in
  Interval {| ivar := vid
            ; ibeg := rbeg (NE_head rs').1
            ; iend := rend (NE_last rs').1
            ; iknd := Whole
            ; rds  := rs' |}.
Proof.
  case: sr => /=.
  move=> x Hsort Hlt r rs Heqe; subst.
  set ups0 := NE_from_list _ _.
  have: NE_StronglySorted range_ltn ups0
    by exact: NE_StronglySorted_from_list.
  elim: ups0 => //= [r'|r' rs' IHrs'].
    move: (I_Sing vid Whole r'.2).
    by destruct r'; destruct x.
  invert.
  move: IHrs' => /(_ H1) i.
  have Hlt': rend r'.1 < rbeg (NE_head rs').1.
    move/NE_Forall_head in H2.
    by rewrite /range_ltn in H2.
  exact: (I_Cons (i:=vid) (knd:=Whole) i Hlt').
Defined.

Inductive SplitPosition :=
  | BeforePos of nat
  | BeforeFirstUsePosReqReg
  | EndOfLifetimeHole.

(* Given an interval, determine its optimal split position.  If no split
   position can be found, it means the interval may be safely spilled, and all
   further variable references should be accessed directly from memory. *)
Definition splitPosition `(i : Interval d) (pos : SplitPosition) :
  option nat :=
  match pos with
  | BeforePos x             => Some x
  | BeforeFirstUsePosReqReg => firstUseReqReg i
  | EndOfLifetimeHole       => None (* jww (2015-01-22): NYI *)
    (* This should be the same thing as splitting at the current position. *)
  end.

Lemma Interval_bounded `(i : Interval d) : ibeg d < iend d.
Proof.
  elim: i => //= [i knd x r|i knd xs i0 H r Hlt].
    exact: Range_bounded r.
  move: (Range_bounded r.2) => H2.
  by ordered.
Qed.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Fixpoint intervalSpan {rs : NonEmpty RangeSig} (before : nat)
  `(i : Interval {| ivar := iv
                  ; ibeg := ib
                  ; iend := ie
                  ; iknd := knd
                  ; rds  := rs |}) {struct rs} :
  { p : option IntervalSig * option IntervalSig | SubIntervalsOf before i p }.
Proof.
  case: (splitKind knd) => [lknd rknd].
  destruct rs as [r|r rs];
  case: (@rangeSpan before _ r.2) => [[[r0| ] [r1| ]]].

  (* We have a single range, and the splitting point occur somewhere within
     that range, meaning that there are use positions both before and after.
     Therefore, we need to create two new intervals out of these parts. *)
  - Case "rs = R_Sing r; (r0, r1) = (Some, Some)".
    move/andP=> [H1 /andP [/eqP H2 /eqP H3]].
    move: (Interval_beg_of_rds i) (Interval_end_of_rds i).
    rewrite H2 H3 /= => *.
    by exists (Some (exist _ _ (I_Sing iv lknd r0.2)),
               Some (exist _ _ (I_Sing iv rknd r1.2))).

  (* All of the use positions occur before the split point.  However, it's
     possible that the range *ends* after the split point, meaning that there
     are simply no use positions in that part of the range.  In that case, we
     throw away that part of the range since none of the code there uses the
     variable anymore. *)
  - Case "rs = R_Sing r; (o, o0) = (Some, None)".
    move: (Interval_exact_beg i) => /= <-.
    move: (Interval_end_of_rds i) => /= /eqP <-.
    move/andP=> [H1 /andP [/eqP H2 /eqP H3]].
    exists (Some (exist _ _ (I_Sing iv knd r0.2)), None).
    by rewrite /= {}H2 {}H3; firstorder.

  (* Likewise, in this case all use positions occur after the split point, but
     we may still be shortening the range if it began before the split point.
     This can be detrimental if the range had been extended to cover a loop
     boundary, but if we're being asked to split it means that nothing more
     optimal was found. *)
  - Case "rs = R_Sing r; (o, o0) = (None, Some)".
    move: (Interval_exact_beg i) => /= <-.
    move: (Interval_end_of_rds i) => /= /eqP <-.
    move/andP=> [H1 /andP [/eqP H2 /eqP H3]].
    exists (None, Some (exist _ _ (I_Sing iv knd r1.2))).
    by rewrite /= {}H2 {}H3; firstorder.

  (* If there are no use positions on either side of the split, it would
     indicate an empty range which is invalid. *)
  - Case "rs = R_Sing r; (o, o0) = (None, None)".
    contradiction.

  (* We have a sequence of ranges, and the split occurs somewhere within the
     first range of that sequence.  This means basically that we are turning
     [(r :: rs)] into [[:: r0]] and [(r1 :: rs)], where [r0] and [r1] are
     the split parts of the first range. *)
  - Case "rs = R_Cons r rs; (o, o0) = (Some, Some)".
    move/andP=> [H1 /andP [/eqP H2 /eqP H3]].

    move: (intervalUncons i) => [_ i1].
    move: (intervalConnected i) => ?.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_beg_of_rds i) (Interval_end_of_rds i) => /= Hb He.

    have Hi: rend r1.1 < rbeg (NE_head rs).1
      by rewrite -H3.
    rewrite H2 in Hb.

    by exists (Some (exist _ _ (I_Sing iv lknd r0.2)),
               Some (exist _ _ (I_Cons i1 Hi))).

  (* In this branch, we know that all use positions in the first range occur
     before the split point, and so we must split in one of the ranges in
     [rs].  This means splitting on [rs], we which accomplish by calling this
     function recursively. *)
  - Case "rs = R_Cons r rs; (o, o0) = (Some, None)".
    move/andP=> [H1 /andP [/eqP Hx /eqP Hy]].

    move: (intervalUncons i) => [i0 i1].
    move: (intervalConnected i) => Hi0.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_beg_of_rds i) (Interval_end_of_rds i) => /=.

    (* After splitting [i1], the result we finally return will effectively be
      (i0 :: i1_1, i1_2).  This means cons'ing [r] from above with [i1_1] to
      form the first interval, and returning [i1_2] as the second interval. *)
    move: (intervalSpan rs before iv _ _ _ i1) => /= [] [[i1_1| ] [i1_2| ]].
    + SCase "(Some, Some)".
      move=> [? /eqP H2 /eqP H3].
      destruct i1_1 as [i1_1d i1_1i] eqn:Heqe.
      destruct i1_1d as [? ? ?].
      move: (Interval_beg_of_rds i1_1i)
            (Interval_end_of_rds i1_1i) => /eqP Hb /eqP He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_1i.
      rewrite Hb in H2.
      rewrite H2 in Hi0.
      have i1_1i' := I_Cons i1_1i Hi0.
      rewrite H3.
      rewrite -He in i1_1i'.

      by exists (Some (exist _ _ i1_1i'), Some i1_2).

    (* In this case, we need to cons the [r] from above with a new interval
       [i1_1], which can only differ by possibly being shorter than i1, in the
       case that there was an extension at the end with no use positions in it
       (for example, to cover the range of a loop). *)
    + SCase "(Some, None)".
      move=> [/eqP H0 /= H2 H3 /eqP H4 /eqP H5].

      destruct i1_1 as [i1_1d i1_1i] eqn:Heqe.
      destruct i1_1d as [? ? ?].
      move: (Interval_beg_of_rds i1_1i)
            (Interval_end_of_rds i1_1i) => /eqP Hb /eqP He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_1i.
      have Hi: rend r.1 < rbeg (NE_head rds0).1
        by rewrite H0 Hb in Hi0.
      have i1_1i' := I_Cons i1_1i Hi.
      rewrite -He in i1_1i'.
      rewrite -H5 in H2.
      move/eqP in H4.

      by exists (Some (exist _ _ i1_1i'), None).

    (* In this case, we return [i0] as the left interval (which only
       references [r]), and [i1] as the right, since nothing has been
       changed. *)
    + SCase "(None, Some)".
      move=> [H0 /= H2 H3 /eqP H4 /eqP H5].

      destruct i1_2 as [i1_2d i1_2i] eqn:Heqe.
      destruct i1_2d as [? ? ?].
      move: (Interval_beg_of_rds i1_2i)
            (Interval_end_of_rds i1_2i) => /eqP Hb /eqP He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_2i.
      rewrite Hb in H2 H3.
      rewrite Hx in H4.
      move/eqP in H4.
      rewrite He in H0.
      rewrite -H5 in H0.
      move/eqP in H5.

      have: rend r0.1 <= before <= rbeg (NE_head rds0).1
        by apply/andP; split => //=.

      by exists (Some (exist _ _ (I_Sing iv lknd r0.2)), Some (_; i1_2i)).

    + SCase "(None, None)".
      contradiction.

  - Case "rs = R_Cons r rs; (o, o0) = (None, Some)".
    move/andP=> [H1 /andP [/eqP H2 /eqP H3]].

    move: (intervalUncons i) => [_ i1].
    move: (intervalConnected i) => Hi0.
    rewrite {}H3 in Hi0.
    move: (Interval_beg_of_rds i) => /= /eqP Heq1.
    rewrite -Heq1 in H2.
    move: (Interval_exact_end i) => /= Heq2.
    rewrite Heq2 in i1.
    move/eqP in Heq2.

    exists (None, Some (exist _ _ (I_Cons i1 Hi0))).
    by rewrite /= {}H2; firstorder.

  - Case "rs = R_Cons r rs; (o, o0) = (None, None)".
    contradiction.
Defined.

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
