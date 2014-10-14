Require Import Lib.
Require Import NonEmpty.
Require Import Range.
Require Import Hask.Alternative.

Open Scope nat_scope.

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

Record IntervalDesc := {
    ibeg : nat;
    iend : nat;
    rds  : NonEmpty RangeSig
}.

(** * Interval *)

Inductive Interval : IntervalDesc -> Prop :=
  | I_Sing : forall x (r : Range x),
      Interval {| ibeg := rbeg x
                ; iend := rend x
                ; rds  := NE_Sing (x; r)
                |}

  | I_Cons : forall xs,
      Interval {| ibeg := rbeg (NE_head xs).1
                ; iend := rend (NE_last xs).1
                ; rds  := xs
                |}
        -> forall r (H : rend r.1 <= rbeg (NE_head xs).1),
      Interval {| ibeg := rbeg r.1
                ; iend := rend (NE_last xs).1
                ; rds  := NE_Cons r xs
                |}.

Tactic Notation "Interval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "I_Sing"
  | Case_aux c "I_Cons"
  ].

Definition getIntervalDesc `(i : Interval d) := d.

Coercion getIntervalDesc : Interval >-> IntervalDesc.

Definition intervalStart `(Interval i) : nat := ibeg i.
Definition intervalEnd   `(Interval i) : nat := iend i.

Definition intervalCoversPos `(i : Interval d) (pos : nat) : bool :=
  (intervalStart i <= pos) && (pos < intervalEnd i).

Definition intervalExtent `(i : Interval d) := intervalEnd i - intervalStart i.

Lemma intervalConnected
  `(i : Interval {| ibeg := rbeg r.1
                  ; iend := rend (NE_last (NE_Cons r rs)).1
                  ; rds := NE_Cons r xs |})
  : rend r.1 <= rbeg (NE_head xs).1.
Proof. move: i. invert as [ [rd0 r0] i [rd1 r1] | ] => //=. Qed.

Definition intervalUncons
  `(i : Interval {| ibeg := rbeg r.1
                  ; iend := rend (NE_last (NE_Cons r rs)).1
                  ; rds := NE_Cons r xs |})
  : [ /\ Interval {| ibeg := rbeg r.1
                   ; iend := rend r.1
                   ; rds := NE_Sing r |}
    &    Interval {| ibeg := rbeg (NE_head xs).1
                   ; iend := rend (NE_last xs).1
                   ; rds := xs |}
    ].
Proof.
  move: i. invert as [ [rd0 r0] i [rd1 r1] | ] => //=.
  split; auto.
  case: r H H2 H4 => rd r *. apply (I_Sing r).
Defined.

Definition intervalsIntersect `(Interval i) `(Interval j) : bool :=
  let f x y := rangesIntersect x.2 y.2 in
  fold_right
    (fun r b => orb b (existsb (f r) (NE_to_list (rds j))))
    false (NE_to_list (rds i)).

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

Definition findIntervalUsePos `(Interval i) (f : UsePos -> bool)
  : option (RangeSig * UsePos) :=
  let f r := match r with
      | exist rd r' => match findRangeUsePos r' f with
          | Some pos => Some (r, pos)
          | None => None
          end
      end in
  let fix go rs := match rs with
      | NE_Sing r     => f r
      | NE_Cons r rs' => f r <|> go rs'
      end in
  go (rds i).

Definition nextUseAfter `(i : Interval d) (pos : nat) : option nat :=
  fmap (uloc ∘ @snd _ _) (findIntervalUsePos i (fun u => pos < uloc u)).

Definition firstUsePos `(i : Interval d) : nat :=
  uloc (NE_head (ups (NE_head (rds d)).1)).

Definition firstUseReqReg `(i : Interval d) : option nat :=
  fmap (uloc ∘ @snd _ _) (findIntervalUsePos i regReq).

Definition lastUsePos `(i : Interval d) : nat :=
  uloc (NE_last (ups (NE_last (rds d)).1)).

Lemma Interval_nonempty : forall `(i : Interval d),
  intervalStart i < intervalEnd i.
Proof.
  rewrite /intervalStart /intervalEnd.
  move=> d. elim=> [rd r|rs i H [rd r] Hend] * /=;
    first (by apply: Range_bounded).
  pose (Range_bounded r). simpl in *.
  by apply (lt_le_shuffle i0 Hend).
Qed.

Lemma Interval_extent_nonzero : forall `(i : Interval d),
  intervalExtent i > 0.
Proof.
  intros.
  unfold intervalExtent.
  pose (Interval_nonempty i).
  by rewrite subn_gt0.
Qed.

Definition IntervalSig := { d : IntervalDesc | Interval d }.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition SubIntervalsOf (before : nat) `(i : Interval d)
  (p : option IntervalSig * option IntervalSig) :=
  let f u := uloc u < before in
  match p with
  | (Some i1, Some i2) =>
      [ /\ NE_all_true f (ups (NE_head (rds i1.1)).1)
      &    f (NE_head (ups (NE_head (rds i2.1)).1)) = false
      ]
  | (Some i1, None) =>
      [ /\ rds d = rds i1.1
      &    NE_all_true f (ups (NE_last (rds i1.1)).1)
      ]
  | (None, Some i2) =>
      [ /\ rds d = rds i2.1
      &    f (NE_head (ups (NE_head (rds i2.1)).1)) = false
      ]
  | (None, None) => False
  end.

Definition splitPosition `(i : Interval d) (before : option nat) : nat :=
  fromMaybe (uloc (NE_last (ups (NE_last (rds d)).1)))
            (before <|> firstUseReqReg i).

Lemma Interval_beg_bounded `(i : Interval d) : ibeg d <= firstUsePos i.
Proof.
  rewrite /firstUsePos.
  elim: i => [rd r|rs i H [rd r]] * /=;
    first (by apply: (Range_beg_bounded r)).
  pose (Range_beg_bounded r). simpl in *. auto.
Qed.

Fixpoint Interval_end_bounded `(i : Interval d) : lastUsePos i < iend d.
Proof.
  rewrite /lastUsePos.
  rewrite /lastUsePos in Interval_end_bounded.
  case: d i => ib ie rds /=.
  invert as [rd r| ] => /=;
    first apply: (Range_end_bounded r);
  rename H1 into i;
  by apply (Interval_end_bounded i).
Qed.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Fixpoint intervalSpan (rs : NonEmpty RangeSig) (before : nat)
  (i : Interval {| ibeg := rbeg (NE_head rs).1
                 ; iend := rend (NE_last rs).1
                 ; rds  := rs |}) {struct rs}
  : { p : (option IntervalSig * option IntervalSig)
    | SubIntervalsOf before i p }.
Proof.
  set f := (fun u => (uloc u < before)).
  destruct rs; destruct (@rangeSpan f _ r.2);
  destruct x; destruct o; destruct o0; destruct s;
  try (pose (@rangeSpan_spec f _ r.2 (exist _ (None, None) s));
       contradiction).

    (* If this is the only [Range], take its span. *)
  - Case "sublists = (Some, Some)".
    by eexists (Some (exist _ _ (I_Sing r0.2)),
                Some (exist _ _ (I_Sing r1.2))).

  - Case "sublists = (Some, None)".
    exists (Some (exist _ _ i), None).
    by rewrite /= H.
  - Case "sublists = (None, Some)".
    exists (None, Some (exist _ _ i)).
    by rewrite /= H.

  (* Otherwise we must split some other [Range], but there must be one. *)
  - Case "(Some, Some)".
    case: (intervalUncons i) => [? i1].
    case: (intervalConnected i) => *.
    have Hi'': rend (NE_head (NE_Cons r1 rs)).1 <= rbeg (NE_head rs).1.
      move/NE_StronglySorted_UsePos_impl: (Range_sorted r.2).
      rewrite H NE_head_append_spec NE_last_append_spec.
      by move/andP: H3 => [_ H3b]; move/eqP: H3b => <-.
    by exists (Some (exist _ _ (I_Sing r0.2)),
               Some (exist _ _ (I_Cons i1 Hi''))).

  - Case "(Some, None)".
    case: (intervalUncons i) => [i0 i1].
    case: (intervalConnected i) => Hi0.
    case: (intervalSpan rs before i1) => /= [] [[o| ] [o0| ]].
    + SCase "(Some, Some)".
      move=> [Htrue Hfalse]. simpl in * |-.
      exists (Some (exist _ _ (I_Cons i1 Hi0)), Some o0).
      split; auto; simpl in *.
      by rewrite <- H in H0.
    + SCase "(Some, None)".
      move=> [Heqe Htrue]. simpl in * |-.
      exists (Some (exist _ _ (I_Cons i1 Hi0)), None).
      unfold SubIntervalsOf.
      split; auto; rewrite <- H in H0. simpl.
      by rewrite Heqe.
    + SCase "(None, Some)".
      exists (Some (exist _ _ i0), Some (exist _ _ i1)).
      split; auto; simpl in *; last by inv p.
      by rewrite <- H in H0.
    + by exists (None, None).

  - Case "(None, Some)".
    exists (None, Some (exist _ _ i)).
    by rewrite /= H.
Defined.

Definition DefiniteSubIntervalsOf (before : nat) `(i : Interval d)
  (p : IntervalSig * IntervalSig) :=
  let f u := uloc u < before in
  match p with
  | (i1, i2) =>
      (* rds d = NE_append (rds i1.1) (rds i2.1) *)
      (*   /\ *) NE_all_true f (ups (NE_head (rds i1.1)).1)
        /\ f (NE_head (ups (NE_head (rds i2.1)).1)) = false
  end.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Definition splitInterval (rs : NonEmpty RangeSig) (before : nat)
  (i : Interval {| ibeg := rbeg (NE_head rs).1
                 ; iend := rend (NE_last rs).1
                 ; rds  := rs |})
  (Hb : firstUsePos i < before) (He : before <= lastUsePos i)
  : { p : (IntervalSig * IntervalSig) | DefiniteSubIntervalsOf before i p }.
Proof.
  set f := fun u => (uloc u < before).
  case: (intervalSpan before i) => // [] [[o| ] [o0| ]] => //=;
   first (by exists (o, o0));
  move=> [Heqe]; rewrite -{}Heqe;
  rewrite /firstUsePos in Hb;
  rewrite /lastUsePos in He; simpl in *;
  try move/NE_Forall_last;
  move/leP=> /le_dec_iff;
  move=> H; [ by ssomega | by contradiction ].
Defined.

(** * Fixed Intervals *)

(** Some machine instructions require their operands in fixed registers. Such
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
