Require Import Lib.
Require Import NonEmpty.
Require Import Range.
Require Import Hask.Alternative.

Open Scope nat_scope.

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

  | I_Cons1 : forall y ib ie,
      Interval {| ibeg := ib
                ; iend := ie
                ; rds  := NE_Sing y
                |}
        -> forall x (r : Range x) (H : rend x <= ib),
      Interval {| ibeg := rbeg x
                ; iend := ie
                ; rds  := NE_Cons (x; r) (NE_Sing y)
                |}

  | I_Consn : forall y xs ib ie,
      Interval {| ibeg := ib
                ; iend := ie
                ; rds  := NE_Cons y xs
                |}
        -> forall x (r : Range x) (H : rend x <= ib),
      Interval {| ibeg := rbeg x
                ; iend := ie
                ; rds  := NE_Cons (x; r) (NE_Cons y xs)
                |}.

Tactic Notation "Interval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "I_Sing"
  | Case_aux c "I_Cons1"
  | Case_aux c "I_Consn"
  ].

Definition getIntervalDesc `(i : Interval d) := d.

Coercion getIntervalDesc : Interval >-> IntervalDesc.

Definition intervalStart `(Interval i) : nat := ibeg i.
Definition intervalEnd   `(Interval i) : nat := iend i.

Definition intervalCoversPos `(i : Interval d) (pos : nat) : bool :=
  andb (intervalStart i <=? pos) (pos <? intervalEnd i).

Definition intervalExtent `(i : Interval d) := intervalEnd i - intervalStart i.

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
  fmap (uloc ∘ @snd _ _) (findIntervalUsePos i (fun u => pos <? uloc u)).

Definition firstUseReqReg `(i : Interval d) : option nat :=
  fmap (uloc ∘ @snd _ _) (findIntervalUsePos i regReq).

Lemma Interval_nonempty : forall `(i : Interval d),
  intervalStart i < intervalEnd i.
Proof.
  intros.
  unfold intervalStart, intervalEnd.
  induction i; simpl in *;
  apply Range_bounded in r; omega.
Qed.

Lemma Interval_extent_nonzero : forall `(i : Interval d),
  intervalExtent i > 0.
Proof.
  intros.
  unfold intervalExtent.
  pose (Interval_nonempty i).
  apply lt_minus in l. assumption.
Qed.

Definition IntervalSig := { d : IntervalDesc | Interval d }.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition SubIntervalsOf `(i : Interval d) :=
  { p : (IntervalSig * IntervalSig)
  | True
  }.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Definition splitInterval `(i : Interval d) (before : option nat) {pos b e} :
  b = uloc (NE_head (ups (NE_head (rds d)).1)) ->
  e = uloc (NE_last (ups (NE_last (rds d)).1)) ->
  pos = fromMaybe e (before <|> firstUseReqReg i) ->
  b < pos -> pos <= e -> SubIntervalsOf i.
Proof.
  intros Hbeg Hend Hpos Hblim Helim.
  destruct d. simpl in *.

  induction rds0.
    (* Find the [Range] to split.  If this is the last [Range], then it must
       be splittable. *)
    destruct a as [rd r]. simpl in *.
    assert (uloc (NE_head (ups rd)) <? pos = true) as H1.
      apply ltb_lt. rewrite <- Hbeg. assumption.
    assert (uloc (NE_last (ups rd)) <? pos = false) as H2.
      rewrite <- Hend. apply ltb_gt. assumption.
    pose (@splitRange (fun u => uloc u <? pos) rd r H1 H2).
    simpl in *. destruct d.
    unfold SubIntervalsOf. destruct x.
    eexists (({| ibeg := rbeg r0.1
               ; iend := rend r0.1
               ; rds  := NE_Sing r0 |}; _),
             ({| ibeg := rbeg r1.1
               ; iend := rend r1.1
               ; rds  := NE_Sing r1 |}; _)); auto.

  (* Otherwise we must split some other [Range], but there must be one. *)
  admit.

  Grab Existential Variables.

  - destruct r1. apply I_Sing.
  - destruct r0. apply I_Sing.
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
