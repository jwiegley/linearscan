Require Import Lib.
Require Import NonEmpty.
Require Import Range.

Generalizable All Variables.

(** ** Interval *)

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
    rds  : NonEmpty { r : RangeDesc & Range r };

    (** Caching this property comes in handy, as it can be tricky to determine
        it by reduction in some cases. *)
    interval_nonempty : ibeg < iend
}.

Inductive Interval : IntervalDesc -> Set :=
  | I_Sing : forall x (r : Range x),
      Interval {| ibeg := rbeg x
                ; iend := rend x
                ; rds  := NE_Sing (existT _ x r)
                ; interval_nonempty := range_nonempty x
                |}

  | I_Cons1 : forall y ib ie ne,
      Interval {| ibeg := ib; iend := ie; rds := NE_Sing y;
                  interval_nonempty := ne |}
        -> forall x (r : Range x) (H : rend x <= ib),
      Interval {| ibeg := rbeg x
                ; iend := ie
                ; rds  := NE_Cons (existT _ x r) (NE_Sing y)
                ; interval_nonempty := lt_le_shuffle (range_nonempty x) H ne
                |}

  | I_Consn : forall y xs ib ie ne,
      Interval {| ibeg := ib; iend := ie; rds := NE_Cons y xs;
                  interval_nonempty := ne |}
        -> forall x (r : Range x) (H : rend x <= ib),
      Interval {| ibeg := rbeg x
                ; iend := ie
                ; rds  := NE_Cons (existT _ x r) (NE_Cons y xs)
                ; interval_nonempty := lt_le_shuffle (range_nonempty x) H ne
                |}.

Definition getIntervalDesc `(i : Interval d) := d.

Coercion getIntervalDesc : Interval >-> IntervalDesc.

Definition intervalStart `(Interval i) : nat := ibeg i.
Definition intervalEnd   `(Interval i) : nat := iend i.

Definition intervalCoversPos `(i : Interval d) (pos : nat) : bool :=
  andb (intervalStart i <=? pos) (pos <? intervalEnd i).

Definition intervalExtent `(i : Interval d) :=
  intervalEnd i - intervalStart i.

Lemma Interval_nonempty : forall `(i : Interval d),
  intervalStart i < intervalEnd i.
Proof.
  intros. unfold intervalStart, intervalEnd.
  induction i; simpl in *;
  induction r; simpl in *; min_max.
Qed.

Lemma Interval_extent_nonzero : forall `(i : Interval d),
  intervalExtent i > 0.
Proof.
  intros.
  unfold intervalExtent.
  pose (Interval_nonempty i).
  apply lt_minus in l. assumption.
Qed.

Definition anyRangeIntersects `(Interval i) `(Interval j) : bool :=
  let f x y := rangesIntersect (projT2 x) (projT2 y) in
  fold_right
    (fun r b => orb b (existsb (f r) (NE_to_list (rds j))))
    false (NE_to_list (rds i)).

Definition firstIntersectionPoint `(Interval i) `(Interval j) : option nat :=
  NE_fold_left
    (fun acc rd =>
       match acc with
       | Some x => Some x
       | None =>
         NE_fold_left
           (fun acc' rd' =>
              match acc' with
              | Some x => Some x
              | None => rangesIntersectionPoint (projT2 rd) (projT2 rd')
              end) (rds j) None
       end) (rds i) None.

(** Fixed Intervals

    Some machine instructions require their operands in fixed
    registers. Such constraints are already considered during the
    construction of the LIR by emitting physical register operands instead
    of virtual register operands. Although the register allocator must
    leave these operands unchanged, they must be considered during
    register allocation because they limit the number of available
    registers. Information about physical registers is collected in fixed
    intervals.

    For each physical register, one fixed interval stores where the
    register is not available for allocation. Use positions are not needed
    for fixed intervals because they are never split and spilled. Register
    constraints at method calls are also modeled using fixed intervals:
    Because all registers are destroyed when the call is executed, ranges
    of length 1 are added to all fixed intervals at the call
    site. Therefore, the allocation pass cannot assign a register to any
    interval there, and all intervals are spilled before the call.

    Note that we do not distinguish between the two types of intervals in this
    code, and in fact make use of the use positions to track the locations of
    fixity (such as call sites) within the code. *)

Definition FixedInterval := Interval.
