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

  | I_Cons1 : forall y,
      Interval {| ibeg := rbeg y.1
                ; iend := rend y.1
                ; rds  := NE_Sing y
                |}
        -> forall r (H : rend r.1 <= rbeg y.1),
      Interval {| ibeg := rbeg r.1
                ; iend := rend y.1
                ; rds  := NE_Cons r (NE_Sing y)
                |}

  | I_Consn : forall y xs,
      Interval {| ibeg := rbeg y.1
                ; iend := rend (NE_last xs).1
                ; rds  := NE_Cons y xs
                |}
        -> forall r (H : rend r.1 <= rbeg y.1),
      Interval {| ibeg := rbeg r.1
                ; iend := rend (NE_last xs).1
                ; rds  := NE_Cons r (NE_Cons y xs)
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

Definition intervalUncons
  `(i : Interval {| ibeg := ib; iend := ie; rds := NE_Cons (rd; r) xs |})
  : Interval {| ibeg := rbeg (NE_head xs).1; iend := ie; rds := xs |}.
Proof. move: i. invert as [ |[rd0 r0] i [rd1 r1] H2 H3 | ] => //=. Qed.

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
  move=> d. elim=> [rd r|[rd r] i H [rd0 r0]|[rd r] rs i H [rd0 r0]] * /=;
    first (by apply: Range_bounded);
  pose (Range_bounded r0); pose (Range_bounded r);
  simpl in *; omega.
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
  { p : (option IntervalSig * option IntervalSig)
  | True
  }.

Definition splitPosition `(i : Interval d) (before : option nat) : nat :=
  fromMaybe (uloc (NE_last (ups (NE_last (rds d)).1)))
            (before <|> firstUseReqReg i).

Lemma Interval_beg_bounded `(i : Interval d) : ibeg d <= firstUsePos i.
Proof.
  rewrite /firstUsePos.
  elim: i => [rd r|[rd r] i H [rd0 r0]|[rd r] rs i H [rd0 r0]] * /=;
    first (by apply: (Range_beg_bounded r));
  pose (Range_beg_bounded r0); pose (Range_beg_bounded r);
  simpl in *; omega.
Qed.

Fixpoint Interval_end_bounded `(i : Interval d) : lastUsePos i < iend d.
Proof.
  rewrite /lastUsePos.
  rewrite /lastUsePos in Interval_end_bounded.
  case: d i => ib ie rds /=.
  invert as [rd r| | ] => /=;
    first apply: (Range_end_bounded r);
  rename H1 into i;
  by apply (Interval_end_bounded i).
Qed.

(*
Function splitInterval {d : IntervalDesc} (i : Interval d) (before : nat)
  (Hbeg : firstUsePos i < before) (Hend : before <= lastUsePos i)
  {measure (fun i => NE_length (rds i)) i} : SubIntervalsOf i :=
  let f := (fun u => (uloc u <? before)) in
  match d with
  | Build_IntervalDesc ibeg iend rds => match rds with
    | NE_Sing r => undefined
    | NE_Cons r rs => @splitInterval undefined undefined before undefined undefined
    end
  end.

  elim: d i => ib ie [[rd r]|[rd r] xs] /= i Hb He.
    have: (f (NE_last (ups rd)) = false). by apply ltb_gt.
    have: (f (NE_head (ups rd)) = true).  by apply ltb_lt.

    (* Find the [Range] to split.  If this is the only [Range], it must be
       splittable. *)
    move=> HPb HPe.
    case: (@splitRange f _ r HPb HPe) => [[r0 r1] Heqe].
    eexists (({| ibeg := rbeg r0.1
               ; iend := rend r0.1
               ; rds  := NE_Sing r0 |}; _),
             ({| ibeg := rbeg r1.1
               ; iend := rend r1.1
               ; rds  := NE_Sing r1 |}; _)); auto.

  (* Otherwise we must split some other [Range], but there must be one. *)
  case: (@rangeSpan f _ r) => [[[r0| ] [r1| ]] [Heqe Hinfo]].
  - Case "(Some, Some)". admit.
  - Case "(Some, None)".
    pose subi := intervalUncons i.
    admit.
    (* apply: (splitInterval _ subi before). *)
    (* - admit. *)
    (* - admit. *)
    (* apply Hb. *)
  - Case "(None, Some)".
    move: Hinfo.
    rewrite /f.
    move/ltb_gt => Hbeg.
    move: Hb.
    rewrite /firstUsePos Heqe /= => ?. omega.

  Grab Existential Variables.

  - destruct r1. apply I_Sing.
  - destruct r0. apply I_Sing.
Defined.
*)

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Fixpoint intervalSpan (rs : NonEmpty RangeSig) {ib ie} (before : nat)
  (i : Interval {| ibeg := ib; iend := ie; rds  := rs |}) {struct rs}
  : SubIntervalsOf i.
Proof.
  set f := (fun u => (uloc u <? before)).
  destruct rs; destruct (@rangeSpan f _ r.2);
  destruct x; destruct o; destruct o0;
  try (pose (@rangeSpan_spec f _ r.2 (exist _ (None, None) s));
       contradiction).

    (* If this is the only [Range], take its span. *)
  - Case "sublists = (Some, Some)".
    exists (None, None). auto.

  - Case "sublists = (Some, None)".
    exists (Some (exist _ _ i), None). auto.
  - Case "sublists = (None, Some)".
    exists (None, Some (exist _ _ i)). auto.

  (* Otherwise we must split some other [Range], but there must be one. *)
  - Case "(Some, Some)".
    exists (None, None). auto.

  - Case "(Some, None)".
    destruct r. apply (@intervalSpan rs _ _ before (intervalUncons i)).

  - Case "(None, Some)".
    exists (None, Some (exist _ _ i)). auto.
Defined.

(*
(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Fixpoint intervalSpan
  (rs : NonEmpty RangeSig)
  `(i : Interval {| ibeg := ib
                  ; iend := ie
                  ; rds  := rs |}) (before : nat)
  {struct rs} : SubIntervalsOf i.
Proof.
  set f := fun u => (uloc u <? before).

  case: rs i => [[rd r] i'|[rd r] rs' i'].
    case: (@rangeSpan f _ r) => [[r0 r1] subr].
    move: r0 r1 subr => [r0| ] [r1| ] subr.
    - Case "sublists = (Some, Some)".
      admit.

    - Case "sublists = (Some, None)".
      exists (Some (exist _ _ i'), None). auto.
    - Case "sublists = (None, Some)".
      exists (None, Some (exist _ _ i')). auto.
    - Case "sublists = (None, None)".
      exists (None, None). auto.

  (* Otherwise we must split some other [Range], but there must be one. *)
  case: (@rangeSpan f _ r) => [[[r0| ] [r1| ]] [Heqe Hinfo]].
  - Case "(Some, Some)".
    admit.

  - Case "(Some, None)".
    apply (intervalSpan rs' _ _ (intervalUncons i') before).

  - Case "(None, Some)".
    exists (None, Some (exist _ _ i')). auto.

  (* Grab Existential Variables. *)

  (* - destruct r1. apply I_Sing. *)
  (* - destruct r0. apply I_Sing. *)
Defined.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Fixpoint splitInterval
  (rs : NonEmpty RangeSig)
  `(i : Interval {| ibeg := ib
                  ; iend := ie
                  ; rds  := rs |})
  (before : nat)
  (* (Hb : firstUsePos i < before) (He : before <= lastUsePos i) *)
  {struct rs} : SubIntervalsOf i.
Proof.
  set f := fun u => (uloc u <? before).
  case: rs i (* Hb He *) => [] [rd r] => [ | rs'] i (* Hb He *).
    have: (f (NE_last (ups rd)) = false). by apply ltb_gt.
    have: (f (NE_head (ups rd)) = true).  by apply ltb_lt.

    (* Find the [Range] to split.  If this is the only [Range], it must be
       splittable. *)
    move=> HPb HPe.
    case: (@splitRange f _ r HPb HPe) => [[r0 r1] Heqe].
    eexists (({| ibeg := rbeg r0.1
               ; iend := rend r0.1
               ; rds  := NE_Sing r0 |}; _),
             ({| ibeg := rbeg r1.1
               ; iend := rend r1.1
               ; rds  := NE_Sing r1 |}; _)); auto.

  (* Otherwise we must split some other [Range], but there must be one. *)
  case: (@rangeSpan f _ r) => [[[r0| ] [r1| ]] [Heqe Hinfo]].
  - Case "(Some, Some)". admit.
  - Case "(Some, None)".
    pose i' := intervalUncons i.
    have: (firstUsePos i' < before).
      pose (Interval_beg_bounded i'). simpl in *.
      unfold firstUsePos in Hb.
    move=> Hb'.
    eapply (splitInterval rs' _ _ i' before Hb' He).
  - Case "(None, Some)".
    move: Hinfo.
    rewrite /f.
    move/ltb_gt => Hbeg.
    move: Hb.
    rewrite /firstUsePos Heqe /= => ?. omega.

  Grab Existential Variables.

  - destruct r1. apply I_Sing.
  - destruct r0. apply I_Sing.
Defined.
*)

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
