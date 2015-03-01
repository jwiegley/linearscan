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

Definition mergeKind (k1 k2 : IntervalKind) : IntervalKind :=
  match k1, k2 with
  | Whole,     Whole     => Whole
  | Whole,     LeftMost  => LeftMost
  | Whole,     Middle    => Middle
  | Whole,     RightMost => RightMost
  | LeftMost,  Whole     => LeftMost
  | LeftMost,  LeftMost  => LeftMost
  | LeftMost,  Middle    => LeftMost
  | LeftMost,  RightMost => Whole
  | Middle,    Whole     => Middle
  | Middle,    LeftMost  => LeftMost
  | Middle,    Middle    => Middle
  | Middle,    RightMost => RightMost
  | RightMost, Whole     => RightMost
  | RightMost, LeftMost  => Whole
  | RightMost, Middle    => RightMost
  | RightMost, RightMost => RightMost
  end.

Record IntervalDesc : Set := {
  (* The [varId] is simply a number that refers to the variable for which this
     interval was created.  This number must be maintained by the caller, and
     has no meaning at this point in the code.  Note that multiple intervals
     can all relate to the same [varId]. *)
  ivar : nat;
  ibeg : nat;
  iend : nat;
  (* [ispl] is true if this interval is the left half of a split block, where
     isplit was [false] for that block; otherwise, isplit is inherited. *)
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

  | I_Cons : forall i oknd knd xs,
      Interval {| ivar := i
                ; ibeg := rbeg (NE_head xs).1
                ; iend := rend (NE_last xs).1
                ; iknd := oknd
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

(* jww (2015-02-28): This may need revisiting. *)
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
                  ; rds := NE_Cons r xs |}) : rend r.1 < rbeg (NE_head xs).1.
Proof. by inv i. Qed.

Lemma Interval_exact_beg `(i : Interval d) : ibeg d = rbeg (NE_head (rds d)).1.
Proof. by inv i. Qed.

Lemma Interval_exact_end `(i : Interval d) : iend d = rend (NE_last (rds d)).1.
Proof. by inv i. Qed.

Definition intervalSetKind `(i : Interval d) : forall k,
  Interval {| ivar := ivar d
            ; ibeg := ibeg d
            ; iend := iend d
            ; iknd := k
            ; rds  := rds d |}.
Proof.
  inversion i.
    by constructor.
  move=> k.
  exact: (@I_Cons _ oknd).
Defined.

Definition intervalUncons
  `(i : Interval {| ivar := iv
                  ; ibeg := ib
                  ; iend := ie
                  ; iknd := z
                  ; rds  := NE_Cons r xs |}) :
  [ /\ Interval  {| ivar := iv
                  ; ibeg := ib
                  ; iend := rend r.1
                  ; iknd := z
                  ; rds  := NE_Sing r |}
  &    Interval  {| ivar := iv
                  ; ibeg := rbeg (NE_head xs).1
                  ; iend := ie
                  ; iknd := z
                  ; rds  := xs |} ].
Proof.
  move: i.
  invert => //=; subst.
  split.
  case: r H6 => [rd r] *.
    exact: (I_Sing iv z r).
  exact: (intervalSetKind H1).
Defined.

Lemma Interval_sorted `(i : Interval d) : StronglySorted range_ltn (rds d).
Proof.
  induction i; simpl in *.
    by constructor; constructor.
  constructor; first exact: IHi.
  induction xs; first by constructor.
  constructor; first by [].
  apply: IHxs.
  - by apply intervalUncons in i0; inv i0.
  - inv IHi.
    move: (Range_bounded a.2) => Hbound.
    case: xs => [x|x xs] /= in i0 H H2 H3 *;
    inv H3;
    rewrite /range_ltn in H4;
    by reduce_last_use; ordered.
  - by inv IHi.
Qed.

Definition intervalsIntersect `(Interval i) `(Interval j) : bool :=
  let f (x y : RangeSig) : bool := rangesIntersect x.2 y.2 in
  has (fun (x : RangeSig) => has (f x) (NE_to_list (rds j)))
      (NE_to_list (rds i)).

Definition intervalIntersectionPoint `(Interval i) `(Interval j) :
  option oddnum :=
  NE_foldl (fun mx rd =>
    option_choose mx
      (NE_foldl
         (fun mx' rd' =>
            option_choose mx
              (rangeIntersectionPoint rd.2 rd'.2))
         None (rds j)))
    None (rds i).

Definition searchInRange (r : RangeSig) (f : UsePos -> bool) :
  option { r' : RangeSig & { u : UsePos | u \in ups r'.1 } }.
Proof.
  case: (findRangeUsePos r.2 f) => [x|];
    last exact: None.
  apply: Some _.
  by exists r.
Defined.

Definition allUsePos (d : IntervalDesc) : seq UsePos :=
  let f acc r := foldl (fun us u => cons u us) acc (ups r.1) in
  NE_foldl f [::] (rds d).
Arguments allUsePos d /.

Definition findIntervalUsePos (d : IntervalDesc) (f : UsePos -> bool) :
  option { r' : RangeSig & { u : UsePos | u \in ups r'.1 } } :=
  let fix go rs := match rs with
      | NE_Sing r     => searchInRange r f
      | NE_Cons r rs' => option_choose (searchInRange r f) (go rs')
      end in
  go (rds d).

Definition lookupUsePos (d : IntervalDesc) (f : UsePos -> bool) : option oddnum.
  case: (findIntervalUsePos d f) => [[r [u Hin]]|];
    last exact: None.
  move: (Range_uses_odd r.2).
  move/allP => /(_ u Hin) /= Hodd.
  apply: Some _.
  by exists u.
Defined.
Arguments lookupUsePos d f /.

Definition nextUseAfter (d : IntervalDesc) (pos : nat) : option oddnum :=
  lookupUsePos d (fun u => pos < uloc u).
Arguments nextUseAfter d pos /.

Definition rangeFirstUsePos (rd : RangeDesc) : option nat :=
  if ups rd is u :: _
  then Some (uloc u)
  else None.
Arguments rangeFirstUsePos rd /.

Definition firstUsePos (d : IntervalDesc) : option nat :=
  let fix go xs :=
      match xs with
        | NE_Sing x => rangeFirstUsePos x.1
        | NE_Cons x xs =>
            option_choose (rangeFirstUsePos x.1) (go xs)
      end in
  go (rds d).
Arguments firstUsePos d /.

Definition firstUseReqReg (d : IntervalDesc) : option oddnum :=
  lookupUsePos d regReq.
Arguments firstUseReqReg d /.

Notation IntervalSig := { d : IntervalDesc | Interval d }.

Definition Interval_fromRanges (vid : nat) `(sr : SortedRanges b) :
  forall r rs, sr.1 = r :: rs ->
  let rs' := NE_from_list r rs in
  Interval {| ivar := vid
            ; ibeg := rbeg (NE_head rs').1
            ; iend := rend (NE_last rs').1
            ; iknd := Whole
            ; rds  := rs' |}.
Proof.
  case: sr => /= [x Hsort Hlt].
  move=> r rs Heqe; subst.
  set rds0 := NE_from_list _ _.
  have: NE_StronglySorted range_ltn rds0
    by exact: NE_StronglySorted_from_list.
  elim: rds0 => //= [r'|r' rs' IHrs'].
    move: (I_Sing vid Whole r'.2).
    by destruct r'; destruct x.
  invert.
  move: IHrs' => /(_ H1) i.
  have Hlt': rend r'.1 < rbeg (NE_head rs').1.
    move/NE_Forall_head in H2.
    by rewrite /range_ltn in H2.
  exact: (@I_Cons vid _ Whole _ i _ Hlt').
Defined.

(* Divide the ranges of an [Interval] such that the first set are entirely
   before the split position (and thus, the split could never occur there),
   and the second set are either after the split position, or the split
   position falls within the first of those ranges. *)
Definition divideIntervalRanges `(i : Interval d) `(Hodd : odd before)
  (Hwithin : ibeg d < before <= iend d) :
  { p : SortedRanges (ibeg d) * SortedRanges (ibeg d)
  | match p with
    | (exist2 [::] _ _,
       exist2 (r2 :: rs2) _ _) =>
        [/\ splittable_range_pos before r2.1
        &   rds d = NE_from_list r2 rs2 ]

    | (exist2 (r1 :: rs1) _ _,
       exist2 (r2 :: rs2) _ _) =>
        [/\ rend (last r1 rs1).1 < rbeg r2.1
        ,   rend (last r1 rs1).1 <= before <= rend r2.1
        &   rds d = NE_append (NE_from_list r1 rs1) (NE_from_list r2 rs2) ]

    | _ => False  (* no other splitting scenario is possible *)
    end }.
Proof.
  case E: (span (fun rd => rend rd.1 < before) (rds d))
    => [[|r1 rs1] [|r2 rs2]];

  symmetry in E;
  move/span_cat: E => [H1 [H2 H3]];
  rewrite -?ltnNge in H3;
  move: (Interval_sorted i) => Hsorted;
  move: (Interval_exact_beg i) => Hbeg;
  move: (Interval_exact_end i) => Hend;
  rewrite ?cat0s ?cats0 in H1 Hsorted;
  rewrite H1 in Hsorted;
  try rewrite (ne_list H1) NE_head_from_list NE_last_from_list /= in Hbeg Hend;
  rewrite Hbeg Hend in Hwithin.

  - apply: exist _ (exist2 _ _ nil _ _, exist2 _ _ nil _ _) _ => //;
    try constructor.
    by case: (rds d) => // [?|? ?] in H1.

  - apply: exist _ (exist2 _ _ nil _ _, exist2 _ _ (r2 :: rs2) _ _) _ => //;
    try constructor;
    try inv Hsorted.
    + by rewrite Hbeg.
    + by ordered.
    + by rewrite (ne_list H1).

  - apply: exist _ (exist2 _ _ (r1 :: rs1) _ _, exist2 _ _ nil _ _) _ => //;
    try constructor;
    try inv Hsorted.
    + by ordered.
    + clear -H2 Hwithin.
      case/lastP: rs1 => [|rs1e r1e] /= in H2 Hwithin *;
      rewrite ?last_rcons in Hwithin *;
      rewrite ?all_rcons in H2 *;
      by ordered.

  - rewrite -/cat in Hend Hwithin.
    pose Hsorted' := Hsorted.
    apply StronglySorted_inv_app in Hsorted'.
    move: Hsorted' => [Hsorted1 Hsorted2].
    apply: exist _ (exist2 _ _ (r1 :: rs1) _ _,
                    exist2 _ _ (r2 :: rs2) _ _) _ => //=.
    + by ordered.
    + apply StronglySorted_cons_cons in Hsorted.
      rewrite /range_ltn in Hsorted.
      rewrite Hbeg.
      move: (Range_bounded r1.2).
      by reduce_last_use; ordered.
    + clear -H1 H2 H3 Hwithin Hsorted.
      case/lastP: rs1 => [|rs r] /= in H1 H2 Hwithin Hsorted *;
      rewrite ?last_rcons ?all_rcons in H1 H2 *;
      split.
      * by inv Hsorted; inv H5.
      * by ordered.
      * by rewrite (ne_list H1) NE_Cons_spec NE_to_list_from_list.
      * inv Hsorted.
        rewrite -cat1s -cat_rcons in H4.
        apply StronglySorted_inv_app in H4; inv H4.
        by apply StronglySorted_rcons_rcons_inv in H.
      * by ordered.
      * rewrite (ne_list H1).
        exact: NE_append_from_list.
Defined.

(* Divide the ranges of an [Interval] into two sets.  Then, if a split is
   needed in first range of the second set, split it two.  Return the two sets
   of Ranges corresponding to the ranges of the two new Intervals after
   splitting is done. *)
Definition splitIntervalRanges `(i : Interval d) `(Hodd : odd before)
  (Hwithin : ibeg d < before <= iend d) :
  { p : SortedRanges (ibeg d) * SortedRanges before
  | match p with
    | (exist2 (r1 :: rs1) _ _,
       exist2 (r2 :: rs2) _ _) =>
        [/\ rend (last r1 rs1).1 <= before <= rbeg r2.1
        ,   ibeg d = rbeg r1.1
        &   iend d = rend (last r2 rs2).1 ]
    | _ => False  (* no other splitting scenario is possible *)
    end }.
Proof.
  move: (Interval_exact_beg i) => Hbeg.
  move: (Interval_exact_end i) => Hend.
  case: (divideIntervalRanges i Hodd Hwithin)
    => [[[rs1 HSrs1 Hbrs1] [[|r2 rs2] HSrs2 Hbrs2]]] // H;
    first by clear -H; case: rs1 => [|? ?] in H *.

  (* If the split pos occurs within a lifetime hole, splitting the ranges
     means just dividing them up, without any actual splitting necessary. *)
  case E: (before <= rbeg r2.1).
    apply: exist _ (exist2 _ _ rs1 _ _, exist2 _ _ (r2 :: rs2) _ _) _ => //.
    case: rs1 => [|? ?] /= in H HSrs1 Hbrs1 *.
      (* This branch is impossible. *)
      move: H => [H1 H2].
      move: (Interval_exact_beg i) (Interval_exact_end i) Hwithin.
      rewrite {}H2 {H1} NE_head_from_list NE_last_from_list /=.
      move=> -> -> /= /andP [H _].
      by rewrite ltnNge E in H.
    move: H Hbeg Hend => [? ? ->].
    rewrite NE_head_append_spec NE_last_append_spec
            NE_last_from_list NE_head_from_list.
    move=> <- <-; split=> //.
    by ordered.

  (* Otherwise, it is somewhere in [r2] and we must split that [Range]. *)
  have Hinr: splittable_range_pos before r2.1.
    clear -H E;
    move/negbT in E; rewrite -ltnNge in E.
    case: rs1 => [|? ?] /= in H.
      by move: H => [? ?].
    move: H => [? ? ?].
    by rewrite /=; ordered.

  move: (@rangeSpan _ r2.2 _ Hodd Hinr) => [[r2a r2b] [H1 H2 H3 H4 H5]] //.
  apply: exist _ (exist2 _ _ (rcons rs1 r2a) _ _,
                  exist2 _ _ (r2b :: rs2) _ _) _ => //=.
  - clear Hbrs1.
    case/lastP: rs1 => [|rs r] /= in HSrs1 H *.
      by constructor; constructor.
    apply: StronglySorted_rcons_rcons => //.
    case R: (rcons rs r) => [|y ys] in H.
      by apply rcons_nil in R.
    have Hlast: last y ys = last r (rcons rs r) by rewrite R.
    rewrite Hlast last_rcons -H1 in H.
    rewrite /range_ltn.
    move/negbT in E; rewrite -ltnNge in E.
    rewrite H3 in E.
    move: H => [? ?].
    by ordered.
  - rewrite /= {HSrs1} in Hbrs2.
    case: rs1 => [|x xs] /= in Hbrs1 H *;
    by rewrite -?H3; ordered.
  - constructor; inv HSrs2 => //.
    have: forall a : RangeSig, range_ltn r2 a -> range_ltn r2b a.
      move=> a.
      rewrite /range_ltn.
      by ordered.
    move/List.Forall_impl.
    by exact.
  - by ordered.
  - clear -H H1 H3 H4 Hbeg Hend.
    case: rs1 => [|r1b rs1b] /= in H *.
      move: H Hbeg Hend => [? ->].
      rewrite NE_last_from_list NE_head_from_list H3 /=.
      move=> <- -> _ H5 _ H6; split=> //.
        by ordered.
      case/lastP: rs2 => //= [? ?].
      by rewrite !last_rcons.
    move: H Hbeg Hend => [? ? ->].
    rewrite NE_head_append_spec NE_last_append_spec
            NE_last_from_list NE_head_from_list /=.
    move=> <- -> _ H5 _ H6; split=> //.
      by rewrite last_rcons; ordered.
    case/lastP: rs2 => //= [? ?].
    by rewrite !last_rcons.
Defined.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Record SplitInterval (i i1 i2 : IntervalDesc) (before : nat) : Prop := {
  (* This property expresses the fact that there may be a lifetime hole
     between [i1] and [i2]. *)
  _ : iend i1 <= before <= ibeg i2;
  _ : ibeg i = ibeg i1;
  _ : iend i = iend i2
}.

Definition SubIntervalsOf `(i : Interval d) (before : nat) :=
  { p : IntervalSig * IntervalSig
  | let: (i1, i2) := p in SplitInterval d i1.1 i2.1 before }.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Definition splitInterval `(i : Interval d) `(Hodd : odd before)
  (Hwithin : ibeg i < before <= iend i) : SubIntervalsOf i before.
Proof.
  case: (splitKind (iknd i)) => [lknd rknd].
  case: (splitIntervalRanges i Hodd Hwithin)
    => [[[[|r1 rs1] HSrs1 Hbrs1] [[|r2 rs2] HSrs2 Hbrs2]]] // [? ? ?].
  have i1 :=
    @Interval_fromRanges (ivar i) _ (exist2 _ _ (r1 :: rs1) HSrs1 Hbrs1)
                         r1 rs1 refl_equal.
  have i2 :=
    @Interval_fromRanges (ivar i) _ (exist2 _ _ (r2 :: rs2) HSrs2 Hbrs2)
                         r2 rs2 refl_equal.
  apply: exist _ (packInterval (intervalSetKind i1 lknd),
                  packInterval (intervalSetKind i2 rknd)) _.
  by constructor; rewrite /= ?NE_last_from_list ?NE_head_from_list.
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
