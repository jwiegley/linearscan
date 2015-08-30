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

Record IntervalDesc : Set := {
  (* The [varId] is simply a number that refers to the variable for which this
     interval was created.  This number must be maintained by the caller, and
     has no meaning at this point in the code.  Note that multiple intervals
     can all relate to the same [varId]. *)
  ivar : nat;
  ibeg : nat;
  iend : nat;
  rds  : NonEmpty RangeSig
}.

(** * Interval *)

Inductive Interval : IntervalDesc -> Prop :=
  | I_Sing : forall i x (r : Range x),
      Interval {| ivar := i
                ; ibeg := rbeg x
                ; iend := rend x
                ; rds  := NE_Sing (x; r)
                |}

  | I_Cons : forall i xs,
      Interval {| ivar := i
                ; ibeg := rbeg (NE_head xs).1
                ; iend := rend (NE_last xs).1
                ; rds  := xs
                |}
        -> forall r (H : rend r.1 < rbeg (NE_head xs).1),
      Interval {| ivar := i
                ; ibeg := rbeg r.1
                ; iend := rend (NE_last xs).1
                ; rds  := NE_Cons r xs (* cons_range H *)
                |}.

Require Coq.Strings.String.

Open Scope string_scope.

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

Definition posWithinInterval `(i : Interval d) (pos : nat) : bool :=
  intervalStart i <= pos < intervalEnd i.
Arguments posWithinInterval [d] i pos /.

Lemma Interval_exact_beg `(i : Interval d) : ibeg d = rbeg (NE_head (rds d)).1.
Proof. by inv i. Qed.

Lemma Interval_exact_end `(i : Interval d) : iend d = rend (NE_last (rds d)).1.
Proof. by inv i. Qed.

Definition intervalUncons
  `(i : Interval {| ivar := iv
                  ; ibeg := ib
                  ; iend := ie
                  ; rds  := NE_Cons r xs |}) :
  [ /\ Interval  {| ivar := iv
                  ; ibeg := ib
                  ; iend := rend r.1
                  ; rds  := NE_Sing r |}
  &    Interval  {| ivar := iv
                  ; ibeg := rbeg (NE_head xs).1
                  ; iend := ie
                  ; rds  := xs |} ].
Proof.
  move: i.
  invert => //=; subst.
  split.
  case: r => [rd r] in H5 *.
    exact: (I_Sing iv r).
  exact.
Defined.

Lemma Interval_NE_sorted `(i : Interval d) :
  NE_StronglySorted range_ltn (rds d).
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
    [ rewrite /range_ltn in H1
    | rewrite /range_ltn in H4 ];
    by reduce_last_use; ordered.
  - by inv IHi.
Qed.

Lemma Interval_sorted `(i : Interval d) : StronglySorted range_ltn (rds d).
Proof. by move/NE_StronglySorted_to_list: (Interval_NE_sorted i). Qed.

Lemma Interval_bounded `(i : Interval d) : ibeg d < iend d.
Proof.
  move: (Interval_NE_sorted i).
  inv i.
    move=> _.
    exact: (Range_bounded r).
  invert.
  move: (Range_bounded r.2) => Hbound.
  move: (Range_bounded (NE_last xs).2) => Hbound2.
  move/NE_Forall_last in H4.
  rewrite /range_ltn in H4.
  by ordered.
Qed.

Lemma isJust_head_filter_cat : forall a (xs ys : seq (option a)),
  isJust (head None [seq x <- xs ++ ys | isJust x]) =
  isJust (head None [seq x <- xs | isJust x]) ||
  isJust (head None [seq y <- ys | isJust y]).
Proof.
  move=> a.
  elim=> //= [x xs IHxs] ys.
  case: ys => /= [|y ys].
    rewrite Bool.orb_false_r.
    case: (isJust x) => //=.
    by rewrite cats0.
  case A: (isJust x) => /=;
  case B: (isJust y) => /=.
  - by rewrite A B.
  - by rewrite A.
  - by rewrite IHxs /= B /= B.
  - by rewrite IHxs /= B.
Qed.

Definition allUsePos (d : IntervalDesc) : seq UsePos :=
  flatten [seq ups r.1 | r <- rds d].
Arguments allUsePos d /.

Lemma NE_StronglySorted_inv : forall (A : Set) a l (R : A -> A -> Prop),
  NE_StronglySorted R (NE_Cons a l)
    -> NE_StronglySorted R l /\ NE_Forall (R a) l.
Proof. intros; inversion H; auto. Qed.

Definition findIntervalUsePos `(i : Interval d) (f : UsePos -> bool) :
  option { r' : RangeSig & { u : UsePos | u \in ups r'.1
                                        & ibeg d <= u < iend d } }.
Proof.
  move: (Interval_exact_beg i).
  move: (Interval_exact_end i) => /=.
  move: (Interval_NE_sorted i) => /=.
  move=> H3 H1 H2.
  move/eqP in H1; rewrite eqn_leq in H1.
  move/andP: H1 => [_ H1].
  move/eqP in H2; rewrite eqn_leq in H2.
  move/andP: H2 => [H2 _].
  elim: (rds d) => [r|r rs IHrs] /= in H1 H2 H3 *.
    move: (findRangeUsePos r.2 f) => [[u Hin]|]; last first.
      exact: None.
    apply: Some _.
    exists r.
    exists u.
      assumption.
    move: (Range_proper r.2) => Hproper.
    rewrite /validRangeBounds in Hproper.
    elim: (ups r.1) => //= [x xs IHxs] in Hin Hproper *.
    case: (uvar x) in Hproper;
    case E: (uloc u == uloc x);
    first
      [ move/eqP in E; rewrite E;
        by ordered
      | rewrite in_cons in Hin;
        move/orP: Hin => [Hin|Hin];
        [ move/eqP in Hin;
          destruct u; destruct x; simpl in *;
          inversion Hin;
          by rewrite H0 eq_refl in E
        | apply: (IHxs Hin);
          case: xs => [|? ?] in IHxs Hin Hproper *;
          by ordered ] ].
  move: (findRangeUsePos r.2 f) => [[u Hin]|]; last first.
    rewrite /= in IHrs.
    apply NE_StronglySorted_inv in H3.
    move: H3 => [H3 H4].
    move/NE_Forall_head in H4.
    rewrite /range_ltn in H4.
    apply: IHrs => //=.
    move: (Range_bounded r.2).
    by ordered.
  clear IHrs.
  apply: Some _.
  exists r.
  exists u.
    assumption.
  move: (Range_proper r.2) => Hproper.
  rewrite /validRangeBounds in Hproper.
  apply NE_StronglySorted_inv in H3.
  move: H3 => [H3 H4].
  move/NE_Forall_last in H4.
  rewrite /range_ltn in H4.
  move: (Range_bounded (NE_last rs).2).
  elim: (ups r.1) => //= [x xs IHxs] in Hin Hproper *.
  case: (uvar x) in Hproper;
  case E: (uloc u == uloc x);
  first
    [ move/eqP in E; rewrite E;
      by ordered
    | rewrite in_cons in Hin;
      move/orP: Hin => [Hin|Hin];
      [ move/eqP in Hin;
        destruct u; destruct x; simpl in *;
        inversion Hin;
        by rewrite H0 eq_refl in E
      | apply: (IHxs Hin);
        case: xs => [|? ?] in IHxs Hin Hproper *;
        by ordered ] ].
Defined.

Definition lookupUsePos `(i : Interval d) (f : UsePos -> bool) :
  option { u : nat | ibeg d <= u < iend d }.
  case: (findIntervalUsePos i f) => [[r [u Hin]]|];
    last exact: None.
  move=> /= H.
  apply: Some _.
  exists (uloc u).
  exact: H.
Defined.
Arguments lookupUsePos [d] i f /.

Definition nextUseAfter `(i : Interval d) (pos : nat) : option nat :=
  if lookupUsePos i (fun u => pos < uloc u) is Some (n; _)
  then Some n
  else None.
Arguments nextUseAfter [d] i pos /.

Definition rangeFirstUsePos (rd : RangeDesc) : option UsePos :=
  if ups rd is u :: _ then Some u else None.
Arguments rangeFirstUsePos rd /.

Definition firstUsePos (d : IntervalDesc) : option UsePos :=
  let fix go xs :=
      match xs with
        | NE_Sing x => rangeFirstUsePos x.1
        | NE_Cons x xs =>
            option_choose (rangeFirstUsePos x.1) (go xs)
      end in
  go (rds d).
Arguments firstUsePos d /.

Definition lastUsePos (d : IntervalDesc) : option UsePos :=
  let fix go xs :=
      match xs with
        | NE_Sing x => olast (ups x.1)
        | NE_Cons x xs =>
            option_choose (go xs) (olast (ups x.1))
      end in
  go (rds d).
Arguments lastUsePos d /.

Definition afterLifetimeHole (d : IntervalDesc) (pos : nat) : nat :=
  let f x k :=
      if rbeg x.1 > pos
      then rbeg x.1
      else k in
  let fix go xs :=
      match xs with
        | NE_Sing x    => f x pos
        | NE_Cons x xs => f x (go xs)
      end in
  go (rds d).
Arguments afterLifetimeHole d pos /.

Definition firstUseReqReg `(i : Interval d) :
  option { u : nat | ibeg d <= u < iend d } := lookupUsePos i regReq.
Arguments firstUseReqReg [d] i /.

Definition intervalsIntersect (x y : IntervalDesc) :
  option nat :=
  if (ibeg x < iend y) && (ibeg y < iend x)
  then Some (if ibeg x < ibeg y then ibeg y else ibeg x)
  else None.

Lemma intervalsIntersect_sym : symmetric (isJust .: intervalsIntersect).
Proof.
  move=> x y.
  rewrite /intervalsIntersect.
  case A: (ibeg x < iend y);
  case B: (ibeg y < iend x);
  case C: (ibeg x < ibeg y);
  case D: (ibeg y < ibeg x);
  intuition;
  try move/idP in C;
  try move/negbT in D;
  try move/idP in D;
  try move/negbT in D;
  by ordered.
Qed.

Definition intervalIntersectsWithSubrange (x y : IntervalDesc) : option nat :=
  let fix go rs :=
      if rs isn't r :: rs
      then None
      else if (ibeg x < rend r.1) && (rbeg r.1 < iend x)
           then Some (if ibeg x < rbeg r.1
                      then rbeg r.1
                      else ibeg x)
           else go rs in
  go (rds y).

Notation IntervalSig := { d : IntervalDesc | Interval d }.

Definition Interval_fromRanges (vid : nat) `(sr : SortedRanges b) :
  forall r rs, sr.1 = r :: rs ->
  let rs' := NE_from_list r rs in
  Interval {| ivar := vid
            ; ibeg := rbeg (NE_head rs').1
            ; iend := rend (NE_last rs').1
            ; rds  := rs' |}.
Proof.
  case: sr => /= [x Hsort Hlt].
  move=> r rs Heqe; subst.
  set rds0 := NE_from_list _ _.
  have: NE_StronglySorted range_ltn rds0
    by exact: NE_StronglySorted_from_list.
  elim: rds0 => //= [r'|r' rs' IHrs'].
    move: (I_Sing vid r'.2).
    by destruct r'; destruct x.
  invert.
  move: IHrs' => /(_ H1) i.
  have Hlt': rend r'.1 < rbeg (NE_head rs').1.
    move/NE_Forall_head in H2.
    by rewrite /range_ltn in H2.
  exact: (@I_Cons vid _ i _ Hlt').
Defined.

(* Divide the ranges of an [Interval] such that the first set are entirely
   before the split position (and thus, the split could never occur there),
   and the second set are either after the split position, or the split
   position falls within the first of those ranges. *)
Definition divideIntervalRanges `(i : Interval d)
  `(Hwithin : ibeg d < before < iend d) :
  { p : SortedRanges (ibeg d) * SortedRanges (ibeg d)
  | match p with
    | (exist2 [::] _ _,
       exist2 (r2 :: rs2) _ _) =>
        [/\ splittable_range_pos before r2.1
        &   rds d = NE_from_list r2 rs2 ]

    | (exist2 (r1 :: rs1) _ _,
       exist2 (r2 :: rs2) _ _) =>
        [/\ rend (last r1 rs1).1 < rbeg r2.1
        ,   rend (last r1 rs1).1 <= before < rend r2.1
        &   rds d = NE_append (NE_from_list r1 rs1) (NE_from_list r2 rs2) ]

    | _ => False  (* no other splitting scenario is possible *)
    end }.
Proof.
  case E: (span (fun rd => rend rd.1 <= before) (rds d))
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

  - apply: ((exist2 _ _ nil _ _, exist2 _ _ nil _ _); _) => //;
    try constructor.
    by case: (rds d) => // [?|? ?] in H1.

  - apply: ((exist2 _ _ nil _ _, exist2 _ _ (r2 :: rs2) _ _); _) => //;
    try constructor;
    try inv Hsorted.
    + by rewrite Hbeg.
    + by ordered.
    + by rewrite (ne_list H1).

  - apply: ((exist2 _ _ (r1 :: rs1) _ _, exist2 _ _ nil _ _); _) => //;
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
    apply: ((exist2 _ _ (r1 :: rs1) _ _,
             exist2 _ _ (r2 :: rs2) _ _); _) => //=.
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
Definition splitIntervalRanges `(i : Interval d)
  `(Hwithin : ibeg d < before < iend d) :
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
  case: (divideIntervalRanges i Hwithin)
    => [[[rs1 HSrs1 Hbrs1] [[|r2 rs2] HSrs2 Hbrs2]]] // H;
    first by clear -H; case: rs1 => [|? ?] in H *.

  (* If the split pos occurs within a lifetime hole, splitting the ranges
     means just dividing them up, without any actual splitting necessary. *)
  case E: (before <= rbeg r2.1).
    apply: ((exist2 _ _ rs1 _ _, exist2 _ _ (r2 :: rs2) _ _); _) => //.
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

  move: (@rangeSpan _ r2.2 _ Hinr) => [[r2a r2b] [H1 H2 H3 H4 H5]] //.
  apply: ((exist2 _ _ (rcons rs1 r2a) _ _,
           exist2 _ _ (r2b :: rs2) _ _); _) => //=.
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

Definition SubIntervalsOf (d : IntervalDesc) (before : nat) :=
  { p : IntervalSig * IntervalSig
  | let: (i1, i2) := p in SplitInterval d i1.1 i2.1 before }.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Definition splitInterval `(i : Interval d)
  `(Hwithin : ibeg d < before < iend d) : SubIntervalsOf d before.
Proof.
  (* If before falls within a lifetime hole for the interval, then splitting
     at that position results in two intervals that are not connected by any
     need ato save and restore variables. *)
  case: (splitIntervalRanges i Hwithin)
    => [[[[|r1 rs1] HSrs1 Hbrs1] [[|r2 rs2] HSrs2 Hbrs2]]] // [? ? ?].
  have i1 :=
    @Interval_fromRanges (ivar i) _ (exist2 _ _ (r1 :: rs1) HSrs1 Hbrs1)
                         r1 rs1 refl_equal.
  have i2 :=
    @Interval_fromRanges (ivar i) _ (exist2 _ _ (r2 :: rs2) HSrs2 Hbrs2)
                         r2 rs2 refl_equal.
  apply: ((packInterval i1, packInterval i2); _).
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
