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

Definition SubIntervalsOf (before : nat) `(i : Interval d) :=
  { p : option IntervalSig * option IntervalSig
  | match p with
    | (Some i1, Some i2) => SplitInterval d i1.1 i2.1 before
    | _ => False
    end }.

Definition divideIntervalRanges `(i : Interval d) `(Hodd : odd before)
  (Hwithin : ibeg d < before < iend d) :
  { p : seq RangeSig * seq RangeSig
  | match p with
    | ([::], r2 :: rs2)      => pos_within_range before r2.1
    | (r1 :: rs1, r2 :: rs2) => rend (last r1 rs1).1 <= before < rend r2.1
    | _                      => False
    end }.
Proof.
  case E: (span (fun rd => rend rd.1 <= before) (rds d))
    => [[|r1 rs1] [|r2 rs2]];
  symmetry in E;
  move/span_cat: E => [H1 [H2 H3]];
  rewrite -?ltnNge in H3.
  - exists (nil, nil).
    by case: (rds d) => // [?|? ?] in H1.

  - exists (nil, r2 :: rs2).
    rewrite cat0s in H1.
    rewrite /pos_within_range.
    move: (Interval_exact_beg i).
    move: (Interval_exact_end i).
    replace (rds d) with (NE_from_list r2 rs2); last first.
      case: (rds d) => [r|r rs] in H1 *.
        by inv H1.
      inv H1.
      by rewrite NE_Cons_spec.
    case: (olast (ups r2.1)) => [u|];
    try case: (inputOnly u);
    rewrite NE_head_from_list;
    move=> _ /= <-;
    by ordered.

  - exists (r1 :: rs1, nil).
    rewrite cats0 in H1.
    move: (Interval_exact_end i).
    replace (rds d) with (NE_from_list r1 rs1); last first.
      case: (rds d) => [r|r rs] in H1 *.
        by inv H1.
      inv H1.
      by rewrite NE_Cons_spec.
    case/lastP: rs1 => [|rs1e r1e] /= in H2 H1 *.
      move=> H.
      rewrite H in Hwithin.
      by ordered.
    rewrite NE_last_from_list last_rcons.
    rewrite all_rcons /= in H2.
    move=> H.
    rewrite H in Hwithin.
    by ordered.

  - exists (r1 :: rs1, r2 :: rs2).
    case/lastP: rs1 => [|rs r] /= in H1 H2 *.
      by ordered.
    rewrite last_rcons.
    rewrite all_rcons in H2.
    by ordered.
Defined.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Definition intervalSpan `(i : Interval d) `(Hodd : odd before)
  (Hwithin : ibeg i < before < iend i) : SubIntervalsOf before i.
Proof.
  case: (divideIntervalRanges i Hodd Hwithin) => [[[|r1 rs1] [|r2 rs2]] H] //;
  case: (splitKind (iknd i)) => [lknd rknd];
  case: (@rangeSpan before Hodd _ r2.2) => [[[r2a| ] [r2b| ]]] //.
  - (* | first range | ...
       |---^---------|
       |   \-- split | *)
    admit.
  - (* Split is at the end of r2, impossible. *)
    admit.
  - (* Split is somewhere before r2, with no r1, impossible. *)
    admit.
  - (* | first range |  lifetime hole?  | later range | ...
       |-------------|                  |---^---------|
       |             |                  |   \-- split | *)
    admit.
  - (* Split is at the end of r2, impossible. *)
    admit.
  - (* | first range |  lifetime hole   | later range | ...
       |-------------|     ^            |-------------|
       |             |     \-- split    |             | *)
    admit.
    (* have id1 := {| ivar := ivar i *)
    (*              ; ibeg := ibeg i *)
    (*              ; iend := before *)
    (*              ; iknd := lknd *)
    (*              ; rds  := NE_from_list r1 rs1 *)
    (*              |} in *)
    (* have id2 := {| ivar := ivar i *)
    (*              ; ibeg := rbeg r2 *)
    (*              ; iend := rend (last r2 rs2).1 *)
    (*              ; iknd := rknd *)
    (*              ; rds  := NE_from_list r2 rs2 *)
    (*              |} in *)
    (* exist _ (Some (exist Interval id1 _), *)
    (*          Some (exist Interval id2 _)) _ *)
Defined.

(*
Obligation 1.
  move: Interval_fromRanges.

Obligation 1.                   (* prove we cannot divide into empty ranges *)
  case: (rds d) => [r|r rs] /= in Heq_anonymous *;
  case: (rend r.1 <= before) in Heq_anonymous *;
  try discriminate.
  case: (span _ rs) => [? ?] in Heq_anonymous;
  discriminate.
Qed.
Obligation 2.                   (* prove that before is beyond the end *)
  clear H.
  split=> //.
  move/span_cat: Heq_anonymous => [H1 [H2 _]].
  rewrite cats0 in H1.
  rewrite -{}H1 in H2.
  move: (Interval_exact_end i) => ->.
  elim: (rds d) => /= [r|r rs IHrs] in H2 *;
  by ordered.
Qed.
Obligation 3.
  clear H H0.
  split=> //.
  move/span_cat: Heq_anonymous => [H1 [_ H3]].
  rewrite cat0s in H1.
  rewrite -{}H1 in H3.
  move: (Interval_exact_beg i) => ->.
  case: (rds d) => [[rd [Hrp _ _ _]]|[rd [Hrp _ _ _]] rs] /= in H3 *;
  rewrite /= /useWithinRange all_predI in Hrp;
  rewrite -ltnNge in H3.
    admit.
  admit.
  (* case: (ups rd) => [|u us] in Hrp. *)
Qed.
Obligation 4.
  move: Interval_fromRanges.
  admit.
Defined.
Obligation 5.
  admit.
Defined.
Obligation 6.
  move/span_cat: Heq_anonymous => [H1 [H2 H3]].
  constructor=> //=.
  - case/lastP: rs1 => [|rs r] /= in H1 H2 *.
      rewrite -ltnNge /= in H3.
      admit.
    rewrite last_rcons.
    admit.
  - admit.
  - admit.
Qed.
Obligation 7.
  split=> //.
Qed.
*)

(*
(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], splitting is done before the first
    use position that does not require a register. *)
Fixpoint intervalSpan {rs : NonEmpty RangeSig}
  (before : nat) (Hodd : odd before)
  `(i : Interval {| ivar := iv
                  ; ibeg := ib
                  ; iend := ie
                  ; iknd := knd
                  ; rds  := rs |}) {struct rs} :
  SubIntervalsOf before i.
Proof.
  case: (splitKind knd) => [lknd rknd].
  destruct rs as [r|r rs];
  case: (@rangeSpan before Hodd _ r.2) => [[[r0| ] [r1| ]]].

  (* We have a single range, and the splitting point occur somewhere within
     that range.  Therefore, we need to create two new intervals out of these
     parts. *)
  - Case "rs = R_Sing r; (r0, r1) = (Some, Some)".
    move=> [H1 H2 H3 H4 H5].
    move: {+}H2 (Interval_exact_beg i) => -> /=.
    move: {+}H3 (Interval_exact_end i) => -> /=.
    rewrite H2 in H1.
    rewrite H4.
    exists (Some (packInterval (I_Sing iv lknd r0.2)),
            Some (packInterval (I_Sing iv rknd r1.2))).
    by constructor=> //=; ordered.

  (* If the split position is at or after the end of the range... *)
  - Case "rs = R_Sing r; (o, o0) = (Some, None)".
    move=> [H1 H2].
    case: r0 => [rd0 r0] in H1 H2; inversion H2 as [H0].
    move: {+}H0 (Interval_exact_beg i) => -> /=.
    move: {+}H0 (Interval_exact_end i) => -> /=.
    exists (Some (packInterval (I_Sing iv knd r.2)), None).
    constructor=> //=; f_equal;
      try by rewrite H0.
    by destruct r.

  (* If the split position is at or before the beginning of the range... *)
  - Case "rs = R_Sing r; (o, o0) = (None, Some)".
    move=> [H1 H2].
    case: r1 => [rd1 r1] in H1 H2; inversion H2 as [H0].
    move: {+}H0 (Interval_exact_beg i) => -> /=.
    move: {+}H0 (Interval_exact_end i) => -> /=.
    exists (None, Some (packInterval (I_Sing iv knd r.2))).
    constructor=> //=; f_equal;
      try by rewrite H0.
    by destruct r.

  (* An empty range with no use positions?  Impossible. *)
  - Case "rs = R_Sing r; (o, o0) = (None, None)". by [].

  (* We have a sequence of ranges, and the split occurs somewhere within the
     first range of that sequence.  This means basically that we are turning
     [(r :: rs)] into [[:: r0]] and [(r1 :: rs)], where [r0] and [r1] are
     the split parts of the first range. *)
  - Case "rs = R_Cons r rs; (o, o0) = (Some, Some)".
    move=> [H1 H2 H3 H4 H5].

    move: (intervalUncons i) => [_ i1].
    move: (intervalConnected i) => ?.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_exact_beg i) => /= Hb.
    move: (Interval_exact_end i) => /= He.

    have Hi: rend r1.1 < rbeg (NE_head rs).1 by rewrite -H4.
    rewrite H3 in Hb.

    exists (Some (packInterval (I_Sing iv lknd r0.2)),
            Some (packInterval (@I_Cons _ _ rknd _ i1 _ Hi))).
    by constructor=> //=; ordered.

  (* In this branch, we are splitting beyond the end of the first range.  This
     means splitting on [rs], we which accomplish by calling this function
     recursively. *)
  - Case "rs = R_Cons r rs; (o, o0) = (Some, None)".
    move=> [Hx Hy].

    move: (intervalUncons i) => [i0 i1].
    move: (intervalConnected i) => Hi0.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_exact_beg i) => /=.
    move: (Interval_exact_end i) => /=.

    (* After splitting [i1], the result we finally return will effectively be
      (i0 :: i1_1, i1_2).  This means cons'ing [r] from above with [i1_1] to
      form the first interval, and returning [i1_2] as the second interval. *)
    move: (intervalSpan rs before Hodd iv
             (rbeg (NE_head rs).1) (rend (NE_last rs).1) knd i1)
        => /= [] [[i1_1| ] [i1_2| ]].
    + SCase "(Some, Some)".
      move=> [H1 /= H2 H3] H4 H5.
      destruct i1_1 as [i1_1d i1_1i] eqn:Heqe.
      destruct i1_1d as [? ? ?].
      move: (Interval_exact_beg i1_1i) => Hb.
      move: (Interval_exact_end i1_1i) => He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_1i.
      rewrite Hb in H2.
      rewrite H2 in Hi0.
      rewrite H3 in H4.
      have i1_1i' := @I_Cons _ _ lknd _ i1_1i _ Hi0.
      rewrite -He in i1_1i'.

      by exists (Some (packInterval i1_1i'),
                 Some (packInterval (intervalSetKind i1_2.2 rknd))).

    (* In this case, we need to cons the [r] from above with a new interval
       [i1_1], which can only differ by possibly being shorter than i1, in the
       case that there was an extension at the end with no use positions in it
       (for example, to cover the range of a loop). *)
    + SCase "(Some, None)".
      move=> [H1 H2] H3 H4.

      destruct i1_1 as [i1_1d i1_1i] eqn:Heqe.
      destruct i1_1d as [? ? ?].
      move: (Interval_exact_beg i1_1i) => Hb.
      move: (Interval_exact_end i1_1i) => He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_1i.
      have Hi: rend r.1 < rbeg (NE_head rds0).1
        by inv H2; ordered.
      have i1_1i' := @I_Cons _ _ knd _ i1_1i _ Hi.
      rewrite -He in i1_1i'.

      exists (Some (packInterval i1_1i'), None).
      by constructor=> //=; inv H2.

    (* In this case, we return [i0] as the left interval (which only
       references [r]), and [i1] as the right, since nothing has been
       changed. *)
    + SCase "(None, Some)".
      move=> [H1 H2] H3 H4.

      destruct i1_2 as [i1_2d i1_2i] eqn:Heqe.
      destruct i1_2d as [? ? ?].
      move: (Interval_exact_beg i1_2i) => Hb.
      move: (Interval_exact_end i1_2i) => He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_2i.
      rewrite Hb in H2 H3.

      exists (Some (packInterval (I_Sing iv lknd r0.2)),
              Some (packInterval (intervalSetKind i1_2i rknd))).
      by constructor=> //=; inv H2; ordered.

    + SCase "(None, None)". by [].

  - Case "rs = R_Cons r rs; (o, o0) = (None, Some)".
    move=> [H1 H2].
    case: r1 => [rd1 r1] in H1 H2; inversion H2 as [H0].

    move: (intervalUncons i) => [_ i1].
    move: (intervalConnected i) => Hi0.
    move: (Interval_exact_beg i) => /= Heq1.
    rewrite H0 in Heq1.
    move: (Interval_exact_end i) => /= Heq2.
    rewrite Heq2 in i1.

    exists (None, Some (packInterval (@I_Cons _ _ knd _ i1 _ Hi0))).
    by constructor=> //=; inv H2.

  - Case "rs = R_Cons r rs; (o, o0) = (None, None)". by [].
Defined.
*)

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
