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
Proof.
  move: i.
  invert => //=.
Qed.

Lemma Interval_exact_beg `(i : Interval d) :
  ibeg d = rbeg (NE_head (rds d)).1.
Proof. move: i. invert => //. Qed.

Lemma Interval_exact_end `(i : Interval d) :
  iend d = rend (NE_last (rds d)).1.
Proof. move: i. invert => //. Qed.

Definition intervalSetKind
  `(i : Interval d) : forall k,
  Interval {| ivar := ivar d
            ; ibeg := ibeg d
            ; iend := iend d
            ; iknd := k
            ; rds  := rds d |}.
Proof.
  inversion i.
    by constructor.
  move=> k.
  subst.
  exact: (@I_Cons _ oknd).
Defined.

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
  move: i.
  invert => //=; subst.
  split.
  case: r H6 => [rd r] *.
    exact: (I_Sing iv z r).
  exact: (intervalSetKind H1).
Defined.

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
  move: (Range_all_odd r.2).
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

Lemma Interval_beg_of_rds `(i : Interval d) :
  ibeg d == rbeg (NE_head (rds d)).2.
Proof. by elim: i => * //=. Qed.

Lemma Interval_end_of_rds `(i : Interval d) :
  iend d == rend (NE_last (rds d)).2.
Proof. by elim: i => * //=. Qed.

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
Definition SubIntervalsOf (before : nat) `(i : Interval d) :=
  { p : option IntervalSig * option IntervalSig
  | let f u := u < before in
    match p with
    | (Some i1, Some i2) => [&& iend i1.1 == before
                            ,   before == ibeg i2.1
                            ,   ibeg i == ibeg i1.1
                            ,   iend i == iend i2.1
                            &   allUsePos i ==
                                  allUsePos i1.1 ++ allUsePos i2.1 ]
    | (Some i1, None)    => [&& ibeg d == ibeg i1.1
                            ,   iend i1.1 == iend d
                            ,   iend i1.1 <= before
                            &   allUsePos i == allUsePos i1.1 ]
    | (None, Some i2)    => [&& ibeg d == ibeg i2.1
                            ,   iend d == iend i2.1
                            ,   before <= ibeg i2.1
                            &   allUsePos i == allUsePos i2.1 ]
    | (None, None)       => false
    end }.

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
     that range, meaning that there are use positions both before and after.
     Therefore, we need to create two new intervals out of these parts. *)
  - Case "rs = R_Sing r; (r0, r1) = (Some, Some)".
    move/andP=> [/eqP ? /andP
                  [/eqP H2 /andP [/eqP H3 /andP [/eqP H4 /eqP H5]]]].
    move: (Interval_beg_of_rds i) (Interval_end_of_rds i).
    rewrite H2 H3 /=.
    exists (Some (packInterval (I_Sing iv lknd r0.2)),
               Some (packInterval (I_Sing iv rknd r1.2))) => /=.
    rewrite foldl_cat_cons -H5.
    by ordered.

  (* All of the use positions occur before the split point.  However, it's
     possible that the range *ends* after the split point, meaning that there
     are simply no use positions in that part of the range.  In that case, we
     throw away that part of the range since none of the code there uses the
     variable anymore. *)
  - Case "rs = R_Sing r; (o, o0) = (Some, None)".
    move: (Interval_exact_beg i) => /= <-.
    move: (Interval_end_of_rds i) => /= /eqP <-.
    move/andP=> [? /andP [/eqP ? /andP [/eqP ? /eqP ?]]].
    exists (Some (packInterval (I_Sing iv knd r0.2)), None) => /=.
    admit.

  (* Likewise, in this case all use positions occur after the split point, but
     we may still be shortening the range if it began before the split point.
     This can be detrimental if the range had been extended to cover a loop
     boundary, but if we're being asked to split it means that nothing more
     optimal was found. *)
  - Case "rs = R_Sing r; (o, o0) = (None, Some)".
    move: (Interval_exact_beg i) => /= <-.
    move: (Interval_end_of_rds i) => /= /eqP <-.
    move/andP=> [? /andP [/eqP ? /andP [/eqP ? /eqP ?]]].
    exists (None, Some (packInterval (I_Sing iv knd r1.2))) => /=.
    admit.

  (* If there are no use positions on either side of the split, it would
     indicate an empty range which is invalid. *)
  - Case "rs = R_Sing r; (o, o0) = (None, None)". by [].

  (* We have a sequence of ranges, and the split occurs somewhere within the
     first range of that sequence.  This means basically that we are turning
     [(r :: rs)] into [[:: r0]] and [(r1 :: rs)], where [r0] and [r1] are
     the split parts of the first range. *)
  - Case "rs = R_Cons r rs; (o, o0) = (Some, Some)".
    move/andP=> [/eqP H1 /andP [/eqP H2 /andP [/eqP H3 /andP [/eqP H4 H5]]]].

    move: (intervalUncons i) => [_ i1].
    move: (intervalConnected i) => ?.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_beg_of_rds i) (Interval_end_of_rds i) => /= Hb He.

    have Hi: rend r1.1 < rbeg (NE_head rs).1 by rewrite -H4.
    rewrite H3 in Hb.

    exists (Some (packInterval (I_Sing iv lknd r0.2)),
            Some (packInterval (@I_Cons _ _ rknd _ i1 _ Hi))) => /=.
    admit.

  (* In this branch, we know that all use positions in the first range occur
     before the split point, and so we must split in one of the ranges in
     [rs].  This means splitting on [rs], we which accomplish by calling this
     function recursively. *)
  - Case "rs = R_Cons r rs; (o, o0) = (Some, None)".
    move/andP=> [? /andP [/eqP Hx /eqP Hy]].

    move: (intervalUncons i) => [i0 i1].
    move: (intervalConnected i) => Hi0.
    move: (Interval_exact_end i) => /= Heq.
    rewrite {}Heq in i1.

    move: (Interval_beg_of_rds i) (Interval_end_of_rds i) => /=.

    (* After splitting [i1], the result we finally return will effectively be
      (i0 :: i1_1, i1_2).  This means cons'ing [r] from above with [i1_1] to
      form the first interval, and returning [i1_2] as the second interval. *)
    move: (intervalSpan rs before Hodd iv _ _ _ i1)
        => /= [] [[i1_1| ] [i1_2| ]].
    + SCase "(Some, Some)".
      move=> [/andP [/eqP H1 /andP [/eqP H2 /andP [/eqP H3 /eqP H4]]]
                    /eqP H5 /eqP H6].
      destruct i1_1 as [i1_1d i1_1i] eqn:Heqe.
      destruct i1_1d as [? ? ?].
      move: (Interval_beg_of_rds i1_1i)
            (Interval_end_of_rds i1_1i) => /eqP Hb /eqP He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_1i.
      rewrite Hb in H3.
      rewrite H3 in Hi0.
      have i1_1i' := @I_Cons _ _ lknd _ i1_1i _ Hi0.
      rewrite -He in i1_1i'.

      exists (Some (packInterval i1_1i'),
              Some (packInterval (intervalSetKind i1_2.2 rknd))).
      admit.

    (* In this case, we need to cons the [r] from above with a new interval
       [i1_1], which can only differ by possibly being shorter than i1, in the
       case that there was an extension at the end with no use positions in it
       (for example, to cover the range of a loop). *)
    + SCase "(Some, None)".
      move=> [/andP [/eqP H1 /andP [/eqP H2 /eqP H3]]] H4 H5.

      destruct i1_1 as [i1_1d i1_1i] eqn:Heqe.
      destruct i1_1d as [? ? ?].
      move: (Interval_beg_of_rds i1_1i)
            (Interval_end_of_rds i1_1i) => /eqP Hb /eqP He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_1i.
      have Hi: rend r.1 < rbeg (NE_head rds0).1
        by admit. (* rewrite H0 Hb in Hi0. *)
      have i1_1i' := @I_Cons _ _ lknd _ i1_1i _ Hi.
      rewrite -He in i1_1i'.

      exists (Some (packInterval i1_1i'), None).
      admit.

    (* In this case, we return [i0] as the left interval (which only
       references [r]), and [i1] as the right, since nothing has been
       changed. *)
    + SCase "(None, Some)".
      move=> [/andP [/eqP H1 /andP [/eqP H2 /eqP H3]]] H4 H5.

      destruct i1_2 as [i1_2d i1_2i] eqn:Heqe.
      destruct i1_2d as [? ? ?].
      move: (Interval_beg_of_rds i1_2i)
            (Interval_end_of_rds i1_2i) => /eqP Hb /eqP He.
      simpl in *; clear Heqe.
      rewrite Hb He in i1_2i.
      rewrite Hb in H2 H3.
      rewrite Hx in H4.
      move/eqP in H4.
      (* rewrite He in H0. *)
      (* rewrite -H5 in H0. *)
      (* move/eqP in H5. *)

      (* have: rend r0.1 <= before <= rbeg (NE_head rds0).1 *)
      (*   by apply/andP; split => //=. *)

      exists (Some (packInterval (I_Sing iv lknd r0.2)),
              Some (packInterval (intervalSetKind i1_2i rknd))).
      admit.

    + SCase "(None, None)". by [].

  - Case "rs = R_Cons r rs; (o, o0) = (None, Some)".
    move/andP=> [H1 /andP [/eqP H2 /andP [/eqP H3 _]]].

    move: (intervalUncons i) => [_ i1].
    move: (intervalConnected i) => Hi0.
    rewrite {}H3 in Hi0.
    move: (Interval_beg_of_rds i) => /= /eqP Heq1.
    rewrite -Heq1 in H2.
    move: (Interval_exact_end i) => /= Heq2.
    rewrite Heq2 in i1.
    move/eqP in Heq2.

    exists (None, Some (packInterval (@I_Cons _ _ knd _ i1 _ Hi0))).
    (* by rewrite /= {}H2; firstorder. *)
    admit.

  - Case "rs = R_Cons r rs; (o, o0) = (None, None)". by [].
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
