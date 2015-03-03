Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** ** RangeDesc *)

(** A [RangeDesc] is built up from a set of use positions, and defines the
    inclusive range of those positions.  It can be extended, or split, but
    never shrunk.  Also, the non-empty list of use positions is not guaranteed
    to be in any order, and overlapping use positions are accepted, where the
    most recent one "wins".

    Although minimally there is at least one position fixing the beginning and
    end of the range, it's possible for the range to extend before or beyond
    the first and last use positions; for example, in the case of a use
    position ranging over the scope of a loop. *)

Record RangeDesc : Set := {
  rbeg : nat;
  rend : nat;                 (* 1 past the last use position *)
  ups  : seq UsePos
}.

Section EqRange.

Fixpoint eqrange s1 s2 {struct s2} :=
  match s1, s2 with
  | {| rbeg := rb1; rend := re1; ups := rus1 |},
    {| rbeg := rb2; rend := re2; ups := rus2 |} =>
      [&& rb1 == rb2, re1 == re2 & rus1 == rus2]
  end.

Lemma eqrangeP : Equality.axiom eqrange.
Proof.
  move.
  case=> [rb1 re1 rus1].
  case=> [rb2 re2 rus2] /=.
  case: (rb1 =P rb2) => [<-|neqx]; last by right; case.
  case: (re1 =P re2) => [<-|neqx]; last by right; case.
  case: (rus1 =P rus2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical range_eqMixin := EqMixin eqrangeP.
Canonical range_eqType := Eval hnf in EqType RangeDesc range_eqMixin.

End EqRange.

Definition head_or_end (rd : RangeDesc) := head_or (rend rd) (ups rd).
Arguments head_or_end rd /.

Definition last_or_beg (rd : RangeDesc) := last_or (rbeg rd) (ups rd).
Arguments last_or_beg rd /.

Definition useWithinRange (b e : nat) (u : UsePos) :=
  (b <= u) && upos_within_bound e u.
Arguments useWithinRange b e u /.

(* When [uses] is not [nil], then either [b < e] or [b <= e], depending on the
   use positions that occur within the range.  For example, an empty range is
   only possible if [b == e] and the only use positions occur at [b] and they
   are [inputOnly].  These other states can be determined from the predicate. *)
Definition validRangeBounds (b e : nat) (uses : seq UsePos) :=
  if uses isn't nil
  then all (useWithinRange b e) uses
  else b <= e.
Arguments validRangeBounds b e uses /.

(** ** Range *)

(** A [Range] constrains how a [RangeDesc] may be constructed, and maintains
    any invariants. *)

Record Range (rd : RangeDesc) : Prop := {
  Range_proper   : validRangeBounds (rbeg rd) (rend rd) (ups rd);
  Range_sorted   : StronglySorted upos_le (ups rd);
  Range_beg_odd  : odd (rbeg rd);
  Range_uses_odd : all (odd \o uloc) (ups rd)
}.

Definition getRangeDesc `(r : Range d) := d.
Arguments getRangeDesc [d] r /.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition packRange `(r : Range d) := exist Range d r.
Arguments packRange [d] r /.

Notation RangeSig := { rd : RangeDesc | Range rd }.

Ltac reduce_last_use :=
  repeat match goal with
  | [ H : context [olast ?X] |- _ ] =>
    case: (olast X) => [?|] in H; rewrite ?all_rcons /= in H
  | [ |- context [olast ?X] ] =>
    case: (olast X) => [?|]; rewrite ?all_rcons /=
  | [ H : context [uvar ?U] |- _ ] => case: (uvar U) in H
  | [ |- context [uvar ?U] ]       => case: (uvar U)
  end.

Lemma Range_bounded `(r : Range rd) : rbeg rd <= rend rd.
Proof.
  case: rd => [? ? rus] /= in r *.
  case: r => /= [Hproper _ _ _].
  case: rus => //= [u us] in Hproper *.
  by reduce_last_use; ordered.
Qed.

Lemma Range_ends_after_use `(r : Range rd) : forall n,
  n <= head_or_end rd -> n <= rend rd.
Proof.
  rewrite /head_or_end /head_or.
  move: (Range_proper r) => /=.
  rewrite /useWithinRange /=.
  case: (ups rd) => //= [u us].
  by reduce_last_use; ordered.
Qed.

Definition Range_shift_down `(r : Range rd) `(Hodd : odd b) (H : b < rbeg rd) :
  RangeSig.
Proof.
  exists {| rbeg := b
          ; rend := rend rd
          ; ups  := ups rd |}.
  move: r => [Hproper Hsorted _ Hallodd].
  constructor=> //=.
  elim: (ups rd) => [|u us IHus] in Hproper Hsorted Hallodd *.
    rewrite /= in Hproper *.
    by ordered.
  rewrite /= in IHus Hproper *.
  case: us => [|x xs] /= in IHus Hproper Hsorted Hallodd *.
    by case E: (uvar u) in Hproper *; ordered.
  case: (uvar u) => /= in Hproper *;
  apply/andP; split;
  inv Hsorted;
  try apply: IHus;
  by ordered.
Defined.

Definition Range_shift_down_spec `(r : Range rd) `(Hodd : odd b)
  (H : b < rbeg rd) :
  forall r1, r1 = Range_shift_down r Hodd H
    -> [/\ rbeg r1.1 = b
       ,   rend r1.1 = rend r
       &   ups  r1.1 = ups r ].
Proof. by move=> r1; invert. Qed.

Definition newRange (upos : UsePos) (Hodd : odd upos)
  (Hinput : uvar upos != Input) : RangeSig.
Proof.
  exists {| rbeg := uloc upos
          ; rend := (uloc upos).+1
          ; ups  := [:: upos] |}.
  move/negbTE in Hinput.
  constructor=> //=.
  - by case (uvar upos); ordered.
  - by constructor; constructor.
  - by apply/andP; split.
Defined.

Definition Range_cons (upos : UsePos) `(r : Range rd)
  (H : validRangeBounds (rbeg rd) (rend rd) (upos :: ups rd))
  (HS : StronglySorted upos_le (upos :: ups rd))
  (Hodd : odd upos) : RangeSig.
Proof.
  exists {| rbeg := rbeg rd
          ; rend := rend rd
          ; ups  := upos :: ups rd |}.
  constructor=> //=.
  - exact: (Range_beg_odd r).
  - apply/andP; split=> //.
    exact: (Range_uses_odd r).
Defined.

Definition Range_split
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := l1 ++ l2 |}) :
  forall before, odd before
    -> validRangeBounds rbeg0 before l1
    -> validRangeBounds before rend0 l2
    -> Range {| rbeg := rbeg0
              ; rend := before
              ; ups  := l1 |} *
       Range {| rbeg := before
              ; rend := rend0
              ; ups  := l2 |}.
Proof.
  move=> *.
  move/StronglySorted_inv_app: (Range_sorted r) => [? ?].
  move: all_cat (Range_uses_odd r) => -> /andP [? ?].
  split; constructor=> //=.
  exact: (Range_beg_odd r).
Defined.

Lemma allWithinRange_leq {n m b e xs} :
  b <= n -> m <= e
    -> all (useWithinRange n m) xs -> all (useWithinRange b e) xs.
Proof.
  move=> Hb He.
  elim: xs => //= [x ? IHxs].
  move/andP=> [/andP [H1 H2] ?].
  apply/andP; split; last exact: IHxs.
  apply/andP; split;
  case: (uvar x) => {IHxs} in H1 H2 *;
  by ordered.
Qed.

Lemma allWithinRange_cat {b1 e1 b2 e2 xs ys} :
  all (useWithinRange b1 e1) xs -> all (useWithinRange b2 e2) ys
    -> b1 <= b2 -> e1 <= e2
    -> all (useWithinRange b1 e2) (xs ++ ys).
Proof.
  move=> ? ? Hb He.
  rewrite all_cat.
  apply/andP; split;
  [ by rewrite (allWithinRange_leq (leqnn _) He)
  | by rewrite (allWithinRange_leq Hb (leqnn _)) ].
Qed.

Definition Range_cat `(r1 : Range rd1) `(r2 : Range rd2) :
  rend rd1 == rbeg rd2
  -> Range {| rbeg := rbeg r1
            ; rend := rend r2
            ; ups  := ups r1 ++ ups r2 |}.
Proof.
  move=> /eqP Heqe.
  pose rd' := {| rbeg := rbeg rd1
               ; rend := rend rd2
               ; ups  := ups rd1 ++ ups rd2 |}.

  have Hb: rbeg rd1 <= rbeg rd2.
    move: (Range_bounded r1).
    move: (Range_bounded r2).
    by reduce_last_use; ordered.

  have He: rend rd1 <= rend rd2.
    move: (Range_bounded r1).
    move: (Range_bounded r2).
    by reduce_last_use; ordered.

  case: r1 => [/= Hr1a Hr1b Hr1c Hr1d].
  case: r2 => [/= Hr2a Hr2b Hr2c Hr2d].

  constructor=> //=; last first.
  - by rewrite all_cat; apply/andP; split.

  - move=> {Hr1d Hr1c Hr2c Hr2d}.
    apply: StronglySorted_cat => //.
    move=> {Hr1b Hr2b rd' Hb He}.
    case: (ups rd1) => // [u1 us1] in Hr1a *;
    rewrite olast_last;
    case: (ups rd2) => // [u2 us2] /= in Hr2a *.
    case/lastP: us1 => /= [|us1e u1e] in Hr1a *.
      case: (uvar u1) in Hr1a *;
      case: (uvar u2) in Hr2a;
      rewrite -Heqe in Hr2a;
      case E: (uloc u1 == uloc u2) => //;
      try move/negbT in E;
      move/eqP in E;
      try ordered.
    rewrite last_rcons.
    move/andP: Hr1a => [/andP [Hr1aA Hr1aB] Hr1aC].
    rewrite all_rcons in Hr1aC.
    move/andP: Hr1aC => [/= /andP [Hr1aC Hr1aD] Hr1aE].
    move/andP: Hr2a => [/= /andP [Hr2aA Hr2aB] Hr2aC].
    abstract (
      case: (uvar u1) in Hr1aA Hr1aB *;
      case: (uvar u1e) in Hr1aC Hr1aD *;
      case: (uvar u2) in Hr2aA Hr2aB;
      rewrite -Heqe in Hr2aA Hr2aB;
      case E: (uloc u1e == uloc u2) => //;
      try move/negbT in E;
      move/eqP in E;
      try ordered).

  - move=> {Hr1b Hr1c Hr1d Hr2b Hr2c Hr2d}.
    case: (ups rd1) => [|u1 us1] in Hr1a *;
    case: (ups rd2) => [|u2 us2] in Hr2a *.
    + by ordered.
    + simpl (_ ++ _).
      case: (u2 :: us2) => // [? ?] in Hr2a *.
      by rewrite (allWithinRange_leq Hb (leqnn _)).
    + rewrite cats0.
      by rewrite (allWithinRange_leq (leqnn _) He).
    + case E: ((u1 :: us1) ++ u2 :: us2) => // [x xs].
      by rewrite -E (allWithinRange_cat Hr1a Hr2a).
Defined.

Definition Range_merge `(r1 : Range rd1) `(r2 : Range rd2) :
  rbeg rd2 <= rend rd1
  -> Range {| rbeg := minn (rbeg r1) (rbeg r2)
            ; rend := maxn (rend r1) (rend r2)
            ; ups  := sortBy upos_le (ups r1 ++ ups r2) |}.
Proof.
  move=> /eqP Heqe.
  (* constructor=> //=; *)
  (* clear -Hp1 Hs1 Hodd1 Hp2 Hs2 Hodd2 E Hminmax; *)
  (* rewrite /range_ltn /= in E; *)
  (* case: (ups rd1) => [|u1 us1] //= in Hp1 Hs1 Hodd1 *; *)
  (* case: (ups rd2) => [|u2 us2] //= in Hp2 Hs2 Hodd2 *. *)
  (* - case: (insert upos_le u2 (sortBy upos_le us2)) => //= [x xs]. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)

  constructor=> //=.
  admit.
  admit.
  admit.
  admit.
Defined.

Definition range_ltn (x y : RangeSig) : bool := rend x.1 < rbeg y.1.
Definition range_leq (x y : RangeSig) : bool := rend x.1 <= rbeg y.1.

Program Instance range_ltn_trans : Transitive range_ltn.
Obligation 1.
  rewrite /range_ltn /= in H H0 *.
  move: (Range_bounded H2).
  case: (olast (ups y)) => [u|];
  first case: (uvar u);
  by ordered.
Qed.

(* A [SortedRanges] is a list of non-contiguous, ordered ranges, for which we
   know that the parameter [bound] is less than or equal to the beginning of
   the first range. *)
Definition SortedRanges bound :=
  { rs : seq RangeSig
  | StronglySorted range_ltn rs
  & bound <= head bound [seq rbeg r.1 | r <- rs] }.

Definition emptySortedRanges {b} : SortedRanges b.
Proof. by exists [::] => //; constructor. Defined.

Lemma Forall_ltn : forall (p r : RangeSig) rs,
  List.Forall (fun y : RangeSig => rend r.1 < rbeg y.1) rs
    -> rend p.1 <= rend r.1
    -> List.Forall (fun y : RangeSig => rend p.1 < rbeg y.1) rs.
Proof.
  move=> p r.
  elim=> [|x xs IHxs] /=.
    by constructor.
  invert; subst.
  move=> H.
  specialize (IHxs H2 H).
  constructor=> //.
  by ordered.
Qed.

Definition SortedRanges_cat `(xs : SortedRanges b) `(ys : SortedRanges pos)
  `(H : last b [seq rend r.1 | r <- xs.1] <= pos) : SortedRanges b.
Proof.
  move: xs => [ps Hpsort Hplt] in H *.
  move: ys => [rs Hrsort Hrlt] in H *.
  case/lastP: ps => [|ps p] //= in Hpsort Hplt H *;
  case: rs => [|r rs] //= in Hrsort Hrlt H *.
  - by apply: exist2 _ _ [::] _ _.
  - apply: exist2 _ _ (r :: rs) Hrsort _ => /=.
    exact: leq_trans H Hrlt.
  - by apply: exist2 _ _ (rcons ps p) Hpsort _.
  - case E: (rend p.1 == rbeg r.1).
      pose r' := packRange (Range_cat p.2 r.2 E).
      apply: exist2 _ _ (ps ++ r' :: rs) _ _.
        case: ps => /= [|p' ps'] in H Hpsort Hplt E r' *.
          by constructor; inv Hrsort.
        apply: StronglySorted_cat_cons => //=.
        + constructor; inv Hpsort.
            exact: (StronglySorted_rcons_inv H2).
          move: H3.
          by apply Forall_rcons_inv.
        + by constructor; inv Hrsort.
        + rewrite /range_ltn {}/r' /=.
          inv Hpsort.
          apply Forall_rcons_inv in H3; inv H3.
          case/lastP: ps' => //= [ys y] in H H0 H2 *.
          rewrite last_rcons.
          by apply StronglySorted_rcons_rcons_inv in H2.
      case: ps => /= [|p' ps'] in H Hpsort Hplt E r' *.
        by ordered.
      by case: ps' => //= [|y ys] in H Hpsort Hplt E r' *.
    apply: exist2 _ _ (rcons ps p ++ r :: rs) _ _ => /=;
    case: ps => //= [|y ys] in H Hpsort Hplt E *.
      constructor=> //.
      rewrite /range_ltn in Hpsort Hrsort *.
      move/negbT in E.
      constructor.
        by ordered.
      inv Hrsort.
      move: (Range_bounded r.2) => Hr.
      apply: (Forall_ltn H3).
      by reduce_last_use; ordered.
    apply: StronglySorted_cat_cons => //=.
    rewrite last_rcons /range_ltn /=.
    move/negbT in E.
    rewrite map_comp 2!last_map last_rcons in H.
    by ordered.
Defined.

(* The bound for a [SortedRanges] may always move downwards. *)
Definition transportSortedRanges `(H : b <= pos)
  `(rp : SortedRanges pos) : SortedRanges b.
Proof.
  case: rp => [rs Hsort Hlt] /=.
  exists rs => //.
  case: rs => [|r rs] //= in Hsort Hlt *.
  by ordered.
Defined.

Lemma NE_Forall_from_list : forall r x xs,
  List.Forall (range_ltn r) (x :: xs)
    -> NE_Forall (range_ltn r) (NE_from_list x xs).
Proof.
  move=> r x xs H.
  elim: xs => /= [|? ? IHys] in r x H *;
  constructor; inv H => //;
  exact: IHys.
Qed.

Lemma NE_StronglySorted_from_list : forall r rs,
  Sorted.StronglySorted range_ltn (r :: rs)
    -> NE_StronglySorted range_ltn (NE_from_list r rs).
Proof.
  move=> r rs.
  elim: rs => /= [|x xs IHxs] in r *.
    by constructor.
  constructor.
  apply: IHxs.
    by inv H.
  inv H.
  exact: NE_Forall_from_list.
Qed.

Definition rangesIntersect `(Range x) `(Range y) : bool :=
  if rbeg x < rbeg y
  then rbeg y < rend x
  else rbeg x < rend y.

Definition rangeIntersectionPoint `(xr : Range x) `(yr : Range y) :
  option oddnum :=
  if rangesIntersect xr yr
  then Some (if rbeg x < rbeg y
             then exist _ (rbeg y) (Range_beg_odd yr)
             else exist _ (rbeg x) (Range_beg_odd xr))
  else None.

Definition findRangeUsePos `(r : Range rd) (f : UsePos -> bool) :
  option { u : UsePos | u \in ups rd }.
Proof.
  elim: (ups r) => [|u us IHxs];
    first by exact: None.
  case: (f u).
    apply: Some _.
    exists u.
    exact: mem_head.
  move: IHxs => [[u' Hu']|];
    last by exact: None.
  apply: Some _.
  exists u'.
  rewrite in_cons.
  apply/orP.
  by right.
Defined.

Definition endsWithInputOnly `(r : Range rd) : bool :=
  if olast (ups rd) is Some u
  then (uloc u == rend rd) && (uvar u == Input)
  else false.

(* When a [Range] is split into two ranges, we preserve a great deal of
   information about how these (possibly) two sub-ranges are related.  If only
   one range results, it must be identical to the original range. *)

Record SplitRange (rd r1 r2 : RangeDesc) (before : nat) : Prop := {
  _ : rend r1 = before;
  _ : before  = rbeg r2;
  _ : rbeg rd = rbeg r1;
  _ : rend rd = rend r2;
  _ : ups rd  = ups r1 ++ ups r2
}.

(* A position is within a range if splitting at that point would divide it
   into two ranges.  Note that input variables are "zero-width", which allows
   splitting at the end of a range, resulting in an empty range referencing
   just those input variables, for the purposes of restoring it from the
   stack. *)
Definition splittable_range_pos (pos : nat) (rd : RangeDesc) :=
  rbeg rd < pos <= rend rd.
Arguments splittable_range_pos pos rd /.

(* Legal split positions:

   Assume a Range from 1-11, with use positions at 1 (must *not* be
   input-only), 5, 9 and 11 (must be input-only).  This is written:

     1-11 [1 5 9 ->11]

   - Cannot split at 1.
   - Split at  3: 1-3  [1    ]  3-11 [5 9 ->11]
   - Split at  5: 1-5  [1    ]  5-11 [5 9 ->11]
   - Split at  7: 1-7  [1 5  ]  7-11 [  9 ->11]
   - Split at  9: 1-9  [1 5  ]  9-11 [  9 ->11]
   - Split at 11: 1-11 [1 5 9] 11-11 [    ->11]
   - Cannot split at 13.

   Note that is possible to produce a zero-width range by splitting at the end
   when no input variable is there.  The algorithms above this can interpret
   this as meaning that the range did not split at all. *)

Definition SubRangesOf `(r : Range rd) (before : nat) :=
  { p : RangeSig * RangeSig
  | let: (r1, r2) := p in SplitRange rd r1.1 r2.1 before }.

Definition rangeSpan `(r : Range rd) `(Hodd : odd before)
  (Hwithin : splittable_range_pos before rd) : SubRangesOf r before.
Proof.
  have Hsort := (Range_sorted r).
  destruct rd; simpl in *.

  (* Anything which is [>= before] moves into the second range. *)
  case E: (span (fun u => uloc u < before) ups0) => [l1 l2].
  symmetry in E.
  move: (span_cat E) => [Hspan _].
  move/andP: (span_all_leq Hsort E) => [H1 H2].
  rewrite Hspan in r Hsort * => {Hspan E}.
  move/StronglySorted_inv_app: Hsort => [Hsort1 Hsort2].

  move: (Range_proper r) => Hpr.
  rewrite /= all_cat /useWithinRange !all_predI in Hpr.

  have Hr1: (validRangeBounds rbeg0 before l1).
    rewrite /= /useWithinRange all_predI => {H2 Hsort1 Hsort2 r}.
    case: l1 => [|u1 us1] in H1 Hpr *.
      by ordered.
    case E: ((u1 :: us1) ++ l2) => [|? ?] in Hpr *.
      by rewrite cat_cons in E.
    apply/andP; split.
      by ordered.
    apply/allP=> [x Hin].
    move/allP: H1 => /(_ x Hin).
    rewrite /=.
    reduce_last_use=> //.
    exact/ltnW.

  have Hr2: (validRangeBounds before rend0 l2).
    rewrite /= /useWithinRange all_predI => {H1 Hsort1 Hsort2 r}.
    case: l2 => [|u2 us2] in H2 Hpr *.
      by ordered.
    case E: (l1 ++ (u2 :: us2)) => [|? ?] in Hpr *.
      by case: l1 => [|? ?] in E Hr1; discriminate.
    by ordered.

  move: (Range_split r Hodd Hr1 Hr2) => [r1 r2].
  by exists (packRange r1, packRange r2).
Defined.

(** ** BoundedRange *)

(** A [BoundedRange] is a [Range] that falls within a specific, possibly
    larger, interval. *)
Definition BoundedRange (b e : nat) :=
  { r : RangeSig | (b <= rbeg r.1) && (rend r.1 <= e) }.

Definition newBoundedRange {b e} (r : RangeSig) :
  (b <= rbeg r.1) && (rend r.1 <= e) -> BoundedRange b e := exist _ r.
Arguments newBoundedRange [b e] r _ /.

Definition emptyBoundedRange (b e : nat) (H : b < e) (Hodd : odd b) :
  BoundedRange b e.
Proof.
  apply: exist _ (exist _ {| rbeg := b; rend := e; ups := [::] |} _) _.
    constructor=> //=; try exact/ltnW.
    by constructor.
  move=> /= r.
  by apply/andP; split.
Defined.

(* [prependRange] takes a [RangePair] and merges in the range under
   construction, resulting in a new [SortedRanges] whose initial bound
   is the beginning of the range that was merged in. *)
Definition prependRange `(rp : BoundedRange b e)
  `(ranges : SortedRanges e) `(H : b <= pos <= rbeg rp.1.1) :
  { ranges' : SortedRanges pos
  | rend (last rp.1 ranges.1).1 = rend (last rp.1 ranges'.1).1 }.
Proof.
  case: ranges => [rs Hsort Hbound].
  case: rp => [r /= Hlt] in H *.
  case: rs => [|x xs] in Hsort Hbound *.
    apply: exist _ (exist2 _ _ [:: r] _ _) _ => //=.
    - by constructor; constructor.
    - by ordered.
  move: (Range_bounded r.2).
  move/andP: Hlt => [Hlt1 Hlt2].
  rewrite /= in Hbound.
  case Heqe: (rend r.1 == rbeg x.1); move=> ?.
    pose r' := packRange (Range_cat r.2 x.2 Heqe).
    apply: exist _ (exist2 _ _ [:: r' & xs] _ _) _ => /=.
    - by constructor; inv Hsort.
    - by ordered.
    - inv Hsort; invert; subst.
      by case: xs => //= in H2 H3 H4 H5 *.
  move: (leq_trans Hlt2 Hbound) => Hleq.
  move/(leq_eqF Heqe) in Hleq.
  apply: exist _ (exist2 _ _ [:: r, x & xs] _ _) _ => /=;
    try by ordered.
  constructor=> //.
  constructor=> //.
  inv Hsort.
  move: (Range_bounded x.2) => Hb.
  rewrite /range_ltn /= in H2 H3 *.
  case: xs => //= [y ys] in H2 H3 *.
  constructor; inv H3.
    by reduce_last_use; ordered.
  move/Forall_all in H5; rewrite -all_map in H5;
  apply/Forall_all; rewrite -all_map;
  by reduce_last_use; match_all.
Defined.
