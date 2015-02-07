Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.

Require Import Coq.Sorting.Sorted.

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

Definition head_or_end (rd : RangeDesc) := head_or (rend rd) (ups rd).
Arguments head_or_end rd /.

Definition last_or_beg (rd : RangeDesc) := last_or (rbeg rd) (ups rd).
Arguments last_or_beg rd /.

(** ** Range *)

(** A [Range] constrains how a [RangeDesc] may be constructed, and maintains
    any invariants. *)

Record Range (rd : RangeDesc) : Prop := {
  Range_beg_bounded :
    if ups rd is u :: _
    then rbeg rd <= u
    else rbeg rd < rend rd;
  Range_end_bounded : last_or_beg rd < rend rd;
  Range_sorted      : StronglySorted upos_lt (ups rd);
  Range_all_odd     : all (odd \o uloc) (ups rd)
}.

Definition getRangeDesc `(r : Range d) := d.
Arguments getRangeDesc [d] r /.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition packRange `(r : Range d) := exist Range d r.
Arguments packRange [d] r /.

Notation RangeSig := { rd : RangeDesc | Range rd }.

Definition BoundedRange (b e : nat) :=
  { r : RangeSig | (b <= rbeg r.1) && (rend r.1 <= e) }.

Definition emptyBoundedRange (b e : nat) (H : b < e) : BoundedRange b e.
Proof.
  apply: exist _ (exist _ {| rbeg := b; rend := e; ups := [::] |} _) _.
    constructor=> //=.
    by constructor.
  move=> /= r.
  by apply/andP; split.
Defined.

Definition transportBoundedRange {e} `(Hlt : a <= b)
  (x : BoundedRange b e) : BoundedRange a e.
  case: x => [r H].
  apply: exist.
  apply: r.
  move/andP: H => [? ?].
  apply/andP; split=> //.
  by ordered.
Defined.

Lemma Range_bounded `(r : Range rd) : rbeg rd < rend rd.
Proof.
  case: rd => [rb re rus] in r *.
  case: rus => /= [|u us] in r *.
    by move: r => [/= *].
  move: r => [/= H1 H2 H3 H4].
  inv H3.
  move: (Forall_last_ltn H2 H6).
  by ordered.
Qed.

Definition Range_split
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := l1 ++ l2 |}) :
  forall before, last_or rbeg0 l1 < before
    -> (if l2 is u :: _
        then before <= u
        else before < rend0)
    -> (Range {| rbeg := rbeg0
               ; rend := before
               ; ups  := l1 |} *
        Range {| rbeg := before
               ; rend := rend0
               ; ups  := l2 |}).
Proof.
  move=> before Hlt1 Hlt2.
  move/StronglySorted_inv_app: (Range_sorted r) => [Hsortedl Hsortedr].
  move/Forall_all/Forall_append: (Range_all_odd r) => /= [Hoddl Hoddr].
  move: (Range_bounded r) => /= Hbound.
  move: (Range_beg_bounded r) => /= Hbeg.
  move: (Range_end_bounded r) => /= Hend.
  split.
    clear Hsortedr Hoddr Hend.
    elim: l1 {r} => /= [|x xs IHxs] in Hlt1 Hsortedl Hoddl Hbeg *.
      by constructor.
    inversion Hsortedl; subst; inv Hoddl.
    constructor=> //=.
    apply/andP; split=> //.
    move/Forall_all in H4.
    by rewrite /funcomp.
  clear Hsortedl Hoddl Hbeg.
  elim: l2 {r} => /= [|x xs IHxs] in Hlt2 Hsortedr Hoddr Hend *.
    by constructor.
  inversion Hsortedr; subst; inv Hoddr.
  constructor=> //=.
  - case: xs => [|y ys] in IHxs Hsortedr Hend H1 H2 H4 *;
    by rewrite last_cat_upos /= in Hend.
  - apply/andP; split=> //.
    move/Forall_all in H4.
    by rewrite /funcomp.
Defined.

Definition range_ltn (x y : RangeSig) : Prop := rend x.1 < rbeg y.1.
Definition range_leq (x y : RangeSig) : Prop := rend x.1 <= rbeg y.1.

Definition Range_cat `(r1 : Range rd1) `(r2 : Range rd2) :
  rend rd1 == rbeg rd2 -> RangeSig.
Proof.
  move=> H.
  pose rd' := {| rbeg := rbeg rd1
               ; rend := rend rd2
               ; ups  := ups rd1 ++ ups rd2 |}.
  exists rd'; rewrite /rd'.

  case: r1 => [/= Hr1a Hr1b Hr1c Hr1d].
  case: r2 => [/= Hr2a Hr2b Hr2c Hr2d].
  constructor=> /=.

  - case: (ups rd1) => [|? ?] //= in Hr1a *.
    case: (ups rd2) => [|? ?] /= in Hr2a *.
      by ordered.
    by ordered.

  - move/eqP in H.
    case: (ups rd1) => [|? ?] /= in Hr1b *.
      case: (ups rd2) => [|? ?] //= in Hr2b *.
      by ordered.
    case: (ups rd2) => [|? ?] /= in Hr2b *.
      rewrite cats0.
      by ordered.
    rewrite last_cat_upos => //=.

  - case: (ups rd1) => //= [? ?] in Hr1a Hr1b Hr1c *.
    case: (ups rd2) => /= [|? ?] in Hr2a Hr2b Hr2c *.
      by rewrite cats0.
    apply: StronglySorted_cat => //=.
    move/eqP in H; rewrite -H in Hr2a.
    rewrite -last_map.
    by ordered.

  - case: (ups rd1) => //= [? ?] in Hr1d *.
    case: (ups rd2) => /= [|? ?] in Hr2d *.
      by rewrite cats0.
    move/andP: Hr1d => [? ?].
    apply/andP; split=> //.
    rewrite all_cat.
    apply/andP; split=> //.
Defined.

(* A [SortedRanges] is a list of non-contiguous, ordered ranges, for which we
   know that the parameter [bound] is less than or equal to the beginning of
   the first range. *)
Definition SortedRanges bound :=
  { rs : seq RangeSig
  | StronglySorted range_ltn rs
  & bound <= head bound [seq rbeg r.1 | r <- rs] }.

Definition emptySortedRanges {bound : nat} : SortedRanges bound.
Proof.
  exists [::] => //.
  by constructor.
Defined.

(* [prependRange] takes a [RangePair] and merges in the
   range-under-construction, resulting in a new [SortedRanges] whose initial
   bound is the beginning of the range that was merged in. *)
Definition prependRange `(rp : BoundedRange b e) (ranges : SortedRanges e) :
  SortedRanges b.
Proof.
  case: rp ranges => [[rd r] /= Hlt] [rs Hsort Hbound].
  move/andP: Hlt => [Hlt1 Hlt2].
  case: rs => [|x xs] in Hsort Hbound *.
    by exists [::] => //.
  rewrite /= in Hbound.
  case Heqe: (rend rd == rbeg x.1).
    exists [:: (Range_cat r x.2 Heqe) & xs] => //=.
    by constructor; inv Hsort => //.
  move: (leq_trans Hlt2 Hbound) => Hleq.
  move/(leq_eqF Heqe) in Hleq.
  exists [:: (rd; r), x & xs] => //.
  constructor=> //.
  constructor=> //.
  inv Hsort.
  move: (Range_bounded x.2) => Hb.
  rewrite /range_ltn /= in H1 H2 *.
  case: xs => //= [y ys] in H1 H2 *.
  constructor.
    inv H2.
    by ordered.
  inv H2.
  move/Forall_all in H4.
  apply/Forall_all.
  rewrite -all_map in H4.
  rewrite -all_map.
  by match_all.
Defined.

(* The bound for a [SortedRanges] may always move downwards. *)
Definition transportSortedRange `(H : base <= prev) (rp : SortedRanges prev) :
  SortedRanges base.
Proof.
  case: rp => [rs Hsort Hlt] /=.
  exists rs => //.
  case: rs => [|r rs] //= in Hsort Hlt *.
  by ordered.
Defined.

Definition mergePendingRanges {base prev} (H : base <= prev)
  (pmap : IntMap (BoundedRange base prev))
  (rmap : IntMap (SortedRanges prev)) : IntMap (SortedRanges base).
Proof.
  apply: (IntMap_mergeWithKey _ _ _ rmap pmap).
  - (* The combining function, when entries are present in both maps. *)
    move=> vid ranges r.
    apply: Some _.
    exact: (prependRange r ranges).
  - (* When no bounded range is present. *)
    exact: (IntMap_map (transportSortedRange H)).
  - (* When no sorted ranges are present. *)
    move=> pending.
    apply: IntMap_map _ pending.
    move=> [r /= Hlt].
    exists [:: r].
      by constructor; constructor.
    by ordered.
Defined.

Lemma NE_Forall_from_list : forall r x xs,
  List.Forall (range_ltn r) (x :: xs)
    -> NE_Forall (range_ltn r) (NE_from_list x xs).
Proof.
  move=> r x xs H.
  elim: xs => /= [|y ys IHys] in r x H *.
    constructor.
    by inv H.
  constructor.
    by inv H.
  apply: IHys.
  by inv H.
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

Definition rangeIntersectionPoint `(xr : Range x) `(yr : Range y) : option nat :=
  if rangesIntersect xr yr
  then Some (minn (rbeg x) (rbeg y))
  else None.

Definition findRangeUsePos `(Range r) (f : UsePos -> bool) : option UsePos :=
  let fix go xs := match xs with
      | [::] => None
      | x :: xs => if f x then Some x else go xs
      end in
  go (ups r).

Definition rangeSpan (before : nat) `(r : Range rd) :
  { p : option RangeSig * option RangeSig
  | match p with
    | (Some r0, Some r1) =>
        [&& rend r0.1 <= before <= rbeg r1.1
        ,   rbeg rd == rbeg r0.1
        &   rend rd == rend r1.1 ]
    | (Some r0, None) =>
        [&& rend r0.1 <= before
        ,   rbeg rd == rbeg r0.1
        &   rend rd == rend r0.1 ]
    | (None, Some r1) =>
        [&& before <= rbeg r1.1
        ,   rbeg rd == rbeg r1.1
        &   rend rd == rend r1.1 ]
    | (None, None)    => False
    end }.
Proof.
  have Hsort := (Range_sorted r).
  destruct rd.
  case E: (span (fun x => uloc x < before) ups0) => [l1 l2].
  symmetry in E.
  move: (span_cat E) => -> in r *.
  move/andP: (span_all Hsort E) => [H1 H2].
  case Hb: (before <= rbeg0) => /=.
    exists (None, Some (packRange r)).
    by repeat (apply/andP; split=> //=).
  case He: (rend0 <= before).
    exists (Some (packRange r), None).
    by repeat (apply/andP; split=> //=).
  move/negbT in Hb; rewrite -ltnNge in Hb.
  move/negbT in He; rewrite -ltnNge in He.
  have H3: last_or rbeg0 l1 < before by exact: all_last.
  have H4: (if l2 is u :: _
            then before <= u
            else before < rend0).
    case: l2 => //= [y ys] in E r H2 *.
    by move/andP: H2; ordered.
  move: (Range_split r H3 H4) => [r1 r2].
  exists (Some (packRange r1), Some (packRange r2)).
  by repeat (apply/andP; split=> //=).
Defined.
