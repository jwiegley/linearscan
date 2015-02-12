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
  Range_beg_bounded : if ups rd is u :: _
                      then rbeg rd <= u
                      else rbeg rd < rend rd;
  Range_end_bounded : last_or_beg rd < rend rd;
  Range_sorted      : StronglySorted upos_lt (ups rd);
  Range_beg_odd     : odd (rbeg rd);
  Range_all_odd     : all (odd \o uloc) (ups rd)
}.

Definition getRangeDesc `(r : Range d) := d.
Arguments getRangeDesc [d] r /.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition packRange `(r : Range d) := exist Range d r.
Arguments packRange [d] r /.

Notation RangeSig := { rd : RangeDesc | Range rd }.

Definition Range_shiftup `(r : Range rd) `(Hodd : odd b)
  `(H : if ups rd is u :: _
        then b <= u
        else b < rend rd) : RangeSig.
Proof.
  exists {| rbeg := b
          ; rend := rend rd
          ; ups  := ups rd |}.
  case: r => [Hbeg Hend Hsort ?].
  constructor=> //=.
  rewrite /last_or_beg /last_or in Hend.
  by case: (ups rd) => [|u us] in H Hbeg Hend Hsort *.
Defined.

Definition Range_shiftup_spec `(r : Range rd) `(Hodd : odd b)
  `(H : if ups rd is u :: _
        then b <= u
        else b < rend rd) :
  forall r1, r1 = Range_shiftup r Hodd H
    -> [/\ rbeg r1.1 = b
       ,   rend r1.1 = rend r
       &   ups  r1.1 = ups r ].
Proof. by move=> r1; invert. Qed.

(* Definition Range_shiftdown `(r : Range rd) `(H : last_or_beg rd < e) : *)
(*   RangeSig. *)
(* Proof. *)
(*   exists {| rbeg := rbeg rd *)
(*           ; rend := e *)
(*           ; ups  := ups rd |}. *)
(*   case: r => [Hbeg Hend Hsort ?]. *)
(*   constructor=> //=. *)
(*   rewrite /last_or_beg /last_or in H. *)
(*   by case: (ups rd) => [|u us] in H Hbeg Hend Hsort *. *)
(* Defined. *)

Definition newRange (upos : UsePos) (Hodd : odd upos) : RangeSig.
Proof.
  exists {| rbeg := uloc upos
          ; rend := (uloc upos).+1
          ; ups  := [:: upos] |}.
  constructor=> //=.
    by constructor; constructor.
  by apply/andP; split.
Defined.

Definition Range_cons (upos : UsePos) (Hodd : odd upos) `(r : Range rd)
  `(H : rbeg rd <= upos < head_or_end rd) : RangeSig.
Proof.
  exists {| rbeg := rbeg rd
          ; rend := rend rd
          ; ups  := upos :: ups rd |}.
  move/andP: H => [H1 H2].
  rewrite /head_or_end /head_or in H2.
  move: (Range_beg_bounded r) => Hbeg.
  move: (Range_end_bounded r) => Hend.
  rewrite /last_or_beg /last_or in Hend.
  move: (Range_sorted r) => Hsort.
  move: (Range_beg_odd r) => Hbegodd.
  move: (Range_all_odd r) => Hall.
  constructor=> //=.
  - by case: (ups rd) => //= in H2 Hend Hsort *.
  - constructor=> //.
    case: (ups rd) => //= [u us] in H2 Hsort *.
    constructor=> //.
    inv Hsort.
    by match_all.
  - by apply/andP; split.
Defined.

Definition BoundedRange (b e : nat) :=
  { r : RangeSig | (b <= rbeg r.1) && (rend r.1 <= e) }.

Definition newBoundedRange {b e} (r : RangeSig) :
  (b <= rbeg r.1) && (rend r.1 <= e) -> BoundedRange b e := exist _ r.
Arguments newBoundedRange [b e] r _ /.

Definition emptyBoundedRange (b e : nat) (H : b < e) (Hodd : odd b) :
  BoundedRange b e.
Proof.
  apply: exist _ (exist _ {| rbeg := b; rend := e; ups := [::] |} _) _.
    constructor=> //=.
    by constructor.
  move=> /= r.
  by apply/andP; split.
Defined.

(* Definition transportBoundedRange {e} `(Hlt : a <= b) *)
(*   (x : BoundedRange b e) : BoundedRange a e. *)
(*   case: x => [r H]. *)
(*   apply: exist. *)
(*   apply: r. *)
(*   move/andP: H => [? ?]. *)
(*   apply/andP; split=> //. *)
(*   by ordered. *)
(* Defined. *)

(* Definition BoundedRange_shiftup {b b' e} (c : BoundedRange b e) *)
(*   (Hlt : b <= b' <= rbeg c.1.1) : BoundedRange b' e. *)
(* Proof. *)
(*   move: c => [r /= H] in Hlt *. *)
(*   exists r. *)
(*   by ordered. *)
(* Defined. *)

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
  forall before, odd before
    -> last_or rbeg0 l1 < before
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
  move=> before Hbeforeodd Hlt1 Hlt2.
  move/StronglySorted_inv_app: (Range_sorted r) => [Hsortedl Hsortedr].
  move/Forall_all/Forall_append: (Range_all_odd r) => /= [Hoddl Hoddr].
  move: (Range_bounded r) => /= Hbound.
  move: (Range_beg_bounded r) => /= Hbeg.
  move: (Range_end_bounded r) => /= Hend.
  move: (Range_beg_odd r) => /= Hbegodd.
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

Program Instance range_ltn_trans : Transitive range_ltn.
Obligation 1.
  rewrite /range_ltn /= in H H0 *.
  move: (Range_bounded H2).
  by ordered.
Qed.

Definition Range_cat `(r1 : Range rd1) `(r2 : Range rd2) :
  rend rd1 == rbeg rd2
  -> Range {| rbeg := rbeg r1
            ; rend := rend r2
            ; ups  := ups r1 ++ ups r2 |}.
Proof.
  move=> H.
  pose rd' := {| rbeg := rbeg rd1
               ; rend := rend rd2
               ; ups  := ups rd1 ++ ups rd2 |}.
  case: r1 => [/= Hr1a Hr1b Hr1c Hr1d Hr1e].
  case: r2 => [/= Hr2a Hr2b Hr2c Hr2d Hr2e].
  constructor=> //=.
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

  - case: (ups rd1) => //= [? ?] in Hr1d Hr1e *.
    case: (ups rd2) => /= [|? ?] in Hr2d Hr2e *.
      by rewrite cats0.
    move/andP: Hr1e => [? ?].
    apply/andP; split=> //=.
    rewrite all_cat.
    apply/andP; split=> //=.
Defined.

(* A [SortedRanges] is a list of non-contiguous, ordered ranges, for which we
   know that the parameter [bound] is less than or equal to the beginning of
   the first range. *)
Definition SortedRanges bound :=
  { rs : seq RangeSig
  | StronglySorted range_ltn rs
  & bound <= head bound [seq rbeg r.1 | r <- rs] }.

Definition emptySortedRanges {b} : SortedRanges b.
Proof. by exists [::] => //; constructor. Defined.

(* [prependRange] takes a [RangePair] and merges in the range under
   construction, resulting in a new [SortedRanges] whose initial bound
   is the beginning of the range that was merged in. *)
Definition prependRange `(rp : BoundedRange b e)
  `(ranges : SortedRanges e) `(H : b <= pos <= rbeg rp.1.1) :
  { ranges' : SortedRanges pos
  | forall x, last x [seq rend i.1 | i <- ranges.1] =
              last x [seq rend i.1 | i <- ranges'.1] }.
Proof.
  case: ranges => [rs Hsort Hbound].
  case: rs => [|x xs] in Hsort Hbound *.
    exact: exist _ (exist2 _ _ [::] _ _) _.
  case: rp => [[rd r] /= Hlt] in H *.
  move: (Range_bounded r).
  move/andP: Hlt => [Hlt1 Hlt2].
  rewrite /= in Hbound.
  case Heqe: (rend rd == rbeg x.1); move=> ?.
    pose r' := packRange (Range_cat r x.2 Heqe).
    apply: exist _ (exist2 _ _ [:: r' & xs] _ _) _ => /=.
    - by constructor; inv Hsort.
    - by ordered.
    - inv Hsort; invert; subst.
      by case: xs => //= in H2 H3 H4 H5 *.
  move: (leq_trans Hlt2 Hbound) => Hleq.
  move/(leq_eqF Heqe) in Hleq.
  apply: exist _ (exist2 _ _ [:: (rd; r), x & xs] _ _) _ => /=;
    try by ordered.
  constructor=> //.
  constructor=> //.
  inv Hsort.
  move: (Range_bounded x.2) => Hb.
  rewrite /range_ltn /= in H2 H3 *.
  case: xs => //= [y ys] in H2 H3 *.
  constructor.
    inv H3.
    rewrite /range_leq in H5.
    by ordered.
  inv H3.
  move/Forall_all in H5.
  apply/Forall_all.
  rewrite -all_map in H5.
  rewrite -all_map.
  by match_all.
Defined.

(* Definition consRange `(r : Range rd) `(ranges : SortedRanges pos) *)
(*   (Hlt : rend rd < pos) : SortedRanges (rbeg rd). *)
(* Proof. *)
(*   case: ranges => [rs Hsort Hbound]. *)
(*   case: rs => [|x xs] in Hsort Hbound *. *)
(*     exact: exist2 _ _ [::] _ _. *)
(*   move: (Range_bounded r). *)
(*   rewrite /= in Hbound. *)
(*   case Heqe: (rend rd == rbeg x.1); move=> ?. *)
(*     pose r' := packRange (Range_cat r x.2 Heqe). *)
(*     apply: exist2 _ _ [:: r' & xs] _ _ => //=. *)
(*     by constructor; inv Hsort. *)
(*   move: (leq_trans Hlt Hbound) => Hleq. *)
(*   apply: exist2 _ _ [:: (rd; r), x & xs] _ _ => //=. *)
(*   constructor=> //. *)
(*   constructor=> //. *)
(*   inv Hsort. *)
(*   move: (Range_bounded x.2) => Hb. *)
(*   rewrite /range_ltn /= in H1 H2 *. *)
(*   case: xs => //= [y ys] in H1 H2 *. *)
(*   constructor. *)
(*     inv H2. *)
(*     by ordered. *)
(*   inv H2. *)
(*   move/Forall_all in H4. *)
(*   apply/Forall_all. *)
(*   rewrite -all_map in H4. *)
(*   rewrite -all_map. *)
(*   by match_all. *)
(* Defined. *)

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
  + by apply: exist2 _ _ [::] _ _.
  + apply: exist2 _ _ (r :: rs) Hrsort _ => /=.
    exact: leq_trans H Hrlt.
  + by apply: exist2 _ _ (rcons ps p) Hpsort _.
  + case E: (rend p.1 == rbeg r.1).
      pose r' := packRange (Range_cat p.2 r.2 E).
      apply: exist2 _ _ (ps ++ r' :: rs) _ _.
        case: ps => /= [|p' ps'] in H Hpsort Hplt E r' *.
          by constructor; inv Hrsort.
        apply: StronglySorted_cat => //=.
        * constructor; inv Hpsort.
            exact: (StronglySorted_rcons_inv H2).
          move: H3.
          by apply Forall_rcons_inv.
        * by constructor; inv Hrsort.
        * rewrite /range_ltn {}/r' /=.
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
      by ordered.
    apply: StronglySorted_cat => //=.
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

Definition rangeIntersectionPoint `(xr : Range x) `(yr : Range y) :
  option oddnum :=
  if rangesIntersect xr yr
  then Some (if rbeg x < rbeg y
             then exist _ (rbeg x) (Range_beg_odd xr)
             else exist _ (rbeg y) (Range_beg_odd yr))
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

Definition rangeSpan (before : nat) (Hodd : odd before) `(r : Range rd) :
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
  move: (Range_split r Hodd H3 H4) => [r1 r2].
  exists (Some (packRange r1), Some (packRange r2)).
  by repeat (apply/andP; split=> //=).
Defined.
