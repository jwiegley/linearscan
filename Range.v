Require Import LinearScan.Lib.
Require Import LinearScan.Ltac.
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

Inductive Range : RangeDesc -> Prop :=
  | R_nil b e : b < e ->
    Range {| rbeg := b
           ; rend := e
           ; ups  := [::]
           |}

  | R_cons u x : odd (uloc u) -> Range x
      -> rbeg x <= uloc u < head_or_end x ->
    Range {| rbeg := rbeg x
           ; rend := rend x
           ; ups  := u :: ups x
           |}

  | R_adjust_beg b x : Range x
      -> (if ups x is u :: _
          then b <= u
          else b < rend x) ->
    Range {| rbeg := b
           ; rend := rend x
           ; ups  := ups x
           |}

  | R_adjust_end e x : Range x
      -> last_or_beg x < e ->
    Range {| rbeg := rbeg x
           ; rend := e
           ; ups  := ups x
           |}.

Tactic Notation "Range_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_nil"
  | Case_aux c "R_cons"
  | Case_aux c "R_adjust_beg"
  | Case_aux c "R_adjust_end"
  ].

Definition getRangeDesc `(r : Range d) := d.
Arguments getRangeDesc [d] r /.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition packRange `(r : Range d) := exist Range d r.
Arguments packRange [d] r /.

Notation RangeSig := { rd : RangeDesc | Range rd }.

Definition BoundedRange (pos : nat) :=
  { r : RangeSig | pos <= head_or_end r.1 }.

Definition transportBoundedRange `(Hlt : base < prev)
  (x : BoundedRange prev) : BoundedRange base.
  case: x => [r H].
  apply: exist.
  apply: r.
  exact/(leq_trans _ H)/ltnW.
Defined.

Lemma Range_beg_bounded `(r : Range rd) :
  if ups rd is u :: _
  then rbeg rd <= u
  else rbeg rd < rend rd.
Proof.
  elim: r => //= ? x;
  case: (ups x) => /= *;
  by ordered.
Qed.

Lemma Range_end_bounded `(r : Range rd) :
  last_or_beg rd < rend rd.
Proof.
  elim: r => //= ? x;
  case: (ups x) => /= *;
  by ordered.
Qed.

Theorem Range_sorted `(r : Range rd) : StronglySorted upos_lt (ups rd).
Proof.
  elim: r => //=; constructor=> //.
  case: (ups x) => //= [y ys] in H1 H2 *.
  constructor.
    by ordered.
  inversion H1; subst.
  by match_all.
Qed.

Theorem Range_all_odd `(r : Range rd) : List.Forall (odd \o uloc) (ups rd).
Proof.
  elim: r => //= [u x Hodd r Hall H].
  by constructor.
Qed.

Lemma last_ltn : forall (z y : nat) (xs : seq nat) (n : nat),
  last z xs < n -> y <= z -> last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma Forall_last_ltn : forall (y : UsePos) (ys : seq UsePos) (n : nat),
  last (uloc y) [seq uloc u | u <- ys] < n
    -> List.Forall (fun x : UsePos => y < x) ys -> y < n.
Proof.
  move=> y.
  elim=> //= [z zs IHzs] n Hlast.
  invert; subst.
  apply: IHzs => //.
  move/ltnW in H1.
  exact (last_ltn Hlast H1).
Qed.

Lemma Range_bounded `(r : Range rd) : rbeg rd < rend rd.
Proof.
  elim: r => //=;
  try ordered;
  move=> n x r;
  move: (Range_sorted r);
  move: (Range_beg_bounded r);
  move: (Range_end_bounded r) => /=;
  case: (ups x) => [|y ys] /= He Hb Hsort H1 H2;
  try ordered; inv Hsort;
    first by move: (Forall_last_ltn He H4); ordered.
  by move: (Forall_last_ltn H2 H4); ordered.
Qed.

Definition Range_cat
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
  move/Forall_append: (Range_all_odd r) => /= [Hoddl Hoddr].
  move: (Range_bounded r) => /= Hbound.
  move: (Range_beg_bounded r) => /= Hbeg.
  move: (Range_end_bounded r) => /= Hend.
  split.
    clear Hsortedr Hoddr Hend.
    elim: l1 {r} => /= [|x xs IHxs] in Hlt1 Hsortedl Hoddl Hbeg *.
      by constructor.
    inv Hsortedl; inv Hoddl.
    apply: (R_cons H3 (IHxs _ H1 H4 _)) => /=.
    - exact: (last_ltn Hlt1).
    - case: xs {IHxs} => /= [|z zs] in H2 Hlt1 Hsortedl Hoddl H1 H4 *;
      try move/StronglySorted_UsePos_cons in Hsortedl;
      inv H2; try ordered.
      case: l2 => //= [w ws] in Hlt2 *.
      by ordered.
    - apply/andP; split=> //.
      move/Forall_all in H2.
      exact: head_last.
  clear Hsortedl Hoddl Hbeg.
  elim: l2 {r} => /= [|x xs IHxs] in Hlt2 Hsortedr Hoddr Hend *.
    by constructor.
  inv Hsortedr; inv Hoddr.
  apply: (R_cons H3 (IHxs _ H1 H4 _)) => /=.
  - case: xs => [|y ys] in IHxs Hsortedr Hoddr Hend H1 H2 H4 *.
      rewrite last_cat_upos /= in Hend.
      by ordered.
    by inv H2; ordered.
  - case: xs => /= [|y ys] in IHxs Hsortedr Hoddr Hend H1 H2 H4 *.
      case: l1 => //= [z zs] in Hlt1 IHxs Hend *.
      rewrite cats0.
      rewrite cats1 last_rcons_upos in Hend.
      by ordered.
    move: Hend.
    by rewrite !last_cat_upos /=.
  - apply/andP; split=> //.
    move/Forall_all in H2.
    apply: head_last => //.
    rewrite last_cat_upos in Hend.
    have: forall (b e : nat) x (xs l1 : seq UsePos),
            last b [seq uloc u | u <- l1 ++ x :: xs] < e
              -> last_or x xs < e.
      move=> b e x0 xs0 l10 Hlast.
      elim: xs0 => /= [|z zs IHzs] in x0 Hlast *.
        by rewrite last_cat_upos /= in Hlast.
      apply: IHzs.
      move: Hlast.
      rewrite !last_cat_upos.
      by rewrite last_cons_upos.
    exact.
Defined.

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
  move: (Range_cat r H3 H4) => [r1 r2].
  exists (Some (packRange r1), Some (packRange r2)).
  by repeat (apply/andP; split=> //=).
Defined.
