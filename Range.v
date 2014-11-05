Require Import Lib.

Open Scope nat_scope.
Open Scope program_scope.

Import EqNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
    uloc   : nat;
    regReq : bool
}.

Coercion uloc : UsePos >-> nat.

Module UsePosNotations.
Notation " (| x |) " := {| uloc := x; regReq := false |}.
Notation " (! x !) " := {| uloc := x; regReq := true |}.
End UsePosNotations.

Definition upos_le (x y : UsePos) : bool := uloc x <= uloc y.
Definition upos_lt (x y : UsePos) : bool := uloc x < uloc y.

Arguments upos_le x y /.
Arguments upos_lt x y /.

Lemma NE_StronglySorted_UsePos_impl : forall xs,
  NE_StronglySorted upos_lt xs -> NE_head xs <= NE_last xs.
Proof.
  intros.
  induction xs; simpl in *; first by [].
  move: H. invert.
  move/NE_Forall_last: H2.
  rewrite /upos_lt /upos_le.
  apply/ltnW.
Qed.

Lemma NE_StronglySorted_UsePos_size_impl : forall xs,
  NE_StronglySorted upos_lt xs -> NE_length xs > 1
    -> NE_head xs < NE_last xs.
Proof.
  intros.
  induction xs; simpl in *; first by [].
  move: H. invert. subst.
  by move/NE_Forall_last: H3.
Qed.

Lemma NE_StronglySorted_lt_trans : forall (x : UsePos) (xs : NonEmpty UsePos),
  x < NE_head xs -> NE_StronglySorted upos_lt xs -> NE_Forall (upos_lt x) xs.
Proof.
  intros. induction xs; simpl in *.
    constructor. assumption.
  constructor. assumption.
  apply IHxs.
  apply NE_StronglySorted_inv in H0. inversion H0.
    apply NE_Forall_head in H2.
    unfold upos_lt in *.
    exact: (ltn_trans H).
  inversion H0. assumption.
Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosSublistsOf (f : UsePos -> bool) (l : NonEmpty UsePos) :=
  { p : (option (NonEmpty UsePos) * option (NonEmpty UsePos))
  | match p with
    | (Some l1, Some l2) =>
        [ /\ l = NE_append l1 l2
        ,    NE_all_true f l1
        &    ~~ f (NE_head l2)
        ]

    | (Some l1, None) => l = l1 /\ NE_all_true f l1
    | (None, Some l2) => l = l2 /\ ~~ f (NE_head l2)
    | (None, None)    => False
    end
  }.

(** Return two sublists of [l] such that for every element in the first
    sublist, [f elem] return [true]. *)
Fixpoint usePosSpan (f : UsePos -> bool) (l : NonEmpty UsePos) :
  UsePosSublistsOf f l.
Proof.
  destruct l as [x|x xs] eqn:Heqe.
    destruct (f x) eqn:Heqef.
      exists (Some (NE_Sing x), None).
      by split; constructor.
    exists (None, Some (NE_Sing x)).
      by split; try apply negbT.

  destruct (f x) eqn:Heqef.
  - Case "f x = true".
    destruct (usePosSpan f xs)
      as [[[l1| ] [l2| ]] Hsublists];
    inversion Hsublists;

    [ SCase "sublists = (Some, Some)";
      eexists (Some (NE_Cons x l1), Some l2)
    | SCase "sublists = (Some, None)";
      eexists (Some (NE_Cons x l1), None)
    | SCase "sublists = (None, Some)";
      eexists (Some (NE_Sing x), Some l2) ];
    simpl; split; f_equal; try assumption;
    intuition; constructor; assumption.

  - Case "f x = false".
    eexists (None, Some (NE_Cons x xs)).
    by split; try apply negbT.
Defined.

Lemma usePosSpan_spec (f : UsePos -> bool) (l : NonEmpty UsePos) :
  forall res, res = usePosSpan f l -> res.1 <> (None, None).
Proof.
  elim: l => [a|a l IHl] res Heqe;
  case: res Heqe => [[[o| ] [o0| ]] H] //.
Qed.

(** ** RangeDesc *)

(** The *extent* of a [RangeDesc] is the set of use positions it ranges over,
    inclusively, plus any extensions that have been applied to the range.

    A [RangeDesc] is built up from a set of use positions, and defines the
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
    ups  : NonEmpty UsePos
}.

(** ** Range *)

(** A [Range] constrains how a [RangeDesc] may be constructed, and maintains
    any invariants. *)

Inductive Range : RangeDesc -> Prop :=
  (** A [Range] built from a single use position covers that use positions, so
      that it begins at the use position, and ends one step after it (range
      ends are always exclusive). *)
  | R_Sing u : odd (uloc u) ->
    Range {| rbeg := uloc u
           ; rend := (uloc u).+1
           ; ups  := NE_Sing u
           |}

  (** A [Range] can be extended by adding a use position to the beginning.
      This means that they must be built up in reverse. *)
  | R_Cons u x : odd (uloc u) -> Range x
      -> forall (H : upos_lt u (NE_head (ups x))),
    Range {| rbeg := uloc u
           ; rend := rend x
           ; ups  := NE_Cons u (ups x)
           |}

  (** The address bounds of a [Range] may be arbitrarily extended, without
      reference to use positions.  This is useful when all of the use
      positions occur in a loop, for example, and you wish for the [Range] to
      bound the entire loop. *)
  | R_Extend x b' e' : Range x ->
    Range {| rbeg := minn b' (rbeg x)
           ; rend := maxn e' (rend x)
           ; ups  := ups x
           |}.

Tactic Notation "Range_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_Sing"
  | Case_aux c "R_Cons"
  | Case_aux c "R_Extend"
  ].

Definition getRangeDesc `(r : Range d) := d.
Arguments getRangeDesc [d] r /.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition rangeExtent `(Range r) := rend r - rbeg r.
Arguments rangeExtent [r] _ /.

Definition RangeSig := { rd : RangeDesc | Range rd }.
Arguments RangeSig /.

Lemma Range_beg_bounded `(r : Range rd) : rbeg rd <= uloc (NE_head (ups rd)).
Proof. induction r; auto. simpl. apply leq_min. assumption. Qed.

Lemma Range_end_bounded `(r : Range rd) : uloc (NE_last (ups rd)) < rend rd.
Proof. induction r; auto. apply ltn_max. assumption. Qed.

Theorem Range_sorted `(r : Range rd) : NE_StronglySorted upos_lt (ups rd).
Proof.
  Range_cases (induction r) Case; simpl.
  - Case "R_Sing". constructor.
  - Case "R_Cons".
    pose (Range_beg_bounded r).
    constructor. apply IHr.
    apply NE_StronglySorted_lt_trans.
    assumption. assumption.
  - Case "R_Extend". assumption.
Qed.

Theorem Range_all_odd `(r : Range rd) : NE_Forall (odd ∘ uloc) (ups rd).
Proof.
  Range_cases (induction r) Case; simpl.
  - Case "R_Sing". by constructor.
  - Case "R_Cons".
    constructor. auto. apply IHr.
  - Case "R_Extend". assumption.
Qed.

Lemma Range_bounded `(r : Range rd) : rbeg rd < rend rd.
Proof.
  Range_cases (induction r) Case; simpl in *.
  - Case "R_Sing". by [].
  - Case "R_Cons".
    pose (Range_beg_bounded r).
    pose (Range_end_bounded r).
    pose (Range_sorted r).
    apply NE_StronglySorted_UsePos_impl in n.
    unfold upos_lt, upos_le in *.
    exact (lt_le_shuffle H0 n i0).
  - Case "R_Extend".
    exact /ltn_min /ltn_max.
Qed.

Lemma Range_ups_bounded `(r : Range rd) : NE_head (ups rd) <= NE_last (ups rd).
Proof.
  Range_cases (induction r) Case; simpl in *.
  - Case "R_Sing".   by [].
  - Case "R_Cons".   unfold upos_lt in *; ssomega.
  - Case "R_Extend". by [].
Qed.

Definition Range_fromList `(us : NonEmpty UsePos) :
  NE_StronglySorted upos_lt us
    -> NE_Forall (odd ∘ uloc) us
    -> Range {| rbeg := uloc (NE_head us)
              ; rend := (uloc (NE_last us)).+1
              ; ups  := us |}.
Proof.
  elim: us => [a|a us IHus] Hsorted Hforall //.
    by apply R_Sing; inv Hforall.
  inv Hsorted; inv Hforall; simpl in *.
  specialize (IHus H1 H4).
  apply (R_Cons H3 IHus). simpl.
  by inversion H2; auto.
Defined.

Definition Range_weaken_beg : forall b x y xs,
  Range {| rbeg := x
         ; rend := y
         ; ups  := xs |}
    -> b <= x
    -> Range {| rbeg := b; rend := y; ups := xs |}.
Proof.
  move=> b x y xs H Hlt.
  move: (R_Extend b y H) => /=.
  rewrite (maxnn y).
  case: (minn_idPl Hlt) => -> //.
Defined.

Definition Range_append_fst
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  Range {| rbeg := rbeg0
         ; rend := (uloc (NE_last l1)).+1
         ; ups  := l1 |}.
Proof.
  move/NE_StronglySorted_inv_app: (Range_sorted r) => [Hsortedl _].
  move/NE_Forall_append: (Range_all_odd r) => /= [Hforall _].
  move: (@NE_head_append_spec) (Range_beg_bounded r) => ->.
  move/Range_weaken_beg: (Range_fromList Hsortedl Hforall). exact.
Defined.

Definition Range_weaken_end : forall e x y xs,
  Range {| rbeg := x
         ; rend := y
         ; ups  := xs |}
    -> y <= e
    -> Range {| rbeg := x; rend := e; ups := xs |}.
Proof.
  move=> e x y xs H Hgt.
  move: (R_Extend x e H) => /=.
  rewrite (minnn x).
  case: (maxn_idPl Hgt) => -> //.
Defined.

Definition Range_append_snd
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  Range {| rbeg := uloc (NE_head l2)
         ; rend := rend0
         ; ups  := l2 |}.
Proof.
  move/NE_StronglySorted_inv_app: (Range_sorted r) => [_ Hsortedr].
  move/NE_Forall_append: (Range_all_odd r) => /= [_ Hforall].
  move: (@NE_last_append_spec) (Range_end_bounded r) => ->.
  move/Range_weaken_end: (Range_fromList Hsortedr Hforall). exact.
Defined.

Lemma Range_append_spec
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  (uloc (NE_last l1)).+1 < uloc (NE_head l2).
Proof.
  move/NE_StronglySorted_impl_app: (Range_sorted r) => Hlt.
  move/NE_Forall_append: (Range_all_odd r) => /= [Hfal Hfar].
  apply NE_Forall_last in Hfal.
  apply NE_Forall_head in Hfar.
  rewrite /upos_lt in Hlt.
  apply ltn_odd.
  exact/andP. done.
Qed.

Definition rangesIntersect `(Range x) `(Range y) : bool :=
  if rbeg x < rbeg y
  then rbeg y < rend x
  else rbeg x < rend y.

Definition rangeIntersectionPoint `(xr : Range x) `(yr : Range y) : option nat :=
  if rangesIntersect xr yr
  then Some (minn (rbeg x) (rbeg y))
  else None.

Definition findRangeUsePos `(Range r) (f : UsePos -> bool) : option UsePos.
Proof.
  induction (ups r) as [u|u us].
    destruct (f u).
      apply (Some u).
    apply None.
  destruct (f u).
    apply (Some u).
  apply IHus.
Defined.

Record SplittableUsePos `(Range r) := {
    splittable_UsePos : UsePos;
    splittable_WithinRange :
         upos_lt (NE_head (ups r)) splittable_UsePos
      /\ upos_lt splittable_UsePos (NE_last (ups r))
}.

Record DividedRange `(r : Range rd) (f : UsePos -> bool)
  `(r1 : Range rd1) `(r2 : Range rd2) : Prop := {
    _ : ups rd = NE_append (ups rd1) (ups rd2);
    _ : NE_all_true f (ups rd1);
    _ : ~~ f (NE_head (ups rd2));
    _ : rbeg r == rbeg rd1;
    _ : rend r == rend rd2;
    _ : (uloc (NE_last (ups rd1))).+1 == rend rd1;
    _ : uloc (NE_head (ups rd2)) == rbeg rd2;
    _ : rend rd1 < rbeg rd2
}.

Definition SubRangesOf (f : UsePos -> bool) `(r : Range rd)
  (p : (option RangeSig * option RangeSig)) :=
  match p with
  | (Some r1, Some r2) => DividedRange r f r1.2 r2.2
  | (Some r1, None)    => ups rd = ups r1.1 /\ NE_all_true f (ups r1.1)
  | (None, Some r2)    => ups rd = ups r2.1 /\ ~~ f (NE_head (ups r2.1))
  | (None, None)       => False
  end.

Definition makeDividedRange (f : UsePos -> bool) `(r : Range rd)
  (l1 l2 : NonEmpty UsePos)
  (Heqe : ups rd = NE_append l1 l2)
  (Hu1 : NE_all_true f l1)
  (Hu2 : ~~ f (NE_head l2)) :
  { p : (option RangeSig * option RangeSig) | SubRangesOf f r p }.
Proof.
  destruct rd. simpl in *. subst.
  eexists (Some ({| rbeg := rbeg0
                  ; rend := (uloc (NE_last l1)).+1
                  ; ups  := l1 |}; _),
           Some ({| rbeg := uloc (NE_head l2)
                  ; rend := rend0
                  ; ups  := l2 |}; _)).
  move: (Range_append_spec r).
  simpl. constructor; auto.

  Grab Existential Variables.
  - apply (Range_append_snd r).
  - apply (Range_append_fst r).
Defined.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition rangeSpan (f : UsePos -> bool) `(r : Range rd) :
  { p : (option RangeSig * option RangeSig) | SubRangesOf f r p } :=
  match usePosSpan f (ups rd) with
  | exist (Some l1, Some l2) (And3 Heqe Hu1 Hu2) =>
      makeDividedRange r Heqe Hu1 Hu2

  | exist (Some _, None) (conj Heqe Hu) =>
      exist (SubRangesOf f r)
        (Some (exist Range rd r), None)
        (conj refl_equal (rew <- Heqe in Hu))

  | exist (None, Some _) (conj Heqe Hu) =>
      exist (SubRangesOf f r)
        (None, Some (exist Range rd r))
        (conj refl_equal (eq_rect_r (fun x => ~~ f (NE_head x)) Hu Heqe))

  | exist (None, None) Hu => ex_falso_quodlibet Hu
  end.

Lemma rangeSpan_spec (f : UsePos -> bool) `(r : Range rd) :
  forall res, res = rangeSpan f r -> res.1 <> (None, None).
Proof. elim: rd r => rbeg rend ups r [[[o| ] [o0| ]] res] Heq //. Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition DefiniteSubRangesOf (f : UsePos -> bool) `(r : Range rd) :=
  { p : (RangeSig * RangeSig)
  | let (r1, r2) := p in DividedRange r f r1.2 r2.2 }.

(** [splitRange] differs from [rangeSpan] in that the first and last elements
    must not be eligible for splitting, and therefore the [Range] will always
    be split into two definite sub-ranges. *)
Definition splitRange (f : UsePos -> bool) `(r : Range rd)
  (Hf : f (NE_head (ups rd))) (Hl : { u | NE_member u (ups rd) & ~~ f u }) :
  DefiniteSubRangesOf f r.
Proof.
  destruct rd. simpl in *.
  pose (rangeSpan f r) as s. destruct s.
  unfold DefiniteSubRangesOf.
  destruct x.

  destruct o as [o| ];
  destruct o0 as [o0| ]; intuition.
  - Case "(Some, Some)".
    exists (o, o0); exact: s.
  - Case "(Some, None)".
    exfalso; destruct s.
    destruct Hl as [H1 H2 H3].
    rewrite -H in H0.
    move: (NE_Forall_member_spec H0 H2).
    by move: H3 => /negbTE -> /=.
  - Case "(None, Some)".
    exfalso; destruct s.
    by move: H H0 Hf => <- /negbTE /= ->.
Defined.

Lemma four_points : forall n m o p,
  (n < m < o) && (o < p) -> (m - n) + (p - o) < p - n.
Proof.
  move=> n m o p /andP [/andP [H1 H2] H3].
  rewrite -ltn_subRL -subnDA.
  apply ltn_sub2l; rewrite subnKC //;
    try exact: ltnW.
  by ssomega.
Qed.

Lemma splitRange_spec (f : UsePos -> bool) `(r : Range rd)
  (Hf : f (NE_head (ups rd))) (Hl : { u | NE_member u (ups rd) & ~~ f u }) :
  let: exist (r1, r2) Hdr := splitRange r Hf Hl in
  rangeExtent r1.2 + rangeExtent r2.2 < rangeExtent r.
Proof.
  case: (splitRange r Hf Hl) => [[r1 r2] [_ _ _ /eqP H4 /eqP H5 _ _ H8]].
  rewrite /rangeExtent {}H4 {}H5 {Hf Hl r rd f}.
  apply four_points.
  apply/andP; split.
    apply/andP; split.
      by move: (Range_bounded r1.2).
    by [].
  by move: (Range_bounded r2.2).
Qed.

(**************************************************************************)

Module RangeTests.

Module Import E := NonEmptyNotations.
Module Import U := UsePosNotations.

Open Scope list_scope.

Fixpoint generateRangeBuilder
  (start index : nat) (Hodd : odd start) {struct index} :
  { rd : RangeDesc | Range rd & uloc (NE_head (ups rd)) = start }.
Proof.
  destruct index.
    pose (@R_Sing (|start|) Hodd).
    exists (getRangeDesc r). apply r. auto.
  pose (generateRangeBuilder start.+2 index) as r.
  destruct r as [rd r Hr].
    assert (upos_lt (|start|) (|start.+2|)) as Hlt.
      by unfold upos_lt; auto.
    by rewrite odd_succ_succ.
  have: (|start|) < NE_head (ups rd) by rewrite Hr.
  move=> Hlt.
  pose (@R_Cons (|start|) rd Hodd r Hlt) as r'.
  exists (getRangeDesc r').
    apply r'.
  auto.
Defined.

Definition generateRange (start finish : nat) (Hodd : odd start)
  (H : start < finish) : RangeSig.
Proof.
  pose (@generateRangeBuilder start ((finish - start)./2 - 1) Hodd).
  destruct s. exists x. apply r.
Defined.

Definition testRangeSpan (start finish : nat) (Hodd : odd start)
  (H : start < finish) (before : nat) :=
  let f u := uloc u < before in
  let r := (rangeSpan f (generateRange Hodd H).2).1 in
  (option_map (fun x => ups x.1) (fst r),
   option_map (fun x => ups x.1) (snd r)).

Example lt_1_9 : 1 < 9. done. Qed.

Definition odd_1 : odd 1. done. Qed.

Example testRangeSpan_1 :
  testRangeSpan odd_1 lt_1_9 1 = (None, Some [(|1|); (|3|); (|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_2 :
  testRangeSpan odd_1 lt_1_9 3 = (Some (NE_Sing (|1|)), Some [(|3|); (|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_3 :
  testRangeSpan odd_1 lt_1_9 5 = (Some [(|1|); (|3|)], Some [(|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_4 :
  testRangeSpan odd_1 lt_1_9 7 = (Some [(|1|); (|3|); (|5|)], Some (NE_Sing (|7|))).
Proof. reflexivity. Qed.

Example testRangeSpan_5 :
  testRangeSpan odd_1 lt_1_9 9 = (Some [(|1|); (|3|); (|5|); (|7|)], None).
Proof. reflexivity. Qed.

End RangeTests.
