Require Import Coq.Program.Equality.
Require Import Lib.
Require Import NonEmpty.
Require Import Hask.Alternative.

Open Scope nat_scope.

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

Definition upos_le (x y : UsePos) := uloc x <= uloc y.
Definition upos_lt (x y : UsePos) := uloc x < uloc y.

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

Lemma NE_StronglySorted_lt_trans
  : forall (x : UsePos) (xs : NonEmpty UsePos),
  x < NE_head xs
    -> NE_StronglySorted upos_lt xs
    -> NE_Forall (upos_lt x) xs.
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
        , NE_all_true f l1
        & f (NE_head l2) = false
        ]

    | (Some l1, None) => l = l1 /\ NE_all_true f l1
    | (None, Some l2) => l = l2 /\ f (NE_head l2) = false
    | (None, None)    => False
    end
  }.

(** Return two sublists of [l] such that for every element in the first
    sublist, [f elem] return [true]. *)
Fixpoint usePosSpan (f : UsePos -> bool) (l : NonEmpty UsePos)
  : UsePosSublistsOf f l.
Proof.
  destruct l as [x|x xs] eqn:Heqe.
    destruct (f x) eqn:Heqef.
      exists (Some (NE_Sing x), None).
      simpl. split. reflexivity.
      constructor. assumption.
    exists (None, Some (NE_Sing x)). auto.

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
    split. reflexivity. assumption.
Defined.

Lemma usePosSpan_spec (f : UsePos -> bool) (l : NonEmpty UsePos)
  : forall res, res = usePosSpan f l -> res.1 <> (None, None).
Proof.
  elim: l => [a|a l IHl] res Heqe;
  case: res Heqe => [[[o| ] [o0| ]] H] //.
Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosDefiniteSublistsOf (l : NonEmpty UsePos) :=
  { p : (NonEmpty UsePos * NonEmpty UsePos)
  | l = NE_append (fst p) (snd p) }.

Definition usePosSplit (f : UsePos -> bool)
  (l : NonEmpty UsePos) (Hlen : NE_length l > 1)
  (Hfirst_true : f (NE_head l))
  (Hlast_false : ~~ f (NE_last l))
  : UsePosDefiniteSublistsOf l.
Proof.
  pose (usePosSpan f l). destruct u.
  unfold UsePosDefiniteSublistsOf.
  induction l; simpl in *. intuition.
  destruct x.

  destruct o as [o| ];
  destruct o0 as [o0| ]; intuition.
  - Case "(Some, Some)".
    inversion y. exists (o, o0). assumption.

  - Case "(Some, None)".
    apply NE_Forall_last in H0.
    rewrite <- H in *. simpl in H0. exfalso.
    apply (eq_true_false_abs (f (NE_last l)));
      [ by [] | exact: negbTE ].

  - Case "(None, Some)".
    rewrite <- H in *. simpl in H0. exfalso.
    apply (eq_true_false_abs (f a)); assumption.
Defined.

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

Record RangeDesc := {
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
  | R_Sing u : even (uloc u) ->
    Range {| rbeg := uloc u
           ; rend := S (uloc u)
           ; ups  := NE_Sing u
           |}

  (** A [Range] can be extended by adding a use position to the beginning.
      This means that they must be built up in reverse. *)
  | R_Cons u x : even (uloc u) -> Range x
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

Coercion getRangeDesc : Range >-> RangeDesc.

Definition rangeExtent `(Range r) := rend r - rbeg r.

Definition RangeSig := { rd : RangeDesc | Range rd }.

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

Theorem Range_all_even `(r : Range rd) : NE_Forall (even ∘ uloc) (ups rd).
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

Definition Range_fromList `(us : NonEmpty UsePos) :
  NE_StronglySorted upos_lt us
    -> NE_Forall (even ∘ uloc) us
    -> Range {| rbeg := uloc (NE_head us)
              ; rend := S (uloc (NE_last us))
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
         ; rend := S (uloc (NE_last l1))
         ; ups  := l1 |}.
Proof.
  move/NE_StronglySorted_inv_app: (Range_sorted r) => [Hsortedl _].
  move/NE_Forall_append: (Range_all_even r) => /= [Hforall _].
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
  move/NE_Forall_append: (Range_all_even r) => /= [_ Hforall].
  move: (@NE_last_append_spec) (Range_end_bounded r) => ->.
  move/Range_weaken_end: (Range_fromList Hsortedr Hforall). exact.
Defined.

Functional Scheme even_ind := Induction for even Sort Prop.

Lemma ltn_even : forall n m, even n && even m -> n < m -> n.+1 < m.
Proof. move=> n; functional induction even n; case=> //; by case. Qed.

Definition Range_append_spec
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  S (uloc (NE_last l1)) < uloc (NE_head l2).
Proof.
  move/NE_StronglySorted_impl_app: (Range_sorted r) => Hlt.
  move/NE_Forall_append: (Range_all_even r) => /= [Hfal Hfar].
  apply NE_Forall_last in Hfal.
  apply NE_Forall_head in Hfar.
  rewrite /upos_lt in Hlt.
  apply ltn_even.
  exact/andP. done.
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
  let check u := if f u then Some u else None in
  let fix go us := match us with
      | NE_Sing u     => check u
      | NE_Cons u us' => check u <|> go us'
      end in
  go (ups r).

Record SplittableUsePos `(Range r) := {
    splittable_UsePos : UsePos;
    splittable_WithinRange :
         upos_lt (NE_head (ups r)) splittable_UsePos
      /\ upos_lt splittable_UsePos (NE_last (ups r))
}.

Definition SubRangesOf (f : UsePos -> bool) `(r : Range rd)
  (p : (option RangeSig * option RangeSig)) :=
  match p with
  | (Some r1, Some r2) =>
      [ /\ ups rd = NE_append (ups r1.1) (ups r2.1)
      , NE_all_true f (ups r1.1)
      , f (NE_head (ups r2.1)) = false
      , rend r1.1 < rbeg r2.1
      & (rbeg r == rbeg r1.1) && (rend r == rend r2.1)
      ]

  | (Some r1, None) =>
      ups rd = ups r1.1 /\ NE_all_true f (ups r1.1)
  | (None, Some r2) =>
      ups rd = ups r2.1 /\ f (NE_head (ups r2.1)) = false

  | (None, None) => False
  end.

Definition dividedRange (f : UsePos -> bool) `(r : Range rd)
  (l1 l2 : NonEmpty UsePos)
  (Heqe : ups rd = NE_append l1 l2)
  (Hu1 : NE_all_true f l1)
  (Hu2 : f (NE_head l2) = false)
  : { p : (option RangeSig * option RangeSig) | SubRangesOf f r p }.
Proof.
  destruct rd. simpl in *. subst.
  eexists (Some ({| rbeg := rbeg0
                  ; rend := S (uloc (NE_last l1))
                  ; ups  := l1 |}; _),
           Some ({| rbeg := uloc (NE_head l2)
                  ; rend := rend0
                  ; ups  := l2 |}; _)).
  simpl. constructor; auto.
    by apply Range_append_spec in r.
  exact/andP.

  Grab Existential Variables.

  - apply (Range_append_snd r).
  - apply (Range_append_fst r).
Defined.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition rangeSpan (f : UsePos -> bool) `(r : Range rd)
  : { p : (option RangeSig * option RangeSig) | SubRangesOf f r p } :=
  match usePosSpan f (ups rd) with
  | exist (Some l1, Some l2) (And3 Heqe Hu1 Hu2) =>
      dividedRange r Heqe Hu1 Hu2

  | exist (Some _, None) (conj Heqe Hu) =>
      exist (SubRangesOf f r)
        (Some (exist Range rd r), None)
        (conj refl_equal (rew <- Heqe in Hu))

  | exist (None, Some _) (conj Heqe Hu) =>
      exist (SubRangesOf f r)
        (None, Some (exist Range rd r))
        (conj refl_equal (eq_rect_r (fun x => f (NE_head x) = false) Hu Heqe))

  | exist (None, None) Hu => ex_falso_quodlibet Hu
  end.

Lemma rangeSpan_spec (f : UsePos -> bool) `(r : Range rd)
  : forall res, res = rangeSpan f r -> res.1 <> (None, None).
Proof. elim: rd r => rbeg rend ups r [[[o| ] [o0| ]] res] Heq //. Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition DefiniteSubRangesOf `(r : Range rd) :=
  { p : (RangeSig * RangeSig)
  | let (r1, r2) := p in ups rd = NE_append (ups r1.1) (ups r2.1) }.

(** [splitRange] differs from [rangeSpan] in that the first and last elements
    must not be eligible for splitting, and therefore the [Range] will always
    be split into two definite sub-ranges. *)
Definition splitRange (f : UsePos -> bool) `(r : Range rd)
  (Hfirst_true : f (NE_head (ups rd)))
  (Hlast_false : ~~ f (NE_last (ups rd)))
  : DefiniteSubRangesOf r.
Proof.
  destruct rd. simpl in *.
  pose (rangeSpan f r) as s. destruct s.
  unfold DefiniteSubRangesOf.
  destruct x.

  destruct o as [o| ];
  destruct o0 as [o0| ]; intuition; destruct s;
  [ Case "(Some, Some)"; exists (o, o0); apply H
  | Case "(Some, None)"; exfalso; apply NE_Forall_last in H0
  | Case "(None, Some)"; exfalso ];

  rewrite <- H in *; simpl in H0;
  [ apply (eq_true_false_abs (f (NE_last ups0)))
  | apply (eq_true_false_abs (f (NE_head ups0))) ];
  auto; exact: negbTE.
Defined.

(**************************************************************************)

Module RangeTests.

Import NonEmptyNotations.
Import UsePosNotations.

Fixpoint generateRangeBuilder
  (start index : nat) (Heven : even start) {struct index}
  : { rd : RangeDesc | Range rd & uloc (NE_head (ups rd)) = start }.
Proof.
  destruct index.
    pose (@R_Sing (|start|) Heven).
    exists (getRangeDesc r). apply r. auto.
  pose (generateRangeBuilder start.+2 index) as r.
  destruct r as [rd r Hr].
    assert (upos_lt (|start|) (|start.+2|)) as Hlt.
      by unfold upos_lt; auto.
    by rewrite Nat.even_succ_succ.
  have: (|start|) < NE_head (ups rd) by rewrite Hr.
  move=> Hlt.
  pose (@R_Cons (|start|) rd Heven r Hlt) as r'.
  exists (getRangeDesc r').
    apply r'.
  auto.
Defined.

Definition generateRange (start finish : nat) (Heven : even start)
  (H : start < finish) : RangeSig.
Proof.
  pose (@generateRangeBuilder start ((finish - start)./2 - 1) Heven).
  destruct s. exists x. apply r.
Defined.

Definition testRangeSpan (start finish : nat) (Heven : even start)
  (H : start < finish) (before : nat) :=
  let r := (rangeSpan (fun u => uloc u < before) (generateRange Heven H).2).1 in
  (fmap (fun x => ups x.1) (fst r), fmap (fun x => ups x.1) (snd r)).

Example lt_2_10 : 2 < 10. done. Qed.

Definition even_2 := Nat.even_2.

Example testRangeSpan_1 :
  testRangeSpan even_2 lt_2_10 2 = (None, Some [(|2|); (|4|); (|6|); (|8|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_2 :
  testRangeSpan even_2 lt_2_10 4 = (Some (NE_Sing (|2|)), Some [(|4|); (|6|); (|8|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_3 :
  testRangeSpan even_2 lt_2_10 6 = (Some [(|2|); (|4|)], Some [(|6|); (|8|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_4 :
  testRangeSpan even_2 lt_2_10 8 = (Some [(|2|); (|4|); (|6|)], Some (NE_Sing (|8|))).
Proof. reflexivity. Qed.

Example testRangeSpan_5 :
  testRangeSpan even_2 lt_2_10 10 = (Some [(|2|); (|4|); (|6|); (|8|)], None).
Proof. reflexivity. Qed.

End RangeTests.
