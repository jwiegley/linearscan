Require Import Lib.
Require Import NonEmpty2.

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

Definition upos_lt (x y : UsePos) : bool := uloc x < uloc y.
Arguments upos_lt x y /.

Section EqUpos.

Variables (T : eqType) (x0 : T).
Implicit Type s : UsePos.

Fixpoint equpos s1 s2 {struct s2} :=
  match s1, s2 with
  | {| uloc := u1; regReq := rr1 |},
    {| uloc := u2; regReq := rr2 |} => (u1 == u2) && (rr1 == rr2)
  end.

Lemma equposP : Equality.axiom equpos.
Proof.
  move.
  case=> [u1 rr1].
  case=> [u2 rr2] /=.
  case: (u1 =P u2) => [<-|neqx]; last by right; case.
  case: (rr1 =P rr2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical upos_eqMixin := EqMixin equposP.
Canonical upos_eqType := Eval hnf in EqType UsePos upos_eqMixin.

Lemma equposE : equpos = eq_op. Proof. by []. Qed.

Definition UsePos_eqType (A : eqType) := Equality.Pack upos_eqMixin UsePos.

End EqUpos.

Program Instance upos_lt_trans : RelationClasses.Transitive upos_lt.
Obligation 1. exact: (ltn_trans H). Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosSublistsOf (f : UsePos -> bool) (l : NonEmpty UsePos) :=
  { p : option (NonEmpty UsePos) * option (NonEmpty UsePos)
  | match p with
    | (Some l1, Some l2) =>
        [ /\ l = NE_append l1 l2
        ,    all f l1
        &    ~~ f (NE_head l2)
        ]

    | (Some l1, None) => l = l1 /\ all f l1
    | (None, Some l2) => l = l2 /\ ~~ f (NE_head l2)
    | (None, None)    => False
    end
  }.

(** Return two sublists of [l] such that for every element in the first
    sublist, [f elem] return [true]. *)
Fixpoint usePosSpan (f : UsePos -> bool) (l : NonEmpty UsePos) :
  UsePosSublistsOf f l.
Proof.
  elim/ne_ind Heqe: l => [x|x xs].
    case Heqef: (f x).
      exists (Some [::: x], None) => /=.
      split; [ by [] | by apply/andP ].
    exists (None, Some [::: x]).
      by split; try apply negbT.

  case Heqef: (f x).
  - Case "f x = true".
    destruct (usePosSpan f xs)
      as [[[[y1 l1]| ] [[y2 l2]| ]] Hsublists];
    inversion Hsublists; clear Hsublists;
    inversion H; clear H; simpl in *.

    + SCase "sublists = (Some, Some)".
      eexists (Some [::: x & y1 :: l1], Some [::: y2 & l2]).
      move/andP: H0 => [H4 H5] /=.
      by split; auto; apply/and3P.
    + SCase "sublists = (Some, None)".
      eexists (Some [::: x & y1 :: l1], None).
      move/andP: H0 => [H4 H5] /=.
      by split; auto; apply/and3P.
    + SCase "sublists = (None, Some)".
      eexists (Some [::: x], Some [::: y2 & l2]).
      by split; auto; apply/andP.

  - Case "f x = false".
    eexists (None, Some (NE x xs)).
    by split; try apply negbT.
Admitted.
(* Defined. *)

Lemma usePosSpan_spec (f : UsePos -> bool) (l : NonEmpty UsePos) :
  forall res, res = usePosSpan f l -> res.1 <> (None, None).
Proof.
  elim/ne_ind: l => [a|a l IHl] res Heqe;
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
           ; ups  := [::: u]
           |}

  (** A [Range] can be extended by adding a use position to the beginning.
      This means that they must be built up in reverse. *)
  | R_Cons u x : odd (uloc u) -> Range x
      -> forall (H : upos_lt u (NE_head (ups x))),
    Range {| rbeg := uloc u
           ; rend := rend x
           ; ups  := [::: u & ups x]
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

Definition packRange `(r : Range d) := exist Range d r.
Arguments packRange [d] r /.

Definition rangeExtent `(Range r) := rend r - rbeg r.
Arguments rangeExtent [r] _ /.

Notation RangeSig := { rd : RangeDesc | Range rd }.

Lemma Range_beg_bounded `(r : Range rd) : rbeg rd <= uloc (NE_head (ups rd)).
Proof. induction r; auto. simpl. apply leq_min. assumption. Qed.

Lemma Range_end_bounded `(r : Range rd) : uloc (NE_last (ups rd)) < rend rd.
Proof.
  induction r; auto; simpl in *.
    move: H0 IHr; case: (ups x) => [y ys].
    by rewrite last_cons.
  exact: ltn_max.
Qed.

Theorem Range_sorted `(r : Range rd) : NE_StronglySorted upos_lt (ups rd).
Proof.
  Range_cases (induction r) Case; simpl.
  - Case "R_Sing". constructor.
  - Case "R_Cons".
    pose (Range_beg_bounded r).
    move: H0 IHr.
    rewrite /NE_StronglySorted.
    case: (ups x) => [y ys] /= H0 IHr.
    by apply/andP.
  - Case "R_Extend". by [].
Qed.

Theorem Range_all_odd `(r : Range rd) : NE_Forall (odd \o uloc) (ups rd).
Proof.
  Range_cases (induction r) Case; simpl.
  - Case "R_Sing". by apply/andP.
  - Case "R_Cons".
    move: IHr.
    rewrite /NE_Forall.
    case: (ups x) => [y ys] /= /andP [H1 H2].
    by apply/and3P.
  - Case "R_Extend". by [].
Qed.

Lemma pairmap_last : forall y ys,
  all id (pairmap upos_lt y ys) -> y <= last y ys.
Proof.
  move=> y ys.
  elim: ys y => [| y1 ys IHys] y //= /andP [H1 H2].
  specialize (IHys y1); apply IHys in H2; clear IHys.
  apply ltnW in H1.
  exact: (leq_trans H1).
Qed.

Lemma Range_bounded `(r : Range rd) : rbeg rd < rend rd.
Proof.
  Range_cases (induction r) Case; simpl in *.
  - Case "R_Sing". by [].
  - Case "R_Cons".
    pose H1 := Range_end_bounded r.
    pose H2 := Range_sorted r.
    case: (ups x) H0 H1 H2 => [y ys] /= H0 H1.
    move/pairmap_last => H2.
    exact/(ltn_trans H0)/(leq_ltn_trans H2).
  - Case "R_Extend".
    exact/ltn_min/ltn_max.
Qed.

Lemma Range_ups_bounded `(r : Range rd) : NE_head (ups rd) <= NE_last (ups rd).
Proof.
  Range_cases (induction r) Case; simpl in *.
  - Case "R_Sing".   by [].
  - Case "R_Cons".
    case: (ups x) => [y ys] /= in H0 IHr *.
    apply ltnW in H0.
    exact: (leq_trans H0).
  - Case "R_Extend". by [].
Qed.

Definition Range_fromList `(us : NonEmpty UsePos) :
  NE_StronglySorted upos_lt us
    -> NE_Forall (odd \o uloc) us
    -> Range {| rbeg := uloc (NE_head us)
              ; rend := (uloc (NE_last us)).+1
              ; ups  := us |}.
Proof.
  elim/ne_ind: us => [a|a us IHus] Hsorted Hforall /=.
    apply R_Sing; inv Hforall.
    move/andP in H0.
    by inversion H0.
  move: IHus Hsorted Hforall.
  rewrite /NE_StronglySorted /NE_Forall.
  case: us => [? ?] /= IHus /andP [? Hsorted] /and3P [H3 H4 H5].
  move: (conj H4 H5) => {H4 H5} /andP => Hforall.
  exact: (R_Cons H3 (IHus Hsorted Hforall)).
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
  induction (ups r) as [u|u us] using ne_ind.
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
      NE_head (ups r) < splittable_UsePos < NE_last (ups r)
}.

Record DividedRange `(r : Range rd) (f : UsePos -> bool)
  `(r1 : Range rd1) `(r2 : Range rd2) : Prop := {
    _ : ups rd = NE_append (ups rd1) (ups rd2);
    _ : all f (ups rd1);
    _ : ~~ f (NE_head (ups rd2));
    _ : rbeg r == rbeg rd1;
    _ : rend r == rend rd2;
    _ : (uloc (NE_last (ups rd1))).+1 == rend rd1;
    _ : uloc (NE_head (ups rd2)) == rbeg rd2;
    _ : rend rd1 < rbeg rd2
}.

Definition SubRangesOf (f : UsePos -> bool) `(r : Range rd)
  (p : option RangeSig * option RangeSig) :=
  match p with
  | (Some r1, Some r2) => DividedRange r f r1.2 r2.2
  | (Some r1, None)    => ups rd = ups r1.1 /\ all f (ups r1.1)
  | (None, Some r2)    => ups rd = ups r2.1 /\ ~~ f (NE_head (ups r2.1))
  | (None, None)       => False
  end.

Definition makeDividedRange (f : UsePos -> bool) `(r : Range rd)
  (l1 l2 : NonEmpty UsePos)
  (Heqe : ups rd = NE_append l1 l2)
  (Hu1 : all f l1)
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

Lemma rewrite_ups_in_all : forall {rd l1 f},
  ups rd = l1 -> all f l1 -> all f (ups rd).
Proof. by move=> rd l1 f ->. Defined.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition rangeSpan (f : UsePos -> bool) `(r : Range rd) :
  { p : option RangeSig * option RangeSig | SubRangesOf f r p } :=
  match usePosSpan f (ups rd) with
  | exist (Some l1, Some l2) (And3 Heqe Hu1 Hu2) =>
      makeDividedRange r Heqe Hu1 Hu2

  | exist (Some l1, None) (conj Heqe Hall) =>
      exist (SubRangesOf f r)
        (Some (exist Range rd r), None)
        (conj refl_equal (rewrite_ups_in_all Heqe Hall))

  | exist (None, Some l2) (conj Heqe Hall) =>
      exist (SubRangesOf f r)
        (None, Some (exist Range rd r))
        (conj refl_equal
              (eq_rect_r (fun x => ~~ f (NE_head x)) Hall Heqe))

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
    destruct Hl as [x H2 H3].
    simpl in *; subst.
    move: H2 H0 Hf r.
    rewrite /NE_member.
    case: (ups o.1) => [y ys] /orP [/eqP H4|H5] /=.
      rewrite {}H4 => _ H4.
      move/negbTE in H3.
      by rewrite H3 in H4.
    move/andP => [H1 H2].
    move/allP: H2 => /(_ x) /(_ H5) H2.
    move/negbTE in H3.
    by rewrite H3 in H2.
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
  exact: (ltn_trans H2).
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

Module RangeTests.

Module Import U := UsePosNotations.

Open Scope list_scope.

Fixpoint generateRangeBuilder
  (start index : nat) (Hodd : odd start) {struct index} :
  { rd : RangeDesc | Range rd & uloc (NE_head (ups rd)) = start }.
Proof.
  destruct index as [|index].
    pose (@R_Sing (|start|) Hodd).
    exists r. apply r. auto.
  pose (generateRangeBuilder start.+2 index) as r.
  destruct r as [rd r Hr].
    assert (upos_lt (|start|) (|start.+2|)) as Hlt.
      by unfold upos_lt; auto.
    by rewrite odd_succ_succ.
  have: (|start|) < NE_head (ups rd) by rewrite Hr.
  move=> Hlt.
  pose (@R_Cons (|start|) rd Hodd r Hlt) as r'.
  exists r'. apply r'. auto.
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
  testRangeSpan odd_1 lt_1_9 1 = (None, Some [::: (|1|) & [:: (|3|); (|5|); (|7|)]]).
Proof. reflexivity. Qed.

Example testRangeSpan_2 :
  testRangeSpan odd_1 lt_1_9 3 = (Some [::: (|1|)], Some [(|3|); (|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_3 :
  testRangeSpan odd_1 lt_1_9 5 = (Some [(|1|); (|3|)], Some [(|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_4 :
  testRangeSpan odd_1 lt_1_9 7 = (Some [(|1|); (|3|); (|5|)], Some [::: (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_5 :
  testRangeSpan odd_1 lt_1_9 9 = (Some [(|1|); (|3|); (|5|); (|7|)], None).
Proof. reflexivity. Qed.

End RangeTests.
