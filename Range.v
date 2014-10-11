Require Import Coq.Program.Equality.
Require Import Lib.
Require Import NonEmpty.
Require Import Hask.Alternative.

Open Scope nat_scope.

Import EqNotations.

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

Module UsePosNotations.
Notation " (| x |) " := {| uloc := x; regReq := false |}.
Notation " (! x !) " := {| uloc := x; regReq := true |}.
End UsePosNotations.

Definition upos_le (x y : UsePos) := uloc x <= uloc y.
Definition upos_lt (x y : UsePos) := uloc x < uloc y.

Program Instance upos_le_PO : PreOrder upos_le.
Obligation 1. constructor. Qed.
Obligation 2.
  unfold Transitive. intros.
  unfold upos_le in *. omega.
Qed.

Program Instance upos_lt_trans : Transitive upos_lt.
Obligation 1. unfold upos_lt in *. omega. Qed.

Lemma NE_StronglySorted_UsePos_impl : forall xs,
  NE_StronglySorted upos_lt xs
    -> upos_le (NE_head xs) (NE_last xs).
Proof.
  intros.
  induction xs; simpl in *.
    unfold upos_le. trivial.
  apply NE_StronglySorted_inv in H; inversion H.
  apply NE_Forall_last in H1.
  unfold upos_lt, upos_le in *. omega.
Qed.

Lemma NE_StronglySorted_lt_trans : forall x xs,
  upos_lt x (NE_head xs)
    -> NE_StronglySorted upos_lt xs
    -> NE_Forall (upos_lt x) xs.
Proof.
  intros. induction xs; simpl in *.
    constructor. assumption.
  constructor. assumption.
  apply IHxs.
  apply NE_StronglySorted_inv in H0. inversion H0.
    apply NE_Forall_head in H2.
    unfold upos_lt in *. omega.
  inversion H0.
  assumption.
Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosSublistsOf (f : UsePos -> bool) (l : NonEmpty UsePos) :=
  { p : (option (NonEmpty UsePos) * option (NonEmpty UsePos))
  | match p with
    | (Some l1, Some l2) =>
        l = NE_append l1 l2 /\ NE_all_true f l1 /\ f (NE_head l2) = false

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

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosDefiniteSublistsOf (l : NonEmpty UsePos) :=
  { p : (NonEmpty UsePos * NonEmpty UsePos)
  | l = NE_append (fst p) (snd p) }.

Definition usePosSplit (f : UsePos -> bool)
  (l : NonEmpty UsePos) (Hlen : NE_length l > 1)
  (Hfirst_true : f (NE_head l) = true)
  (Hlast_false : f (NE_last l) = false)
  : UsePosDefiniteSublistsOf l.
Proof.
  pose (usePosSpan f l). destruct u.
  unfold UsePosDefiniteSublistsOf.
  induction l; simpl in *. intuition.
  destruct x.

  destruct o as [o| ];
  destruct o0 as [o0| ]; intuition.
  - Case "(Some, Some)".
    exists (o, o0). assumption.

  - Case "(Some, None)".
    apply NE_Forall_last in H0.
    rewrite <- H in *. simpl in H0. exfalso.
    apply (eq_true_false_abs (f (NE_last l))); assumption.

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
  | R_Sing u :
    Range {| rbeg := uloc u
           ; rend := S (uloc u)
           ; ups  := NE_Sing u
           |}

  (** A [Range] can be extended by adding a use position to the beginning.
      This means that they must be built up in reverse. *)
  | R_Cons u x : Range x -> forall (H : upos_lt u (NE_head (ups x))),
    Range {| rbeg := uloc u
           ; rend := rend x
           ; ups  := NE_Cons u (ups x)
           |}

  (** The address bounds of a [Range] may be arbitrarily extended, without
      reference to use positions.  This is useful when all of the use
      positions occur in a loop, for example, and you wish for the [Range] to
      bound the entire loop. *)
  | R_Extend x b' e' : Range x ->
    Range {| rbeg := min b' (rbeg x)
           ; rend := Peano.max e' (rend x)
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
Proof. induction r; auto. apply le_min. assumption. Qed.

Lemma Range_end_bounded `(r : Range rd) : uloc (NE_last (ups rd)) < rend rd.
Proof. induction r; auto. apply lt_max. assumption. Qed.

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

Lemma Range_bounded `(r : Range rd) : rbeg rd < rend rd.
Proof.
  Range_cases (induction r) Case; simpl in *.
  - Case "R_Sing". omega.
  - Case "R_Cons".
    pose (Range_beg_bounded r).
    pose (Range_end_bounded r).
    pose (Range_sorted r).
    apply NE_StronglySorted_UsePos_impl in n.
    unfold upos_lt, upos_le in *. omega.
  - Case "R_Extend".
    apply lt_min. apply lt_max.
    assumption.
Qed.

Definition Range_fromList `(us : NonEmpty UsePos) :
  NE_StronglySorted upos_lt us
    -> Range {| rbeg := uloc (NE_head us)
              ; rend := S (uloc (NE_last us))
              ; ups  := us |}.
Proof.
  intros.
  induction us.
    apply R_Sing.
  inversion H.
  specialize (IHus H2).
  apply (R_Cons a IHus).
    apply IHus.
  subst. simpl.
  apply NE_Forall_head in H3.
  assumption.
Defined.

Definition Range_weaken_beg : forall b x y xs,
  Range {| rbeg := x
         ; rend := y
         ; ups  := xs |}
    -> b <= x
    -> Range {| rbeg := b; rend := y; ups := xs |}.
Proof.
  intros.
  pose (R_Extend {| rbeg := x; rend := y; ups := xs |} b y H).
  simpl in *.
  rewrite Max.max_idempotent in r.
  pose (Min.min_spec b x) as m.
  destruct (le_lt_eq_dec b x).
  - assumption.
  - intuition. rewrite <- H3. assumption.
  - intuition. rewrite e. rewrite <- H3. assumption.
Defined.

Definition Range_append_fst
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  Range {| rbeg := rbeg0
         ; rend := S (uloc (NE_last l1))
         ; ups  := l1 |}.
Proof.
  pose (Range_sorted r) as Hsorted.
  apply NE_StronglySorted_inv_app in Hsorted.
  inversion Hsorted as [Hsortedl ?].

  pose (Range_beg_bounded r) as Hbeg.
  simpl in Hbeg.
  rewrite NE_head_append_spec in Hbeg.

  pose (Range_fromList l1 Hsortedl) as r'.
  apply Range_weaken_beg with (x := uloc (NE_head l1)).
  apply r'.
  assumption.
Defined.

Definition Range_weaken_end : forall e x y xs,
  Range {| rbeg := x
         ; rend := y
         ; ups  := xs |}
    -> y <= e
    -> Range {| rbeg := x; rend := e; ups := xs |}.
Proof.
  intros.
  pose (R_Extend {| rbeg := x; rend := y; ups := xs |} x e H).
  simpl in *.
  rewrite Min.min_idempotent in r.
  pose (Max.max_spec e y) as m.
  destruct (le_lt_eq_dec y e).
  - assumption.
  - intuition. rewrite <- H3. assumption.
  - intuition. rewrite <- H3. assumption.
Defined.

Definition Range_append_snd
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  Range {| rbeg := uloc (NE_head l2)
         ; rend := rend0
         ; ups  := l2 |}.
Proof.
  pose (Range_sorted r) as Hsorted.
  apply NE_StronglySorted_inv_app in Hsorted.
  inversion Hsorted as [? Hsortedr].

  pose (Range_end_bounded r) as Hend.
  simpl in Hend.
  rewrite NE_last_append_spec in Hend.

  pose (Range_fromList l2 Hsortedr) as r'.
  apply Range_weaken_end with (y := S (uloc (NE_last l2))).
  apply r'. assumption.
Defined.

Definition rangesIntersect `(Range x) `(Range y) : bool :=
  if rbeg x <? rbeg y
  then rbeg y <? rend x
  else rbeg x <? rend y.

Definition rangeIntersectionPoint `(xr : Range x) `(yr : Range y) : option nat :=
  if rangesIntersect xr yr
  then Some (min (rbeg x) (rbeg y))
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

Definition SubRangesOfEvidence (f : UsePos -> bool) `(r : Range rd)
  (p : (option RangeSig * option RangeSig)) :=
  match p with
  | (Some r1, Some r2) =>
      ups rd = NE_append (ups r1.1) (ups r2.1)
        /\ NE_all_true f (ups r1.1) /\ f (NE_head (ups r2.1)) = false

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
  : { p : (option RangeSig * option RangeSig) | SubRangesOfEvidence f r p }.
Proof.
  destruct rd. simpl in *. subst.
  eexists (Some (exist _ {| rbeg := rbeg0
                          ; rend := S (uloc (NE_last l1))
                          ; ups  := l1 |} _),
           Some (exist _ {| rbeg := uloc (NE_head l2)
                          ; rend := rend0
                          ; ups  := l2 |} _)).
  simpl. intuition.

  Grab Existential Variables.
  - apply (Range_append_snd r).
  - apply (Range_append_fst r).
Defined.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition rangeSpan (f : UsePos -> bool) `(r : Range rd)
  : { p : (option RangeSig * option RangeSig) | SubRangesOfEvidence f r p } :=
  match usePosSpan f (ups rd) with
  | exist (Some l1, Some l2) (conj Heqe (conj Hu1 Hu2)) =>
      dividedRange f r l1 l2 Heqe Hu1 Hu2

  | exist (Some _, None) (conj Heqe Hu) =>
    exist (SubRangesOfEvidence f r)
      (Some (exist Range rd r), None)
      (conj eq_refl (rew <- Heqe in Hu))

  | exist (None, Some _) (conj Heqe Hu) =>
    exist (SubRangesOfEvidence f r)
      (None, Some (exist Range rd r))
      (conj eq_refl (eq_rect_r (fun x => f (NE_head x) = false) Hu Heqe))

  | exist (None, None) Hu => ex_falso_quodlibet Hu
  end.

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
  (Hfirst_true : f (NE_head (ups rd)) = true)
  (Hlast_false : f (NE_last (ups rd)) = false)
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
  assumption.
Defined.

(**************************************************************************)

Module RangeTests.

Import NonEmptyNotations.
Import UsePosNotations.

Fixpoint generateRangeBuilder (start index : nat) {struct index}
  : { rd : RangeDesc | Range rd & uloc (NE_head (ups rd)) = start }.
Proof.
  destruct index.
    pose (R_Sing (|start|)).
    exists (getRangeDesc r). apply r. auto.
  pose (generateRangeBuilder (S start) index) as r.
  destruct r as [rd r Hr].
  assert (upos_lt (|start|) (|S start|)) as Hlt.
    unfold upos_lt. auto.
  rewrite <- Hr in Hlt.
  pose (R_Cons (|start|) rd r Hlt) as r'.
  exists (getRangeDesc r'). apply r'. auto.
Defined.

Definition generateRange (start finish : nat) (H : start < finish) : RangeSig.
Proof.
  pose (generateRangeBuilder start (finish - start - 1)).
  destruct s. exists x. apply r.
Defined.

Definition testRangeSpan (start finish n : nat) (H : start < finish) :=
  let r := (rangeSpan (fun u => uloc u <? n)
                      (generateRange start finish H).2).1 in
  (fmap (fun x => ups x.1) (fst r),
   fmap (fun x => ups x.1) (snd r)).

Example lt_1_5 : 1 < 5. omega. Qed.

Example testRangeSpan_1 :
  testRangeSpan 1 5 1 lt_1_5 = (None, Some [(|1|); (|2|); (|3|); (|4|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_2 :
  testRangeSpan 1 5 2 lt_1_5 = (Some [(|1|)], Some [(|2|); (|3|); (|4|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_3 :
  testRangeSpan 1 5 3 lt_1_5 = (Some [(|1|); (|2|)], Some [(|3|); (|4|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_4 :
  testRangeSpan 1 5 4 lt_1_5 = (Some [(|1|); (|2|); (|3|)], Some [(|4|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_5 :
  testRangeSpan 1 5 5 lt_1_5 = (Some [(|1|); (|2|); (|3|); (|4|)], None).
Proof. reflexivity. Qed.

End RangeTests.
