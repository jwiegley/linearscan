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

Lemma upos_lt_le_weak : forall n m : UsePos, upos_lt n m -> upos_le n m.
Proof.
  unfold upos_lt, upos_le.
  intros. apply lt_le_weak.
  assumption.
Qed.

Lemma NE_Forall_UsePos_lt_impl : forall x xs,
  NE_Forall UsePos (upos_lt x) xs
    -> upos_lt x (NE_head xs) /\ upos_lt x (NE_last xs).
Proof.
  intros. split;
  [ apply NE_Forall_head in H
  | apply NE_Forall_last in H ];
  assumption.
Qed.

Lemma NE_StronglySorted_UsePos_connected : forall l1 l2,
  NE_StronglySorted UsePos upos_lt (NE_append l1 l2)
    -> S (uloc (NE_last l1)) ≤ uloc (NE_head l2).
Proof.
  intros.
  induction l1; simpl in *;
  apply NE_StronglySorted_inv in H; inversion H;
  [ apply NE_Forall_head in H1
  | apply NE_Forall_append in H1 ];
  intuition.
Qed.

Lemma NE_StronglySorted_UsePos_impl : forall xs,
  NE_StronglySorted UsePos upos_lt xs
    -> upos_le (NE_head xs) (NE_last xs).
Proof.
  intros.
  induction xs; simpl in *.
    unfold upos_le. trivial.
  apply NE_StronglySorted_inv in H; inversion H.
  apply NE_Forall_last in H1.
  unfold upos_lt, upos_le in *. omega.
Qed.

Lemma NE_StronglySorted_UsePos_impl_app : forall l1 l2,
  NE_StronglySorted UsePos upos_lt (NE_append l1 l2)
    ->    upos_le (NE_head l1) (NE_last l1)
       /\ upos_le (NE_head l1) (NE_head l2)
       /\ upos_le (NE_head l1) (NE_last l2)
       /\ upos_le (NE_last l1) (NE_head l2)
       /\ upos_le (NE_last l1) (NE_last l2)
       /\ upos_le (NE_head l2) (NE_last l2).
Proof.
  intros.
  induction l1; simpl in *;
  apply NE_StronglySorted_inv in H; inversion H.
    pose proof H1 as H1'.
    apply NE_Forall_head in H1.
    apply NE_Forall_last in H1'.
    unfold upos_lt, upos_le in *.
    intuition.
  apply NE_StronglySorted_UsePos_impl in H2. auto.
  apply NE_Forall_append in H1; inversion H1.
  pose proof H2 as H2'.
  pose proof H2 as H2''.
  apply NE_Forall_head in H2'.
  apply NE_Forall_last in H2''.
  pose proof H3 as H3'.
  pose proof H3 as H3''.
  apply NE_Forall_head in H3'.
  apply NE_Forall_last in H3''.
  unfold upos_lt, upos_le in *.
  intuition.
Qed.

Definition UsePosSublist (l : NonEmpty UsePos) :=
  { us : NonEmpty UsePos
  | NE_StronglySorted UsePos upos_lt us
  & upos_le (NE_head l) (NE_head us)
  }.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosSublistsOf (f : UsePos -> bool) (l : NonEmpty UsePos) :=
  { p : (option (UsePosSublist l) * option (UsePosSublist l))
  | match p with
    | (Some l1, Some l2) =>
        let l1' := proj1_sigg l1 in
        let l2' := proj1_sigg l2 in
        l = NE_append l1' l2' /\ NE_all_true f l1' /\ f (NE_head l2') = false

    | (Some l1, None) =>
        let l1' := proj1_sigg l1 in l = l1' /\ NE_all_true f l1'
    | (None, Some l2) =>
        let l2' := proj1_sigg l2 in l = l2' /\ f (NE_head l2') = false

    | (None, None) => False
    end
  }.

(** Return two sublists of [l] such that for every element in the first
    sublist, [f elem] return [true]. *)
Fixpoint usePosSpan (f : UsePos -> bool) (l : NonEmpty UsePos)
  (H : NE_StronglySorted UsePos upos_lt l) : UsePosSublistsOf f l.
Proof.
  destruct l as [x|x xs] eqn:Heqe.
    destruct (f x) eqn:Heqef.
      exists (Some (exist2 _ _ (NE_Sing x) H (le_n _)), None).
      simpl. split. reflexivity.
      constructor. assumption.
    exists (None, Some (exist2 _ _ (NE_Sing x) H (le_n _))). auto.

  { destruct (f x) eqn:Heqef.
    - Case "f x = true".
      apply NE_StronglySorted_inv in H. inversion H as [H1 ?].
      destruct (usePosSpan f xs H1)
        as [[[[l1 Hsorted1 Hle1]| ] [[l2 Hsorted2 Hle2]| ]] Hsublists];
      inversion Hsublists;

      [ SCase "sublists = (Some, Some)";
        eexists (Some (exist2 _ _ (NE_Cons x l1) _ _),
                 Some (exist2 _ _ l2 _ _))
      | SCase "sublists = (Some, None)";
        eexists (Some (exist2 _ _ (NE_Cons x l1) _ _), None)
      | SCase "sublists = (None, Some)";
        eexists (Some (exist2 _ _ (NE_Sing x) _ _),
                 Some (exist2 _ _ l2 _ _)) ];
      simpl; split; f_equal; try assumption;
      intuition; constructor; assumption.

    - Case "f x = false".
      eexists (None, Some (exist2 _ _ (NE_Cons x xs) _ _)).
      split. reflexivity. assumption.
  }

  Grab Existential Variables.

  - simpl. reflexivity.
  - assumption.
  - simpl in H2. rewrite H2 in H0.
    apply NE_Forall_head in H0.
    simpl. apply upos_lt_le_weak.
    apply H0.
  - trivial.
  - simpl. reflexivity.
  - constructor; assumption.

  - simpl. reflexivity.
  - constructor. apply Hsorted1.
    simpl in H2. rewrite <- H2. apply H0.
  - apply NE_Forall_UsePos_lt_impl in H0.
    inversion H0.
    unfold upos_lt, upos_le in *.
    transitivity (uloc (NE_head xs)).
      apply lt_le_weak. assumption.
    assumption.
  - apply Hsorted2.
  - simpl. reflexivity.
  - constructor. assumption.
    simpl in H2. rewrite H2 in H0.
    apply NE_Forall_append in H0.
    inversion H0. apply H4.
Defined.

Import NonEmptyNotations.
Import UsePosNotations.

Fixpoint generateUsePosListBuilder (start index : nat)
  : { l : NonEmpty UsePos
    | NE_StronglySorted UsePos upos_lt l & NE_head l = (|start|) }.
Proof.
  destruct index.
    exists (NE_Sing (|start|)). constructor. auto.
  pose (generateUsePosListBuilder (S start) index) as u.
  destruct u as [l Hl Heq].
  exists (NE_Cons (|start|) l).
    constructor. assumption.
    destruct l; simpl in *.
      constructor; unfold upos_lt.
      rewrite Heq; apply lt_n_Sn.
    constructor.
      rewrite Heq; apply lt_n_Sn.
    inversion Hl. rewrite Heq in H2.
    apply (NE_Forall_impl _ _ (upos_lt (|S start|))).
      intros. unfold upos_lt in *.
      simpl in *. apply Nat.lt_succ_l.
      assumption.
    assumption.
  constructor.
Defined.

Definition generateUsePosList (start finish : nat) (H : start < finish)
  : { l : NonEmpty UsePos | NE_StronglySorted UsePos upos_lt l }.
Proof.
  pose (generateUsePosListBuilder start (finish - start - 1)).
  destruct s. exists x. apply n.
Defined.

Example lt_1_2 : 1 < 2. omega. Qed.
Example lt_1_3 : 1 < 3. omega. Qed.
Example lt_1_4 : 1 < 4. omega. Qed.
Example lt_1_5 : 1 < 5. omega. Qed.

(* Compute generateUsePosList 1 5 lt_1_5. *)

(* Compute usePosSpan (fun u => uloc u <? 1) *)
(*                    (generateUsePosList 1 5 lt_1_5).1 *)
(*                    (generateUsePosList 1 5 lt_1_5).2. *)
(* Compute usePosSpan (fun u => uloc u <? 2) *)
(*                    (generateUsePosList 1 5 lt_1_5).1 *)
(*                    (generateUsePosList 1 5 lt_1_5).2. *)
(* Compute usePosSpan (fun u => uloc u <? 3) *)
(*                    (generateUsePosList 1 5 lt_1_5).1 *)
(*                    (generateUsePosList 1 5 lt_1_5).2. *)
(* Compute usePosSpan (fun u => uloc u <? 4) *)
(*                    (generateUsePosList 1 5 lt_1_5).1 *)
(*                    (generateUsePosList 1 5 lt_1_5).2. *)
(* Compute usePosSpan (fun u => uloc u <? 5) *)
(*                    (generateUsePosList 1 5 lt_1_5).1 *)
(*                    (generateUsePosList 1 5 lt_1_5).2. *)

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosDefiniteSublistsOf (l : NonEmpty UsePos) :=
  { p : (UsePosSublist l * UsePosSublist l)
  | l = NE_append (proj1_sigg (fst p)) (proj1_sigg (snd p))
  }.

Definition usePosSplit (f : UsePos -> bool)
  (l : NonEmpty UsePos) (Hlen : NE_length l > 1)
  (Hfirst_true : f (NE_head l) = true)
  (Hlast_false : f (NE_last l) = false)
  (Hsorted : NE_StronglySorted UsePos upos_lt l)
  : UsePosDefiniteSublistsOf l.
Proof.
  pose (usePosSpan f l Hsorted). destruct u.
  unfold UsePosDefiniteSublistsOf.
  induction l; simpl in *. intuition.
  destruct x.

  destruct o; destruct o0; intuition.
  - Case "(Some, Some)".
    exists (u, u0). assumption.

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
    ups  : NonEmpty UsePos;

    ups_head : rbeg <= uloc (NE_head ups);
    ups_last : uloc (NE_last ups) < rend;
    ups_sorted : NE_StronglySorted UsePos upos_lt ups;

    range_nonempty : rbeg < rend         (* this comes in handy *)
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

           ; ups_head   := le_n (uloc u)
           ; ups_last   := lt_n_Sn (uloc u)
           ; ups_sorted := NE_SSorted_sing _ _ u

           ; range_nonempty := le_n (S (uloc u))
           |}

  (** A [Range] can be extended by adding a use position to the beginning.
      This means that they must be built up in reverse. *)
  | R_Cons u x : Range x -> forall (H : uloc u < rbeg x),
    Range {| rbeg := uloc u
           ; rend := rend x
           ; ups  := NE_Cons u (ups x)

           ; ups_head   := le_n (uloc u)
           ; ups_last   := ups_last x
           ; ups_sorted := NE_StronglySorted_cons _ _ _ _
               (lt_le_trans _ _ _ H (ups_head x)) (ups_sorted x)

           ; range_nonempty := Lt.lt_trans _ _ _ H (range_nonempty x)
           |}

  (** The address bounds of a [Range] may be arbitrarily extended, without
      reference to use positions.  This is useful when all of the use
      positions occur in a loop, for example, and you wish for the [Range] to
      bound the entire loop. *)
  | R_Extend x b' e' : Range x ->
    Range {| rbeg := min b' (rbeg x)
           ; rend := Peano.max e' (rend x)
           ; ups  := ups x

           ; ups_head   := le_min _ _ _ (ups_head x)
           ; ups_last   := lt_max _ _ _ (ups_last x)
           ; ups_sorted := ups_sorted x

           ; range_nonempty := min_lt_max _ _ _ _ (range_nonempty x)
           |}

  (** A [Range] can be bootstrapped by providing a properly sorted list of use
      positions, and all of its details, so long as the laws are fulfilled
      upon doing so. *)
  | R_FromList b e us :
    forall ups_head' : b <= uloc (NE_head us),
    forall ups_last' : uloc (NE_last us) < e,
    forall ups_sorted' : NE_StronglySorted UsePos upos_lt us,
    forall range_nonempty' : b < e,
    Range {| rbeg := b
           ; rend := e
           ; ups  := us

           ; ups_head   := ups_head'
           ; ups_last   := ups_last'
           ; ups_sorted := ups_sorted'

           ; range_nonempty := range_nonempty'
           |}.

Tactic Notation "Range_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_Sing"
  | Case_aux c "R_Cons"
  | Case_aux c "R_Extend"
  | Case_aux c "R_FromList"
  ].

Definition getRangeDesc `(r : Range d) := d.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition rangeExtent `(Range r) := rend r - rbeg r.

Definition Range_append `(l : Range ld) `(r : Range rd)
  (H : rend ld <= rbeg rd) : RangeDesc :=
  {| rbeg := rbeg ld
   ; rend := rend rd
   ; ups  := NE_append (ups ld) (ups rd)

   ; ups_head   := eq_ind_r (fun u => rbeg ld ≤ uloc u)
                            (ups_head ld) NE_head_append_spec
   ; ups_last   := eq_ind_r (fun u => uloc u < rend rd)
                            (ups_last rd) NE_last_append_spec
   ; ups_sorted := NE_StronglySorted_append _ _
        (lt_le_trans _ _ _ (ups_last ld) (le_trans _ _ _ H (ups_head rd)))
        (ups_sorted ld) (ups_sorted rd)

   ; range_nonempty :=
       lt_le_shuffle (range_nonempty ld) H (range_nonempty rd)
   |}.

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

Definition SubRange `(r : Range rd) :=
  { rd' : RangeDesc | Range rd'
  & rbeg rd <= rbeg rd' /\ rend rd' <= rend rd
  }.

Definition SubRangeEvidence `(r : Range rd)
  (p : (option (SubRange r) * option (SubRange r))) :=
  match p with
  | (Some r1, Some r2) => rend (proj1_sigg r1) <= rbeg (proj1_sigg r2)
  | (Some _, None)     => True
  | (None, Some _)     => True
  | (None, None)       => False
  end.

Definition SubRangesOfEvidence (f : UsePos -> bool) `(r : Range rd)
  (ev : { p : (option (SubRange r) * option (SubRange r))
          | SubRangeEvidence r p }) :=
  match ev with
  | (exist (Some r1, Some r2) H) =>
      let r1' := proj2_sigg r1 in
      let r2' := proj2_sigg r2 in
      rd = Range_append r1' r2' H
        /\ NE_all_true f (ups r1') /\ f (NE_head (ups r2')) = false

  | (exist (Some r1, None) _) =>
      let rd1' := proj1_sigg r1 in
      rd = rd1' /\ NE_all_true f (ups rd1')
  | (exist (None, Some r2) _) =>
      let rd2' := proj1_sigg r2 in
      rd = rd2' /\ f (NE_head (ups rd2')) = false

  | (exist (None, None) _) => False
  end.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition SubRangesOf (f : UsePos -> bool) `(r : Range rd) :=
  { ev : { p : (option (SubRange r) * option (SubRange r))
         | SubRangeEvidence r p }
  | SubRangesOfEvidence f r ev }.

Definition rangeSpan (f : UsePos -> bool) `(r : Range rd) : SubRangesOf f r.
Proof.
  destruct rd.
  pose (usePosSpan f ups0 ups_sorted0) as u.

  { destruct u
      as [[[[l1 Hsorted1 Hle1]| ] [[l2 Hsorted2 Hle2]| ]] Hu] eqn:Heqe;
    remember {| rbeg           := rbeg0
              ; rend           := rend0
              ; ups            := ups0
              ; ups_head       := ups_head0
              ; ups_last       := ups_last0
              ; ups_sorted     := ups_sorted0
              ; range_nonempty := range_nonempty0
              |} as rd.

    - Case "sublists = (Some, Some)".
      inversion Hu; simpl in *.
      clear Heqe. subst.
      pose proof ups_sorted0 as ups_sorted0'.
      pose proof ups_head0 as ups_head0'.
      pose proof ups_last0 as ups_last0'.
      apply NE_StronglySorted_UsePos_impl_app in ups_sorted0'.
      rewrite NE_head_append_spec in ups_head0'.
      rewrite NE_last_append_spec in ups_last0'.
      rewrite NE_head_append_spec in Hle1.
      rewrite NE_head_append_spec in Hle2.
      intuition.

      eexists (exist _
        (Some (exist2 _ _
           {| rbeg := rbeg0
            ; rend := S (uloc (NE_last l1))
            ; ups  := l1

            ; range_nonempty :=
                le_lt_trans _ _ _ ups_head0' (le_lt_n_Sm _ _ H3)
            |} _ _),
         Some (exist2 _ _
           {| rbeg := uloc (NE_head l2)
            ; rend := rend0
            ; ups  := l2

            ; range_nonempty := le_lt_trans _ _ _ H10 ups_last0'
            |} _ _)) _).
      simpl. intuition.
      unfold Range_append.
      f_equal; apply proof_irrelevance.

    - Case "sublists = (Some, None)".
      eexists (exist _ (Some (exist2 _ _ rd _ _), None) _).
      simpl. split. reflexivity.
      rewrite Heqrd. inversion Hu.
      rewrite <- H in H0. assumption.

    - Case "sublists = (None, Some)".
      eexists (exist _ (None, Some (exist2 _ _ rd _ _)) _).
      simpl. split. reflexivity.
      rewrite Heqrd. inversion Hu.
      rewrite <- H in H0. assumption.

    - exfalso. assumption.
  }

  Grab Existential Variables.

  - simpl. reflexivity.
  - destruct rd. simpl. inversion Heqrd. easy.
  - trivial.

  - simpl. reflexivity.
  - destruct rd. simpl. inversion Heqrd. easy.
  - trivial.

  (* These proofs all relate to the (Some, Some) existentials. *)
  - apply NE_StronglySorted_UsePos_connected. auto.

  - simpl. split.
    transitivity (uloc (NE_head l1)); assumption.
    reflexivity.
  - constructor.
  - assumption.
  - trivial.
  - trivial.

  - simpl. split. reflexivity.
    unfold upos_le in *. intuition.
  - constructor.
  - assumption.
  - apply lt_n_Sn.
  - assumption.
Defined.

Fixpoint generateRangeBuilder (start index : nat)
  : { rd : RangeDesc | Range rd & rbeg rd = start }.
Proof.
  destruct index.
    pose (R_Sing (|start|)).
    exists (getRangeDesc r). apply r. auto.
  pose (generateRangeBuilder (S start) index) as r.
  destruct r as [rd r Hr].
  assert (start < rbeg rd) as Hlt.
    rewrite Hr. apply lt_n_Sn.
  pose (R_Cons (|start|) rd r Hlt) as r'.
  exists (getRangeDesc r'). apply r'. auto.
Defined.

Definition generateRange (start finish : nat) (H : start < finish)
  : { rd : RangeDesc | Range rd }.
Proof.
  pose (generateRangeBuilder start (finish - start - 1)).
  destruct s. exists x. apply r.
Defined.

(* Compute R_Sing (|1|). *)

(* Compute rangeSpan (fun u => uloc u <? 2) (R_Sing (|1|)). *)
(* Compute rangeSpan (fun u => uloc u <? 2) (R_Sing (|2|)). *)

(* Compute generateRange 1 2 lt_1_2. *)

(* Compute rangeSpan (fun u => uloc u <? 2) (generateRange 1 2 lt_1_2).2. *)
(* Compute rangeSpan (fun u => uloc u <? 2) (generateRange 1 2 lt_1_2).2. *)

(* Compute generateRange 1 3 lt_1_3. *)

Definition testRangeSpan (start finish n : nat) (H : start < finish) :=
  (fun r => (fmap (fun x => ups (proj1_sigg x)) (fst r),
             fmap (fun x => ups (proj1_sigg x)) (snd r)))
  (rangeSpan (fun u => uloc u <? n)
             (generateRange start finish H).2).1.1.

Example testRangeSpan_1 :
  testRangeSpan 1 4 1 lt_1_4 = (None, Some (NE_Cons (|1|) [(|2|); (|3|)])).
Proof. reflexivity. Qed.

(*
Example testRangeSpan_2 :
  testRangeSpan 1 4 2 lt_1_4 = (Some [(|1|)], Some [(|2|); (|3|)]).
Proof. unfold testRangeSpan. simpl. Qed.

Example testRangeSpan_3 :
  testRangeSpan 1 4 3 lt_1_4 = (Some [(|1|); (|2|)], Some [(|3|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_4 :
  testRangeSpan 1 4 4 lt_1_4 = (Some (NE_Cons (|1|) [(|2|); (|3|)]), None).
Proof. reflexivity. Qed.
*)

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition DefiniteSubRangesOf `(r : Range rd) :=
  { ev : { p : (SubRange r * SubRange r)
         | rend (proj1_sigg (fst p)) <= rbeg (proj1_sigg (snd p))
         }
  | match ev with
    | exist (r1, r2) H =>
        rd = Range_append (proj2_sigg r1) (proj2_sigg r2) H
    end
  }.

Definition splitRange (f : UsePos -> bool) `(r : Range rd)
  (Hfirst_true : f (NE_head (ups rd)) = true)
  (Hlast_false : f (NE_last (ups rd)) = false)
  : DefiniteSubRangesOf r.
Proof.
  destruct rd. simpl in *.
  pose (rangeSpan f r) as s. destruct s.
  unfold DefiniteSubRangesOf.
  destruct x. destruct x.
  destruct o; destruct o0; intuition; destruct s.
  - Case "(Some, Some)".
    eexists (exist _ (s1, s2) _). apply H.

  - Case "(Some, None)". exfalso. intuition.
    rewrite <- H in *. simpl in H0.
    apply NE_Forall_last in H0.
    apply (eq_true_false_abs (f (NE_last ups0))); assumption.

  - Case "(None, Some)". exfalso. intuition.
    rewrite <- H in *. simpl in H0.
    apply (eq_true_false_abs (f (NE_head ups0))); assumption.
Defined.
