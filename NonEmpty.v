Require Import Coq.Classes.RelationClasses.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Relations.Relations.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** NonEmpty lists *)

Inductive NonEmpty (a : Type) : Type :=
  | NE_Sing : a -> NonEmpty a
  | NE_Cons : a -> NonEmpty a -> NonEmpty a.

Arguments NE_Sing [_] _.
Arguments NE_Cons [_] _ _.

Fixpoint NE_length {a} (ne : NonEmpty a) : nat :=
  match ne with
    | NE_Sing x => 1
    | NE_Cons x xs => 1 + NE_length xs
  end.

Lemma NE_length_spec {a} (ne : NonEmpty a) : NE_length ne > 0.
Proof. induction ne; simpl; auto. Qed.

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => cons x nil
    | NE_Cons x xs => cons x (NE_to_list xs)
  end.

Definition destruct_NonEmpty {a} (l : NonEmpty a) :
  ({x : a & {tl : NonEmpty a | l = NE_Cons x tl}} +
     {x : a | l = NE_Sing x})%type.
Proof.
  destruct l.
    right. exists a0. reflexivity.
  left. exists a0. exists l. reflexivity.
Defined.

Definition NE_head {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x _ => x
  end.

Fixpoint NE_last {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x xs => NE_last xs
  end.

Fixpoint NE_map {a b : Type} (f : a -> b) (ne : NonEmpty a) : NonEmpty b :=
  match ne with
    | NE_Sing x => NE_Sing (f x)
    | NE_Cons x xs => NE_Cons (f x) (NE_map f xs)
  end.

Lemma NE_map_head_spec : forall {a b : Type} (f : a -> b) (xs : NonEmpty a),
  NE_head (NE_map f xs) = f (NE_head xs).
Proof. induction xs; auto. Qed.

Lemma NE_map_last_spec : forall {a b : Type} (f : a -> b) (xs : NonEmpty a),
  NE_last (NE_map f xs) = f (NE_last xs).
Proof. induction xs; auto. Qed.

Fixpoint NE_fold_left {a b : Type} (f : a -> b -> a) (ne : NonEmpty b) (z : a) : a :=
  match ne with
    | NE_Sing x => f z x
    | NE_Cons x xs => NE_fold_left f xs (f z x)
  end.

Fixpoint NE_append {a : Type} (l1 l2 : NonEmpty a) : NonEmpty a :=
  match l1 with
    | NE_Sing x => NE_Cons x l2
    | NE_Cons x xs => NE_Cons x (NE_append xs l2)
  end.

Lemma NE_append_spec : forall {a : Type} {x} {xs ys : NonEmpty a},
  NE_Sing x = NE_append xs ys -> False.
Proof. intros. induction xs; destruct ys; simpl in *; inversion H. Qed.

Lemma NE_append_sing : forall {a : Type} {x} {l1 l2 : NonEmpty a},
  NE_Sing x = NE_append l1 l2 -> False.
Proof. intros. induction l1; simpl in H; inversion H. Qed.

Lemma NE_map_append_spec : forall {a b : Type} (f : a -> b) {xs ys : NonEmpty a},
  NE_map f (NE_append xs ys) = NE_append (NE_map f xs) (NE_map f ys).
Proof.
  induction xs; intros; simpl; auto.
  f_equal. apply IHxs.
Qed.

Lemma NE_head_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_head (NE_append xs ys) = NE_head xs.
Proof. induction xs; auto. Qed.

Lemma NE_last_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_last (NE_append xs ys) = NE_last ys.
Proof. induction xs; auto. Qed.

Fixpoint NE_reverse {a} (ne : NonEmpty a) : NonEmpty a :=
  match ne with
    | NE_Sing x => NE_Sing x
    | NE_Cons x xs => NE_append (NE_reverse xs) (NE_Sing x)
  end.

Lemma NE_append_assoc : forall {a} (x y z : NonEmpty a),
  NE_append x (NE_append y z) = NE_append (NE_append x y) z.
Proof.
  induction x; intros; simpl.
    reflexivity.
  f_equal. apply IHx.
Qed.

Lemma NE_distr_reverse : forall {a} (x y : NonEmpty a),
  NE_reverse (NE_append x y) = NE_append (NE_reverse y) (NE_reverse x).
Proof.
  intros.
  induction x; simpl. reflexivity.
  rewrite IHx. rewrite NE_append_assoc.
  reflexivity.
Qed.

Remark NE_reverse_sing_unit : forall {a} (l : NonEmpty a) (x : a),
  NE_reverse (NE_Sing x) = NE_Sing x.
Proof. auto. Qed.

Remark NE_reverse_unit : forall {a} (l : NonEmpty a) (x : a),
  NE_reverse (NE_append l (NE_Sing x)) = NE_append (NE_Sing x) (NE_reverse l).
Proof. intros. rewrite NE_distr_reverse. reflexivity. Qed.

Lemma NE_reverse_involutive : forall {a} (l : NonEmpty a),
  NE_reverse (NE_reverse l) = l.
Proof.
  induction l; auto.
  simpl. rewrite NE_distr_reverse.
  rewrite IHl. reflexivity.
Qed.

Lemma NE_length_plus_1 : forall {a} x (xs : NonEmpty a),
  NE_length (NE_append xs (NE_Sing x)) = S (NE_length xs).
Proof. induction xs; simpl; auto. Qed.

Lemma NE_length_1_plus : forall {a} x (xs : NonEmpty a),
  NE_length (NE_append (NE_Sing x) xs) = S (NE_length xs).
Proof. induction xs; simpl; auto. Qed.

Lemma NE_reverse_length : forall {a} (l : NonEmpty a),
  NE_length (NE_reverse l) = NE_length l.
Proof.
  induction l; auto. simpl.
  rewrite NE_length_plus_1. auto.
Qed.

Section Reverse_Induction.

Variable A : Type.

Unset Implicit Arguments.

Lemma NE_reverse_list_ind : forall P : NonEmpty A -> Prop,
  (forall (a : A), P (NE_reverse (NE_Sing a)))
    -> (forall (a : A) (l : NonEmpty A), P (NE_reverse l)
          -> P (NE_reverse (NE_Cons a l)))
    -> forall l : NonEmpty A, P (NE_reverse l).
Proof.
  induction l; auto.
Qed.

Set Implicit Arguments.

Theorem NE_reverse_ind : forall P : NonEmpty A -> Prop,
  (forall (x : A), P (NE_Sing x))
    -> (forall (x : A) (l : NonEmpty A), P l -> P (NE_append l (NE_Sing x)))
    -> forall l : NonEmpty A, P l.
Proof.
  intros.
  generalize (NE_reverse_involutive l).
  intros E; rewrite <- E.
  apply (NE_reverse_list_ind P).
  auto.

  simpl in |- *.
  intros.
  apply (H0 a (NE_reverse l0)).
  auto.
Qed.

End Reverse_Induction.

Fixpoint NE_span {a : Type} (f : a -> bool) (l : NonEmpty a) :
  (option (NonEmpty a) * option (NonEmpty a)) :=
  let maybeAppend (x : a) (xs : option (NonEmpty a)) :=
      match xs with
        | Some xs' => Some (NE_Cons x xs')
        | None     => Some (NE_Sing x)
      end in
  match l with
    | NE_Sing x =>
        if f x
        then (Some l, None)
        else (None, Some l)
    | NE_Cons x xs =>
        let (xl, xr) := NE_span f xs in
        if f x
        then (maybeAppend x xl, xr)
        else (xl, maybeAppend x xr)
  end.

Lemma NE_span_spec : forall a (l : NonEmpty a),
  let (xs,ys) := NE_span (fun _ => true) l in
  match xs with
    | Some xs' => match ys with
        | Some ys' => l = NE_append xs' ys'
        | None => l = xs'
      end
    | None => match ys with
        | Some ys' => l = ys'
        | None => False
      end
  end.
Proof.
  intros.
  induction l; simpl in *.
    reflexivity.
  destruct (NE_span _ l);
  destruct o; destruct o0; simpl;
  try (f_equal; apply IHl).
  contradiction.
Qed.

Section Sorted.

Variable A : Set.
Variable R : relation A.
Context `{H : Transitive A R}.

Fixpoint NE_In (a : A) (l : NonEmpty A) : Prop :=
  match l with
    | NE_Sing b => b = a
    | NE_Cons b m => b = a \/ NE_In a m
  end.

Inductive NE_Exists (P : A -> Prop) : NonEmpty A -> Prop :=
 | NE_Exists_sing    : forall x,   P x -> NE_Exists P (NE_Sing x)
 | NE_Exists_cons_hd : forall x l, P x -> NE_Exists P (NE_Cons x l)
 | NE_Exists_cons_tl : forall x l, NE_Exists P l -> NE_Exists P (NE_Cons x l).

Hint Constructors NE_Exists.

Lemma NE_Exists_exists : forall P (l : NonEmpty A),
  NE_Exists P l <-> (exists x, NE_In x l /\ P x).
Proof.
  split. induction 1; firstorder.
  induction l; firstorder;
  inversion H0; subst;
  constructor; assumption.
Qed.

Lemma NE_Exists_cons : forall (P : A -> Prop) x l,
  NE_Exists P (NE_Cons x l) <-> P x \/ NE_Exists P l.
Proof. split; inversion 1; auto. Qed.

Inductive NE_Forall (P : A -> Prop) : NonEmpty A -> Prop :=
 | NE_Forall_sing : forall x, P x -> NE_Forall P (NE_Sing x)
 | NE_Forall_cons : forall x l, P x -> NE_Forall P l -> NE_Forall P (NE_Cons x l).

Hint Constructors NE_Forall.

Definition NE_all_true  (f : A -> bool) := NE_Forall (fun x => f x = true).
Definition NE_all_false (f : A -> bool) := NE_Forall (fun x => f x = false).

Lemma NE_Forall_forall : forall P (l : NonEmpty A),
  NE_Forall P l <-> (forall x, NE_In x l -> P x).
Proof.
  split.
    induction 1; firstorder;
    inversion H1; subst; auto.
  intros. induction l.
    constructor. apply H0. constructor.
  constructor. apply H0. constructor.
    reflexivity.
  apply IHl. intros.
  apply H0. right. apply H1.
Qed.

Lemma NE_Forall_inv : forall P (a : A) l, NE_Forall P (NE_Cons a l) -> P a.
Proof. intros; inversion H0; trivial. Qed.

Lemma NE_Forall_rect : forall (P : A -> Prop) (Q : NonEmpty A -> Type),
  (forall b, P b -> Q (NE_Sing b))
    -> (forall b l, P b -> Q (NE_Cons b l)) -> forall l, NE_Forall P l -> Q l.
Proof.
  intros P Q H1 H2; induction l; intro;
  [|eapply H2, NE_Forall_inv].
    apply H1. inversion H0. assumption.
    apply H0.
Qed.

Lemma NE_Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
  forall l, NE_Forall P l -> NE_Forall Q l.
Proof.
  intros P Q Himp l H1.
  induction H1; firstorder.
Qed.

Lemma NE_Forall_head : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_head xs).
Proof. induction xs; intros; inversion H0; assumption. Qed.

Lemma NE_Forall_last : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_last xs).
Proof.
  intros. induction xs; simpl in *.
    inversion H0. assumption.
  apply IHxs. inversion H0. assumption.
Qed.

Lemma NE_Forall_append : forall (P : A -> Prop) xs ys,
   NE_Forall P xs /\ NE_Forall P ys <-> NE_Forall P (NE_append xs ys).
Proof.
  split; induction xs; intros; simpl;
  constructor; intuition;
  try inversion H1; auto;
  try inversion H0; auto;
  try constructor; auto.
  apply IHxs. assumption.
  intuition.
Qed.

Section Membership.

Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

Fixpoint NE_member (z : A) (ne : NonEmpty A) : Prop :=
  match ne with
    | NE_Sing x => x = z
    | NE_Cons x xs => (x = z) \/ NE_member z xs
  end.

Lemma NE_member_head (ne : NonEmpty A) : NE_member (NE_head ne) ne.
Proof. induction ne; simpl; auto. Qed.

Lemma NE_member_append_fst (z : A) (xs ys : NonEmpty A) :
  NE_member z xs -> NE_member z (NE_append xs ys).
Proof.
  induction xs; simpl; auto.
  destruct (eq_dec a z).
    left. assumption.
  right.
  inversion H0.
    contradiction.
  apply IHxs.
  assumption.
Qed.

Lemma NE_member_append_snd (z : A) (xs ys : NonEmpty A) :
  NE_member z ys -> NE_member z (NE_append xs ys).
Proof. induction xs; simpl; auto. Qed.

Lemma NE_Forall_member_spec (z : A) (ne : NonEmpty A) :
  forall f, NE_Forall f ne -> NE_member z ne -> f z.
Proof.
  induction ne; simpl; intros.
    inversion H0. subst. assumption.
  inversion H1.
    inversion H0. subst. assumption.
  apply IHne.
    inversion H0. assumption.
  assumption.
Qed.

End Membership.

Inductive NE_StronglySorted : NonEmpty A -> Prop :=
  | NE_SSorted_sing a   : NE_StronglySorted (NE_Sing a)
  | NE_SSorted_cons a l : NE_StronglySorted l -> NE_Forall (R a) l
                            -> NE_StronglySorted (NE_Cons a l).

Lemma NE_StronglySorted_inv : forall a l,
  NE_StronglySorted (NE_Cons a l)
    -> NE_StronglySorted l /\ NE_Forall (R a) l.
Proof. intros; inversion H0; auto. Qed.

Lemma NE_StronglySorted_inv_app : forall (l1 l2 : NonEmpty A),
  NE_StronglySorted (NE_append l1 l2)
    -> NE_StronglySorted l1 /\ NE_StronglySorted l2.
Proof.
  induction l1; intros; simpl; inversion H0.
    split; [ constructor | assumption ].
  specialize (IHl1 l2 H3).
  inversion IHl1.
  split.
    constructor. assumption.
    apply NE_Forall_append in H4. intuition.
  assumption.
Qed.

Lemma NE_StronglySorted_rect :
  forall P : NonEmpty A -> Type,
    (forall a, P (NE_Sing a)) ->
    (forall a l, NE_StronglySorted l -> P l -> NE_Forall (R a) l
                   -> P (NE_Cons a l)) ->
    forall l, NE_StronglySorted l -> P l.
Proof.
  induction l; firstorder using NE_StronglySorted_inv.
Qed.

Lemma NE_StronglySorted_rec :
  forall P : NonEmpty A -> Type,
    (forall a, P (NE_Sing a)) ->
    (forall a l, NE_StronglySorted l -> P l -> NE_Forall (R a) l
                   -> P (NE_Cons a l)) ->
   forall l, NE_StronglySorted l -> P l.
Proof.
  firstorder using NE_StronglySorted_rect.
Qed.

Lemma NE_StronglySorted_Sorted : forall l,
  NE_StronglySorted l -> Sorted R (NE_to_list l).
Proof.
  induction 1 as [|? ? ? ? HForall]; constructor; trivial.
  destruct HForall; constructor; trivial.
Qed.

Lemma NE_StronglySorted_cons : forall x (xs : NonEmpty A),
  R x (NE_head xs) -> NE_StronglySorted xs -> NE_StronglySorted (NE_Cons x xs).
Proof.
  intros.
  induction xs; simpl in *;
  repeat (constructor; try assumption).
  apply NE_StronglySorted_inv in H1. inversion H1.
  apply NE_Forall_impl with (P := (R a)) (Q := (R x));
    try transitivity a; assumption.
Qed.

Lemma NE_StronglySorted_cons_middle : forall x xs ys,
  NE_StronglySorted (NE_append xs (NE_Cons x ys))
    -> NE_StronglySorted (NE_append xs ys).
Proof.
  induction xs; intros; simpl in *;
  apply NE_StronglySorted_inv in H0; inversion H0.
    constructor;
    inversion H1; inversion H2; assumption.
  constructor. apply IHxs.
    inversion H0. assumption.
  apply NE_Forall_append in H2.
  apply NE_Forall_append. intuition.
  inversion H5. assumption.
Qed.

Lemma NE_Forall_Sorted : forall x xs ys,
  R (NE_last xs) (NE_head ys)
    -> NE_Forall (R x) xs
    -> NE_StronglySorted (NE_append xs ys)
    -> NE_Forall (R x) ys.
Proof.
  intros.
  induction ys; simpl in *;
  try (constructor;
       pose proof H1;
       apply NE_Forall_last in H1;
       try transitivity (NE_last xs); try assumption).
  apply IHys.
    apply NE_StronglySorted_inv_app in H2.
    inversion H2. intuition. clear H4 H5.
    inversion H7; subst.
    apply NE_Forall_head in H8.
    transitivity a; try assumption.
  apply NE_StronglySorted_cons_middle with (x := a).
  assumption.
Qed.

Fixpoint NE_StronglySorted_append {xs ys : NonEmpty A} :
  R (NE_last xs) (NE_head ys)
    -> NE_StronglySorted xs
    -> NE_StronglySorted ys
    -> NE_StronglySorted (NE_append xs ys).
Proof.
  intros.
  induction xs; simpl in *.
    constructor. assumption.
    destruct ys; simpl in *.
      constructor. assumption.
    constructor. assumption.
    apply NE_StronglySorted_inv in H2.
    inversion H2.
    apply NE_Forall_impl
      with (P := R a0)
           (Q := R a).
      intros. transitivity a0; assumption.
    assumption.
  apply NE_StronglySorted_inv in H1.
  inversion H1. intuition.
  constructor. assumption.
  apply NE_Forall_append.
  intuition.
  apply NE_Forall_Sorted with (xs := xs); assumption.
Qed.

Lemma NE_StronglySorted_impl `{Reflexive _ R} : forall xs,
  NE_StronglySorted xs -> R (NE_head xs) (NE_last xs).
Proof.
  intros.
  induction xs; simpl in *. reflexivity.
  apply NE_StronglySorted_inv in H1; inversion H1.
  apply NE_Forall_last in H3.
  assumption.
Qed.

Lemma NE_StronglySorted_impl_app : forall (l1 l2 : NonEmpty A),
  NE_StronglySorted (NE_append l1 l2)
    -> R (NE_last l1) (NE_head l2).
Proof.
  intros.
  induction l1; simpl in *.
    inversion H0; subst.
    apply NE_Forall_head in H4.
    assumption.
  apply IHl1.
  inversion H0.
  assumption.
Qed.

End Sorted.

Arguments NE_all_true  [A] f _.
Arguments NE_all_false [A] f _.

Module NonEmptyNotations.

Notation " [ x ] " := (NE_Sing x) : list_scope.
Notation " [ x ; y ] " := (NE_Cons x (NE_Sing y)) : list_scope.
Notation " [ x ; y ; z ] " := (NE_Cons x (NE_Cons y (NE_Sing z))) : list_scope.
Notation " [ x ; y ; z ; w ] " :=
  (NE_Cons x (NE_Cons y (NE_Cons z (NE_Sing w)))) : list_scope.
Notation " [ x ; y ; z ; w ; v ] " :=
  (NE_Cons x (NE_Cons y (NE_Cons z (NE_Cons w (NE_Sing v))))) : list_scope.

Infix "++" := NE_append.

End NonEmptyNotations.
