Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
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

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => cons x nil
    | NE_Cons x xs => cons x (NE_to_list xs)
  end.

Coercion NE_to_list : NonEmpty >-> list.

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

Definition NE_fold_left {a b : Type} (f : a -> b -> a) (ne : NonEmpty b) (z : a) : a :=
  fold_left f ne z.

Fixpoint NE_append {a : Type} (l1 l2 : NonEmpty a) : NonEmpty a :=
  match l1 with
    | NE_Sing x => NE_Cons x l2
    | NE_Cons x xs => NE_Cons x (NE_append xs l2)
  end.

Lemma NE_head_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_head (NE_append xs ys) = NE_head xs.
Proof. induction xs; auto. Qed.

Lemma NE_last_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_last (NE_append xs ys) = NE_last ys.
Proof. induction xs; auto. Qed.

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

Inductive NE_Forall (P : A -> Prop) : NonEmpty A -> Prop :=
 | NE_Forall_sing : forall x, P x -> NE_Forall P (NE_Sing x)
 | NE_Forall_cons : forall x l, P x -> NE_Forall P l -> NE_Forall P (NE_Cons x l).

Hint Constructors NE_Forall.

Definition NE_all_true  (f : A -> bool) := NE_Forall (fun x => f x = true).
Definition NE_all_false (f : A -> bool) := NE_Forall (fun x => f x = false).

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

Fixpoint NE_member (z : A) (ne : NonEmpty A) : Prop :=
  match ne with
    | NE_Sing x => x = z
    | NE_Cons x xs => (x = z) \/ NE_member z xs
  end.

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
