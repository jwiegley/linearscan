Require Import LinearScan.Ssr.

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

Notation "[ ::: x1 ]" := (NE_Sing x1)
  (at level 0, format "[ :::  x1 ]") : seq_scope.

Fixpoint NE_from_list {a} (x : a) (xs : seq a) : NonEmpty a :=
  match xs with
    | nil => NE_Sing x
    | cons y ys => NE_Cons x (NE_from_list y ys)
  end.

Notation "[ ::: x & s ]" := (NE_from_list x s)
  (at level 0, only parsing) : seq_scope.

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

Definition NE_foldl {a b : Type} (f : a -> b -> a) (z : a)
  (ne : NonEmpty b) : a := foldl f z ne.
Arguments NE_foldl {a b} f z ne /.

Fixpoint NE_mapAccumL {A X Y : Type} (f : A -> X -> (A * Y))
  (s : A) (v : NonEmpty X) : A * NonEmpty Y :=
  match v with
  | NE_Sing x =>
    let: (s', y) := f s x in
    (s', NE_Sing y)
  | NE_Cons x xs =>
    let: (s', y) := f s x in
    let: (s'', ys) := NE_mapAccumL f s' xs in
    (s'', NE_Cons y ys)
  end.

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
Variable R : A -> A -> Prop.
Context `{H : Transitive A R}.

Inductive NE_Forall (P : A -> Prop) : NonEmpty A -> Prop :=
 | NE_Forall_sing : forall x, P x -> NE_Forall P (NE_Sing x)
 | NE_Forall_cons : forall x l, P x -> NE_Forall P l
                      -> NE_Forall P (NE_Cons x l).

Hint Constructors NE_Forall.

Definition NE_all_true  (f : A -> bool) := NE_Forall (fun x => f x = true).
Definition NE_all_false (f : A -> bool) := NE_Forall (fun x => f x = false).

Lemma NE_Forall_head : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_head xs).
Proof. induction xs; intros; inversion H0; assumption. Qed.

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

Extract Inductive NonEmpty => "[]" ["(:[])" "(:)"]
  "(\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)".

Extract Inlined Constant NE_length  => "Prelude.length".
Extract Inlined Constant NE_to_list => "".
Extract Inlined Constant NE_head    => "Prelude.head".
Extract Inlined Constant NE_last    => "Prelude.last".
Extract Inlined Constant NE_map     => "Prelude.map".
Extract Inlined Constant NE_foldl   => "Data.List.foldl'".
