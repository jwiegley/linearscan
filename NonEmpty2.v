Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrfun.
Require Import Ssreflect.ssrbool.
Require Import Ssreflect.eqtype.
Require Import Ssreflect.seq.
Require Import Ssreflect.ssrnat.
Require Import Ssreflect.fintype.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** NonEmpty lists *)

Definition NonEmpty a := (a * seq a)%type.

Notation "[ ::: x1 ]" := (x1, nil)
  (at level 0, format "[ :::  x1 ]") : seq_scope.

Notation "[ ::: x & s ]" := (x, s)
  (at level 0, only parsing) : seq_scope.

Definition NE_to_list {a} (ne : NonEmpty a) : list a :=
  let: (x, xs) := ne in x :: xs.

Coercion NE_to_list : NonEmpty >-> list.

Definition NE_from_list {a} (l : seq a) : 0 < size l -> NonEmpty a.
Proof. move=> H; constructor; case: l => // [|x xs] in H *. Defined.

Arguments NE_from_list [a] l _.

Definition ne_rect : forall a (P : NonEmpty a -> Type),
  (forall x : a, P [::: x])
    -> (forall (x : a) (l : NonEmpty a), P l -> P [::: x & NE_to_list l])
    -> forall l : NonEmpty a, P l.
Proof.
  move=> a P H1 H2; case=> [x xs].
  elim: xs => [|y ys IHys] in x *.
    exact: H1.
  exact/(H2 x (y, ys))/IHys.
Defined.

Definition ne_rec : forall a (P : NonEmpty a -> Set),
  (forall x : a, P [::: x])
    -> (forall (x : a) (l : NonEmpty a), P l -> P [::: x & NE_to_list l])
    -> forall l : NonEmpty a, P l := [eta ne_rect].

Definition ne_ind : forall a (P : NonEmpty a -> Prop),
  (forall x : a, P [::: x])
    -> (forall (x : a) (l : NonEmpty a), P l -> P [::: x & NE_to_list l])
    -> forall l : NonEmpty a, P l := [eta ne_rect].

Definition NE_length {a} (ne : NonEmpty a) : nat := (size ne).+1.
Arguments NE_length [a] ne /.

Definition NE_head {a} (ne : NonEmpty a) := let: (x, _) := ne in x.
Arguments NE_head [a] ne /.

Definition NE_last {a} (ne : NonEmpty a) := let: (x, xs) := ne in last x xs.
Arguments NE_last [a] ne /.

Lemma last_ne : forall a x (xs : NonEmpty a), NE_last xs = last x xs.
Proof. by move=> a x; case=> [y ys]. Qed.

Definition NE_map {a b : Type} (f : a -> b) (ne : NonEmpty a) : NonEmpty b :=
  let: (x, xs) := ne in (f x, map f xs).
Arguments NE_map [a b] f ne /.

Definition NE_fold_left {a b} (f : a -> b -> a) (ne : NonEmpty b) (z : a) :=
  foldl f z ne.
Arguments NE_fold_left [a b] f ne z /.

Definition NE_append {a : Type} (l1 l2 : NonEmpty a) : NonEmpty a :=
  let: (x1, xs1) := l1 in
  let: (x2, xs2) := l2 in (x1, xs1 ++ x2 :: xs2).
Arguments NE_append [a] l1 l2 /.

Lemma NE_head_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_head (NE_append xs ys) = NE_head xs.
Proof. move=> a; case=> x; case=> /= [|z zs] ys; by case: ys. Qed.

Lemma NE_last_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_last (NE_append xs ys) = NE_last ys.
Proof.
  move=> a; case=> x.
  case=> /= [|z zs] ys.
    by case: ys.
  case: ys => [w ws] /=.
  by rewrite last_cat.
Qed.

Section Sorted.

Variable A : eqType.
Variable R : A -> A -> bool.

Definition NE_Forall (P : A -> bool) (ne : NonEmpty A) : bool :=
  let: (x, xs) := ne in P x && all P xs.
Arguments NE_Forall P ne /.

Lemma NE_Forall_head : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_head xs).
Proof. by move=> P; case=> [x xs] /= /andP [H1 _]. Defined.

Lemma NE_Forall_last : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_last xs).
Proof.
  move=> P; case=> [x l] /= /andP [H1 H2].
  move: H2 => /allP /(_ (last x l)) /=.
  case: l => //= => [y ys] => H2.
  exact/H2/mem_last.
Defined.

Lemma NE_Forall_append : forall (P : A -> bool) xs ys,
   NE_Forall P xs /\ NE_Forall P ys <-> NE_Forall P (NE_append xs ys).
Proof.
  move=> P;
  case=> x0; elim=> [|x1 xs IHxs];
  case=> [z0]; case=> [|z1 zs] => /=; split.
  - by move=> [/andP [H1 _] /andP [H2 _]]; apply/and3P.
  - by move/and3P=> [H1 H2]; split; apply/andP.
  - by move=> [/andP [H1 _] /and3P [H2 H3 H4]]; apply/and4P.
  - by move/and4P=> [H1 H2 H3 H4]; split;
       [ apply/andP | apply/and3P ].
  - move=> [/and3P [H1 H2 H3] /andP [H4 H5]];
    apply/and3P; split; trivial.
    by rewrite cats1 all_rcons; apply/andP.
  - move/and3P=> [H1 H2 H3]; split;
    move: H3; rewrite cats1 all_rcons => /andP [H3 H4];
      [ by apply/and3P | by apply/andP ].
  - move=> [/and3P [H1 H2 H3] /and3P [H4 H5 H6]].
    rewrite all_cat -cat1s all_cat -[z1 :: _]cat1s all_cat /=.
    apply/and5P; split; auto;
      [ by apply/andP | by rewrite -andbA; apply/and3P ].
  - rewrite all_cat -cat1s all_cat -[z1 :: _]cat1s all_cat /=.
    move/and5P=> [H1 H2 H3 /andP [H4 H5] /andP [/andP [H6 H7] H8]].
    by split; apply/and3P.
Defined.

Definition NE_StronglySorted (ne : NonEmpty A) : Prop :=
  let: (x, xs) := ne in all id (pairmap R x xs).
Arguments NE_StronglySorted ne /.

Lemma NE_StronglySorted_inv_app : forall (l1 l2 : NonEmpty A),
  NE_StronglySorted (NE_append l1 l2)
    -> NE_StronglySorted l1 /\ NE_StronglySorted l2.
Proof.
  elim/ne_ind=> [x|x xs IHxs] //=.
    by case=> [y ys] /= /andP [H1 H2].
  case=> [y ys] /=.
  rewrite pairmap_cat all_cat /=.
  by move/and3P=> [H1 H2 H3].
Defined.

Lemma NE_StronglySorted_impl_app : forall (l1 l2 : NonEmpty A),
  NE_StronglySorted (NE_append l1 l2) -> R (NE_last l1) (NE_head l2).
Proof.
  elim/ne_ind=> [x|x xs IHxs] //=.
    elim/ne_ind=> [y|y ys IHys] //=;
    by move/andP => [? ?].
  elim/ne_ind=> [y|y ys IHys] //=;
  rewrite pairmap_cat all_cat /=;
  by move/and3P => [? ? ?].
Defined.

End Sorted.

Section Membership.

Definition NE_member {a : eqType} (z : a) (ne : NonEmpty a) : Prop :=
  let: (x, xs) := ne in (x == z) || (z \in xs).
Arguments NE_member [a] z ne /.

Lemma NE_Forall_member_spec {a : eqType} (z : a) (ne : NonEmpty a) :
  forall f, NE_Forall f ne -> NE_member z ne -> f z.
Proof.
  case: ne => [x xs] f /= /andP [H1 H2] /orP [/eqP H3|H3].
    by subst.
  move/allP in H2.
  exact: H2.
Defined.

End Membership.
