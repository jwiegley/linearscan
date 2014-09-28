Require Export Coq.Lists.List.

Require Import Compare.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Sorting.Permutation.
Require Import Recdef.

Section Elems.

Variable a : Set.
Variable cmp_eq_dec : forall x y : a, {x = y} + {x <> y}.

Function NoDup_from_list (l : list a) {measure length l} : option (NoDup l) :=
  match l with
  | nil => Some (NoDup_nil a)
  | cons x xs =>
      match in_dec cmp_eq_dec x xs with
      | left H => None
      | right H =>
          match NoDup_from_list xs with
          | None => None
          | Some l' => Some (NoDup_cons _ H l')
          end
      end
  end.
Proof. auto. Qed.

Lemma NoDup_unapp : forall (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup xs /\ NoDup ys.
Proof.
  intros. induction xs.
    split; [ constructor | auto ].
  simpl in H. inversion H.
  apply IHxs in H3.
  inversion H3. subst.
  split.
    apply NoDup_cons.
      unfold not in *. intros.
      apply H2. apply in_or_app.
      left. assumption.
    assumption.
  assumption.
Defined.

Lemma NoDup_swap : forall (xs ys : list a),
  NoDup (xs ++ ys) -> NoDup (ys ++ xs).
Proof.
  intros.
  generalize dependent xs.
  induction ys; intros.
    rewrite app_nil_r in H. auto.
  simpl. pose proof H.
  apply NoDup_remove_1 in H.
  apply NoDup_remove_2 in H0.
  apply NoDup_cons.
    unfold not in *. intros.
    apply H0.
    apply in_app_iff.
    apply in_app_iff in H1.
    destruct H1. right. assumption.
    left. assumption.
  apply IHys. assumption.
Qed.

Lemma NoDup_swap2 : forall (xs ys zs : list a),
  NoDup (xs ++ ys ++ zs) -> NoDup (xs ++ zs ++ ys).
Proof.
  intros. induction xs; simpl in *.
    apply NoDup_swap.
    assumption.
  apply NoDup_cons.
    inversion H; subst.
    unfold not in *. intros.
    apply H2.
    apply in_app_iff.
    apply in_app_iff in H0.
    destruct H0.
      left. assumption.
    right.
    apply in_app_iff.
    apply in_app_iff in H0.
    destruct H0.
      right. assumption.
    left. assumption.
  apply IHxs.
  inversion H. assumption.
Qed.

Lemma NoDup_swap_cons : forall x (xs ys : list a),
  NoDup (x :: xs ++ ys) -> NoDup (x :: ys ++ xs).
Proof.
  intros.
  constructor.
    inversion H; subst.
    unfold not in *. intros.
    apply H2.
    apply in_app_iff.
    apply in_app_iff in H0.
    intuition.
  inversion H.
  apply NoDup_swap.
  assumption.
Defined.

Lemma NoDup_app_cons : forall x (xs ys : list a),
  NoDup (xs ++ x :: ys) <-> NoDup (x :: xs ++ ys).
Proof.
  induction xs; simpl; split; intros; auto.
    rewrite app_comm_cons in H.
    pose proof H.
    apply NoDup_remove_1 in H. simpl in H.
    apply NoDup_remove_2 in H0. simpl in H0.
    apply NoDup_cons.
      unfold not in *. intros.
      apply H0. right.
      apply in_inv in H1. contradiction.
    assumption.
  rewrite app_comm_cons.
  apply NoDup_swap. simpl.
  inversion H; subst.
  apply NoDup_cons.
    unfold not in *. intros.
    apply H2. simpl.
    right.
    apply in_app_iff in H0.
    apply in_app_iff.
    destruct H0. right. assumption.
    left. apply in_inv in H0.
    destruct H0. subst.
      contradiction H2.
      apply in_eq.
    assumption.
  apply NoDup_swap. simpl.
  inversion H. assumption.
Qed.

Lemma NoDup_uncons : forall x (xs ys : list a),
  NoDup ((x :: xs) ++ ys) -> NoDup (xs ++ ys).
Proof. intros. inversion H. assumption. Qed.

Lemma In_remove_spec : forall x y l,
  x <> y -> In y (remove cmp_eq_dec x l) -> In y l.
Proof.
  induction l; intros; simpl in *.
    apply H0.
  destruct (cmp_eq_dec x a0); subst.
    right. apply IHl; assumption.
  apply in_inv in H0.
  destruct H0.
    left. assumption.
  right. apply IHl; assumption.
Qed.

Lemma remove_spec3 : forall x l, ~ In x l -> remove cmp_eq_dec x l = l.
Proof.
  induction l; intros; simpl.
    reflexivity.
  destruct (cmp_eq_dec x a0).
    subst. contradiction H.
    apply in_eq.
  f_equal. apply IHl.
  unfold not in *. intros.
  apply H. apply in_cons.
  assumption.
Qed.

Lemma not_in_app : forall x (l l' : list a), ~ In x (l ++ l') -> ~ In x l.
Proof.
  intros. unfold not in *. intros.
  apply H. apply in_app_iff.
  left. assumption.
Qed.

Lemma NoDup_juggle : forall (xs ys zs : list a),
  NoDup (xs ++ ys ++ zs) -> forall x, In x xs
    -> NoDup (remove cmp_eq_dec x xs ++ (x :: ys) ++ zs).
Proof.
  induction xs as [| x xs']; intros; simpl in *.
    inversion H0.
  destruct (cmp_eq_dec x0 x).
    inversion H; subst.
    apply not_in_app in H3.
    rewrite remove_spec3.
      apply NoDup_app_cons.
      assumption.
    assumption.
  simpl. constructor.
    inversion H; subst.
    unfold not. intros.
    contradiction H3.
    apply in_app_iff.
    apply in_app_iff in H1.
    destruct H1.
      left. apply (In_remove_spec x0 x xs') in H1;
        assumption.
    right.
    apply in_app_iff.
    rewrite app_comm_cons in H1.
    apply in_app_iff in H1.
    destruct H1.
      left. apply in_inv in H1.
        destruct H1. contradiction.
      assumption.
    right. assumption.
  apply IHxs'. inversion H. assumption.
  destruct H0.
    symmetry in H0.
    contradiction.
  assumption.
Qed.

Lemma not_in_list : forall x xs,
  ~ In x xs -> count_occ cmp_eq_dec xs x = 0.
Proof.
  intros. induction xs; simpl; auto.
  destruct (cmp_eq_dec a0 x); subst.
    contradiction H. apply in_eq.
  apply IHxs.
  unfold not in *. intros.
  apply H. right. assumption.
Qed.

Lemma In_spec : forall (x : a) y xs, In x xs -> ~ In y xs -> y <> x.
Proof.
  unfold not in *. intros. subst.
  contradiction.
Qed.

Lemma Forall_uncons :
  forall {A : Type} {P : A -> Prop} {x l l0},
  Forall P l -> l = x :: l0 -> P x * Forall P l0.
Proof.
  intros.
  generalize dependent l.
  induction l0; intros.
    destruct l; inversion H0.
    inversion H; subst. auto.
  specialize (IHl0 (x :: l0)). subst.
  split; inversion H; subst; auto.
Qed.

End Elems.

Theorem Permutation_not_in : forall {A} {l l' : list A} (x : A),
  Permutation l l' -> ~ In x l -> ~ In x l'.
Proof.
  intros A l l' x Hperm; induction Hperm; simpl; tauto.
Qed.

Lemma not_in_uncons : forall {A} x y (l : list A), ~ In y (x :: l) -> ~ In y l.
Proof.
  unfold not. intros.
  apply H.
  apply in_cons. assumption.
Qed.

Lemma NoDup_perm : forall (a : Set) (xs ys : list a),
  Permutation xs ys -> NoDup xs -> NoDup ys.
Proof.
  intros.
  induction H; intros.
  - constructor.
  - apply (Permutation_not_in x) in H.
      apply NoDup_cons. assumption.
      inversion H0.
      apply IHPermutation.
      assumption.
    inversion H0. assumption.
  - inversion H0; subst.
    inversion H3; subst.
    apply NoDup_cons.
      unfold not in *. intros.
      apply in_inv in H.
      destruct H.
        subst. apply H2.
        apply in_eq.
      apply H4. assumption.
    apply not_in_uncons in H2.
    apply NoDup_cons; assumption.
  - auto.
Qed.
