Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import Coq.Vectors.Fin.
Require Import FunctionalExtensionality.
Require Import Iso.
Require Import Recdef.

Module Import LN := ListNotations.

Infix "$" := apply (at level 90, right associativity) : program_scope.

Open Scope nat_scope.
Open Scope program_scope.

Generalizable All Variables.

(** The following are extensions to the Coq standard library. *)

Definition undefined {a : Type} : a. Admitted.

Definition curry_sig {A C} {B : A -> Prop}
  (f : forall x : A, B x -> C) (p : { x : A | B x }) : C :=
  let (x,H) := p in f x H.

Definition curry_sigT {A C} {B : A -> Type}
  (f : forall x : A, B x -> C) (p : { x : A & B x }) : C :=
  let (x,H) := p in f x H.

Definition fromMaybe {a} (d : a) (mx : option a) : a :=
  match mx with
    | Some x => x
    | None => d
  end.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require String.
Open Scope string_scope.

Definition existT_in_cons : forall {A a} {l : list A},
  {x : A & In x l} -> {x : A & In x (a :: l)}.
Proof.
  destruct l; intros; simpl.
    destruct X. inversion i.
  destruct X. exists x.
  apply in_inv in i.
  destruct i.
    right. left. assumption.
  right. right. assumption.
Defined.

Definition projTT1 {A} {P Q : A -> Type} (e : {x : A & P x & Q x}) : A :=
  let (x,_,_) := e in x.

Definition projTT2 {A} {P Q : A -> Type} (e : {x : A & P x & Q x})
  : P (projTT1 e) := let (x,p,_) as x return (P (projTT1 x)) := e in p.

Definition projTT3 {A} {P Q : A -> Type} (e : {x : A & P x & Q x})
  : Q (projTT1 e) := let (x,_,q) as x return (Q (projTT1 x)) := e in q.

Lemma one_gt_zero : forall n, n = 1 -> n > 0.
Proof. intros. omega. Qed.

Lemma nil_list_0 : forall a (xs : list a), length xs = 0 <-> xs = [].
Proof.
  split; intros.
    induction xs. reflexivity.
    inversion H.
  rewrite H. auto.
Qed.

Lemma gt_one_gt_zero : forall n, n > 1 -> n > 0.
Proof. intros. omega. Qed.

Lemma lt_le_shuffle : forall {x y z w}, x < y -> y <= z -> z < w -> x < w.
Proof. intros. omega. Qed.

Lemma plus_eq_zero : forall n m, n + m = n -> m = 0.
Proof. intros. omega. Qed.

Lemma plus_gt_zero : forall n m, n + m > n -> m > 0.
Proof. intros. omega. Qed.

Lemma fold_gt : forall a f n m (xs : list a),
  n > m -> fold_left (fun n x => n + f x) xs n > m.
Proof.
  intros.
  generalize dependent n.
  induction xs; intros; simpl. assumption.
  apply IHxs. omega.
Qed.

Lemma fold_fold_le : forall a f n m (xs : list a),
  n <= m -> fold_left (fun n x => n + f x) xs n <=
            fold_left (fun n x => n + f x) xs m.
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  induction xs; intros; simpl. assumption.
  apply IHxs. omega.
Qed.

Lemma fold_fold_lt : forall a f n m (xs : list a),
  n < m -> fold_left (fun n x => n + f x) xs n <
           fold_left (fun n x => n + f x) xs m.
Proof.
  intros.
  generalize dependent n.
  generalize dependent m.
  induction xs; intros; simpl. assumption.
  apply IHxs. omega.
Qed.

(** ** option *)

Fixpoint catMaybes {a : Set} (l : list (option a)) : list a :=
  match l with
    | nil => nil
    | cons None xs => catMaybes xs
    | cons (Some x) xs => x :: catMaybes xs
  end.

Definition mapMaybe {a b : Set} (f : a -> option b) (l : list a) : list b :=
  catMaybes (map f l).

Lemma min_lt_max : forall n m b e, n < m -> min b n < Peano.max e m.
Proof.
  induction n; intros; simpl;
  apply Nat.max_lt_iff; right;
  apply Nat.min_lt_iff; right; assumption.
Qed.

Lemma minus_lt : forall n m, n - m > 0 -> n > m.
Proof. intros; omega. Qed.

Lemma lt_minus : forall n m, n > m -> n - m > 0.
Proof. intros; omega. Qed.

Lemma min_max_minus : forall n m b e, n - m > 0 -> Peano.max e n - min b m > 0.
Proof.
  induction n; intros; simpl; try omega.
  apply lt_minus.
  apply minus_lt in H.
  unfold gt in *.
  apply Nat.max_lt_iff.
  right.
  apply Nat.min_lt_iff.
  right. assumption.
Qed.

Ltac min_max :=
  auto; try omega;
  repeat match goal with
  | [ H : ?X < ?Y |- _ ] =>
    match goal with
      [ |- min _ X < Peano.max _ Y ] =>
      apply min_lt_max; assumption
    end
  | [ H: ?X < ?Y |- _ ] =>
    match goal with
      [ H0: _ -> Y < ?Z |- _ ] =>
      match goal with
        [ |- X < Z ] =>
          transitivity Y; auto
      end
    end
  | [ IH: _ -> ?X < ?Y |- _] =>
    match goal with
      [ |- min _ X < Y ] =>
      apply Nat.min_lt_iff; right; apply IH
    end
  | [ H: Peano.max _ ?X <= ?Y |- _ ] =>
    match goal with
      [ |- ?X <= ?Y ] =>
        apply Max.max_lub_r in H; auto
    end
  end.

Lemma rew_in_not_eq : forall {a : Type} {x y z : a}, x = y -> z <> x -> z <> y.
Proof.
  intros. unfold not in *. intros. apply H0.
  rewrite H. assumption.
Qed.

(** ** Lists *)

Lemma fold_left_plus : forall a f xs n,
   fold_left (fun (n : nat) (x : a) => n + f x) xs n =
   fold_left (fun (n : nat) (x : a) => n + f x) xs 0 + n.
Proof.
  intros a f xs.
  induction xs. reflexivity.
  intros. simpl.
  rewrite IHxs. simpl.
  symmetry.
  rewrite IHxs. simpl.
  rewrite <- Plus.plus_assoc.
  rewrite (Plus.plus_comm n) at 1. reflexivity.
Qed.

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

Lemma NoDup_uncons : forall x (xs ys : list a),
  NoDup ((x :: xs) ++ ys) -> NoDup (xs ++ ys).
Proof. intros. inversion H. assumption. Qed.

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

Definition find_in (n : a) (l : list a) : {In n l} + {~ In n l}.
Proof.
  induction l as [| x xs].
    right. auto.
  destruct (cmp_eq_dec n x).
    subst. left. apply in_eq.
  inversion IHxs.
    left. apply in_cons.
    assumption.
  right. unfold not in *.
  intros. apply in_inv in H0.
  inversion H0.
     symmetry in H1. contradiction.
  contradiction.
Defined.

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

Arguments find_in [_] _ _ _.

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

Lemma LocallySorted_uncons : forall a (R : a -> a -> Prop) (x : a) xs,
  LocallySorted R (x :: xs) -> LocallySorted R xs.
Proof. intros. inversion H; subst; [ constructor | assumption ]. Qed.

Lemma StronglySorted_uncons : forall a (R : a -> a -> Prop) (x : a) xs,
  StronglySorted R (x :: xs) -> StronglySorted R xs.
Proof. intros. inversion H; subst. assumption. Qed.

Definition safe_hd {a} (xs : list a) (H : (length xs > 0)%nat) : a.
Proof.
  destruct xs.
    simpl in H.
    unfold gt in H.
    unfold Peano.lt in H.
    apply Le.le_Sn_n in H.
    inversion H.
  apply a0.
Defined.

Fixpoint safe_last {a} (xs : list a) (H : (length xs > 0)%nat) : a.
Proof.
  induction xs.
    simpl in H.
    unfold gt in H.
    unfold Peano.lt in H.
    apply Le.le_Sn_n in H.
    inversion H.
  destruct xs.
    apply a0.
  apply IHxs. simpl.
  apply Gt.gt_Sn_O.
Defined.

(** ** Comparisons *)

(** These definitions avoid boilerplate involved with setting up properly
    behaved comparisons between types. *)

Lemma mk_compare_spec : forall {a} (x y : a)
  (cmp         : a -> a -> comparison)
  (cmp_eq_iff  : cmp x y = Eq <-> x = y)
  (cmp_gt_flip : cmp x y = Gt  -> cmp y x = Lt),
  CompSpec eq (fun x y => cmp x y = Lt) x y (cmp x y).
Proof.
  intros.
  destruct (cmp x y) eqn:Heqe.
  - apply CompEq. apply cmp_eq_iff. reflexivity.
  - apply CompLt. assumption.
  - apply CompGt. auto.
Defined.

Lemma mk_cmp_eq_dec : forall {a} (x y : a)
  (cmp        : a -> a -> comparison)
  (cmp_eq_iff : cmp x y = Eq <-> x = y),
  { x = y } + { x <> y }.
Proof.
  intros.
  destruct (cmp x y) eqn:Heqe.
  - left. apply cmp_eq_iff. reflexivity.
  - right. intuition. inversion H2.
  - right. intuition. inversion H2.
Defined.

Class CompareSpec (a : Set) := {
  cmp         : a -> a -> comparison;
  cmp_eq x y  := cmp x y = Eq;
  cmp_eq_iff  : forall x y, cmp x y = Eq <-> x = y;
  cmp_lt x y  := cmp x y = Lt;
  cmp_le x y  := cmp_lt x y \/ cmp_eq x y;
  cmp_gt x y  := cmp x y = Gt;
  cmp_ge x y  := cmp_gt x y \/ cmp_eq x y;
  cmp_gt_flip : forall x y, cmp_gt x y -> cmp_lt y x;

  cmp_spec x y : CompSpec eq cmp_lt x y (cmp x y) :=
    mk_compare_spec x y cmp (cmp_eq_iff x y) (cmp_gt_flip x y);

  cmp_eq_dec x y : { x = y } + { x <> y } :=
    mk_cmp_eq_dec x y cmp (cmp_eq_iff x y)
}.

Lemma nat_compare_gt_flip : forall (x y : nat),
  nat_compare x y = Gt -> nat_compare y x = Lt.
Proof.
  intros.
  apply nat_compare_lt.
  apply nat_compare_gt in H.
  trivial.
Qed.

Program Instance nat_CompareSpec : CompareSpec nat := {
  cmp         := nat_compare;
  cmp_eq_iff  := nat_compare_eq_iff;
  cmp_gt_flip := nat_compare_gt_flip
}.

(** ** NonEmpty lists *)

Inductive NonEmpty (a : Set) : Set :=
  | NE_Sing : a -> NonEmpty a
  | NE_Cons : a -> NonEmpty a -> NonEmpty a.

Arguments NE_Sing [_] _.
Arguments NE_Cons [_] _ _.

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => x :: nil
    | NE_Cons x xs => x :: NE_to_list xs
  end.

Definition NE_hd {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x _ => x
  end.

Fixpoint NE_tl {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x xs => NE_tl xs
  end.

(** ** Finite sets *)

Definition fin := Coq.Vectors.Fin.t.

Definition fin_contra : forall {x}, fin 0 -> x.
Proof. intros. inversion H. Defined.

Definition from_nat {m} (n : nat) (H : n < m) : fin m := @of_nat_lt n m H.

Definition fin_to_nat {n} (f : fin n) : nat := proj1_sig (to_nat f).

Definition last_fin_from_nat (n : nat) : fin (S n) := from_nat n (le_n (S n)).

(** Return the last possible inhabitant of a [fin n]. *)
Definition ultimate_from_nat (n : nat) (H : n > 0) : fin n.
  apply (@from_nat n (pred n)).
  apply lt_pred_n_n.
  trivial.
Defined.

(** Given a value [x] of type [fin n], return the next lower inhabitant [y],
    such that y < x.  Returns [None] if [x = 0]. *)
Definition pred_fin {n} (f : fin n) : option (fin n).
  apply to_nat in f.
  destruct f.
  destruct x. apply None.
  apply Some.
  apply Le.le_Sn_le in l.
  apply (from_nat x l).
Defined.

Definition fin_Sn_inv {n:nat} (P : fin (S n) -> Type)
  (PO : P F1) (PS : forall y : fin n, P (FS y)) :
  forall x : fin (S n), P x :=
  fun x =>
    match x in (t Sn) return
      (match Sn return (fin Sn -> Type) with
       | 0 => const unit
       | S n' => fun x => forall (P : fin (S n') -> Type),
         P F1 -> (forall y : fin n', P (FS y)) ->
         P x
       end x) with
    | F1 _ => fun P PO PS => PO
    | FS _ y => fun P PO PS => PS y
    end P PO PS.

(** [to_nat] and [from_nat] compose to an identity module the hypothesis that
    [n < m]. *)
Lemma fin_to_from_id : forall m n (H : n < m),
  m > 0 -> to_nat (from_nat n H) = exist _ n H.
Proof.
  intros.
  generalize dependent n.
  induction m; intros. omega.
  destruct n; simpl.
    f_equal. apply proof_irrelevance.
  rewrite IHm.
    f_equal. apply proof_irrelevance.
  omega.
Qed.

Definition FS_inv {n} (x : fin (S n)) : option (fin n) :=
  fin_Sn_inv (const (option (fin n))) None (@Some _) x.

Lemma fin_to_nat_Sn : forall {m} (n : fin m),
  fin_to_nat (@FS m n) = S (fin_to_nat n).
Proof.
  intros. unfold fin_to_nat. simpl.
  induction (to_nat n); reflexivity.
Qed.

Lemma fin_from_to_id : forall n (x : fin n),
  (let (m,H) := to_nat x in from_nat m H) = x.
Proof.
  induction n; intros. inversion x.
  destruct x using fin_Sn_inv; trivial.
  specialize (IHn x). simpl in *.
  destruct (to_nat x) eqn:Heqe. simpl.
  f_equal.
  assert (l = lt_S_n x0 n (lt_n_S x0 n l)) by (apply proof_irrelevance).
  rewrite <- H.
  apply IHn.
Qed.

Program Instance fin_nat_iso : forall {n}, fin n ≅ { m : nat | m < n } := {
    to   := to_nat;
    from := curry_sig (@from_nat n)
}.
Obligation 1.
  extensionality x.
  unfold compose, id, curry_sig.
  apply fin_from_to_id.
Qed.
Obligation 2.
  extensionality x.
  unfold compose, id, curry_sig.
  destruct x.
  apply fin_to_from_id. omega.
Qed.

(** Given a value of type [fin (S n)], return the equivalent [fin n],
    returning None if the input value was the highest possible value of [fin
    (S n)]. *)

Definition fin_reduce {n : nat} (x : fin (S n)) : option (fin n) :=
  let n' := fin_to_nat x in
  match le_lt_dec n n' with
  | right H => Some (from_nat n' H)
  | left _  => None
  end.

(** The behavior of [pred_fin] is specified as follows: the predecessor of a
    successor, by way of [fin n], is a no-op. *)
Lemma pred_fin_spec : forall (n m : nat) (H : S n < m),
  pred_fin (@from_nat m _ H) = Some (from_nat n (Le.le_Sn_le _ _ H)).
Proof.
  intros. unfold pred_fin.
  rewrite fin_to_from_id.
    reflexivity.
  omega.
Qed.

(** If [pred_fin] produces a value, this value converted to [nat] is less than
    the input converted to [nat]. *)
Lemma pred_fin_lt : forall n (x y : fin n),
  @pred_fin n x = Some y -> fin_to_nat y < fin_to_nat x.
Proof.
  unfold fin_to_nat.
  destruct n; intros.
    inversion x.
  unfold pred_fin in H.
  destruct (to_nat x).
  destruct x0; inversion H.
  subst. simpl. clear H.
  destruct x0; simpl. omega.
  rewrite fin_to_from_id.
  simpl. omega. omega.
Qed.

(** The function [fin_to_nat] is bijective. *)
Lemma fin_to_nat_bijective : forall n (x y : fin n),
  fin_to_nat x = fin_to_nat y <-> x = y.
Proof.
  unfold fin_to_nat.
  split; intros.
  - destruct n. inversion x.
    generalize dependent y.
    induction x; intros.
      dependent destruction y.
        reflexivity.
      simpl in H.
      destruct (to_nat y).
      simpl in H. inversion H.
    dependent destruction y.
      simpl in H.
      destruct (to_nat x).
      simpl in H. inversion H.
    specialize (IHx y).
    f_equal. apply IHx.
    simpl in H.
    destruct (to_nat x).
    destruct (to_nat y).
    simpl in H.
    apply eq_add_S in H.
    subst. reflexivity.
  - f_equal. f_equal. assumption.
Qed.

Definition map_FS_inv {n:nat} (l : list (fin (S n))) : list (fin n) :=
  catMaybes (map FS_inv l).

Lemma map_FS_inv_len_noO : forall {n} (l : list (fin (S n))),
  ~ In F1 l -> length (map_FS_inv l) = length l.
Proof.
  induction l; simpl. reflexivity.
  destruct a using fin_Sn_inv; simpl; intuition.
Qed.

Lemma map_FS_inv_len_NoDup : forall {n} (l : list (fin (S n))),
  NoDup l -> length l <= S (length (map_FS_inv l)).
Proof.
  induction 1; simpl.
    apply le_0_n.
  unfold map_FS_inv, catMaybes. simpl.
  destruct x using fin_Sn_inv; simpl; intros.
    fold (@catMaybes).
    pose (map_FS_inv_len_noO l H).
    unfold map_FS_inv in *.
    rewrite e. reflexivity.
  auto with arith.
Qed.

Lemma in_map_FS_inv : forall {n} (l : list (fin (S n))) (y : fin n),
  In y (map_FS_inv l) <-> In (FS y) l.
Proof.
  split.
    induction l; simpl. trivial.
    destruct a using fin_Sn_inv; simpl. auto.
    destruct 1. left; f_equal; trivial.
    right; auto.
  induction l; simpl. trivial.
  destruct a using fin_Sn_inv; simpl in *.
    unfold map_FS_inv. simpl.
    intros. apply IHl.
    intuition. inversion H0.
  intros. inversion H.
  left. apply FS_inj in H0. trivial.
  right. apply IHl. assumption.
Qed.

Lemma map_FS_inv_NoDup : forall {n:nat} (l : list (fin (S n))),
  NoDup l -> NoDup (map_FS_inv l).
Proof.
  induction 1; simpl. constructor.
  destruct x using fin_Sn_inv; simpl. trivial.
  constructor; trivial.
  contradict H.
  apply in_map_FS_inv; trivial.
Qed.

Theorem fin_list n (l : list (fin n)) : NoDup l -> length l <= n.
Proof.
  induction n as [|n']; intros.
    destruct l as [|hd ?]; trivial; inversion hd.
  apply le_trans with (1 := map_FS_inv_len_NoDup l H).
  auto using le_n_S, map_FS_inv_NoDup.
Qed.

(** *** Comparison of values from the same finite set. *)

(** [fin] values may be compared.  It is simply a comparison of their
    underlying naturals, owing to proof irrelevance. *)

Definition fin_compare {n} (x y : fin n) : comparison :=
  nat_compare (fin_to_nat x) (fin_to_nat y).

Lemma fin_compare_eq_iff : forall n (x y : fin n),
  fin_compare x y = Eq <-> x = y.
Proof.
  unfold fin_compare.
  split; intros;
  first [ apply nat_compare_eq_iff
        | apply nat_compare_eq in H ];
  apply fin_to_nat_bijective; assumption.
Qed.

Lemma fin_compare_gt_flip : forall n (x y : fin n),
  fin_compare x y = Gt -> fin_compare y x = Lt.
Proof.
  unfold fin_compare. intros.
  apply nat_compare_gt in H.
  apply nat_compare_lt. omega.
Qed.

Program Instance fin_CompareSpec {n} : CompareSpec (fin n) := {
  cmp         := fin_compare;
  cmp_eq_iff  := fin_compare_eq_iff n;
  cmp_gt_flip := fin_compare_gt_flip n
}.

Definition is_le (c : comparison) : bool :=
  match c with
    | Gt => false
    | _  => true
  end.

Module FinOrder <: TotalLeBool.
  Parameter n : nat.
  Definition t := fin n.

  Definition leb (x y : fin n) : bool := is_le (cmp x y).
  Definition leb_true x y := is_true (leb x y).

  Theorem leb_total : forall (a1 a2 : fin n),
    leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros. unfold leb.
    destruct (cmp a1 a2) eqn:Heqe.
    - left. reflexivity.
    - left. reflexivity.
    - right. apply cmp_gt_flip in Heqe.
      rewrite Heqe. reflexivity.
  Qed.
End FinOrder.

Definition fin_safe_reduce {n : nat} (x : fin (S n))
  (H : x <> last_fin_from_nat n) : fin n.
Proof.
  induction n; simpl in *;
  destruct x using fin_Sn_inv.
  - contradiction H. reflexivity.
  - apply x.
  - apply F1.
  - apply x.
Defined.

Lemma last_fin_from_nat_spec : forall n, fin_to_nat (last_fin_from_nat n) = n.
Proof.
  intros.
  induction n. reflexivity.
  unfold last_fin_from_nat, fin_to_nat.
  rewrite fin_to_from_id.
  reflexivity.
  apply gt_Sn_O.
Qed.

Lemma fin_lt {n : nat} (l : list (fin n)) : forall x, In x l -> fin_to_nat x < n.
Proof.
  intros.
  induction n. inversion x.
  destruct x using fin_Sn_inv.
    unfold fin_to_nat.
    unfold proj1_sig, to_nat.
    apply lt_0_Sn.
  rewrite fin_to_nat_Sn.
  apply lt_n_S.
  apply (IHn (map_FS_inv l)).
  apply in_map_FS_inv. assumption.
Qed.

Definition fin_expand {n} (p : t n) : t (S n).
  induction n. inversion p.
  destruct p using fin_Sn_inv.
    apply F1.
  apply FS.
  apply IHn.
  apply y.
Defined.

(*
Example fin_expand_sane : forall m n, fin_reduce (@fin_expand m n) = Some n.
Proof.
  intros.
  induction m. inversion n.
  destruct n using fin_Sn_inv.
    reflexivity.
  simpl.
*)

Lemma fin_bounded : forall m (n : fin m), fin_expand n <> last_fin_from_nat m.
Proof.
  intros.
  induction m. inversion n.
  destruct n using fin_Sn_inv; intuition. inversion H.
  apply (IHm n).
  unfold last_fin_from_nat in *.
  simpl in *.
  apply FS_inj in H.
  rewrite H. f_equal.
  apply proof_irrelevance.
Qed.

Lemma last_fin_from_nat_not_In {n : nat} (l : list (fin n))
  : ~ In (last_fin_from_nat n) (map fin_expand l).
Proof.
  induction l; simpl. now easy.
  unfold not. intros.
  destruct H.
    pose (fin_bounded n a). contradiction.
  contradiction.
Qed.

Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Lemma Injective_map_NoDup A B (f : A -> B) (l : list A) :
 Injective f -> NoDup l -> NoDup (map f l).
Proof.
  intros Ij.
  induction 1; simpl; constructor; trivial.
  rewrite in_map_iff. intros (y & E & Y). apply Ij in E. now subst.
Qed.

Lemma NoDup_map_inv {A B} {f : A -> B} l : NoDup (map f l) -> NoDup l.
Proof.
 induction l; simpl; inversion_clear 1; subst; constructor; auto.
 intro H. now apply (in_map f) in H.
Qed.

Lemma fin_expand_inj {n} (x y: t n) (eq: fin_expand x = fin_expand y): x = y.
Proof.
  induction n. inversion x.
  destruct x using fin_Sn_inv;
  destruct y using fin_Sn_inv.
  - reflexivity.
  - inversion eq.
  - inversion eq.
  - f_equal. apply IHn.
    simpl in eq.
    apply FS_inj in eq.
    assumption.
Qed.

Lemma NoDup_fin_cons {n} (x : fin (S n)) (l : list (fin n))
  : NoDup l -> x = last_fin_from_nat n -> NoDup (x :: map fin_expand l).
Proof.
  intros.
  constructor.
    rewrite H0.
    apply last_fin_from_nat_not_In.
  apply Injective_map_NoDup.
    unfold Injective. intros.
    apply fin_expand_inj in H1.
    assumption.
  assumption.
Qed.
