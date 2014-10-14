Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Numbers.Natural.Peano.NPeano.
Require Export Coq.Sorting.Sorting.
Require Export List.
Require Export Omega.
Require Export Tactics.

Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrnat.
(* Require Export Ssreflect.ssrfun. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Export LN := ListNotations.

(** The following are extensions to the Coq standard library. *)

Definition undefined {a : Type} : a. Admitted.

Definition ex_falso_quodlibet : forall {P : Type}, False -> P.
Proof. intros P. contra. Defined.

Definition predicate {a} (f : a -> bool) : a -> Prop :=
  fun x => Is_true (f x).

Notation "p .1" := (proj1_sig p)
  (at level 2, left associativity, format "p .1").
Notation "p .2" := (proj2_sig p)
  (at level 2, left associativity, format "p .2").
Notation "( x ; y )" := (exist _ x y).

Definition uncurry_sig {A C} {B : A -> Prop}
  (f : forall x : A, B x -> C) (p : { x : A | B x }) : C :=
  let (x,H) := p in f x H.

Definition uncurry_sigT {A C} {B : A -> Type}
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

Definition exist_in_cons : forall {A a} {l : list A},
  {x : A | In x l} -> {x : A | In x (a :: l)}.
Proof.
  destruct l; intros; simpl; destruct X.
    inversion i.
  exists x.
  apply in_inv in i.
  destruct i; right; [ left | right]; assumption.
Defined.

Lemma list_cons_nonzero : forall {a x} {xs l : list a},
  l = x :: xs -> length l > 0.
Proof. by move=> a x xs l ->. Qed.

Definition list_membership {a} (l : list a) : list { x : a | In x l } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          exist _ x (in_eq x xs) :: map exist_in_cons (go xs)
      end in
  go l.

(** Move an element from one position within a vector to another position in
    the same vector. *)

Definition projTT1 {A} {P Q : A -> Type} (e : {x : A & P x & Q x}) : A :=
  let (x,_,_) := e in x.

Definition projTT2 {A} {P Q : A -> Type} (e : {x : A & P x & Q x})
  : P (projTT1 e) := let (x,p,_) as x return (P (projTT1 x)) := e in p.

Definition projTT3 {A} {P Q : A -> Type} (e : {x : A & P x & Q x})
  : Q (projTT1 e) := let (x,_,q) as x return (Q (projTT1 x)) := e in q.

Definition proj1_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x}) : A :=
  let (x,_,_) := e in x.

Definition proj2_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x})
  : P (proj1_sigg e) := let (x,p,_) as x return (P (proj1_sigg x)) := e in p.

Definition proj3_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x})
  : Q (proj1_sigg e) := let (x,_,q) as x return (Q (proj1_sigg x)) := e in q.

Lemma lt_dec : forall n m, (n < m) -> (n < m)%coq_nat.
Proof. move=> n m H. destruct (@ltP n m); [ done | inv H ]. Qed.

Lemma lt_dec_iff : forall n m, (n < m) <-> (n < m)%coq_nat.
Proof.
  split. apply lt_dec.
  move=> H. destruct (@ltP n m); [ done | inv H ].
Qed.

Lemma le_dec : forall n m, (n <= m) -> (n <= m)%coq_nat.
Proof. move=> n m H. destruct (@leP n m); [ done | inv H ]. Qed.

Lemma le_dec_iff : forall n m, (n <= m) <-> (n <= m)%coq_nat.
Proof.
  split. apply le_dec.
  move=> H. destruct (@leP n m); [ done | inv H ].
Qed.

Ltac ssomega :=
  repeat match goal with
    | [ H : is_true (leq (S ?N) ?M)  |- _ ] =>
        destruct (@ltP N M); last done
    | [ H : is_true (leq ?N ?M)  |- _ ] =>
        destruct (@leP N M); last done
    | [ |- is_true (leq (S _) _) ] => apply lt_dec_iff
    | [ |- is_true (leq _ _) ] => apply le_dec_iff
  end; omega.

Lemma leq_min : forall m n p, n <= p -> minn m n <= p.
Proof. intros. rewrite geq_min. by elim: (m <= p). Qed.

Lemma ltn_min : forall m n p, n < p -> minn m n < p.
Proof. intros. rewrite gtn_min. by elim: (m < p). Qed.

Lemma ltn_max : forall m n p, p < n -> p < maxn m n.
 Proof. move=> *. by rewrite leq_max; intuition. Qed.

Lemma lt_le_shuffle : forall {x y z w}, x < y -> y <= z -> z < w -> x < w.
Proof. intros. ssomega. Qed.

Lemma lt_lt_le_shuffle : forall {x y z w}, x < y -> y < z -> z <= w -> x < w.
Proof. intros. ssomega. Qed.

Lemma lt_le_le_shuffle : forall {x y z w}, x < y -> y <= z -> z <= w -> x < w.
Proof. intros. ssomega. Qed.

Lemma le_Sn_le : forall n m : nat, n.+1 <= m -> n <= m.
Proof. intros. ssomega. Qed.

Lemma ltn_plus : forall m n, 0 < n -> m < n + m.
  elim=> [|m IHm] // n H;
    first by rewrite addn0.
  rewrite addnS; by apply IHm.
Qed.

(*
Lemma ltb_gt : forall n m : nat, (n < m) = false <-> m <= n.
Proof.
  split; intros;
  generalize dependent m;
  induction n; destruct m;
  intros; simpl in *; auto.
  - inversion H.
  - apply le_n_S; apply IHn.
    apply H.
  - inversion H.
  - apply IHn. omega.
Qed.

Lemma lt_sub : forall n m, n < m -> { p : nat | p = m - n }.
Proof. intros. exists (m - n). reflexivity. Defined.

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

Lemma lt_le_le_shuffle : forall {x y z w}, x < y -> y <= z -> z <= w -> x < w.
Proof. intros. omega. Qed.

Lemma plus_eq_zero : forall n m, n + m = n -> m = 0.
Proof. intros. omega. Qed.

Lemma plus_gt_zero : forall n m, n + m > n -> m > 0.
Proof. intros. omega. Qed.

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

Lemma le_min : forall m n p, n <= p -> min m n <= p.
Proof. intros. apply Nat.min_le_iff. right. assumption. Qed.

Lemma lt_min : forall m n p, n < p -> min m n < p.
Proof. intros. apply Nat.min_lt_iff. right. assumption. Qed.

Lemma lt_max : forall m n p, p < n -> p < max m n.
Proof. intros. apply Nat.max_lt_iff. right. assumption. Qed.

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
*)

Lemma fold_gt : forall a f n m (xs : list a),
  n > m -> fold_left (fun n x => n + f x) xs n > m.
Proof.
  move=> a f n m xs.
  elim: xs n => // ? ? IHxs *.
  by apply /IHxs /ltn_addr.
Qed.

Lemma fold_fold_le : forall a f n m (xs : list a),
  n <= m -> fold_left (fun n x => n + f x) xs n <=
            fold_left (fun n x => n + f x) xs m.
Proof.
  move=> a f n m xs.
  elim: xs n m => // ? ? IHxs *.
  by apply /IHxs /leq_add.
Qed.

Lemma fold_fold_lt : forall a f n m (xs : list a),
  n < m -> fold_left (fun n x => n + f x) xs n <
           fold_left (fun n x => n + f x) xs m.
Proof.
  move=> a f n m xs.
  elim: xs n m => // ? ? IHxs *.
  apply IHxs.
  by rewrite ltn_add2r.
Qed.

Lemma fold_left_plus : forall a f xs n,
   fold_left (fun (n : nat) (x : a) => n + f x) xs n =
   fold_left (fun (n : nat) (x : a) => n + f x) xs 0 + n.
Proof.
  move=> a f; elim=> // a' ? IHxs n /=.
  rewrite add0n IHxs (IHxs (f a')) [n+_]addnC addnA //.
Qed.

Definition find_in {a} (eq_dec : forall x y : a, { x = y } + { x <> y })
  (n : a) (l : list a) : {In n l} + {~ In n l}.
Proof.
  induction l as [| x xs].
    right. auto.
  destruct (eq_dec n x).
    subst. left. apply in_eq.
  inversion IHxs.
    left. apply List.in_cons.
    assumption.
  right. unfold not in *.
  intros. apply in_inv in H0.
  inversion H0.
     symmetry in H1. contradiction.
  contradiction.
Defined.

Arguments find_in [_] _ _ _.

Lemma LocallySorted_uncons : forall a (R : a -> a -> Prop) (x : a) xs,
  LocallySorted R (x :: xs) -> LocallySorted R xs.
Proof. intros. inversion H; subst; [ constructor | assumption ]. Qed.

Lemma StronglySorted_uncons : forall a (R : a -> a -> Prop) (x : a) xs,
  StronglySorted R (x :: xs) -> StronglySorted R xs.
Proof. intros. inversion H; subst. assumption. Qed.

Definition safe_hd {a} (xs : list a) (H : (length xs > 0)%nat) : a.
Proof. elim: xs H => //. Qed.

Fixpoint safe_last {a} (xs : list a) (H : (length xs > 0)%nat) : a.
Proof. elim: xs H => //. Qed.
