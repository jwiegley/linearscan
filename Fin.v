Require Export Compare.
Require Export Coq.Vectors.Fin.

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Equality.
Require Import Coq.Structures.Orders.
Require Import Coq.omega.Omega.

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
       | 0 => fun _ => unit
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
  fin_Sn_inv (fun _ => option (fin n)) None (@Some _) x.

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

(*
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
*)

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

Fixpoint catMaybes {a : Set} (l : list (option a)) : list a :=
  match l with
    | nil => nil
    | cons None xs => catMaybes xs
    | cons (Some x) xs => cons x (catMaybes xs)
  end.

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

Module FinOrder <: TotalTransitiveLeBool.

  Parameter n : nat.
  Definition t := fin n.

  Definition leb (x y : fin n) : bool := is_le (cmp x y).
  Definition le (x y : fin n) := is_true (leb x y).

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

  Theorem leb_trans : Transitive le.
  Proof.
    unfold Transitive. intros.
    unfold le, is_true, leb, is_le, cmp in *.
    induction n. inversion x.
    destruct x using fin_Sn_inv;
    destruct y using fin_Sn_inv;
    destruct z using fin_Sn_inv;
    simpl in *; unfold fin_compare in *;
    simpl in *; auto;
    repeat rewrite fin_to_nat_Sn.
    - reflexivity.
    - rewrite fin_to_nat_Sn in H.
      simpl in H. inversion H.
    - rewrite fin_to_nat_Sn in H0.
      simpl in H0. inversion H0.
    - apply (IHn0 x y z).
        repeat rewrite fin_to_nat_Sn in H.
        simpl in H. apply H.
      repeat rewrite fin_to_nat_Sn in H0.
      simpl in H0. apply H0.
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
    apply FS_inj in eq. assumption.
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

Lemma map_fin_expand_rewrite : forall {m : nat} {newi unh act inact hnd},
  NoDup (newi :: map (@fin_expand m) (unh ++ act ++ inact ++ hnd))
    -> NoDup ((newi :: map (@fin_expand m) unh) ++
               map fin_expand act ++ map fin_expand inact ++
               map fin_expand hnd).
Proof.
  intros.
  repeat rewrite map_app in H.
  rewrite <- app_comm_cons. assumption.
Qed.
