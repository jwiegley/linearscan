Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.VectorSpec.

Lemma to_nat_of_nat {p}{n} (h : p < n) :
  Fin.to_nat (Fin.of_nat_lt h) = exist _ p h.
Proof.
 revert n h.
 induction p;
 (destruct n ; intros h; [ destruct (Lt.lt_n_O _ h) | simpl]);
 try rewrite (IHp _ (Lt.lt_S_n p n h));
 f_equal; apply Peano_dec.le_unique.
Qed.

Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrfun.
Require Import Ssreflect.ssrbool.
Require Import Ssreflect.eqtype.
Require Import Ssreflect.seq.
Require Import Ssreflect.ssrnat.
Require Import Ssreflect.fintype.

Module V := Coq.Vectors.Vector.
Notation Vec := V.t.

(* Extract Inductive Vec => "[]" ["[]" "(\x _ xs -> (x:xs))"]. *)

(* Extract Inlined Constant V.hd      => "(const Prelude.head)". *)
(* Extract Inlined Constant V.last    => "(const Prelude.last)". *)
(* Extract Inlined Constant V.tl      => "(const Prelude.tail)". *)
(* Extract Inlined Constant V.shiftin => "(const Data.List.(:))". *)
(* Extract Inlined Constant V.const   => "(const Prelude.repeat)". *)
(* Extract Inlined Constant V.append  => "(\_ _ -> Prelude.(++))". *)
(* Extract Inlined Constant V.map     => "(const Prelude.map)". *)
(* Extract Inlined Constant V.nth     => "(const Prelude.nth)". *)

Notation fin  := ordinal.
Notation vfin := Coq.Vectors.Fin.t.

Definition vfin_contra : forall {x}, vfin 0 -> x.
Proof. by move=> x v; inversion v. Defined.

Definition fin_contra : forall {x}, fin 0 -> x.
Proof. by move=> x; case=> m; move/eqP: (ltn0 m) => Hcontra //. Defined.

Definition to_vfin {n} (x : fin n) : vfin n :=
  let: Ordinal m H := x in @Fin.of_nat_lt m n (ltP H).

Definition from_vfin {n} (x : vfin n) : fin n :=
  let: exist m H := Fin.to_nat x in @Ordinal n m (introT ltP H).

Theorem fin_vfin_spec : forall n (x : fin n), from_vfin (to_vfin x) = x.
Proof.
  rewrite /from_vfin /to_vfin.
  move=> n; case=> m H.
  rewrite to_nat_of_nat.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Theorem vfin_fin_spec : forall n (x : vfin n), to_vfin (from_vfin x) = x.
Proof.
  rewrite /from_vfin /to_vfin.
  move=> n; elim=> [m|m ms IHm] //=.
  rewrite -[X in Fin.FS X]IHm.
  case: (Fin.to_nat ms) => o H /=.
  congr (Fin.FS (Fin.of_nat_lt _)).
  exact: Peano_dec.le_unique.
Qed.

(* Definition fin_ind : forall n (H : 0 < n) (P : forall {n}, fin n -> Type), *)
(*   P (@Ordinal n 0 H) *)
(*     -> (forall m (H : m.+1 < n), *)
(*           P (@Ordinal n m (ltnW H)) -> P (@Ordinal n m.+1 H)) *)
(*     -> forall m (H : m < n), P (@Ordinal n m H). *)

Lemma L_R_FS : forall n (x : vfin n),
  Fin.L_R 1 (Fin.FS x) = Fin.FS (Fin.L_R 1 x).
Proof. by case. Qed.

Definition widen_vfin {n} (x : vfin n) :
  Fin.L_R 1 x = to_vfin (widen_ord (leqnSn n) (from_vfin x)).
Proof.
  elim: x => // [m x IHx].
  rewrite L_R_FS {}IHx.
Admitted.

Definition widen_fin {n} (x : fin n) :
  widen_ord (leqnSn n) x = from_vfin (Fin.L_R 1 (to_vfin x)).
Proof. by rewrite widen_vfin !fin_vfin_spec. Defined.

Definition fold_left_with_index {A B : Type} {n} (f : fin n -> B -> A -> B) :
  forall (b : B) (v : Vec A n), B.
  intros b v.
  induction v.
    apply b.
  apply IHv.
  intros. apply X0.
Defined.

Definition replace {A : Type} {n} v i := @V.replace A _ v (@to_vfin n i).

Definition vnth {A : Type} {n} v i := @V.nth A _ v (@to_vfin n i).

Lemma vnth_last {A : Type} {n} : forall (x : A) v,
  vnth (V.shiftin x v) (@ord_max n) = x.
Proof.
  move=> ?; rewrite /vnth /=.
  elim=> [|? vn ? ?] //=.
  have ->: Lt.lt_S_n vn vn.+1 (ltP (ltnSn vn.+1)) = ltP (ltnSn vn)
    by exact: le_irrelevance.
  by [].
Qed.

Lemma vnth_replace {A : Type} : forall n (v : Vec A n) k x,
  vnth (replace v k x) k = x.
Proof.
  move=> n v k x.
Admitted.

Lemma vnth_replace_neq {A : Type} : forall n (v : Vec A n) k j x,
  k != j -> vnth (replace v k x) j = vnth v j.
Admitted.

Definition vnth_shiftin {A : Type} {n} : forall i (x : A) xs,
  vnth (V.shiftin x xs) (widen_ord (leqnSn n) i) = vnth xs i.
Proof.
  move=> i x xs; rewrite /vnth.
  rewrite -(@V.shiftin_nth A x n xs (to_vfin i) (to_vfin i)); last by [].
  congr (V.nth _ _) => {x xs}.
  by rewrite widen_fin vfin_fin_spec.
Qed.

Coercion to_vfin : fin >-> vfin.
(* Coercion from_vfin : vfin >-> fin. *)
