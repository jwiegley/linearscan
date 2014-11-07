Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.VectorSpec.

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

Notation fin := ordinal.
Notation vfin := Coq.Vectors.Fin.t.

Definition vfin_contra : forall {x}, vfin 0 -> x.
Proof. by move=> x v; inversion v. Defined.

Definition fin_contra : forall {x}, fin 0 -> x.
Proof.
  move=> x; case=> m.
  by move/eqP: (ltn0 m) => Hcontra //.
Defined.

Definition to_vfin {n} (x : fin n) : vfin n :=
  let: Ordinal m H := x in @Fin.of_nat_lt m n (ltP H).

Coercion to_vfin : fin >-> vfin.

Fixpoint from_vfin {n} (x : vfin n) : fin n :=
  match x with
  | Fin.F1 _    => ord0
  | Fin.FS _ x' => inord (from_vfin x').+1
  end.

Theorem fin_vfin_spec : forall n (x : fin n), from_vfin (to_vfin x) = x.
Proof.
  move=> n; case.
  elim=> [|m IHm] H /=.
    case: n => [|n] // in H *.
    rewrite /= /ord0.
    by have ->: ltn0Sn n = H by exact: eq_irrelevance.
  case: n => [|n] //= in IHm H *.
Admitted.

Theorem vfin_fin_spec : forall n (x : vfin n), to_vfin (from_vfin x) = x.
Proof.
  move=> n x.
  elim: x => [|x xs IHxs] //=.
Admitted.

Lemma widen_vfin n : forall i,
  to_vfin (widen_ord (leqnSn n) i) = Fin.L_R 1 (to_vfin i).
Proof.
  elim: n => [|n IHn] i.
    exact: fin_contra.
(*   rewrite (widen_vfin n _). *)
(*   Qed. *)
(*   have H1: m < n.+1 by exact: ltnW. *)
(*   case=> [|m] H; *)
(*     first by case: n => // in H IHn *. *)
(* Qed. *)
(*   have H1: m < n by exact: ltnW. *)
(*   move: IHm; move/(_ H1) => IHm. *)
(*   apply (widen_vfin n). *)
(* Qed. *)
(*   case: n => // [n] in H IHm * *)
(*   congr (Fin.FS _). *)
Admitted.

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
  rewrite -(@V.shiftin_nth A x n xs i i); last by [].
  congr (V.nth _ _) => {x xs}.
  exact: widen_vfin.
Qed.