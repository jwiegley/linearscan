Require Import Coq.Vectors.Vector.

Require Export Ssreflect.ssreflect.
(* Require Export Ssreflect.ssrfun. *)
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrnat.
Require Export Ssreflect.fintype.

Module V := Coq.Vectors.Vector.
Definition Vec := V.t.

Definition fin := ordinal.
Definition vfin := Coq.Vectors.Fin.t.

Definition fin_contra : forall {x}, fin 0 -> x.
Proof.
  move=> x; case=> m.
  by move/eqP: (ltn0 m) => Hcontra //.
Defined.

Definition to_vfin {n} (x : fin n) : vfin n.
Proof.
  case: n x => [H|n [m Hm]].
    exact: fin_contra.
  by apply/(@Coq.Vectors.Fin.of_nat_lt m)/ltP.
Defined.

Definition fold_left_with_index {A B : Type} {n} (f : fin n -> B -> A -> B) :
  forall (b : B) (v : Vec A n), B.
  intros b v.
  induction v.
    apply b.
  apply IHv.
  intros. apply X0.
Defined.
