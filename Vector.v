Require Import Fin.

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Init.Logic.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Vectors.Vector.

Open Scope nat_scope.

Module V := Coq.Vectors.Vector.
Definition Vec := V.t.

Module Import VN := Vector.VectorNotations.
Module Import EQ := EqNotations.

Definition relocate {A n} (v : Vec A n) (p q : fin n) : Vec A n :=
  V.replace v q (V.nth v p).

Definition fold_left_with_index {A B : Type} {n} (f : fin n -> B -> A -> B)
  : forall (b : B) (v : Vec A n), B.
  intros b v.
  induction v.
    apply b.
  apply IHv.
  intros.
  apply fin_expand in H.
  apply (f H X X0).
Defined.
