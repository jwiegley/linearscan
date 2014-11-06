Require Import Coq.Vectors.Vector.

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

Definition fin_contra : forall {x}, fin 0 -> x.
Proof.
  move=> x; case=> m.
  by move/eqP: (ltn0 m) => Hcontra //.
Defined.

Definition to_vfin {n} (x : fin n) : vfin n.
Proof.
  case: n x => [H|n [m Hm]].
    exact: fin_contra.
  exact/(@Coq.Vectors.Fin.of_nat_lt m)/ltP.
Defined.

Coercion to_vfin : fin >-> vfin.

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

Lemma nth_replace : forall A n v i (x : A), vnth (@replace A n v i x) i = x.
Proof.
Admitted.
