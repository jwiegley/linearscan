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

Definition vnth_last {A : Type} {n} : forall (x : A) v,
  vnth (V.shiftin x v) (@ord_max n) = x.
Proof.
  move=> x; rewrite /vnth /=.
  elim=> [|v vn vs IHvs] //=.
  have ->: Lt.lt_S_n vn vn.+1 (ltP (ltnSn vn.+1)) = ltP (ltnSn vn)
    by exact: le_irrelevance.
  by [].
Qed.

Definition fin_ind {n} : forall (P : 'I_n.+1 -> Prop),
  P ord0
    -> (forall m, P (inord m) -> P (inord m.+1))
    -> forall (f : 'I_n.+1), P f.
Proof.
  move=> nP Hbase Hind.
Admitted.
(*   case; case: n => [|n] //=. *)
(*   elim=> [|m IHm] H. *)
(*     rewrite /ord0 in Hbase. *)
(*     have <-: ltn0Sn n = H by exact: eq_irrelevance. *)
(*     exact: Hbase. *)
(*   set v := Ordinal _. *)
(*   have <-: inord m.+1 = v by rewrite (inord_val v). *)
(*   move=> {Hbase v}. *)
(*   apply: Hind. *)
(*   have H1: m < n.+1 by exact: ltnW. *)
(*   move: IHm {H}. *)
(*   move/(_ H1). *)
(*   set v := Ordinal _. *)
(*   have ->: inord m = v by rewrite (inord_val v). *)
(*   exact. *)
(* Qed. *)

Definition vnth_shiftin {A : Type} {n} : forall i (x : A) xs,
  vnth (V.shiftin x xs) (widen_ord (leqnSn n) i) = vnth xs i.
Proof.
  move=> i x xs.
  elim: xs i => *.
    admit.
Admitted.
(*   case: n => [|n] in i xs *. *)
(*     exact: fin_contra. *)
(*   elim/(@fin_ind n): i => [y|y IHy] /= in xs *. *)
(*     admit. *)
  
(*   rewrite IHns. *)
(* Admitted. *)