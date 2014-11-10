Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrfun.
Require Import Ssreflect.ssrbool.
Require Import Ssreflect.eqtype.
Require Import Ssreflect.seq.
Require Import Ssreflect.ssrnat.
Require Import Ssreflect.fintype.

Notation fin := ordinal.

Inductive Void : Type :=.

Section Vector.

Variable A : Type.

Definition Vec : nat -> Type :=
  fix vec n := match n return Type with
               | O   => Void
               | S O => A
               | S n => prod A (vec n)
               end.

Definition vsing (x : A) : Vec 1.
Proof. apply x. Defined.

Definition vcons {n} (x : A) (v : Vec n) : Vec n.+1.
Proof. case: n => [|n] in v *; [ exact: x | exact: (x, v) ]. Defined.

Definition fin_contra : forall {x}, fin 0 -> x.
Proof. by move=> x; case=> m; move/eqP: (ltn0 m) => Hcontra //. Defined.

Definition fin_rect {n} : forall (P : fin n.+1 -> Type),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : fin n.+1), P x.
Proof.
  move=> P Hz HSn; case=> m H.
  elim: m => [|m IHm] in H *.
    exact: Hz.
  exact/HSn/IHm.
Defined.

Definition fin_rec {n} : forall (P : fin n.+1 -> Set),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : fin n.+1), P x := [eta fin_rect].

Definition fin_ind {n} : forall (P : fin n.+1 -> Prop),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : fin n.+1), P x := [eta fin_rect].

Definition vec_rect : forall (P : forall {n}, Vec n -> Type),
  (forall x : A, P (vsing x))
    -> (forall {n} (x : A) (v : Vec n), P v -> P (vcons x v))
    -> forall {n} (v : Vec n), P v.
Proof.
  move=> P Hsing Hcons n v.
  elim: n => [|n IHn] in Hsing Hcons v *.
    contradiction.
  simpl in v.
  case: n => [|n] in v IHn *; first exact: Hsing.
  move: v => [x v].
  exact: (Hcons n.+1 x v (IHn Hsing Hcons v)).
Defined.

Definition vec_rec : forall (P : forall {n}, Vec n -> Set),
  (forall x : A, P (vsing x))
    -> (forall {n} (x : A) (v : Vec n), P v -> P (vcons x v))
    -> forall {n} (v : Vec n), P v := [eta vec_rect].

Definition vec_ind : forall (P : forall {n}, Vec n -> Prop),
  (forall x : A, P (vsing x))
    -> (forall {n} (x : A) (v : Vec n), P v -> P (vcons x v))
    -> forall {n} (v : Vec n), P v := [eta vec_rect].

(* Extract Inductive Vec => "[]" ["[]" "(\x _ xs -> (x:xs))"]. *)

(* Extract Inlined Constant V.hd      => "(const Prelude.head)". *)
(* Extract Inlined Constant V.last    => "(const Prelude.last)". *)
(* Extract Inlined Constant V.tl      => "(const Prelude.tail)". *)
(* Extract Inlined Constant V.shiftin => "(const Data.List.(:))". *)
(* Extract Inlined Constant V.const   => "(const Prelude.repeat)". *)
(* Extract Inlined Constant V.append  => "(\_ _ -> Prelude.(++))". *)
(* Extract Inlined Constant V.map     => "(const Prelude.map)". *)
(* Extract Inlined Constant V.nth     => "(const Prelude.nth)". *)

Definition vrcons {n} (v : Vec n) (i : A) : Vec n.+1.
Proof.
  elim/vec_rect: v => [x|sz x xs IHxs].
    exact: (x, i).
  exact: (x, IHxs).
Defined.

Definition foldl_with_index
  {B : Type} {n} (f : nat -> B -> A -> B) (b : B) (v : Vec n) : B.
Proof.
  elim/vec_rect: v => [x|sz x ? IHxs].
    exact: (f n b x).
  exact: (f (n - sz) IHxs x).
Defined.

Definition replace {n} (v : Vec n) (p : fin n) (i : A) : Vec n.
Proof.
  elim/vec_rect: v => [_|? x xs IHxs] in p *.
    exact: (vsing i).
  elim/@fin_rect: p => [_|p ? _].
    exact: (vcons i xs).
  exact: (vcons x (IHxs (@Ordinal _ p _))).
Defined.

Definition vnth {n} (v : Vec n) (p : fin n) : A.
Proof.
  elim/vec_rect: v => [x|? x _ IHxs] in p *; first exact: x.
  elim/@fin_rect: p => [_|p ? _]; first exact: x.
  exact: (IHxs (@Ordinal _ p _)).
Defined.

Definition shiftin {n} (v : Vec n) (i : A) : Vec n.+1.
Proof.
  elim/vec_rect: v => [x|? x ? IHxs].
    exact: (x, i).
  exact: (x, IHxs).
Defined.

Definition vapp {n m} (v : Vec n) (u : Vec m) : Vec (n + m).
Proof.
  elim/vec_rect: v => [x|? x _ IHxs];
    [ exact: (vcons x u) | exact: (vcons x IHxs) ].
Defined.

Lemma vapp_cons : forall n i (v : Vec n),
  vcons i v = vapp (vsing i) v.
Proof. move=> n i; elim/vec_ind=> //. Qed.

Lemma vnth_cons0 : forall n i (v : Vec n) H,
  vnth (vcons i v) (@Ordinal n.+1 0 H) = i.
Proof. move=> n i; elim/vec_ind=> //. Qed.

Definition widen_id {n} := widen_ord (leqnSn n).
Arguments widen_id [n] i /.

Lemma vnth_consn : forall n i (v : Vec n) m, forall H: m < n,
  vnth (vcons i v) (@Ordinal n.+1 m.+1 H) = vnth v (@Ordinal n m H).
Proof. move=> n i; elim/vec_ind=> //. Qed.

Lemma vrcons_cons : forall n z (v : Vec n) i,
  vrcons (vcons z v) i = vcons z (vrcons v i).
Proof. move=> n i; elim/vec_ind=> //. Qed.

Lemma vnth_rcons : forall n m i (v : Vec n) H,
  vnth (vrcons v i) (@Ordinal n.+1 m (ltnW H)) = vnth v (@Ordinal n m H).
Proof.
  move=> n m i v H.
  elim/vec_ind: v => [x|? x xs IHxs] in m H *.
    by case: m => // in H *.
  rewrite vrcons_cons.
  case: m => [|m] in H IHxs *.
    by rewrite !vnth_cons0.
  rewrite !vnth_consn -IHxs.
  congr (vnth _ (Ordinal _)).
  exact: eq_irrelevance.
Qed.

Lemma shiftin_cons : forall n z (v : Vec n) i,
  shiftin (vcons z v) i = vcons z (shiftin v i).
Proof. move=> n z; by elim/vec_ind. Qed.

Lemma vnth_last : forall n (i : A) (v : Vec n),
  vnth (shiftin v i) ord_max = i.
Proof.
  move=> n i.
  elim/vec_ind=> // [sz x xs IHxs].
  rewrite shiftin_cons vnth_consn.
  have ->: Ordinal (n:=sz.+1) (m:=sz) (ltnSn sz.+1) = ord_max.
    congr (Ordinal _).
    exact: eq_irrelevance.
  exact: IHxs.
Qed.

Lemma replace_cons0 n (k : fin n.+1) : forall i (v : Vec n) z,
  k == ord0 -> replace (vcons i v) k z = vcons z v.
Proof.
  move=> i v z H.
  elim/vec_ind: v => [x|sz x xs IHxs] in k H *;
  by elim/@fin_ind: k => // in H *.
Qed.

Lemma replace_consn : forall n m i (v : Vec n) z, forall H: m < n,
  replace (vcons i v) (@Ordinal n.+1 m.+1 H) z
    = vcons i (replace v (@Ordinal n m H) z).
Proof. move=> n m i; elim/vec_ind=> //. Qed.

Lemma vnth_replace : forall n (v : Vec n) k z,
  vnth (replace v k z) k = z.
Proof.
  move=> n v k z.
  elim/vec_ind: v => // [sz x xs IHxs] in k *.
  elim/@fin_ind: k => [H|k ? IHk].
    rewrite replace_cons0; last by [].
    by rewrite vnth_cons0.
  by rewrite replace_consn vnth_consn IHxs.
Qed.

Lemma fin1_eq : forall (j k : fin 1), j == k.
Proof.
  elim/@fin_ind=> [Hj|j Hj IHj].
    elim/@fin_ind=> [Hk|k Hk IHk].
      by [].
    discriminate.
  discriminate.
Qed.

Lemma vnth_replace_neq : forall n (v : Vec n) (k j : fin n) (z : A),
  k != j -> vnth (replace v k z) j = vnth v j.
Proof.
  move=> n v k j z.
  elim/vec_ind: v => // [x|sz x xs IHxs] in k j *.
    by move: (fin1_eq k j) => /eqP ? /eqP ?.
  elim/@fin_ind: k; elim/@fin_ind: j;
    try by elim: sz => // in xs IHxs *.
  move=> ? ? _ ? ? _ Hneg.
  rewrite replace_consn !vnth_consn IHxs; first by [].
  exact: Hneg.
Qed.

Definition vnth_shiftin {n} : forall k (z : A) (v : Vec n),
  vnth (shiftin v z) (widen_id k) = vnth v k.
Proof.
  move=> k z v.
  elim/vec_ind: v => [x|sz x xs IHxs] in k *.
    rewrite /shiftin /=.
    by elim/@fin_ind: k => //.
  rewrite shiftin_cons.
  elim/@fin_ind: k => [Hk|k Hk IHk].
    have ->: Hk = ltn0Sn sz by exact: eq_irrelevance.
    by rewrite /widen_id /widen_ord /= !vnth_cons0.
  rewrite !vnth_consn -IHxs.
  congr (vnth _ (Ordinal _)).
  exact: eq_irrelevance.
Qed.

End Vector.

Module VectorSpec.

Arguments vsing [A] _.
Arguments vcons [A n] _ _.
Arguments foldl_with_index [A B n] f b v.
Arguments replace [A n] v p i.
Arguments vnth [A n] v p.
Arguments vapp [A n m] v u.

Example flwi_check :
  foldl_with_index (fun i acc x => (i, x) :: acc) nil
    (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
    == [:: (1, 1); (2, 2); (3, 3); (4, 4); (5, 5)].
Proof. reflexivity. Qed.

Lemma _2_ltn_5 : 2 < 5. Proof. by []. Qed.

Example replace_check :
  replace (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
          (@Ordinal 5 2 _2_ltn_5) 6
    = (vcons 1 (vcons 2 (vcons 6 (vcons 4 (vsing 5))))).
Proof. reflexivity. Qed.

Lemma _3_ltn_5 : 3 < 5. Proof. by []. Defined.

Example vnth_check :
  vnth (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
       (@Ordinal 5 3 _3_ltn_5) == 4.
Proof. reflexivity. Qed.

Example vapp_check :
  vapp (vcons 1 (vsing 2))
       (vcons 3 (vcons 4 (vsing 5))) ==
  vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))).
Proof. reflexivity. Qed.

End VectorSpec.
