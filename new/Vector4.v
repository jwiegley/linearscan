Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrfun.
Require Import Ssreflect.ssrbool.
Require Import Ssreflect.eqtype.
Require Import Ssreflect.seq.
Require Import Ssreflect.ssrnat.
Require Import Ssreflect.fintype.
Require Import ssrtuple.

Section Vector.

Variable T : Type.

Definition vnil : 0.-tuple T := [tuple].

Definition vsing (x : T) : 1.-tuple T := in_tuple [:: x].

Definition vcons {n} (x : T) (n : n.-tuple T) := cons_tuple x n.

Definition fin_contra : forall {x}, 'I_0 -> x.
Proof. by move=> x; case=> m; move/eqP: (ltn0 m) => Hcontra //. Defined.

Definition fin_rect {n} : forall (P : 'I_n.+1 -> Type),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : 'I_n.+1), P x.
Proof.
  move=> P Hz HSn; case=> m H.
  elim: m => [|m IHm] in H *; [ exact: Hz | exact/HSn/IHm ].
Defined.

Definition fin_rec {n} : forall (P : 'I_n.+1 -> Set),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : 'I_n.+1), P x := [eta fin_rect].

Definition fin_ind {n} : forall (P : 'I_n.+1 -> Prop),
  (forall {H}, P (@Ordinal n.+1 0 H))
    -> (forall {m H}, P (@Ordinal n.+1 m (ltnW H))
          -> P (@Ordinal n.+1 m.+1 H))
    -> forall (x : 'I_n.+1), P x := [eta fin_rect].

Definition vec_rect : forall (P : forall {n}, n.-tuple T -> Type),
  P vnil
    -> (forall {n} (x : T) (v : n.-tuple T), P v -> P (vcons x v))
    -> forall {n} (v : n.-tuple T), P v.
Proof.
  move=> P Hnil Hcons n v.
  elim: n => [|n IHn] in Hnil Hcons v *.
    have ->: v = vnil by exact: tuple0.
    exact: Hnil.
  case v => tval i.
  
            ; exact/Hcons/IHn.
Defined.

Definition vec_rec : forall (P : forall {n}, n.-tuple -> Set),
  P vnil
    -> (forall {n} (x : T) (v : n.-tuple), P v -> P (vcons x v))
    -> forall {n} (v : n.-tuple), P v := [eta vec_rect].

Definition vec_ind : forall (P : forall {n}, n.-tuple -> Prop),
  P vnil
    -> (forall {n} (x : T) (v : n.-tuple), P v -> P (vcons x v))
    -> forall {n} (v : n.-tuple), P v := [eta vec_rect].

Definition vecn_rect : forall (P : forall {n}, n.-tuple -> Type),
  (forall x : T, P (vsing x))
    -> (forall {n} (x : T) (v : n.+1-tuple), P v -> P (vcons x v))
    -> forall {n} (v : n.+1-tuple), P v.
Proof.
  move=> P Hsing Hcons n v.
  elim: n => [|n IHn] in Hsing Hcons v *.
    case: v => a b; case: b; exact: Hsing.
  case: v => *; exact/Hcons/IHn.
Defined.

Definition vecn_rec : forall (P : forall {n}, n.-tuple -> Set),
  (forall x : T, P (vsing x))
    -> (forall {n} (x : T) (v : n.+1-tuple), P v -> P (vcons x v))
    -> forall {n} (v : n.+1-tuple), P v := [eta vecn_rect].

Definition vecn_ind : forall (P : forall {n}, n.-tuple -> Prop),
  (forall x : T, P (vsing x))
    -> (forall {n} (x : T) (v : n.+1-tuple), P v -> P (vcons x v))
    -> forall {n} (v : n.+1-tuple), P v := [eta vecn_rect].

Definition vrcons {n} (v : n.-tuple) (i : T) : n.+1-tuple
Proof.
  elim/vec_rect: v => [|sz x xs IHxs];
    [ exact: (vsing i) | exact: (vcons x IHxs) ].
Defined.

Definition vfoldl_with_index
  {B : Type} {n} (f : 'I_n -> B -> T -> B) (b : B) (v : n.-tuple) : B.
Proof.
  case: n => [//|n] in f v *.
  elim/vecn_rect: v => [x|sz x xs IHxs].
    exact: (f (inord n) b x).
  exact: (f (inord (n - sz.+1)) IHxs x).
Defined.

Definition vfoldl
  {B : Type} {n} (f : B -> T -> B) (b : B) (v : n.-tuple) : B :=
  vfoldl_with_index (fun _ => f) b v.

Definition vconst {n} (i : T) : n.-tuple
Proof.
  elim: n => [|n IHn]; [ exact: vnil | exact: (vcons i IHn) ].
Defined.

Definition vreplace {n} (v : n.-tuple) (p : 'I_n) (i : T) : n.-tuple
Proof.
  case: n => [|n] in v p *;
    first exact: fin_contra.
  elim/vecn_rect: v => [x|? x xs IHxs] in p *.
    exact: (vsing i).
  elim/@fin_rect: p => [_|p ? _].
    exact: (vcons i xs).
  exact: (vcons x (IHxs (@Ordinal _ p _))).
Defined.

Definition vnth {n} (v : n.-tuple) (p : 'I_n) : T.
Proof.
  case: n => [|n] in v p *;
    first exact: fin_contra.
  elim/vecn_rect: v => [x|? x _ IHxs] in p *; first exact: x.
  elim/@fin_rect: p => [_|p ? _]; first exact: x.
  exact: (IHxs (@Ordinal _ p _)).
Defined.

Definition vshiftin {n} (v : n.-tuple) (i : T) : n.+1-tuple
Proof.
  elim/vec_rect: v => [|? x ? IHxs]; [ exact: (vsing i) | exact: (x, IHxs) ].
Defined.

Definition vapp {n m} (v : n.-tuple) (u : m.-tuple) : Vec (n + m).
Proof.
  elim/vec_rect: v => [|? x _ IHxs]; [ exact: u | exact: (vcons x IHxs) ].
Defined.

Lemma vnth_cons0 : forall n i (v : n.-tuple) H,
  vnth (vcons i v) (@Ordinal n.+1 0 H) = i.
Proof. by move=> n i; elim/vec_ind. Qed.

Definition widen_id {n} := widen_ord (leqnSn n).

Lemma vnth_consn : forall n i (v : n.-tuple) m, forall H: m < n,
  vnth (vcons i v) (@Ordinal n.+1 m.+1 H) = vnth v (@Ordinal n m H).
Proof. by move=> n i; elim/vec_ind. Qed.

Lemma vrcons_cons : forall n z (v : n.-tuple) i,
  vrcons (vcons z v) i = vcons z (vrcons v i).
Proof. by move=> n i; elim/vec_ind. Qed.

Lemma vshiftin_cons : forall n z (v : n.-tuple) i,
  vshiftin (vcons z v) i = vcons z (vshiftin v i).
Proof. by move=> n z; elim/vec_ind. Qed.

Lemma vnth_last : forall n (i : T) (v : n.-tuple),
  vnth (vshiftin v i) ord_max = i.
Proof.
  move=> n i.
  elim/vec_ind=> // [sz x xs IHxs].
  rewrite vshiftin_cons vnth_consn.
  have ->: Ordinal (n:=sz.+1) (m:=sz) (ltnSn sz.+1) = ord_max.
    congr (Ordinal _).
    exact: eq_irrelevance.
  exact: IHxs.
Qed.

Lemma vreplace_cons0 n (k : 'I_n.+1) : forall i (v : n.-tuple) z,
  k == ord0 -> vreplace (vcons i v) k z = vcons z v.
Proof.
  move=> i v z H.
  elim/vec_ind: v => [|? ? ? _] in k H *;
  by elim/@fin_ind: k => // in H *.
Qed.

Lemma vreplace_consn : forall n m i (v : n.-tuple) z, forall H: m < n,
  vreplace (vcons i v) (@Ordinal n.+1 m.+1 H) z
    = vcons i (vreplace v (@Ordinal n m H) z).
Proof. by move=> n m i; elim/vec_ind. Qed.

Lemma vnth_vreplace : forall n (v : n.-tuple) k z,
  vnth (vreplace v k z) k = z.
Proof.
  move=> n v k z.
  case: n => [|n] in k v *;
    first exact: fin_contra.
  elim/vecn_ind: v => // [sz x xs IHxs] in k *.
  elim/@fin_ind: k => [H|k ? IHk].
    rewrite vreplace_cons0; last by [].
    by rewrite vnth_cons0.
  by rewrite vreplace_consn vnth_consn IHxs.
Qed.

Lemma fin1_eq : forall (j k : 'I_1), j == k.
Proof.
  elim/@fin_ind=> [?|? ? _];
  elim/@fin_ind=> [?|? ? _]; first by [];
  discriminate.
Qed.

Lemma vnth_vreplace_neq : forall n (v : n.-tuple) (k j : 'I_n) (z : T),
  k != j -> vnth (vreplace v k z) j = vnth v j.
Proof.
  move=> n v k j z.
  case: n => [|n] in k j v *;
    first exact: fin_contra.
  elim/vecn_ind: v => // [x|sz x xs IHxs] in k j *.
    by move: (fin1_eq k j) => /eqP ? /eqP ?.
  elim/@fin_ind: k; elim/@fin_ind: j;
    try by elim: sz => // in xs IHxs *.
  move=> ? ? _ ? ? _ Hneg.
  rewrite vreplace_consn !vnth_consn IHxs; first by [].
  exact: Hneg.
Qed.

Definition vnth_vshiftin {n} : forall k (z : T) (v : n.-tuple),
  vnth (vshiftin v z) (widen_id k) = vnth v k.
Proof.
  move=> k z v.
  case: n => [|n] in k v *;
    first exact: fin_contra.
  elim/vecn_ind: v => [x|sz x xs IHxs] in k *.
    rewrite /vshiftin /=.
    by elim/@fin_ind: k => //.
  rewrite vshiftin_cons.
  elim/@fin_ind: k => [Hk|? ? _].
    have ->: Hk = ltn0Sn sz by exact: eq_irrelevance.
    by rewrite vnth_cons0.
  rewrite !vnth_consn -IHxs.
  congr (vnth _ (Ordinal _)).
  exact: eq_irrelevance.
Qed.

End Vector.

Definition vmap {T B : Type} {n} (f : T -> B) (v : T.-tuple n) : B.-tuple n.
Proof.
  elim: n => // [n IHn] in v *.
  elim/vecn_rect: v => [x|sz x xs IHxs] in IHn *.
    exact: (vsing _ (f x)).
  exact: (vcons _ (f x) (IHxs IHn)).
Defined.

Module VectorSpec.

Arguments vsing [T] _ /.
Arguments vcons [T n] _ _ /.
Arguments vconst [T n] !i.
Arguments vfoldl_with_index [T B n] f !b !v.
Arguments vfoldl [T B n] f !b !v.
Arguments vreplace [T n] !v !p !i.
Arguments vnth [T n] !v !p.
Arguments vapp [T n m] !v !u.
Arguments vshiftin [T n] !v !i.
Arguments vmap [T B n] f !v.

Example flwi_check :
  map (fun x => (@nat_of_ord 5 (fst x), (snd x)))
      (vfoldl_with_index (fun i acc x => (i, x) :: acc) nil
         (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5))))))
    == [:: (0, 1); (1, 2); (2, 3); (3, 4); (4, 5)].
Proof. rewrite /= !inordK; by []. Qed.

Lemma _2_ltn_5 : 2 < 5. Proof. by []. Qed.

Example vreplace_check :
  vreplace (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
          (@Ordinal 5 2 _2_ltn_5) 6
    == (vcons 1 (vcons 2 (vcons 6 (vcons 4 (vsing 5))))).
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

Example const_check :
  vconst 42 = vcons 42 (vcons 42 (vcons 42 (vcons 42 (vsing 42)))).
Proof. reflexivity. Qed.

Example vmap_check :
  vmap (addn 2) (vcons 1 (vcons 2 (vcons 3 (vcons 4 (vsing 5)))))
    == (vcons 3 (vcons 4 (vcons 5 (vcons 6 (vsing 7))))).
Proof. reflexivity. Qed.

End VectorSpec.

Extract Inductive ordinal => "Prelude.Int" [""].

Extract Constant Vec "a" => "[a]".

Extract Inlined Constant vnil     => "[]".
Extract Inlined Constant vsing    => "[]".
Extract Inlined Constant vcons    => "(:)".
Extract Inlined Constant vshiftin => "LinearScan.Utils.snoc".
Extract Inlined Constant vreplace => "LinearScan.Utils.set_nth".
Extract Inlined Constant vec_rect => "LinearScan.Utils.list_rect".
Extract Inlined Constant vconst   => "Data.List.replicate".
Extract Inlined Constant vfoldl   => "LinearScan.Utils.vfoldl'".
Extract Inlined Constant vapp     => "Prelude.(++)".
Extract Inlined Constant vmap     => "LinearScan.Utils.vmap".
Extract Inlined Constant vnth     => "LinearScan.Utils.nth".

Extract Inlined Constant vfoldl_with_index
  => "(LinearScan.Utils.foldl'_with_index)".
