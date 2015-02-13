Require Import LinearScan.Ssr.

Section Vector.

Variable A : Type.

Definition Vec : nat -> Type :=
  fix vec n := match n return Type with
               | O   => unit
               | S n => prod A (vec n)
               end.

Definition vnil : Vec 0 := tt.

Definition vsing (x : A) : Vec 1 := (x, tt).

Definition vcons {n} (x : A) (v : Vec n) : Vec n.+1 := (x, v).

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

Definition vec_rect : forall (P : forall {n}, Vec n -> Type),
  P vnil
    -> (forall {n} (x : A) (v : Vec n), P v -> P (vcons x v))
    -> forall {n} (v : Vec n), P v.
Proof.
  move=> P Hnil Hcons n v.
  elim: n => [|n IHn] in Hnil Hcons v *.
    case: v; exact: Hnil.
  case: v => *; exact/Hcons/IHn.
Defined.

Definition vecn_rect : forall (P : forall {n}, Vec n -> Type),
  (forall x : A, P (vsing x))
    -> (forall {n} (x : A) (v : Vec n.+1), P v -> P (vcons x v))
    -> forall {n} (v : Vec n.+1), P v.
Proof.
  move=> P Hsing Hcons n v.
  elim: n => [|n IHn] in Hsing Hcons v *.
    case: v => a b; case: b; exact: Hsing.
  case: v => *; exact/Hcons/IHn.
Defined.

Definition vfoldl_with_index
  {B : Type} {n} (f : 'I_n -> B -> A -> B) (b : B) (v : Vec n) : B.
Proof.
  case: n => [//|n] in f v *.
  elim/vecn_rect: v => [x|sz x xs IHxs].
    exact: (f (inord n) b x).
  exact: (f (inord (n - sz.+1)) IHxs x).
Defined.

Definition vfoldl {B : Type} {n} (f : B -> A -> B) (b : B) (v : Vec n) : B :=
  vfoldl_with_index (fun _ => f) b v.

Definition vconst {n} (i : A) : Vec n.
Proof.
  elim: n => [|n IHn]; [ exact: vnil | exact: (vcons i IHn) ].
Defined.

Definition vreplace {n} (v : Vec n) (p : 'I_n) (i : A) : Vec n.
Proof.
  case: n => [|n] in v p *;
    first exact: fin_contra.
  elim/vecn_rect: v => [x|? x xs IHxs] in p *.
    exact: (vsing i).
  elim/@fin_rect: p => [_|p ? _].
    exact: (vcons i xs).
  exact: (vcons x (IHxs (@Ordinal _ p _))).
Defined.

Definition vnth {n} (v : Vec n) (p : 'I_n) : A.
Proof.
  case: n => [|n] in v p *;
    first exact: fin_contra.
  elim/vecn_rect: v => [x|? x _ IHxs] in p *; first exact: x.
  elim/@fin_rect: p => [_|p ? _]; first exact: x.
  exact: (IHxs (@Ordinal _ p _)).
Defined.

Definition vshiftin {n} (v : Vec n) (i : A) : Vec n.+1.
Proof.
  elim/vec_rect: v => [|? x ? IHxs]; [ exact: (vsing i) | exact: (x, IHxs) ].
Defined.

Definition vapp {n m} (v : Vec n) (u : Vec m) : Vec (n + m).
Proof.
  elim/vec_rect: v => [|? x _ IHxs]; [ exact: u | exact: (vcons x IHxs) ].
Defined.

Definition widen_id {n} := widen_ord (leqnSn n).

End Vector.

Definition vmap {A B : Type} {n} (f : A -> B) (v : Vec A n) : Vec B n.
Proof.
  elim: n => // [n IHn] in v *.
  elim/vecn_rect: v => [x|sz x xs IHxs] in IHn *.
    exact: (vsing _ (f x)).
  exact: (vcons _ (f x) (IHxs IHn)).
Defined.

Module VectorSpec.

Arguments vsing [A] _ /.
Arguments vcons [A n] _ _ /.
Arguments vconst [A n] !i.
Arguments vfoldl_with_index [A B n] f !b !v.
Arguments vfoldl [A B n] f !b !v.
Arguments vreplace [A n] !v !p !i.
Arguments vnth [A n] !v !p.
Arguments vapp [A n m] !v !u.
Arguments vshiftin [A n] !v !i.
Arguments vmap [A B n] f !v.

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

Extract Constant Vec "a" => "[]".
Extraction Inline Vec.

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
  => "(LinearScan.Utils.vfoldl'_with_index)".
