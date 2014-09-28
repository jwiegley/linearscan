(** ** Comparisons *)

(** These definitions avoid boilerplate involved with setting up properly
    behaved comparisons between types. *)

Lemma mk_compare_spec : forall {a} (x y : a)
  (cmp         : a -> a -> comparison)
  (cmp_eq_iff  : cmp x y = Eq <-> x = y)
  (cmp_gt_flip : cmp x y = Gt  -> cmp y x = Lt),
  CompSpec eq (fun x y => cmp x y = Lt) x y (cmp x y).
Proof.
  intros.
  destruct (cmp x y) eqn:Heqe.
  - apply CompEq. apply cmp_eq_iff. reflexivity.
  - apply CompLt. assumption.
  - apply CompGt. auto.
Defined.

Lemma mk_cmp_eq_dec : forall {a} (x y : a)
  (cmp        : a -> a -> comparison)
  (cmp_eq_iff : cmp x y = Eq <-> x = y),
  { x = y } + { x <> y }.
Proof.
  intros.
  destruct (cmp x y) eqn:Heqe.
  - left. apply cmp_eq_iff. reflexivity.
  - right. intuition. inversion H2.
  - right. intuition. inversion H2.
Defined.

Class CompareSpec (a : Set) := {
  cmp         : a -> a -> comparison;
  cmp_eq x y  := cmp x y = Eq;
  cmp_eq_iff  : forall x y, cmp x y = Eq <-> x = y;
  cmp_lt x y  := cmp x y = Lt;
  cmp_le x y  := cmp x y <> Gt;
  cmp_gt x y  := cmp x y = Gt;
  cmp_ge x y  := cmp x y <> Lt;
  cmp_gt_flip : forall x y, cmp_gt x y -> cmp_lt y x;

  cmp_spec x y : CompSpec eq cmp_lt x y (cmp x y) :=
    mk_compare_spec x y cmp (cmp_eq_iff x y) (cmp_gt_flip x y);

  cmp_eq_dec x y : { x = y } + { x <> y } :=
    mk_cmp_eq_dec x y cmp (cmp_eq_iff x y)
}.
