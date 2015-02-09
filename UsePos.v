Require Import LinearScan.Lib.

Require Import Coq.Sorting.Sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
    uloc   : nat;
    regReq : bool
}.

Coercion uloc : UsePos >-> nat.

Module UsePosNotations.
Notation " (| x |) " := {| uloc := x; regReq := false |}.
Notation " (! x !) " := {| uloc := x; regReq := true |}.
End UsePosNotations.

Definition upos_lt (x y : UsePos) : bool := uloc x < uloc y.
Arguments upos_lt x y /.

Definition upos_ge (x y : UsePos) : bool := ~~ upos_lt x y.
Arguments upos_ge x y /.

Program Instance upos_lt_trans : Transitive upos_lt.
Obligation 1. exact: (ltn_trans H). Qed.

Definition head_or x xs := head x [seq uloc u | u <- xs].
Arguments head_or x xs /.

Definition last_or x xs := last x [seq uloc u | u <- xs].
Arguments last_or x xs /.

Section EqUpos.

Variables (T : eqType) (x0 : T).
Implicit Type s : UsePos.

Fixpoint equpos s1 s2 {struct s2} :=
  match s1, s2 with
  | {| uloc := u1; regReq := rr1 |},
    {| uloc := u2; regReq := rr2 |} => (u1 == u2) && (rr1 == rr2)
  end.

Lemma equposP : Equality.axiom equpos.
Proof.
  move.
  case=> [u1 rr1].
  case=> [u2 rr2] /=.
  case: (u1 =P u2) => [<-|neqx]; last by right; case.
  case: (rr1 =P rr2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical upos_eqMixin := EqMixin equposP.
Canonical upos_eqType := Eval hnf in EqType UsePos upos_eqMixin.

Lemma equposE : equpos = eq_op. Proof. by []. Qed.

Definition UsePos_eqType (A : eqType) :=
  Equality.Pack upos_eqMixin UsePos.

End EqUpos.

Lemma all_leq : forall x y xs,
  all (fun u : UsePos => y <= u) xs -> x <= y
    -> all (fun u : UsePos => x <= u) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    exact: (leq_trans H3 _).
  exact: IHzs.
Qed.

Lemma all_leq_ltn : forall x y xs,
  all (fun u : UsePos => y <= u) xs -> x < y
    -> all (fun u : UsePos => x < u) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    exact: (leq_trans H3 _).
  exact: IHzs.
Qed.

Lemma all_ltn_leq : forall x y xs,
  all (fun u : UsePos => y < u) xs -> x <= y
    -> all (fun u : UsePos => x <= u) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    apply: (leq_trans H3 _).
    exact/ltnW.
  exact: IHzs.
Qed.

Lemma all_ltn : forall x y xs,
  all (fun u : UsePos => u < y) xs -> y <= x
    -> all (fun u : UsePos => u < x) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    exact: (ltn_leq_trans H1 _).
  exact: IHzs.
Qed.

Lemma all_last : forall x xs before,
  x < before
    -> all (fun y : UsePos => uloc y < before) xs
    -> last_or x xs < before.
Proof.
  move=> x xs before Hlt Hall.
  elim: xs => //= [y ys IHys] in x Hlt Hall *.
  move/andP: Hall => [H1 H2].
  exact: IHys.
Qed.

Lemma all_head : forall x xs before,
  before <= x
    -> all (fun y : UsePos => before <= uloc y) xs
    -> before <= head_or x xs.
Proof.
  move=> x xs before Hlt Hall.
  case: xs => //= [y ys] in x Hlt Hall *.
  move/andP: Hall => [H1 H2] //.
Qed.

Lemma head_last : forall x xs before,
  StronglySorted upos_lt (x :: xs)
    -> last_or x xs < before
    -> x < head_or before xs.
Proof.
  move=> x xs before Hsort Hlast.
  inv Hsort.
  elim: xs => //= [y ys IHys] in x H1 H2 Hlast *.
  by inv H2.
Qed.

Lemma last_rcons_upos : forall (b : nat) x (l1 : seq UsePos),
  last b [seq uloc u | u <- rcons l1 x] = x.
Proof. by move=> b x l1; elim: l1 b => //=. Qed.

Lemma last_cat_upos : forall (b : nat) x (xs l1 : seq UsePos),
  last b [seq uloc u | u <- l1 ++ x :: xs] =
  last b [seq uloc u | u <- x :: xs].
Proof.
  move=> b x xs l1.
  elim: xs => /= [|y ys IHys] in x l1 *.
    by rewrite cats1 last_rcons_upos.
  by rewrite -(IHys y l1) -cat1s catA cats1 !IHys.
Qed.

Lemma last_cons_upos : forall (b : nat) x y (xs : seq UsePos),
  last b [seq uloc u | u <- x :: y :: xs] =
  last b [seq uloc u | u <- y :: xs].
Proof. by move=> b x y; elim=> //= [z zs IHzs]. Qed.

Lemma span_all (l : list UsePos) : forall (x : nat) l1 l2,
  StronglySorted upos_lt l
    -> (l1, l2) = span (fun y => uloc y < x) l
    -> all (fun y => uloc y < x) l1 && all (fun y => x <= uloc y) l2.
Proof.
  move=> p l1 l2 Hsort Heqe.
  elim: l => /= [|x xs IHxs] in l1 l2 Hsort Heqe *.
    by inv Heqe.
  case E: (x < p) in Heqe *.
    inv Hsort.
    case: (span _ xs) => [l1' l2'] in Heqe IHxs *.
    move: (IHxs l1' l2' H1 refl_equal) => /andP [? ?].
    apply/andP; split.
      inv Heqe.
      by apply/andP; split.
    by inv Heqe.
  inv Hsort; inv Heqe.
  clear IHxs H1.
  move/negbT: E.
  rewrite -leqNgt => Hle.
  apply/andP; split=> //.
  move/Forall_all in H2.
  exact: (all_ltn_leq H2).
Qed.

Lemma last_ltn : forall (z y : nat) (xs : seq nat) (n : nat),
  last z xs < n -> y <= z -> last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma Forall_last_ltn : forall (y : UsePos) (ys : seq UsePos) (n : nat),
  last (uloc y) [seq uloc u | u <- ys] < n
    -> List.Forall (fun x : UsePos => y < x) ys -> y < n.
Proof.
  move=> y.
  elim=> //= [z zs IHzs] n Hlast.
  invert; subst.
  apply: IHzs => //.
  move/ltnW in H1.
  exact (last_ltn Hlast H1).
Qed.

Lemma last_leq : forall (z y : nat) (xs : seq nat) (n : nat),
  last z xs <= n -> y <= z -> last y xs <= n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_trans IHxs _.
Qed.
