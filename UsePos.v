Require Import LinearScan.Lib.

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
  uloc      : nat;
  regReq    : bool;
  inputOnly : bool
}.

Coercion uloc : UsePos >-> nat.

Module UsePosNotations.
Notation " (| x |) " := {| uloc := x; regReq := false |}.
Notation " (! x !) " := {| uloc := x; regReq := true |}.
End UsePosNotations.

Definition upos_lt (x y : UsePos) : bool := uloc x < uloc y.
Arguments upos_lt x y /.

Definition upos_le (x y : UsePos) : bool := uloc x <= uloc y.
Arguments upos_le x y /.

Definition upos_ge (x y : UsePos) : bool := ~~ upos_lt x y.
Arguments upos_ge x y /.

Program Instance upos_lt_trans : Transitive upos_lt.
Obligation 1. exact: (ltn_trans H). Qed.

Program Instance upos_le_trans : Transitive upos_le.
Obligation 1. exact: (leq_trans H). Qed.

Definition head_or x xs := head x [seq uloc u | u <- xs].
Arguments head_or x xs /.

Definition last_or x xs := last x [seq uloc u | u <- xs].
Arguments last_or x xs /.

Section EqUpos.

Variables (T : eqType) (x0 : T).
Implicit Type s : UsePos.

Fixpoint equpos s1 s2 {struct s2} :=
  match s1, s2 with
  | {| uloc := u1; regReq := rr1; inputOnly := io1 |},
    {| uloc := u2; regReq := rr2; inputOnly := io2 |} =>
      [&& u1 == u2, rr1 == rr2 & io1 == io2]
  end.

Lemma equposP : Equality.axiom equpos.
Proof.
  move.
  case=> [u1 rr1 io1].
  case=> [u2 rr2 io2] /=.
  case: (u1 =P u2) => [<-|neqx]; last by right; case.
  case: (rr1 =P rr2) => [<-|neqx]; last by right; case.
  case: (io1 =P io2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical upos_eqMixin := EqMixin equposP.
Canonical upos_eqType := Eval hnf in EqType UsePos upos_eqMixin.

End EqUpos.

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

Lemma all_leq_ltn : forall x y xs,
  all (fun u : UsePos => y <= u) xs -> x < y
    -> all (fun u : UsePos => x <= u) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    by ordered.
  exact: IHzs.
Qed.

Lemma all_last_ltn : forall x xs before,
  x < before
    -> all (fun y : UsePos => uloc y < before) xs
    -> last_or x xs < before.
Proof.
  move=> x xs before Hlt Hall.
  elim: xs => //= [y ys IHys] in x Hlt Hall *.
  move/andP: Hall => [H1 H2].
  exact: IHys.
Qed.

Lemma all_last_leq : forall x xs before,
  x <= before
    -> all (fun y : UsePos => uloc y <= before) xs
    -> last_or x xs <= before.
Proof.
  move=> x xs before Hlt Hall.
  elim: xs => //= [y ys IHys] in x Hlt Hall *.
  move/andP: Hall => [H1 H2].
  exact: IHys.
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

Lemma span_all_ltn (l : list UsePos) : forall (x : nat) l1 l2,
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

Lemma span_all_leq (l : list UsePos) : forall (x : nat) l1 l2,
  StronglySorted upos_le l
    -> (l1, l2) = span (fun y => uloc y <= x) l
    -> all (fun y => uloc y <= x) l1 && all (fun y => x <= uloc y) l2.
Proof.
  move=> p l1 l2 Hsort Heqe.
  elim: l => /= [|x xs IHxs] in l1 l2 Hsort Heqe *.
    by inv Heqe.
  case E: (x <= p) in Heqe *.
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
  rewrite -ltnNge => Hle.
  move/Forall_all in H2.
  apply/andP; split=> //.
    exact/ltnW.
  exact: (all_leq_ltn H2).
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

Lemma last_leq_ltn : forall (z y : nat) (xs : seq nat) (n : nat),
  last z xs < n -> y <= z -> last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma Forall_last_leq : forall (y : UsePos) (ys : seq UsePos) (n : nat),
  last (uloc y) [seq uloc u | u <- ys] <= n
    -> List.Forall (fun x : UsePos => y <= x) ys -> y <= n.
Proof.
  move=> y.
  elim=> //= [z zs IHzs] n Hlast.
  invert; subst.
  apply: IHzs => //.
  exact (last_leq Hlast H1).
Qed.
