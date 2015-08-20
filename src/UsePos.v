Require Import LinearScan.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Inductive VarKind : Set := Input | Temp | Output.

Definition VarKind_leq (x y : VarKind) : bool :=
  match x with
    | Input => true
    | Temp => if y is Input then false else true
    | Output => if y is Output then true else false
  end.

Example VarKind_leq_ex1 : VarKind_leq Input Input.
Proof. by []. Qed.
Example VarKind_leq_ex2 : VarKind_leq Input Temp.
Proof. by []. Qed.
Example VarKind_leq_ex3 : VarKind_leq Input Output.
Proof. by []. Qed.
Example VarKind_leq_ex4 : ~~ VarKind_leq Temp Input.
Proof. by []. Qed.
Example VarKind_leq_ex5 : VarKind_leq Temp Temp.
Proof. by []. Qed.
Example VarKind_leq_ex6 : VarKind_leq Temp Output.
Proof. by []. Qed.
Example VarKind_leq_ex7 : ~~ VarKind_leq Output Input.
Proof. by []. Qed.
Example VarKind_leq_ex8 : ~~ VarKind_leq Output Temp.
Proof. by []. Qed.
Example VarKind_leq_ex9 : VarKind_leq Output Output.
Proof. by []. Qed.

Section EqVarKind.

Implicit Type s : VarKind.

Fixpoint eqVarKind s1 s2 {struct s2} :=
  match s1, s2 with
  | Input, Input   => true
  | Temp, Temp     => true
  | Output, Output => true
  | _, _           => false
  end.

Lemma eqVarKindP : Equality.axiom eqVarKind.
Proof.
  move.
  move=> b1 b2 /=.
  case: b1; case: b2=> /=;
  constructor=> //=;
  by case.
Qed.

Canonical VarKind_eqMixin := EqMixin eqVarKindP.
Canonical VarKind_eqType :=
  Eval hnf in EqType VarKind VarKind_eqMixin.

End EqVarKind.

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
  uloc   : nat;
  regReq : bool;
  uvar   : VarKind
}.

Coercion uloc : UsePos >-> nat.

Module UsePosNotations.
Notation " (| x |) " := {| uloc := x; regReq := false |}.
Notation " (! x !) " := {| uloc := x; regReq := true |}.
End UsePosNotations.

Definition upos_le (x y : UsePos) : bool := uloc x <= uloc y.
Arguments upos_le x y /.

(* A [UsePos] is within bound of a range position if, be it an input-only use
   position, it fall on or before that position; or, be it not input-only, it
   fall before it.  Examples:

   Input-Only use positions:

     1                     21
     |                     | use at 21
     +---------------------+

     1                     21
     |         use at 13   |
     +---------+-----------+

   Non Input-Only use positions (i.e., Temp and/or Output):

     1                     21
     |                     | use at 19
     +-------------------+-+

     1                     21
     |         use at 13   |
     +---------+-----------+

  The reason for this distinction is that, when a range ends, whatever
  variables it had live in registers at that time should still be in those
  registers, so they are in a sense "still live" for the next instruction, if
  they are only being used as inputs there.  Thus, we want the range to *not*
  cover that position just for the sake of those input variables, so we can
  use those same registers as outputs for another variable; but we also need
  to know that if the range is spilled, those inputs are reloaded before that
  instruction.  Hence this notion of a "use position not covered by a range",
  if it be input-only and coincide with the end of the previous range. *)

Definition upos_within_bound (before : nat) (u : UsePos) :=
  if uvar u is Input
  then uloc u <= before
  else uloc u < before.
Arguments upos_within_bound before u /.

Program Instance upos_le_trans : Transitive upos_le.
Obligation 1. by ordered. Qed.

Definition head_or x xs := head x [seq uloc u | u <- xs].
Arguments head_or x xs /.

Definition last_or x xs := last x [seq uloc u | u <- xs].
Arguments last_or x xs /.

Section EqUpos.

Fixpoint equpos s1 s2 {struct s2} :=
  match s1, s2 with
  | {| uloc := u1; regReq := rr1; uvar := io1 |},
    {| uloc := u2; regReq := rr2; uvar := io2 |} =>
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

Lemma upos_eq : forall x y, x == y -> uloc x == uloc y.
Proof.
  move=> x y H.
  move/eqP in H.
  by rewrite H.
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

Lemma span_all_leq (l : list UsePos) : forall (x : nat) l1 l2,
  StronglySorted upos_le l
    -> (l1, l2) = span (fun u => uloc u < x) l
    -> all (fun u => uloc u < x) l1 && all (fun u => x <= uloc u) l2.
Proof.
  move=> p l1 l2 Hsort Heqe.
  elim: l => /= [|x xs IHxs] in l1 l2 Hsort Heqe *.
    by inv Heqe.
  rewrite /= in IHxs Hsort Heqe *.
  case E1: (x < p) in Heqe *.
    inv Hsort.
    case: (span _ xs) => [l1' l2'] in Heqe IHxs *.
    move: (IHxs l1' l2' H1 refl_equal) => /andP [? ?].
    apply/andP; split.
      inv Heqe.
      by apply/andP; split.
    by inv Heqe.
  inv Hsort.
  move/Forall_all in H2.
  clear IHxs H1.
  inv Heqe.
  move/negbT in E1; rewrite -leqNgt in E1.
  apply/andP; split=> //.
  apply/allP=> [x0 Hin].
  move/allP: H2 => /(_ x0 Hin).
  rewrite /funcomp.
  by ordered.
Qed.
