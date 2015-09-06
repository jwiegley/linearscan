Require Import LinearScan.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Inductive VarKind : Set := Input | InputOutput | Temp | Output.

Definition VarKind_leq (x y : VarKind) : bool :=
  match x, y with
    | Output, _           => false
    | Temp,   InputOutput => false
    | Temp,   Input       => false
    | InputOutput, Input  => false
    | _,  _               => true
  end.

Example VarKind_leq_ex1 :    VarKind_leq Input  Input.  Proof. by []. Qed.
Example VarKind_leq_ex2 :    VarKind_leq Input  Temp.   Proof. by []. Qed.
Example VarKind_leq_ex3 :    VarKind_leq Input  Output. Proof. by []. Qed.
Example VarKind_leq_ex4 : ~~ VarKind_leq Temp   Input.  Proof. by []. Qed.
Example VarKind_leq_ex5 :    VarKind_leq Temp   Temp.   Proof. by []. Qed.
Example VarKind_leq_ex6 :    VarKind_leq Temp   Output. Proof. by []. Qed.
Example VarKind_leq_ex7 : ~~ VarKind_leq Output Input.  Proof. by []. Qed.
Example VarKind_leq_ex8 : ~~ VarKind_leq Output Temp.   Proof. by []. Qed.
Example VarKind_leq_ex9 : ~~ VarKind_leq Output Output. Proof. by []. Qed.

Section EqVarKind.

Definition eqVarKind s1 s2 :=
  match s1, s2 with
  | Input,  Input             => true
  | InputOutput,  InputOutput => true
  | Temp,   Temp              => true
  | Output, Output            => true
  | _, _                      => false
  end.

Lemma eqVarKindP : Equality.axiom eqVarKind.
Proof. by case; case=> /=; constructor=> //=; case. Qed.

Canonical VarKind_eqMixin := EqMixin eqVarKindP.
Canonical VarKind_eqType  := Eval hnf in EqType VarKind VarKind_eqMixin.

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
Canonical upos_eqType  := Eval hnf in EqType UsePos upos_eqMixin.

End EqUpos.

Coercion uloc : UsePos >-> nat.

Definition upos_le : rel UsePos := leq.
Arguments upos_le x y /.

Program Instance upos_le_trans : Transitive upos_le.
Obligation 1. by ordered. Qed.

Definition head_or x xs := head x [seq uloc u | u <- xs].
Arguments head_or x xs /.

Definition last_or x xs := last x [seq uloc u | u <- xs].
Arguments last_or x xs /.

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
