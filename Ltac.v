Require Import LinearScan.Ssr.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
Proof.
  move=> n m p H1 H2.
  exact: (leq_trans H1).
Qed.

Ltac breakup :=
  repeat match goal with
    | [ H: is_true (_ && _) |- _ ] => move/andP: H => [? ?]
    | [ |- is_true (_ && _) ] => apply/andP; split
    | [ H: is_true (?X <  ?Y <  ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <= ?Y <= ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <  ?Y <= ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <= ?Y <  ?Z) |- _ ] => move/andP: H => [? ?]
    | [ |- is_true (?X <  ?Y <  ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <  ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <  ?Z) ] => apply/andP; split
    end;
  repeat match goal with
    | [ H1: is_true (?X <  ?Y), H2: is_true (?Y <  ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X < Z) |- _ ] => idtac
        | _ => move: (ltn_trans H1 H2) => ?
        end
    | [ H1: is_true (?X <  ?Y), H2: is_true (?Y <= ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X < Z) |- _ ] => idtac
        | _ => move: (ltn_leq_trans H1 H2) => ?
        end
    | [ H1: is_true (?X <= ?Y), H2: is_true (?Y <  ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X < Z) |- _ ] => idtac
        | _ => move: (leq_ltn_trans H1 H2) => ?
        end
    | [ H1: is_true (?X <= ?Y), H2: is_true (?Y <= ?Z) |- _ ] =>
        match goal with
        | [ H: is_true (X <= Z) |- _ ] => idtac
        | _ => move: (leq_trans H1 H2) => ?
        end
    end;
  intuition;
  repeat match goal with
    | [ H: is_true (?X <  ?Y) |- _ ] => move/ltP in H
    | [ H: is_true (?X <= ?Y) |- _ ] => move/leP in H
    | [ H: is_true (?X == ?Y) |- _ ] => move/eqP in H
    | [ H: is_true (?X != ?Y) |- _ ] => move/eqP in H
    | [ |- is_true (?X <  ?Y) ] => apply/ltP
    | [ |- is_true (?X <= ?Y) ] => apply/leP
    | [ |- is_true (?X == ?Y) ] => apply/eqP
    | [ |- is_true (?X != ?Y) ] => apply/eqP
    end.

Ltac ordered := abstract (intuition; breakup; omega).

Lemma Forall_all : forall (T : Type) (a : pred T) (s : seq T),
  reflect (List.Forall a s) (all a s).
Proof.
  move=> T a.
  elim=> [|x xs IHxs] //=.
    by constructor; constructor.
  case E: (a x) => /=.
    case A: (all a xs).
      constructor.
      constructor.
        by rewrite E.
      exact/IHxs.
    constructor.
    move=> Hcontra.
    inversion Hcontra; subst.
    rewrite A in IHxs.
    by move/IHxs in H2.
  constructor.
  move=> Hcontra.
  inversion Hcontra; subst.
  by rewrite E in H1.
Qed.

Ltac match_all :=
  repeat match goal with
  | [ H: List.Forall _ ?Z |- _ ] => move/Forall_all in H
  | [ |- List.Forall _ ?Z ]      => apply/Forall_all
  end;
  match goal with
  | [  H: is_true (all _ ?Z) |- is_true (all _ ?Z) ] =>
      move/allP in H;
      apply/allP;
      intros x_1 H_1;
      specialize (H x_1 H_1);
      clear H_1;
      ordered
  end.