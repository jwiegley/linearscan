Require Import LinearScan.Lib.
Require Import Omega.

Ltac ordered :=
  repeat match goal with
    | [ H: is_true (?X <  ?Y <  ?Z) |- _ ] => move: H => /andP [? ?]
    | [ H: is_true (?X <= ?Y <= ?Z) |- _ ] => move: H => /andP [? ?]
    | [ H: is_true (?X <  ?Y <= ?Z) |- _ ] => move: H => /andP [? ?]
    | [ H: is_true (?X <= ?Y <  ?Z) |- _ ] => move: H => /andP [? ?]
    | [ |- is_true (?X <  ?Y <  ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <  ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <  ?Z) ] => apply/andP; split
    end;
  repeat match goal with
    | [ H: is_true (?X <  ?Y) |- _ ] => move/ltP in H
    | [ H: is_true (?X <= ?Y) |- _ ] => move/leP in H
    | [ H: is_true (?X == ?Y) |- _ ] => move/eqP in H
    | [ H: is_true (?X != ?Y) |- _ ] => move/eqP in H
    | [ |- is_true (?X <  ?Y) ] => apply/ltP
    | [ |- is_true (?X <= ?Y) ] => apply/leP
    | [ |- is_true (?X == ?Y) ] => apply/eqP
    | [ |- is_true (?X != ?Y) ] => apply/eqP
    end;
  abstract omega.

Ltac match_all :=
  repeat match goal with
  | [ H: List.Forall _ ?Z |- _ ] =>
      move/Forall_all in H
  | [ |- List.Forall _ ?Z ] =>
      apply/Forall_all
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