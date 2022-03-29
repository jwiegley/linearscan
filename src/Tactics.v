Require Export Hask.Ltac.
Require Export LinearScan.Ssr.

Require Import Coq.micromega.Lia.

Ltac reflection ctor :=
  unfold Equality.axiom; intros;
  repeat match goal with
           [ H : ctor |- _ ] => destruct H
         end;
  simpl; try constructor;
  intuition; try discriminate.

Ltac consider_member x y :=
  case: (x =P y) => [<-|?]; last by right; case.

Ltac breakup :=
  repeat match goal with
    | [ H: is_true (_ && _) |- _ ] => move/andP: H => [? ?]
    | [ |- is_true (_ && _) ] => apply/andP; split
    | [ H: is_true (_ || _) |- _ ] => move/orP: H => [?|?]
    | [ |- is_true (_ || _) ] => apply/orP; split
    | [ H: is_true (?X <  ?Y <  ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <= ?Y <= ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <  ?Y <= ?Z) |- _ ] => move/andP: H => [? ?]
    | [ H: is_true (?X <= ?Y <  ?Z) |- _ ] => move/andP: H => [? ?]
    | [ |- is_true (?X <  ?Y <  ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <  ?Y <= ?Z) ] => apply/andP; split
    | [ |- is_true (?X <= ?Y <  ?Z) ] => apply/andP; split
    | [ H: is_true (~~ (?X <  ?Y <  ?Z)) |- _ ] => move/nandP in H
    | [ H: is_true (~~ (?X <= ?Y <  ?Z)) |- _ ] => move/nandP in H
    | [ H: is_true (~~ (?X <  ?Y <= ?Z)) |- _ ] => move/nandP in H
    | [ H: is_true (~~ (?X <= ?Y <= ?Z)) |- _ ] => move/nandP in H
    | [ |- is_true (~~ (?X <  ?Y <  ?Z)) ] => apply/nandP
    | [ |- is_true (~~ (?X <= ?Y <  ?Z)) ] => apply/nandP
    | [ |- is_true (~~ (?X <  ?Y <= ?Z)) ] => apply/nandP
    | [ |- is_true (~~ (?X <= ?Y <= ?Z)) ] => apply/nandP
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
  intuition.

Lemma negneg : forall (a : eqType) (x y : a), ~~ (x != y) -> x = y.
Proof.
  move=> a x y H.
  move/negbTE in H.
  case E: (x == y).
    by move/eqP in E.
  move/eqP in E.
  by move/eqP in H.
Qed.

Lemma negb_eq : forall (T : eqType) (a b : T), ~~ (a != b) = (a == b).
Proof. by move=> T a b; case: (a == b). Qed.

Ltac ordered := abstract (
  intuition;
  breakup;
  repeat match goal with
  | [ H: (_ <= _) = false |- _ ] => move/negbT in H
  | [ H: (_ <  _) = false |- _ ] => move/negbT in H
  end;
  repeat match goal with
  | [ H: is_true (~~ (?X <  ?Y)) |- _ ] => rewrite -leqNgt in H
  | [ H: is_true (~~ (?X <= ?Y)) |- _ ] => rewrite -ltnNge in H
  | [ H: is_true (~~ (?X == ?Y)) |- _ ] => idtac
  | [ H: is_true (~~ (?X != ?Y)) |- _ ] => rewrite negb_eq in H
  | [ |- is_true (~~ (?X <  ?Y)) ] => rewrite -leqNgt
  | [ |- is_true (~~ (?X <= ?Y)) ] => rewrite -ltnNge
  | [ |- is_true (~~ (?X == ?Y)) ] => idtac
  | [ |- is_true (~~ (?X != ?Y)) ] => rewrite negb_eq
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
  lia).

Lemma ltn_addn1 : forall n m, n < m -> n.+1 < m.+1.
Proof. by []. Qed.

Lemma leq_addn1 : forall n m, n <= m -> n.+1 <= m.+1.
Proof. by []. Qed.

Ltac undoubled :=
  breakup;
  do [ apply/ltn_addn1; rewrite ltn_double
     | apply/leq_addn1; rewrite leq_double
     | rewrite doubleS ];
  do [ ordered
     | do [ exact/ltnW/ltnW
          | exact/ltnW
          | exact/leqW/leqW
          | exact/leqW ];
       ordered ].

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
  abstract match goal with
  | [  H: is_true (all _ ?Z) |- is_true (all _ ?Z) ] =>
      move/allP in H;
      apply/allP;
      intros x_1 H_1;
      specialize (H x_1 H_1);
      clear H_1;
      ordered
  end.
