Set Warnings "-notation-overridden".

Require Import LinearScan.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Context.

Variable errType : Set.

(* The Indexed Reader State Either monad. *)
Definition Context (i o a : Type) := seq errType -> i -> seq errType + (a * o).

Definition iask {i} : Context i i (seq errType) := fun e i => inr (e, i).

Definition context {i o a} (c : errType) (x : Context i o a) :
  Context i o a := fun e => x (c :: e).

Definition iget {i} : Context i i i := fun _ i => inr (i, i).
Definition iput {i o} (x : o) : Context i o unit := fun _ _ => inr (tt, x).

Definition imap {I O X Y} : (X -> Y) -> Context I O X -> Context I O Y :=
  fun f x e st =>
    match x e st with
    | inl err     => inl err
    | inr (a,st') => inr (f a, st')
    end.

Definition ipure {I X} : X -> Context I I X := fun x _ st => inr (x, st).

Definition ijoin {I A O X} : Context I A (Context A O X) -> Context I O X :=
  fun x e st =>
    match x e st with
    | inl err => inl err
    | inr (y, st') =>
        match y e st' with
        | inl err => inl err
        | inr (a, st'') => inr (a, st'')
        end
    end.

Definition ibind {I A O X Y} (f : X -> Context A O Y) (x : Context I A X) :
  Context I O Y := @ijoin I A O Y (@imap I A X _ f x).

Definition conseq `(x : Context P2 Q2 a) `(f : P1 -> P2) `(g : Q2 -> Q1) :
  Context P1 Q1 a.
Proof.
  rewrite /Context in x *.
  move=> e p.
  case (x e (f p)) => [e'|[a' q]].
    exact: inl e'.
  apply: inr (a', _).
  exact: g q.
Defined.

Definition strengthen `(x : Context P2 Q a) `(f : P1 -> P2) : Context P1 Q a :=
  conseq x f id.

Definition weaken `(x : Context P Q2 a) `(g : Q2 -> Q1) : Context P Q1 a :=
  conseq x id g.

End Context.

Set Maximal Implicit Insertion.

Arguments iask : default implicits.
Arguments iget : default implicits.
Arguments iput : default implicits.
Arguments imap : default implicits.
Arguments ipure : default implicits.
Arguments ijoin : default implicits.
Arguments ibind : default implicits.
Arguments conseq : default implicits.
Arguments strengthen : default implicits.
Arguments weaken : default implicits.

Unset Maximal Implicit Insertion.

Notation "m >>>= f" := (ibind f m) (at level 25, left associativity).

Notation "X <<- A ;;; B" := (A >>>= (fun X => B))
  (at level 92, A at next level, right associativity).

Notation "A ;;; B" := (_ <<- A ;;; B) (at level 92, right associativity).
