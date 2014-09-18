Require Export Coq.Init.Datatypes.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import FunctionalExtensionality.
Require Export Endo.
Require Export Applicative.
Require Export Monad.
Require Import Recdef.

Open Scope program_scope.

Section RState.

Variable   s : Type.
Hypothesis P : relation s.
Context  `(e : PreOrder s P).

Record StateP (before : s) (a : Type) := {
    after  : s;
    result : a;
    holds  : P before after
}.

Arguments after [before] [a] _.
Arguments result [before] [a] _.
Arguments holds [before] [a] _.

(** The [RState] monad requires that a given equivalence relation hold
    between state transitions. *)
Inductive RState (a : Type) : Type :=
  | St : (forall st : s, StateP st a) -> RState a.

Arguments St [a] _.

Definition runRState {a : Type} (v : RState a)
  : forall st : s, StateP st a :=
      match v with St f => fun st => f st end.

Definition RState_fmap (a b : Type) (f : a -> b) (x : RState a)
  : RState b :=
  St (fun st =>
        let sp := runRState x st in
        {| after  := after sp
         ; result := f (result sp)
         ; holds  := holds sp
         |}).

Hint Unfold RState_fmap.

Ltac RState_auto :=
  intros; simpl;
  repeat (
    autounfold; unfold id, compose; simpl;
    f_equal; try apply proof_irrelevance; auto;
    match goal with
    | [ |- (fun _ : RState _ => _) = (fun _ : RState _ => _) ] =>
        extensionality sx
    | [ |- (fun _ : s => _) = _ ] =>
        extensionality st
    | [ st : s, sp : forall st : s, StateP st _ |- _ ] =>
        destruct (sp st)
    | [ sx : RState _ |- _ ] => destruct sx as [sp]
    | [ |- St _ = St _ ] => f_equal
    end).

Obligation Tactic := RState_auto.

Program Instance RState_Functor : Functor RState := {
    fmap := RState_fmap
}.

Definition RState_pure (a : Type) (x : a) : RState a :=
  St (fun st =>
        {| after  := st
         ; result := x
         ; holds  := reflexivity st
         |}).

Hint Unfold RState_pure.

Definition RState_ap (a b : Type) (f : RState (a -> b)) (x : RState a)
  : RState b :=
  St (fun st =>
        let spf := runRState f st in
        let spx := runRState x (after spf) in
        {| after  := after spx
         ; result := (result spf) (result spx)
         ; holds  := transitivity (holds spf) (holds spx)
         |}).

Hint Unfold RState_ap.

Program Instance RState_Applicative : Applicative RState := {
    pure := RState_pure;
    ap   := RState_ap
}.

Definition RState_join (a : Type) (x : RState (RState a)) : RState a :=
  St (fun st =>
        let sp := runRState x st in
        let sp' := runRState (result sp) (after sp) in
        {| after  := after sp'
         ; result := result sp'
         ; holds  := transitivity (holds sp) (holds sp')
         |}).

Hint Unfold RState_join.

Program Instance RState_Monad : Monad RState := {
    join := RState_join
}.

Definition get : RState s :=
  St (fun st =>
        {| after  := st
         ; result := st
         ; holds  := reflexivity st
         |}).

(** There cannot be a definition of [put], since we can only lawfully
    transform the state, not simply replace it.  Therefore, [modify] must be
    used in all cases where [put] would ordinarily have been. *)
Definition modify (f : forall st : s, { st' : s & P st st' }) : RState unit :=
  St (fun st =>
        let (st', H) := f st in
        {| after  := st'
         ; result := tt
         ; holds  := H
         |}).

End RState.