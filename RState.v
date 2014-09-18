Require Export Coq.Init.Datatypes.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import FunctionalExtensionality.
Require Import Endo.
Require Import Applicative.
Require Import Monad.
Require Import Recdef.

Open Scope program_scope.

Section RState.

Variable   s   : Type.
Variable   ist : s.
Hypothesis P   : relation s.
Context  `(e   : PreOrder s P).

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
  | St : (forall st : s, P ist st -> StateP st a) -> RState a.

Arguments St [a] _.

Definition runRState {a : Type} (v : RState a)
  : forall st : s, P ist st -> StateP st a := match v with St f => f end.

Definition RState_fmap (a b : Type) (f : a -> b) (x : RState a) : RState b :=
  St (fun st H =>
        let sp := runRState x st H in
        {| after  := after sp
         ; result := f (result sp)
         ; holds  := holds sp
         |}).

Hint Unfold RState_fmap.

Ltac RState_auto :=
  intros; simpl;
  repeat (
    autounfold; simpl;
    f_equal; try apply proof_irrelevance; simpl;
    repeat match goal with
    | [ |- (fun _ : RState _ => _) = (fun _ : RState _ => _) ] =>
        extensionality sx
    | [ |- (fun _ : s => _) = _ ] =>
        extensionality st
    | [ |- (fun _ : P ist _ => _) = _ ] =>
        extensionality Hp
    | [ st : s, Hp: P ist _,
        sp : forall st : s, P ist st -> StateP st _ |- _ ] =>
        repeat match goal with [ |- context [sp st ?H] ] =>
          first [ is_var H
                | assert (Hp = H) as Hi by (apply proof_irrelevance);
                  rewrite <- Hi; clear Hi ]
        end;
        destruct (sp st); clear sp
    | [ sx : RState _ |- _ ] =>
        destruct sx; clear sx
    | [ |- St _ = St _ ] =>
        f_equal
    end; simpl).

Program Instance RState_Functor : Functor RState := {
    fmap := RState_fmap
}.
Solve All Obligations using RState_auto.

Definition RState_pure (a : Type) (x : a) : RState a :=
  St (fun st _ =>
        {| after  := st
         ; result := x
         ; holds  := reflexivity st
         |}).

Hint Unfold RState_pure.

Definition RState_ap (a b : Type) (f : RState (a -> b)) (x : RState a)
  : RState b :=
  St (fun st H =>
        let spf := runRState f st H in
        let spx := runRState x (after spf)
                             (transitivity H (holds spf)) in
        {| after  := after spx
         ; result := (result spf) (result spx)
         ; holds  := transitivity (holds spf) (holds spx)
         |}).

Hint Unfold RState_ap.

Program Instance RState_Applicative : Applicative RState := {
    pure := RState_pure;
    ap   := RState_ap
}.
Obligation 2.
  destruct u as [su].
  destruct v as [sv].
  destruct w as [sw].
  unfold RState_pure, compose.
  unfold RState_ap. simpl.
  f_equal.
  extensionality st.
  extensionality Hp. simpl.
  assert (Hp = transitivity (x:=ist) (y:=st) (z:=st) Hp (reflexivity st))
    by (apply proof_irrelevance).
  rewrite <- H. clear H.
  destruct (su st). simpl.
  assert (transitivity (x:=ist) (y:=st) (z:=after0) Hp
                       (transitivity (x:=st) (y:=st) (z:=after0)
                          (reflexivity st) holds0) =
          transitivity (x:=ist) (y:=st) (z:=after0) Hp holds0)
    by (apply proof_irrelevance).
  rewrite <- H. clear H.
  destruct (sv after0). simpl.
  assert (transitivity (x:=ist) (y:=st) (z:=after1) Hp
                       (transitivity (x:=st) (y:=after0) (z:=after1)
                         (transitivity (x:=st) (y:=st) (z:=after0)
                            (reflexivity st) holds0) holds1) =
          transitivity (x:=ist) (y:=after0) (z:=after1)
                       (transitivity (x:=ist) (y:=st) (z:=after0) Hp
                          (transitivity (x:=st) (y:=st) (z:=after0)
                             (reflexivity st) holds0)) holds1)
    by (apply proof_irrelevance).
  rewrite <- H. clear H.
  destruct (sw after1). simpl.
  f_equal. apply proof_irrelevance.
Qed.
Obligation 4.
  RState_auto.
  assert (Hp = transitivity (x:=ist) (y:=st) (z:=st) Hp (reflexivity st))
    by (apply proof_irrelevance).
  rewrite <- H. clear H.
  f_equal. apply proof_irrelevance.
Qed.
Solve All Obligations using RState_auto.

Definition RState_join (a : Type) (x : RState (RState a)) : RState a :=
  St (fun st H =>
        let sp := runRState x st H in
        let sp' := runRState (result sp) (after sp)
                             (transitivity H (holds sp)) in
        {| after  := after sp'
         ; result := result sp'
         ; holds  := transitivity (holds sp) (holds sp')
         |}).

Hint Unfold RState_join.

Program Instance RState_Monad : Monad RState := {
    join := RState_join
}.
Obligation 1.
  intros. autounfold. simpl.
  extensionality sx. f_equal.
  destruct sx as [sp]. simpl.
  extensionality st.
  extensionality H.
  destruct (sp st). simpl.
  destruct result0. simpl.
  destruct (s0 after0). simpl.
  assert (transitivity (x:=ist) (y:=after0) (z:=after1)
            (transitivity (x:=ist) (y:=st) (z:=after0) H holds0) holds1 =
          transitivity (x:=ist) (y:=st) (z:=after1) H
            (transitivity (x:=st) (y:=after0) (z:=after1) holds0 holds1))
    by (apply proof_irrelevance).
  rewrite H0. clear H0.
  f_equal. apply proof_irrelevance.
Qed.
Solve All Obligations using RState_auto.

Definition get : RState s :=
  St (fun st _ =>
        {| after  := st
         ; result := st
         ; holds  := reflexivity st
         |}).

(** There cannot be a definition of [put], since we can only lawfully
    transform the state, not simply replace it.  Therefore, [modify] must be
    used in all cases where [put] would ordinarily have been. *)

Definition modify (f : forall st : s, { st' : s & P st st' }) : RState unit :=
  St (fun st _ =>
        let (st', H') := f st in
        {| after  := st'
         ; result := tt
         ; holds  := H'
         |}).

End RState.