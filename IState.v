Require Import IEndo.
Require Import IApplicative.
Require Import IMonad.

Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrfun.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrnat.
Require Export Ssreflect.fintype.

Generalizable All Variables.

Inductive IState (i o a : Type) := mkIState : (i -> (a * o)) -> IState i o a.

Arguments mkIState [i o a] _.

Definition runIState {i o a} (x : IState i o a) :=
  match x with mkIState f => f end.

Axiom funext : forall a b (f g : a -> b), f =1 g -> f = g.

Lemma eq_mkIState : forall (i o a : Type) (f1 f2 : i -> (a * o)),
  f1 =1 f2 -> mkIState f1 = mkIState f2.
Proof.
  move=> i o a f1 f2 Ef.
  congr (mkIState _).
  apply/funext/Ef.
Qed.

Program Instance IState_IFunctor : IFunctor IState := {
    imap := fun _ _ _ _ f x =>
      mkIState (fun st => let (a,st') := runIState x st in (f a, st'))
}.
Obligation 1.
  destruct x.
  set f := (X in mkIState X).
  apply eq_mkIState.
  move=> st.
  compute.
  by case: (p st).
Qed.
Obligation 2.
  destruct x. simpl.
  apply eq_mkIState.
  move=> st.
  compute.
  by case: (p st).
Qed.

Definition iget  {i}     : IState i i i := mkIState (fun i => (i, i)).
Definition igets {i a} f : IState i i a := mkIState (fun s => (f s, s)).

Definition iput {i o} (x : o) : IState i o unit := mkIState (fun s => (tt, x)).

Definition imodify {i o} (f : i -> o) : IState i o unit :=
  mkIState (fun i => (tt, f i)).

Program Instance IState_IApplicative : IApplicative IState := {
    ipure := fun _ _ x => mkIState (fun st => (x, st));
    iap := fun _ _ _ _ _ f x =>
      mkIState (fun st =>
        let (f', st') := runIState f st in
        let (x', st'') := runIState x st' in
        (f' x', st''))
}.
Obligation 1.
  destruct x. compute.
  apply eq_mkIState.
  move=> st; compute.
  destruct (p st).
  reflexivity.
Qed.
Obligation 2.
  destruct u.
  destruct v.
  destruct w. simpl.
  apply eq_mkIState.
  move=> st; compute.
  destruct (p st).
  destruct (p0 j).
  destruct (p1 k).
  reflexivity.
Qed.

Program Instance IState_IMonad : IMonad IState := {
    ijoin := fun _ _ _ _ x => mkIState (fun st =>
      let (y, st') := runIState x st in
      let (a, st'') := runIState y st' in
      (a, st''))
}.
Obligation 1.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  destruct (p y).
  destruct i. simpl.
  destruct (p0 j).
  destruct i. simpl.
  destruct (p1 k).
  reflexivity.
Qed.
Obligation 2.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  destruct (p y).
  reflexivity.
Qed.
Obligation 3.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  destruct (p y).
  reflexivity.
Qed.
Obligation 4.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  destruct (p y). simpl.
  destruct i. simpl.
  destruct (p0 a).
  reflexivity.
Qed.
