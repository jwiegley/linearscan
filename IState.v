Require Export LinearScan.IMonad.

Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrfun.
Require Import Ssreflect.seq.

Generalizable All Variables.

Section IState.

Variable errType : Set.

Inductive IState (i o a : Type) :=
  mkIState : (i -> errType + (a * o)) -> IState i o a.

Arguments mkIState [i o a] _.

Definition runIState {i o a} (x : IState i o a) :=
  match x with mkIState f => f end.

Axiom funext : forall a b (f g : a -> b), f =1 g -> f = g.

Lemma eq_mkIState : forall (i o a : Type)
  (f1 f2 : i -> errType + (a * o)),
  f1 =1 f2 -> mkIState f1 = mkIState f2.
Proof.
  move=> i o a f1 f2 Ef.
  congr (mkIState _).
  apply/funext/Ef.
Qed.

Global Program Instance IState_IFunctor : IFunctor IState := {
    imap := fun _ _ _ _ f x =>
      mkIState (fun st =>
                  match runIState x st with
                  | inl err => inl err
                  | inr (a,st') => inr (f a, st')
                  end)
}.
Obligation 1.
  destruct x.
  set f := (X in mkIState X).
  apply eq_mkIState.
  move=> st.
  compute.
  case: (s st); auto.
  by case.
Qed.
Obligation 2.
  destruct x. simpl.
  apply eq_mkIState.
  move=> st.
  compute.
  case: (s st); auto.
  by case.
Qed.

Definition ierr {i} (err : errType) : IState i i i :=
  mkIState (fun i => inl err).

Definition iget  {i}     : IState i i i := mkIState (fun i => inr (i, i)).
Definition igets {i a} f : IState i i a := mkIState (fun s => inr (f s, s)).

Definition iput {i o} (x : o) : IState i o unit :=
  mkIState (fun s => inr (tt, x)).

Definition imodify {i o} (f : i -> o) : IState i o unit :=
  mkIState (fun i => inr (tt, f i)).

Global Program Instance IState_IApplicative : IApplicative IState := {
    ipure := fun _ _ x => mkIState (fun st => inr (x, st));
    iap := fun _ _ _ _ _ f x =>
      mkIState (fun st =>
        match runIState f st with
        | inl err => inl err
        | inr (f', st') =>
            match runIState x st' with
            | inl err => inl err
            | inr (x', st'') => inr (f' x', st'')
            end
        end)
}.
Obligation 1.
  destruct x. compute.
  apply eq_mkIState.
  move=> st; compute.
  case: (s st); auto.
  by case.
Qed.
Obligation 2.
  destruct u.
  destruct v.
  destruct w. simpl.
  apply eq_mkIState.
  move=> st; compute.
  case: (s st); auto.
  case; move=> a b.
  case: (s0 b); auto.
  case; move=> a0 b0.
  case: (s1 b0); auto.
  by case.
Qed.

Global Program Instance IState_IMonad : IMonad IState := {
    ijoin := fun _ _ _ _ x => mkIState (fun st =>
      match runIState x st with
      | inl err => inl err
      | inr (y, st') =>
          match runIState y st' with
          | inl err => inl err
          | inr (a, st'') => inr (a, st'')
          end
      end)
}.
Obligation 1.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  case: (s y); auto.
  case; case=> s0 b.
  case: (s0 b); auto.
  case; case=> s1 b1.
  case: (s1 b1); auto.
  by case.
Qed.
Obligation 2.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  case: (s y); auto.
  by case.
Qed.
Obligation 3.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  case: (s y) => //.
  by case.
Qed.
Obligation 4.
  destruct x.
  unfold funcomp.
  apply eq_mkIState.
  move=> y; compute.
  case: (s y) => //=.
  case; case=> s0 b.
  case: (s0 b) => //.
  by case.
Qed.

End IState.
