Require Export LinearScan.IMonad.

Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrfun.
Require Import Ssreflect.seq.

Generalizable All Variables.

Section IState.

Variable errType : Set.

Definition IState (i o a : Type) := (i -> errType + (a * o)).

Axiom funext : forall a b (f g : a -> b), f =1 g -> f = g.

Global Program Instance IState_IFunctor : IFunctor IState := {
    imap := fun _ _ _ _ f x =>
      (fun st =>
                  match x st with
                  | inl err => inl err
                  | inr (a,st') => inr (f a, st')
                  end)
}.
Obligation 1.
  compute; move=> x.
  apply funext.
  compute; move=> st.
  case: (x st); auto.
  by case.
Qed.
Obligation 2.
  compute; move=> x.
  apply funext.
  compute; move=> st.
  case: (x st); auto.
  by case.
Qed.

Definition ierr {i o a} (err : errType) : IState i o a :=
  fun _ => inl err.

Definition iget  {i}     : IState i i i := fun i => inr (i, i).
Definition igets {i a} f : IState i i a := fun s => inr (f s, s).

Definition iput {i o} (x : o) : IState i o unit := fun _ => inr (tt, x).

Definition imodify {i o} (f : i -> o) : IState i o unit :=
  fun i => inr (tt, f i).

Global Program Instance IState_IApplicative : IApplicative IState := {
    ipure := fun _ _ x => fun st => inr (x, st);
    iap := fun _ _ _ _ _ f x =>
      fun st =>
        match f st with
        | inl err => inl err
        | inr (f', st') =>
            match x st' with
            | inl err => inl err
            | inr (x', st'') => inr (f' x', st'')
            end
        end
}.
Obligation 1.
  compute; move=> x.
  apply funext.
  compute; move=> st.
  case: (x st); auto.
  by case.
Qed.
Obligation 2.
  apply funext.
  move=> st; compute.
  case: (u st); auto.
  case; move=> a b.
  case: (v b); auto.
  case; move=> a0 b0.
  case: (w b0); auto.
  by case.
Qed.

Global Program Instance IState_IMonad : IMonad IState := {
    ijoin := fun _ _ _ _ x => fun st =>
      match x st with
      | inl err => inl err
      | inr (y, st') =>
          match y st' with
          | inl err => inl err
          | inr (a, st'') => inr (a, st'')
          end
      end
}.
Obligation 1.
Admitted.
(*   apply funext. *)
(*   move=> y; compute. *)
(*   case: (s y); auto. *)
(*   case; case=> s0 b. *)
(*   case: (s0 b); auto. *)
(*   case; case=> s1 b1. *)
(*   case: (s1 b1); auto. *)
(*   by case. *)
(* Qed. *)
Obligation 2.
Admitted.
(*   destruct x. *)
(*   unfold funcomp. *)
(*   apply eq_mkIState. *)
(*   move=> y; compute. *)
(*   case: (s y); auto. *)
(*   by case. *)
(* Qed. *)
Obligation 3.
Admitted.
(*   destruct x. *)
(*   unfold funcomp. *)
(*   apply eq_mkIState. *)
(*   move=> y; compute. *)
(*   case: (s y) => //. *)
(*   by case. *)
(* Qed. *)
Obligation 4.
Admitted.
(*   destruct x. *)
(*   unfold funcomp. *)
(*   apply eq_mkIState. *)
(*   move=> y; compute. *)
(*   case: (s y) => //=. *)
(*   case; case=> s0 b. *)
(*   case: (s0 b) => //. *)
(*   by case. *)
(* Qed. *)

End IState.
