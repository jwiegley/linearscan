Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section IState.

Variable errType : Set.

Definition IState (i o a : Type) := (i -> errType + (a * o)).

Definition iget  {i}     : IState i i i := fun i => inr (i, i).
Definition iput {i o} (x : o) : IState i o unit := fun _ => inr (tt, x).

Definition imap {I O X Y} : (X -> Y) -> IState I O X -> IState I O Y :=
  fun f x =>
  (fun st =>
              match x st with
              | inl err => inl err
              | inr (a,st') => inr (f a, st')
              end).

Definition ipure {I X} : X -> IState I I X :=
  fun x => fun st => inr (x, st).

Definition ijoin {I A O X} : IState I A (IState A O X) -> IState I O X :=
  fun x => fun st =>
  match x st with
  | inl err => inl err
  | inr (y, st') =>
      match y st' with
      | inl err => inl err
      | inr (a, st'') => inr (a, st'')
      end
  end.

End IState.