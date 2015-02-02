Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section IState.

Variable errType : Set.

Definition IState (i o a : Type) := (i -> errType + (a * o)).

Axiom funext : forall a b (f g : a -> b), (forall x, f x = g x) -> f = g.

Definition ierr {i o a} (err : errType) : IState i o a :=
  fun _ => inl err.

Definition iget  {i}     : IState i i i := fun i => inr (i, i).
Definition igets {i a} f : IState i i a := fun s => inr (f s, s).

Definition iput {i o} (x : o) : IState i o unit := fun _ => inr (tt, x).

Definition imodify {i o} (f : i -> o) : IState i o unit :=
  fun i => inr (tt, f i).

Definition imap {I O X Y} : (X -> Y) -> IState I O X -> IState I O Y :=
  fun f x =>
  (fun st =>
              match x st with
              | inl err => inl err
              | inr (a,st') => inr (f a, st')
              end).

Definition ipure {I X} : X -> IState I I X :=
  fun x => fun st => inr (x, st).

Definition iap {I J K X Y} :
  IState I J (X -> Y) -> IState J K X -> IState I K Y :=
  fun f x =>
  fun st =>
    match f st with
    | inl err => inl err
    | inr (f', st') =>
        match x st' with
        | inl err => inl err
        | inr (x', st'') => inr (f' x', st'')
        end
    end.

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