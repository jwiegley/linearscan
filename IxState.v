Require Export Coq.Init.Datatypes.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import FunctionalExtensionality.
Require Import Recdef.

Open Scope program_scope.

Class Monad (m : Type -> Type) := {
    fmap : forall {a b}, (a -> b) -> m a -> m b;
    pure : forall {a}, a -> m a;
    join : forall {a}, m (m a) -> m a;

    fun_identity : forall {X}, fmap (@id X) = id;
    fun_composition : forall {X Y Z} (f : Y -> Z) (g : X -> Y),
      fmap f ∘ fmap g = fmap (f ∘ g);

    monad_law_1 : forall {X}, join ∘ fmap join = (@join X) ∘ join;
    monad_law_2 : forall {X}, join ∘ fmap (@pure X) = id;
    monad_law_3 : forall {X}, (@join X) ∘ pure = id;
    monad_law_4 : forall {X Y} (f : X -> Y),
      join ∘ fmap (fmap f) = fmap f ∘ join
}.

Arguments fmap [m] [_] [a] [b] f x.
Arguments pure [m] [_] [a] x.
Arguments join [m] [_] [a] x.

Definition bind {M} `{Monad M} {X Y}
  (f : (X -> M Y)) (x : M X) : M Y := join (fmap f x).

Notation "m >>= f" := (bind f m) (at level 65, left associativity).

Notation "x <- c1 ;; c2" := (@bind _ _ _ _ _ c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2) (at level 100, right associativity).

Section IxState.

Variable  s : Type.
Parameter P : relation s.
Context   `{e : Equivalence s P}.

(** The [IxState] monad requires that a given equivalence relation hold
    between state transitions. *)
Inductive IxState (a : Type) : Type :=
  | St : (forall (x : s), { r : a * s & P x (snd r) }) -> IxState a.

Arguments St [a] _.

Definition runIxState {a : Type} (x : IxState a)
  : forall (x : s), { r : a * s & P x (snd r) } :=
      match x with St f => f end.

Definition IxState_fmap (a b : Type) (f : a -> b) (x : IxState a)
  : IxState b :=
  St (fun st => match runIxState x st with
        | existT (r, st') H =>
            existT (fun r : b * s => P st (snd r)) (f r, st') H
        end).

Definition IxState_pure (a : Type) (x : a) : IxState a :=
  St (fun st => existT (fun r : a * s => P st (snd r)) (x, st)
                       (reflexivity st)).

Definition IxState_join (a : Type) (x : IxState (IxState a)) : IxState a :=
  St (fun st => match runIxState x st with
        | existT (r, st') H => match runIxState r st' with
            | existT (r', st'') H' =>
                existT (fun r : a * s => P st (snd r)) (r', st'')
                       (transitivity H H')
            end
        end).

Program Instance IxState_Monad : Monad IxState := {
    fmap := IxState_fmap;
    pure := IxState_pure;
    join := IxState_join
}.
Obligation 1.
  unfold IxState_fmap.
  extensionality st.
  unfold id. simpl.
  destruct st. f_equal.
  extensionality st'. simpl.
  destruct (s0 st').
  destruct x. reflexivity.
Qed.
Obligation 2.
  unfold IxState_fmap.
  extensionality st.
  unfold compose, id. simpl.
  destruct st. f_equal.
  extensionality st'. simpl.
  destruct (s0 st').
  destruct x. reflexivity.
Qed.
Obligation 3.
  unfold IxState_join, IxState_fmap.
  extensionality st.
  unfold compose, id. simpl.
  destruct st. f_equal.
  extensionality st'. simpl.
  destruct (s0 st') as [r].
  destruct r as [x' st''].
  destruct x' as [s1]. simpl.
  destruct (s1 st'') as [r'].
  destruct r' as [x'' st'''].
  destruct x'' as [s2]. simpl.
  destruct (s2 st''') as [r''].
  destruct r'' as [x''' st''''].
  f_equal. simpl in *.
  apply proof_irrelevance.
Qed.
Obligation 4.
  unfold IxState_join, IxState_fmap, IxState_pure.
  extensionality st.
  unfold compose, id. simpl.
  destruct st. f_equal.
  extensionality st'. simpl.
  destruct (s0 st') as [r].
  destruct r as [x' st'']. simpl.
  f_equal. apply proof_irrelevance.
Qed.
Obligation 5.
  unfold IxState_join, IxState_pure.
  extensionality st.
  unfold compose, id. simpl.
  destruct st. f_equal.
  extensionality st'. simpl.
  destruct (s0 st') as [r].
  destruct r as [x' st'']. simpl.
  f_equal. apply proof_irrelevance.
Qed.
Obligation 6.
  unfold IxState_join, IxState_fmap.
  extensionality st.
  unfold compose, id. simpl.
  destruct st. f_equal.
  extensionality st'. simpl.
  destruct (s0 st') as [r].
  destruct r as [x' st''].
  destruct x' as [s1]. simpl.
  destruct (s1 st'') as [r'].
  destruct r' as [x'' st''']. simpl.
  f_equal.
Qed.

Definition get : IxState s :=
  St (fun st => existT (fun r : s * s => P st (snd r)) (st, st)
                       (reflexivity st)).

(** There cannot be a definition of [put], since we can only lawfully
    transform the state, not simply replace it.  Therefore, [modify] must be
    used in all cases where [put] would ordinarily have been. *)
Definition modify (f : forall st : s, { st' : s & P st st' }) : IxState unit :=
  St (fun st => match f st with
        | existT st' H =>
            existT (fun r : unit * s => P st (snd r)) (tt, st') H
        end).

End IxState.