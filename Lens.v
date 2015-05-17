Require Import LinearScan.Ssr.
Require Import LinearScan.Monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Definition Identity (a : Type) := a.

Program Instance Identity_Functor : Functor Identity := {
  fmap := fun _ _ => id
}.

Program Instance Identity_Applicative : Applicative Identity := {
  pure := fun _ => id;
  ap := fun _ _ => id
}.

Program Instance Identity_Monad : Monad Identity := {
  join := fun _ => id
}.

Definition Const (c a : Type) := c.

Program Instance Const_Functor (c : Type) : Functor (Const c) := {
  fmap := fun _ _ _ => id
}.

Definition Lens s t a b `{Functor f} := (a -> f b) -> s -> f t.

Definition Lens' s a `{Functor f} := Lens s s a a.

Notation "x &+ f" := (f x) (at level 101).

Definition set `(l : @Lens s t a b Identity _) (x : b) : s -> t :=
  l (fun _ => x).

Notation "l .~ x" := (set l x) (at level 100).

Definition over `(l : @Lens s t a b Identity _) (x : a -> b) : s -> t :=
  l x.

Notation "l %~ f" := (over l f) (at level 100).

Definition Getting r s a := @Lens s s a a (Const r) _.

Definition view `(f : Getting a s a) : s -> a := f id.

Notation "x ^_ l" := (view l x) (at level 100).

Definition _1 {a b : Type} `{Functor f} : Lens' (a * b) a := fun f s =>
  let: (x, y) := s in fmap (fun z => (z, y)) (f x).

Definition _2 {a b : Type} `{Functor f} : Lens' (a * b) b := fun f s =>
  let: (x, y) := s in fmap (fun z => (x, z)) (f y).

Compute (view _1 (10, 20)).
Compute (view _2 (10, 20)).
Compute ((10, 20) ^_ _2).
Compute ((10, 20) &+ _1 .~ 500).
Compute ((10, 20) &+ _1 %~ plus 1).
