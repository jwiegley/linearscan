Require Import Ssr.
Require Import FunctionalExtensionality.

Generalizable All Variables.

Definition State (s a : Type) := s -> (a * s).

Definition get  {s}     : State s s := fun i => (i, i).
Definition gets {s a} f : State s a := fun s => (f s, s).
Definition put  {s} x   : State s unit := fun _ => (tt, x).

Definition modify {s} (f : s -> s) : State s unit := fun i => (tt, f i).

Class Functor (f : Type -> Type) := {
  fmap : forall {a b}, (a -> b) -> f a -> f b;

  fun_id   : forall a, fmap (@id a) =1 id;
  fun_comp : forall a b c f g, @fmap b c f \o @fmap a b g =1 @fmap a c (f \o g)
}.

Arguments fmap {f _ a b} _ x.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f;

  pure : forall {a}, a -> f a;
  ap   : forall {a b}, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g);

  ap_id : forall a, ap (pure (@id a)) =1 id;
  ap_comp : forall a b c (v : f (a -> b)) (u : f (b -> c)) (w : f a),
    pure (funcomp tt) <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : forall a b (x : a) (f : a -> b), pure f <*> pure x = pure (f x);
  ap_interchange : forall a b (y : a) (u : f (a -> b)),
    u <*> pure y = pure (fun f => f y) <*> u;

  ap_fmap : forall a b (f : a -> b), ap (pure f) =1 @fmap _ is_functor _ _ f
}.

Arguments pure {f _ _} _.
Arguments ap   {f _ _ _} _ x.

Class Monad (m : Type -> Type) := {
  is_applicative :> Applicative m;

  join : forall {a}, m (m a) -> m a;

  join_fmap_join : forall a, join \o fmap (@join a) =1 join \o join;
  join_fmap_pure : forall a, join \o fmap (pure (a:=a)) =1 id;
  join_pure      : forall a, join \o pure =1 @id (m a);
  join_fmap_fmap : forall a b (f : a -> b),
    join \o fmap (fmap f) =1 fmap f \o join
}.

Arguments join {m _ _} _.

Program Instance State_Functor {S} : Functor (State S) := {
  fmap := fun A B f (x : State S A) => fun st => match x st with
    | (a,st') => (f a, st')
    end
}.
Obligation 1.
  move=> x.
  extensionality st.
  by case: (x st).
Qed.
Obligation 2.
  rewrite /funcomp => x.
  extensionality st.
  by case: (x st).
Qed.

Program Instance State_Applicative {S} : Applicative (State S) := {
  pure := fun _ x => fun st => (x, st);

  ap := fun _ _ f x => fun st => match f st with
    | (f', st') =>
        match x st' with
        | (x', st'') => (f' x', st'')
        end
    end
}.
Obligation 1.
  move=> x.
  extensionality st.
  by case: (x st).
Qed.
Obligation 2.
  extensionality st.
  case: (u st) => f' st'.
  case: (v st') => f'' st''.
  by case: (w st'').
Qed.

Program Instance State_Monad {S} : Monad (State S) := {
  join := fun _ x => fun st => match x st with
    | (y, st') => match y st' with
      | (a, st'') => (a, st'')
      end
    end
}.
Obligation 1.
  move=> f.
  extensionality st.
  rewrite /funcomp /=.
  case: (f st) => f' st'.
  case: (f' st') => f'' st''.
  by case: (f'' st'') => f''' st'''.
Qed.
Obligation 2.
  move=> f.
  extensionality st.
  rewrite /funcomp /=.
  by case: (f st) => f' st'.
Qed.
Obligation 3.
  move=> f.
  extensionality st.
  rewrite /funcomp /=.
  by case: (f st) => f' st'.
Qed.
Obligation 4.
  move=> x.
  extensionality st.
  rewrite /funcomp /=.
  case: (x st) => f' st'.
  by case: (f' st') => f'' st''.
Qed.

Definition bind `{Monad m} {X Y} (f : (X -> m Y)) (x : m X) : m Y :=
  join (fmap f x).

Definition liftA2 `{Monad m} {A B C}
  (f : A -> B -> C) (x : m A) (y : m B) : m C := ap (fmap f x) y.

Notation "m >>= f" := (bind f m) (at level 25, left associativity).

Notation "X <-- A ;; B" := (A >>= (fun X => B))
  (right associativity, at level 84, A at next level).

Notation "A ;; B" := (_ <-- A ;; B)
  (right associativity, at level 84).

Fixpoint mapM `{Monad m} {A B} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM `{Monad m} {A B} (l : list A) (f : A -> m B) : m (list B) :=
  mapM f l.

Fixpoint mapM_ `{Monad m} {A B} (f : A -> m B) (l : list A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => f x >>= fun _ => mapM_ f xs
  end.

Definition forM_ `{Monad m} {A B} (l : list A) (f : A -> m B) : m unit :=
  mapM_ f l.

Definition foldM `{Monad m} {A B}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM `{Monad m} {A B}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM `{Monad m} {A B}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM `{Monad m} {A B}
  (s : A) (l : list B) (f : B -> A -> m A) : m A := foldrM f s l.

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x xs => app x (concat xs)
  end.

Definition concatMapM `{Monad m} {A B}
  (f : A -> m (list B)) (l : list A) : m (list B) :=
  fmap (concat) (mapM f l).
