Generalizable All Variables.

Definition State (s a : Type) := s -> (a * s).

Definition get  {s}     : State s s := fun i => (i, i).
Definition gets {s a} f : State s a := fun s => (f s, s).
Definition put  {s} x   : State s unit := fun _ => (tt, x).

Definition modify {s} (f : s -> s) : State s unit := fun i => (tt, f i).

Record Monad (m : Type -> Type) := {
  fmap : forall a b, (a -> b) -> m a -> m b;
  pure : forall a, a -> m a;
  ap   : forall a b, m (a -> b) -> m a -> m b;
  join : forall a, m (m a) -> m a
}.

Arguments fmap {m} _ {a b} f x.
Arguments pure {m} _ {a} _.
Arguments ap   {m} _ {a b} f x.
Arguments join {m} _ {a} _.

Definition State_Monad {S} :=
  {| fmap := fun A B f (x : State S A) => fun st => match x st with
       | (a,st') => (f a, st')
       end

   ; pure := fun _ x => fun st => (x, st)

   ; ap := fun _ _ f x => fun st => match f st with
       | (f', st') =>
           match x st' with
           | (x', st'') => (f' x', st'')
           end
       end

   ; join := fun _ x => fun st => match x st with
       | (y, st') => match y st' with
         | (a, st'') => (a, st'')
         end
       end
   |}.

Definition bind `(d : Monad m) {X Y} (f : (X -> m Y)) (x : m X) : m Y :=
  join d (fmap d f x).

Definition liftA2 `(d : Monad m) {A B C}
  (f : A -> B -> C) (x : m A) (y : m B) : m C := ap d (fmap d f x) y.

Notation "m >>=[ d ] f" := (bind d f m) (at level 25, left associativity).

Notation "X <-- A ;;[ d ] B" := (A >>=[d] (fun X => B))
  (right associativity, at level 84, A at next level).

Notation "A ;;[ d ] B" := (_ <-- A ;;[d] B)
  (right associativity, at level 84).

Fixpoint mapM `(d : Monad m) {A B} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure d nil
  | cons x xs => liftA2 d (@cons _) (f x) (mapM d f xs)
  end.

Definition forM `(d : Monad m) {A B} (l : list A) (f : A -> m B) : m (list B) :=
  mapM d f l.

Fixpoint mapM_ `(d : Monad m) {A B} (f : A -> m B) (l : list A) : m unit :=
  match l with
  | nil => pure d tt
  | cons x xs => f x >>=[d] fun _ => mapM_ d f xs
  end.

Definition forM_ `(d : Monad m) {A B} (l : list A) (f : A -> m B) : m unit :=
  mapM_ d f l.

Definition foldM `(d : Monad m) {A B}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure d z
        | cons y ys => f z y >>=[d] go ys
      end in
  go l s.

Definition forFoldM `(d : Monad m) {A B}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM d f s l.

Definition foldrM `(d : Monad m) {A B}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure d z
        | cons y ys => go ys z >>=[d] f y
      end in
  go l s.

Definition forFoldrM `(d : Monad m) {A B}
  (s : A) (l : list B) (f : B -> A -> m A) : m A := foldrM d f s l.

Fixpoint concat `(d : Monad m) {A} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x xs => app x (concat d xs)
  end.

Definition concatMapM `(d : Monad m) {A B}
  (f : A -> m (list B)) (l : list A) : m (list B) :=
  fmap d (concat d) (mapM d f l).
