Generalizable All Variables.

Definition State (s a : Type) := s -> (a * s).

Definition get  {s}     : State s s := fun i => (i, i).
Definition gets {s a} f : State s a := fun s => (f s, s).
Definition put  {s} x   : State s unit := fun _ => (tt, x).

Definition modify {s} (f : s -> s) : State s unit := fun i => (tt, f i).

Definition join : forall {S X}, State S (State S X) -> State S X :=
  fun _ _ x => fun st => match x st with
    | (y, st') => match y st' with
      | (a, st'') => (a, st'')
      end
    end.

Definition fmap : forall {S A B}, (A -> B) -> State S A -> State S B :=
  fun _ _ _ f x => fun st => match x st with
    | (a,st') => (f a, st')
    end.

Definition bind {S X Y} (f : (X -> State S Y)) (x : State S X) : State S Y :=
  @join _ Y (@fmap _ _ _ f x).

Definition pure {S X} : X -> State S X := fun x => fun st => (x, st).

Definition ap {S X Y} (f : State S (X -> Y)) (x : State S X) : State S Y :=
  fun st =>
    match f st with
    | (f', st') =>
        match x st' with
        | (x', st'') => (f' x', st'')
        end
    end.

Definition liftA2 {S A B C} (f : A -> B -> C)
  (x : State S A) (y : State S B) : State S C :=
  ap (fmap f x) y.

Notation "m >>= f" := (bind f m) (at level 25, left associativity).

Notation "X <-- A ;; B" := (A >>= (fun X => B))
  (right associativity, at level 84, A at next level).

Notation "A ;; B" := (_ <-- A ;; B)
  (right associativity, at level 84, A1 at next level).

Fixpoint mapM {S A B} (f : A -> State S B) (l : list A) : State S (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM {S A B} (l : list A) (f : A -> State S B) : State S (list B) :=
  mapM f l.

Fixpoint mapM_ {S A B} (f : A -> State S B) (l : list A) : State S unit :=
  match l with
  | nil => pure tt
  | cons x xs => f x >>= fun _ => mapM_ f xs
  end.

Definition forM_ {S A B} (l : list A) (f : A -> State S B) : State S unit :=
  mapM_ f l.

Definition foldM {S A B}
  (f : A -> B -> State S A) (s : A) (l : list B) : State S A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM {S A B}
  (s : A) (l : list B) (f : A -> B -> State S A) : State S A := foldM f s l.

Definition foldrM {S A B}
  (f : B -> A -> State S A) (s : A) (l : list B) : State S A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM {S A B}
  (s : A) (l : list B) (f : B -> A -> State S A) : State S A := foldrM f s l.

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x xs => app x (concat xs)
  end.

Definition concatMapM {S A B}
  (f : A -> State S (list B)) (l : list A) : State S (list B) :=
  fmap concat (mapM f l).
