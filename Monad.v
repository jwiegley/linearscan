Require Import Ssr.
Require Import FunctionalExtensionality.

Generalizable All Variables.

Class Functor (f : Set -> Set) := {
  fmap : forall {a b : Set}, (a -> b) -> f a -> f b;

  fmap_id   : forall a : Set, fmap (@id a) =1 id;
  fmap_comp : forall (a b c : Set) (f : b -> c) (g : a -> b),
    fmap f \o fmap g =1 fmap (f \o g)
}.

Arguments fmap {f _ a b} _ x.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Definition apply `(f : a -> b) (x : a) : b := f x.

Definition compose {a b c : Set} (f : b -> c) (g : a -> b) : a -> c := f \o g.

Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Lemma first_id : forall a z, first (a:=a) (b:=a) (z:=z) id = id.
Proof.
  rewrite /first.
  move=> a z.
  extensionality x.
  by case: x.
Qed.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Lemma curry_apply_first : forall a b c d (f : (a -> b) -> c -> d),
  curry apply \o first (a:=a -> b) (b:=c -> d) (z:=c) f = curry f.
Proof.
  move=> a b c d f.
  extensionality x.
  by case: x.
Qed.

Notation "f <$> x" :=
  (fmap f x) (at level 28, left associativity, only parsing).
Notation "x <&> f" :=
  (fmap f x) (at level 28, left associativity, only parsing).

Corollary fmap_id_x `{Functor f} : forall (a : Set) x, fmap (@id a) x = x.
Proof. exact: fmap_id. Qed.

Corollary fmap_comp_x `{Functor F} :
  forall (a b c : Set) (f : b -> c) (g : a -> b) x,
  fmap f (fmap g x) = fmap (fun y => f (g y)) x.
Proof. exact: fmap_comp. Qed.

Ltac recomp :=
  repeat match goal with
    | [ |- ?F (?G ?X) = _ ] =>
        replace (F (G X)) with ((F \o G) X); last by rewrite /funcomp
    | [ |- _ = ?F (?G ?X) ] =>
        replace (F (G X)) with ((F \o G) X); last by rewrite /funcomp
    end.

Corollary fmap_docomp `{Functor F} :
  forall (a b c : Set) (f : b -> c) (g : a -> b) x,
  fmap f (fmap g x) = (fmap f \o fmap g) x.
Proof. by rewrite /funcomp. Qed.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Set -> Set) := {
  is_functor :> Functor f;

  pure : forall {a : Set}, a -> f a;
  ap   : forall {a b : Set}, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g);

  ap_id : forall a : Set, ap (pure (@id a)) =1 id;
  ap_comp : forall (a b c : Set) (v : f (a -> b)) (u : f (b -> c)) (w : f a),
    pure compose <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : forall (a b : Set) (x : a) (f : a -> b),
    pure f <*> pure x = pure (f x);
  ap_interchange : forall (a b : Set) (y : a) (u : f (a -> b)),
    u <*> pure y = pure (fun f => f y) <*> u;

  ap_fmap : forall (a b : Set) (f : a -> b),
    ap (pure f) =1 @fmap _ is_functor _ _ f
}.

Arguments pure {f _ _} _.
Arguments ap   {f _ _ _} _ x.

Notation "f <*> g" := (ap f g) (at level 28, left associativity).

Corollary fmap_pure `{Applicative m} : forall (a b : Set) (f : a -> b),
  fmap f \o pure =1 pure \o f.
Proof.
  move=> a b f x.
  rewrite /funcomp -ap_fmap.
  exact: ap_homo.
Qed.

Corollary fmap_pure_x `{Applicative m} : forall (a b : Set) (f : a -> b) x,
  fmap f (pure x) = pure (f x).
Proof. exact: fmap_pure. Qed.

Class Monad (m : Set -> Set) := {
  is_applicative :> Applicative m;

  join : forall {a : Set}, m (m a) -> m a;

  join_fmap_join : forall a : Set, join \o fmap (@join a) =1 join \o join;
  join_fmap_pure : forall a : Set, join \o fmap (pure (a:=a)) =1 id;
  join_pure      : forall a : Set, join \o pure =1 @id (m a);
  join_fmap_fmap : forall (a b : Set) (f : a -> b),
    join \o fmap (fmap f) =1 fmap f \o join
}.

Arguments join {m _ _} _.

Corollary join_fmap_join_x `{Monad m} : forall a x,
  join (fmap (join (a:=a)) x) = join (join x).
Proof. exact: join_fmap_join. Qed.

Corollary join_fmap_pure_x `{Monad m} : forall a x,
  join (fmap (pure (a:=a)) x) = x.
Proof. exact: join_fmap_pure. Qed.

Corollary join_pure_x `{Monad m} : forall a x,
  join (pure x) = @id (m a) x.
Proof. exact: join_pure. Qed.

Corollary join_fmap_fmap_x `{Monad m} : forall (a b : Set) (f : a -> b) x,
    join (fmap (fmap f) x) = fmap f (join x).
Proof. exact: join_fmap_fmap. Qed.

Definition liftA2 `{Applicative m} {A B C : Set}
  (f : A -> B -> C) (x : m A) (y : m B) : m C := ap (fmap f x) y.

Definition const {A B : Set} (x : B) : A -> B := fun _ => x.

Definition chain `{Applicative m} {X Y} (a : m X) (b : m Y) : m Y :=
  fmap const b <*> a.

Notation "a >> b" := (chain a b) (at level 25, left associativity).

Definition bind `{Monad m} {X Y : Set} (f : (X -> m Y)) : m X -> m Y :=
  join \o fmap f.

Notation "m >>= f" := (bind f m) (at level 25, left associativity).

Notation "X <-- A ;; B" := (A >>= (fun X => B))
  (right associativity, at level 84, A at next level).

Notation "A ;; B" := (_ <-- A ;; B)
  (right associativity, at level 84).

Fixpoint mapM `{Applicative m} {A B} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM `{Applicative m} {A B} (l : list A) (f : A -> m B) :
  m (list B) := mapM f l.

Fixpoint mapM_ `{Applicative m} {A B} (f : A -> m B) (l : list A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => f x >> mapM_ f xs
  end.

Definition forM_ `{Applicative m} {A B} (l : list A) (f : A -> m B) : m unit :=
  mapM_ f l.

Definition foldM `{Monad m} {A B : Set}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM `{Monad m} {A B : Set}
  (s : A) (l : list B) (f : A -> B -> m A) : m A := foldM f s l.

Definition foldrM `{Monad m} {A B : Set}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM `{Monad m} {A B : Set}
  (s : A) (l : list B) (f : B -> A -> m A) : m A := foldrM f s l.

Fixpoint concat {A : Set} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x xs => x ++ concat xs
  end.

Definition concatMapM `{Applicative m} {A B : Set}
  (f : A -> m (list B)) (l : list A) : m (list B) :=
  fmap (concat) (mapM f l).

(******************************************************************************
 * The State Monad
 *)

Definition State (s a : Set) := s -> (a * s).

Definition get  {s : Set}     : State s s := fun i => (i, i).
Definition gets {s a : Set} f : State s a := fun s => (f s, s).
Definition put  {s : Set} x   : State s unit := fun _ => (tt, x).

Definition modify {s : Set} (f : s -> s) : State s unit := fun i => (tt, f i).

Program Instance State_Functor {s : Set} : Functor (State s) := {
  fmap := fun A B f (x : State s A) => fun st => match x st with
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

Program Instance State_Applicative {s : Set} : Applicative (State s) := {
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

Program Instance State_Monad {s : Set} : Monad (State s) := {
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

(******************************************************************************
 * The StateT Monad transformer
 *)


Definition StateT (s : Set) (m : Set -> Set) (a : Set):=
  s -> m (a * s)%type.

Definition getT  `{Applicative m} {s : Set}     : StateT s m s :=
  fun i => pure (i, i).
Definition getsT `{Applicative m} {s a : Set} f : StateT s m a :=
  fun s => pure (f s, s).
Definition putT  `{Applicative m} {s : Set} x   : StateT s m unit :=
  fun _ => pure (tt, x).

Definition modifyT `{Applicative m} {s : Set} (f : s -> s) : StateT s m unit :=
  fun i => pure (tt, f i).

Program Instance StateT_Functor {s} `{Functor m} : Functor (StateT s m) := {
  fmap := fun A B f (x : StateT s m A) => fun st =>
    x st <&> first f
}.
Obligation 1.
  move=> x.
  extensionality st.
  rewrite first_id.
  replace (fun z : a * s => (z.1, z.2)) with (@id (a * s)%type); last first.
    by extensionality z; case z.
  by rewrite fmap_id.
Qed.
Obligation 2.
  rewrite /funcomp => x.
  extensionality st.
  rewrite fmap_comp_x /first.
  f_equal.
  extensionality y.
  by case: y.
Qed.

Definition StateT_ap `{Monad m} {s : Set} {a b : Set}
  (f : StateT s m (a -> b)) (x : StateT s m a) : StateT s m b := fun st =>
  join $ f st <&> fun z => match z with
    | (f', st') => x st' <&> first f'
    end.

Program Instance StateT_Applicative `{Monad m} {s : Set} :
  Applicative (StateT s m) := {
  pure := fun _ x => fun st => pure (x, st);
  ap   := @StateT_ap m _ s
}.
Obligation 1.
  move=> x.
  extensionality st.
  rewrite /StateT_ap fmap_pure_x join_pure_x.
  set f := (X in fmap X).
  replace f with (@id (a * s)%type); last first.
    extensionality z.
    by case: z.
  by rewrite fmap_id.
Qed.
Obligation 2.
  extensionality st.
  rewrite /StateT_ap.
  set f := (X in join (fmap X _)).
  set g := (X in fmap f (join (fmap X _))).
  set h := (X in fmap g (join (fmap X _))).
  set i := (X in join (fmap X (u st))).
  rewrite -!join_fmap_fmap_x !fmap_comp_x fmap_pure_x
          join_pure_x -join_fmap_join_x.
  f_equal; rewrite !fmap_comp_x; f_equal.
  extensionality u'.
  case: u' => f' st'.
  rewrite /i -join_fmap_fmap_x.
  f_equal; rewrite !fmap_comp_x; f_equal.
  extensionality v'.
  case: v' => f'' st''.
  rewrite /f /first !fmap_comp_x; f_equal.
  extensionality w'.
  case: w' => f''' st'''.
  by rewrite /funcomp.
Qed.
Obligation 3.
  extensionality st.
  by rewrite /StateT_ap fmap_pure_x join_pure_x fmap_pure_x.
Qed.
Obligation 4.
  extensionality st.
  rewrite /StateT_ap fmap_pure_x.
  set f := (X in join (fmap X _)).
  set g := (X in _ = join (pure (fmap X _))).
  rewrite join_pure_x.
  recomp; f_equal.
  extensionality z.
  have H1 : pure \o g = f.
    rewrite /f /g /funcomp.
    extensionality x.
    case: x => f' st'.
    by rewrite fmap_pure_x.
  by rewrite -H1 /funcomp -fmap_comp_x join_fmap_pure_x.
Qed.
Obligation 5.
  move=> x.
  extensionality st.
  rewrite /StateT_ap fmap_pure_x join_pure_x.
  f_equal.
Qed.

Definition StateT_join `{Monad m} {s a : Set} (x : StateT s m (StateT s m a)) :
  StateT s m a := join \o fmap (curry apply) \o x.

Program Instance StateT_Monad `{Monad m} {s : Set} : Monad (StateT s m) := {
  join := @StateT_join m _ s
}.
Obligation 1.
  move=> f.
  extensionality st.
Admitted.
(*   rewrite /StateT_join /= -!ap_fmap -ap_comp !ap_homo *)
(*           curry_apply_first !ap_fmap -join_fmap_fmap_x *)
(*           -join_fmap_join_x fmap_comp_x. *)
(*   f_equal. *)
(*   rewrite fmap_comp_x. *)
(*   f_equal. *)
(*   extensionality y. *)
(*   by case: y => f' st'. *)
(* Qed. *)
Obligation 2.
  move=> f.
  extensionality st.
  rewrite /StateT_join /= fmap_comp_x /curry /apply /first.
  set h := (X in fmap X _).
  replace h with (@pure m _ (a * s)%type); last first.
    extensionality z.
    by case: z.
  by rewrite join_fmap_pure_x.
Qed.
Obligation 3.
  move=> f.
  extensionality st.
  by rewrite /StateT_join /= fmap_pure_x join_pure_x.
Qed.
Obligation 4.
  move=> x.
  extensionality st.
  rewrite /StateT_join /= -join_fmap_fmap_x.
  f_equal; rewrite !fmap_comp_x; f_equal.
  extensionality y.
  by case: y.
Qed.

Definition lift `{Monad m} {s} `(x : m a) : StateT s m a :=
  fun st => (fun z => (z, st)) <$> x.