Require Export LinearScan.IApplicative.

Require Import Ssreflect.ssrfun.

Class IMonad (M : Type -> Type -> Type -> Type) :=
{ is_iapplicative :> IApplicative M

; ijoin : forall {I A O X}, M I A (M A O X) -> M I O X

; imonad_law_1 : forall {I O J K X},
    (@ijoin I J O X) \o imap ijoin =1 (@ijoin I K O X) \o (@ijoin I J K _)
; imonad_law_2 : forall {I X},
    ijoin \o @imap _ _ I _ _ _ (@ipure M is_iapplicative I X) =1 id
; imonad_law_3 : forall {I O X},
    (@ijoin _ _ O X) \o (@ipure _ _ I _) =1 id
; imonad_law_4 : forall {I O A X Y} (f : X -> Y),
    ijoin \o imap (imap f) =1 imap f \o (@ijoin I A O _)
}.

Notation "ijoin/ M" := (@ijoin M _ _ _ _ _) (at level 28).
Notation "ijoin/ M N" := (@ijoin (fun X => M (N X)) _ _ _ _ _) (at level 26).

Definition ibind {M : Type -> Type -> Type -> Type} `{IMonad M} {I J K X Y}
  (f : (X -> M J K Y)) (x : M I J X) : M I K Y :=
  @ijoin M _ I J K Y (@imap _ _ I J _ _ f x).

Notation "m >>>= f" := (ibind f m) (at level 25, left associativity).

Notation "X <<- A ;; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

Notation "A ;;; B" := (_ <<- A ;; B)
  (right associativity, at level 84, A1 at next level).

Theorem imonad_law_1_x
  : forall M (m_dict : IMonad M) I J K O A (x : M I J (M J K (M K O A))),
  ijoin (imap ijoin x) = (@ijoin M m_dict _ _ _ A) (ijoin x).
Proof.
  intros.
  assert (ijoin (imap ijoin x) = (ijoin \o imap ijoin) x).
    unfold funcomp. reflexivity.
  assert (ijoin (ijoin x) = (ijoin \o ijoin) x).
    unfold funcomp. reflexivity.
  rewrite H. rewrite H0.
  rewrite imonad_law_1.
  reflexivity.
Qed.

Theorem imonad_law_2_x
  : forall M (m_dict : IMonad M) I A (x : M I I A),
  ijoin (@imap _ _ I I _ _ (@ipure M _ I A) x) = x.
Proof.
  intros.
  assert (ijoin (imap ipure x) = (ijoin \o imap ipure) x).
    unfold funcomp. reflexivity.
  rewrite H.
  rewrite imonad_law_2.
  reflexivity.
Qed.

Theorem imonad_law_3_x
  : forall M (m_dict : IMonad M) I A (x : M I I A),
  (@ijoin M m_dict _ _ _ A) (ipure x) = x.
Proof.
  intros.
  assert (ijoin (ipure x) = (ijoin \o ipure) x).
    unfold funcomp. reflexivity.
  rewrite H.
  rewrite imonad_law_3.
  reflexivity.
Qed.

Theorem imonad_law_4_x
  : forall M (m_dict : IMonad M)
      I J O A B (f : A -> B) (x : M I J (M J O A)),
  ijoin (imap (imap f) x) = imap f (ijoin x).
Proof.
  intros.
  assert (ijoin (imap (imap f) x) = (ijoin \o imap (imap f)) x).
    unfold funcomp. reflexivity.
  assert (imap f (ijoin x) = (imap f \o ijoin) x).
    unfold funcomp. reflexivity.
  rewrite H. rewrite H0.
  rewrite imonad_law_4.
  reflexivity.
Qed.

Theorem imonad_assoc : forall M `{IMonad M}
  {I J K L A B C} (m : M I J A) (f : A -> M J K B) (g : B -> M K L C),
  m >>>= f >>>= g = m >>>= (fun x => f x >>>= g).
Proof.
  intros.
  unfold ibind.
  rewrite <- imonad_law_4_x.
  rewrite ifun_composition_x.
  rewrite <- imonad_law_1_x.
  rewrite ifun_composition_x.
  f_equal.
Qed.

Fixpoint mapM {M} `{IMonad M} {I A B}
  (f : A -> M I I B) (l : list A) : M I I (list B) :=
  match l with
  | nil => ipure nil
  | cons x xs => liftIA2 M (@cons _) (f x) (mapM f xs)
  end.

Definition foldM {M} `{IMonad M} {I A B}
  (f : A -> B -> M I I A) (s : A) (l : list B) : M I I A :=
  let fix go xs z :=
      match xs with
        | nil => ipure z
        | cons y ys => f z y >>>= go ys
      end in
  go l s.

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x xs => app x (concat xs)
  end.

Definition concatMapM {M} `{IMonad M} {I A B}
  (f : A -> M I I (list B)) (l : list A) : M I I (list B) :=
  concat <$$> mapM f l.

Definition mapMaybeM {M} `{IMonad M} {I A B}
  (f : A -> M I I (option B)) : list A -> M I I (list B) :=
  foldM (fun acc x =>
           mx' <<- f x ;;
           ipure (match mx' with
             | None => acc
             | Some x' => cons x' acc
             end)) nil.
