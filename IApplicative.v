Require Export IEndo.

Require Import Ssreflect.ssrfun.

Generalizable All Variables.

Reserved Notation "f <**> g" (at level 28, left associativity).

Class IApplicative (F : Type -> Type -> Type -> Type) :=
{ is_ifunctor :> IFunctor F

; ipure : forall {I X}, X -> F I I X
; iap : forall {I J K X Y}, F I J (X -> Y) -> F J K X -> F I K Y
    where "f <**> g" := (iap f g)

; iapp_identity : forall {I X}, @iap _ _ I _ _ (@ipure I _ (@id X)) =1 id
; iapp_composition
    : forall {I J K L X Y Z}
             (u : F I J (Y -> Z)) (v : F J K (X -> Y)) (w : F K L X),
    ipure comp <**> u <**> v <**> w = u <**> (v <**> w)
; iapp_homomorphism : forall {I X Y} (x : X) (f : X -> Y),
    ipure f <**> ipure x = @ipure I _ (f x)
; iapp_interchange : forall {I J X Y} (y : X) (u : F I J (X -> Y)),
    u <**> ipure y = ipure (fun f => f y) <**> u

; app_imap_unit : forall {I O X Y} (f : X -> Y),
    iap (ipure f) = @imap _ _ I O _ _ f
}.

Notation "ipure/ M" := (@ipure M _ _) (at level 28).
Notation "ipure/ M N" := (@ipure (fun X => M (N X)) _ _) (at level 26).

Notation "iap[ M ]  f" := (@iap M _ _ _ f) (at level 28).
Notation "iap[ M N ]  f" := (@iap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "iap[ M N O ]  f" := (@iap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Notation "f <**> g" := (iap f g) (at level 28, left associativity).

(* Notation "[| f x y .. z |]" := (.. (f <$$> x <**> y) .. <**> z) *)
(*     (at level 9, left associativity, f at level 9, *)
(*      x at level 9, y at level 9, z at level 9). *)

Definition iapp_merge {X Y Z W} (f : X -> Y) (g : Z -> W)
  (t : X * Z) : Y * W  :=
  match t with (x, z) => (f x, g z) end.

Definition iapp_prod {F : Type -> Type -> Type -> Type} `{IApplicative F}
  {I J K X Y} (x : F I J X) (y : F J K Y) : F I K (X * Y)%type := pair <$$> x <**> y.

Notation "f *** g" := (iapp_merge f g) (at level 28, left associativity).

Notation "f ** g" := (iapp_prod f g) (at level 28, left associativity).

Ltac rewrite_iapp_homomorphisms :=
  (repeat (rewrite <- app_imap_unit);
   rewrite iapp_homomorphism;
   repeat (rewrite app_imap_unit)).

Section IApplicatives.

  Variable F : Type -> Type -> Type -> Type.
  Context `{IApplicative F}.

  Theorem iapp_homomorphism_2
    : forall {I X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
    f <$$> ipure x <**> ipure y = @ipure _ _ I _ (f x y).
  Proof.
    intros.
    rewrite <- iapp_homomorphism.
    rewrite <- iapp_homomorphism.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  (* This theorem was given as an exercise by Brent Yorgey at:

     http://www.haskell.org/haskellwiki/Typeclassopedia#IApplicative
  *)
  Theorem iapp_flip : forall {J K X Y} (x : F J K X) (f : X -> Y),
    ipure f <**> x = ipure (fun x f => f x) <**> x <**> ipure f.
  Proof.
    intros.
    rewrite iapp_interchange.
    rewrite <- iapp_composition.
    rewrite app_imap_unit.
    rewrite app_imap_unit.
    rewrite iapp_homomorphism_2.
    unfold funcomp.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  Definition iapp_unit : F unit unit unit := ipure tt.

  Theorem iapp_embed
    : forall {G : Type -> Type -> Type -> Type} `{IApplicative G}
             {I J K X Y} (x : G I J (X -> Y)) (y : G J K X),
    ipure (x <**> y) = ipure iap <**> ipure x <**> @ipure _ _ K _ y.
  Proof.
    intros.
    rewrite_iapp_homomorphisms.
    rewrite <- iapp_homomorphism.
    rewrite <- app_imap_unit.
    reflexivity.
  Qed.

  Theorem iapp_naturality
    : forall {I J K A B C D}
             (f : A -> C) (g : B -> D) (u : F I J A) (v : F J K B),
    imap (f *** g) (u ** v) = (imap f u) ** (imap g v).
  Proof.
    intros.
    unfold iapp_prod.
    rewrite <- app_imap_unit.
    rewrite ifun_composition_x.
    repeat (rewrite <- app_imap_unit).
    rewrite <- iapp_composition.
    rewrite <- iapp_composition.
    rewrite <- iapp_composition.
    rewrite <- iapp_composition.
    rewrite iapp_composition.
    rewrite iapp_composition.
    f_equal.
    rewrite_iapp_homomorphisms.
    rewrite ifun_composition_x.
    rewrite ifun_composition_x.
    rewrite iapp_interchange.
    rewrite app_imap_unit.
    rewrite ifun_composition_x.
    f_equal.
  Qed.

  Definition liftIA2 {I J K A B C} (f : A -> B -> C)
    (x : F I J A) (y : F J K B) : F I K C :=
    f <$$> x <**> y.

End IApplicatives.
