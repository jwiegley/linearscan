Require Export Ssreflect.ssrfun.

Generalizable All Variables.

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class IFunctor (F : Type -> Type -> Type -> Type) :=
{ iobj := F
; imap : forall {I O X Y}, (X -> Y) -> F I O X -> F I O Y

; ifun_identity : forall {I O X}, @imap I O _ _ (@id X) =1 id
; ifun_composition : forall {I O X Y Z} (f : Y -> Z) (g : X -> Y),
    imap f \o imap g =1 @imap I O _ _ (f \o g)
}.

Arguments imap             [F] [IFunctor] [I O X] [Y] f g.
Arguments ifun_identity    [F] [IFunctor] [I O X] x.
Arguments ifun_composition [F] [IFunctor] [I O X] [Y] [Z] f g x.

Notation "f <$$> g" := (imap f g) (at level 28, left associativity).

Notation "imap[ M ]  f" := (@imap M _ _ _ f) (at level 28).
Notation "imap[ M N ]  f" := (@imap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "imap[ M N O ]  f" := (@imap (fun X => M (N (O X))) _ _ _ f) (at level 24).

Coercion iobj : IFunctor >-> Funclass.

Section IFunctors.

  Variable F : Type -> Type -> Type -> Type.
  Context `{IFunctor F}.

  Theorem ifun_composition_x
    : forall {I O X Y Z} (f : Y -> Z) (g : X -> Y) (x : F I O X),
    f <$$> (g <$$> x) = (f \o g) <$$> x.
  Proof.
    intros.
    rewrite <- ifun_composition.
    reflexivity.
  Qed.

End IFunctors.
