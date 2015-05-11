Require Import Ssr.
Require Import Monad.
Require Import FunctionalExtensionality.

Generalizable All Variables.

Definition Yoneda (f : Type -> Type) (a : Type) :=
  forall {r : Type}, (a -> r) -> f r.

Class Isomorphism (A B : Type) : Type := {
    iso_to   : A -> B;
    iso_from : B -> A;

    iso_to_id   : iso_from \o iso_to =1 id;
    iso_from_id : iso_to \o iso_from =1 id
}.

Arguments iso_to   {A} {B} {Isomorphism} _.
Arguments iso_from {A} {B} {Isomorphism} _.

Infix "≅" := Isomorphism (at level 30) : type_scope.

Definition Iso (A B : Type) : Prop := inhabited (A ≅ B).

Program Instance Yoneda_lemma `{Functor f} : forall a, Yoneda f a ≅ f a := {
    iso_to   := fun x => x _ id;
    iso_from := fun x => fun _ k => fmap k x
}.
Obligation 1.
  move=> x /=.
  extensionality r.
  extensionality g.
  exact: fmap_cps.
Qed.
Obligation 2.
  move=> x.
  by rewrite /funcomp fmap_id.
Qed.

Program Instance Yoneda_Functor {f : Type -> Type} : Functor (Yoneda f) := {
  fmap := fun _ _ g k => fun _ h => k _ (h \o g)
}.

Program Instance Yoneda_Applicative `{Applicative f} :
  Applicative (Yoneda f) := {
  pure := fun _ x => fun _ k => pure (k x);
  ap   := fun a b g x => fun _ k => g _ (comp k) <*> iso_to x
}.
Obligation 1.
  move=> x /=.
  extensionality r.
  extensionality k0.
  rewrite ap_fmap -fmap_comp /funcomp fmap_id.
  exact: fmap_cps.
Qed.
Obligation 2.
  extensionality r.
  extensionality k.
  rewrite -ap_comp; f_equal.
  rewrite !ap_fmap; f_equal.
  rewrite !fmap_cps; f_equal.
Qed.
Obligation 3.
  extensionality r.
  extensionality k.
  by rewrite ap_fmap /compose -fmap_comp /funcomp !fmap_pure_x.
Qed.
Obligation 4.
  extensionality r.
  extensionality k.
  rewrite ap_fmap -fmap_comp ap_interchange /funcomp
          ap_fmap !fmap_cps.
  f_equal.
Qed.
Obligation 5.
  move=> k /=.
  extensionality r.
  extensionality g.
  rewrite ap_fmap -fmap_comp /funcomp !fmap_cps.
  f_equal.
Qed.

Definition Yoneda_join `{Monad m} `(k : Yoneda m (Yoneda m a)) : Yoneda m a :=
  fun _ h => join (k _ (fun y => y _ h)).

Program Instance Yoneda_Monad `{Monad m} : Monad (Yoneda m) := {
  join := @Yoneda_join m _
}.
Obligation 1.
  move=> k /=.
  rewrite /Yoneda_join.
  extensionality r.
  extensionality h.
  by rewrite -join_fmap_join_x fmap_cps.
Qed.
Obligation 2.
  move=> k /=.
  rewrite /Yoneda_join.
  extensionality r.
  extensionality h.
  by rewrite -fmap_cps join_fmap_pure_x.
Qed.
Obligation 3.
  move=> k /=.
  rewrite /Yoneda_join.
  extensionality r.
  extensionality h.
  by rewrite join_pure_x.
Qed.