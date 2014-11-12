Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrfun.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrnat.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** NonEmpty lists *)

Section NonEmptySub.

Variable T : Type.

Structure NonEmpty : Type := NE {neval :> seq T; _ : size neval > 0}.

Notation "[ ::: x1 ]" := (@NE [:: x1] (ltn0Sn 0))
  (at level 0, format "[ :::  x1 ]") : seq_scope.

Notation "[ ::: x & s ]" := (@NE (x :: s) (ltn0Sn (size s)))
  (at level 0, only parsing) : seq_scope.

Coercion list_of_ne i := let: NE s _ := i in s.

Canonical NonEmpty_subType := [subType for list_of_ne].
(* Definition NonEmpty_eqMixin := Eval hnf in [eqMixin of NonEmpty by <:]. *)
(* Canonical NonEmpty_eqType := Eval hnf in EqType NonEmpty NonEmpty_eqMixin. *)
(* Definition NonEmpty_choiceMixin := [choiceMixin of NonEmpty by <:]. *)
(* Canonical NonEmpty_choiceType := *)
(*   Eval hnf in ChoiceType NonEmpty NonEmpty_choiceMixin. *)
(* Definition NonEmpty_countMixin := [countMixin of NonEmpty by <:]. *)
(* Canonical NonEmpty_countType := Eval hnf in CountType NonEmpty NonEmpty_countMixin. *)
(* Canonical NonEmpty_subCountType := [subCountType of NonEmpty]. *)

Definition ne_pred_sort (pT : predType NonEmpty) := pred_sort pT.
Identity Coercion pred_sort_of_ne : ne_pred_sort >-> pred_sort.

Definition NE_ev (ne : NonEmpty) : size ne > 0 :=
  let: NE _ ev := ne in ev.

Definition ne_rect : forall (P : NonEmpty -> Type),
  (forall a, P [::: a])
    -> (forall a (l : NonEmpty), P l -> P [::: a & l])
    -> forall l : NonEmpty, P l.
Proof.
  move=> P H1 H2.
  case. elim=> [//|x xs IHx] H.
  case: xs => [|y ys] in IHx H *.
    have irr: ltn0Sn 0 = H by exact: eq_irrelevance.
    rewrite -irr.
    exact: H1.
  have irr: ltn0Sn (size (y :: ys)) = H by exact: eq_irrelevance.
  rewrite -irr.
  eapply (H2 x (@NE (y :: ys) _)).
  apply IHx.

  Grab Existential Variables.
  by [].
Defined.

Definition ne_rec : forall (P : NonEmpty -> Set),
  (forall a, P [::: a])
    -> (forall a (l : NonEmpty), P l -> P [::: a & l])
    -> forall l : NonEmpty, P l := [eta ne_rect].

Definition ne_ind : forall (P : NonEmpty -> Prop),
  (forall a, P [::: a])
    -> (forall a (l : NonEmpty), P l -> P [::: a & l])
    -> forall l : NonEmpty, P l := [eta ne_rect].

Definition NE_length : NonEmpty -> nat := size.

Definition NE_head (ne : NonEmpty) : T.
Proof.
  move: ne => [s H].
  case: s => //= [|s] in H *.
Defined.

Definition NE_rcons (ne : NonEmpty) (a : T) : NonEmpty.
Proof.
  move: ne => [s H].
  apply: (@NE (rcons s a) _).
  rewrite size_rcons.
  exact: ltn0Sn.
Defined.

Definition NE_reverse (ne : NonEmpty) : NonEmpty.
Proof.
  move: ne => [s H].
  apply: (@NE (rev s) _).
  by rewrite size_rev.
Defined.

Definition NE_last (ne : NonEmpty) : T.
Proof.
  move: ne => [s H].
  case: s => [//|x xs] in H *.
  exact: (last x xs).
Defined.

End NonEmptySub.

Arguments NE [T] neval H.
Arguments NE_last [T] ne.

Notation "[ ::: x1 ]" := (NE [:: x1] (ltn0Sn 0))
  (at level 0, format "[ :::  x1 ]") : seq_scope.

Notation "[ ::: x & s ]" := (NE (x :: s) (ltn0Sn (size s)))
  (at level 0, only parsing) : seq_scope.

Definition NE_map {a b : Type} (f : a -> b) (ne : NonEmpty a) : NonEmpty b.
Proof.
  move: ne => [s H].
  apply: (@NE _ (map f s) _).
  by rewrite size_map.
Defined.

Definition NE_fold_left {a b} (f : a -> b -> a) (ne : NonEmpty b) (z : a) :=
  foldl f z ne.

Definition NE_append {T} (l1 l2 : NonEmpty T) : NonEmpty T.
Proof.
  move: l1 => [s1 H1].
  move: l2 => [s2 H2].
  apply: (@NE _ (s1 ++ s2) _).
  rewrite size_cat addn_gt0.
  by apply/orP; left.
Defined.

Lemma NE_head_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_head (NE_append xs ys) = NE_head xs.
Proof.
  move=> a xs ys.
  rewrite /NE_head.
  elim/ne_ind: xs => //= [x|x xs IHxs].
    by case: ys.
  by case: ys => // in IHxs *.
Qed.

Lemma NE_last_append_spec : forall {a} {xs ys : NonEmpty a},
  NE_last (NE_append xs ys) = NE_last ys.
Proof.
  move=> a xs ys.
  move: xs => [s1 H1].
  move: ys => [s2 H2].
  case: s1 => //= [? ?] in H1 *.
  case: s2 => //= [? ?] in H2 *.
  by rewrite last_cat.
Qed.

Section Sorted.

Variable A : eqType.
Variable R : rel A.

Definition NE_Forall (P : A -> bool) (ne : NonEmpty A) : bool :=
  let: NE xs H := ne in all P xs.
Arguments NE_Forall P ne /.

Lemma NE_Forall_head : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_head xs).
Proof.
  move=> P.
  case=> [s H] Hall.
  case: s => //= [? ?] in H Hall *.
  by move/andP: Hall => [? _].
Defined.

Lemma NE_Forall_last : forall P (xs : NonEmpty A),
  NE_Forall P xs -> P (NE_last xs).
Proof.
  move=> P.
  case=> [s H].
  move/allP.
  apply.
  move: mem_last.
  case: s => //= in H *.
Defined.

Lemma NE_Forall_append : forall (P : A -> bool) xs ys,
   NE_Forall P xs /\ NE_Forall P ys <-> NE_Forall P (NE_append xs ys).
Proof.
  move=> ? //=.
  case=> [? ?].
  case=> [? ?].
  split.
    move=> [? ?] /=.
    rewrite all_cat.
    by apply/andP.
  move: all_cat => /= -> /andP [? ?].
  by split.
Defined.

Definition NE_StronglySorted (ne : NonEmpty A) : bool :=
  let: NE s H := ne in
  if s is s :: ss then all id (pairmap R s ss) else true.
Arguments NE_StronglySorted ne /.

Lemma NE_StronglySorted_inv_app : forall (l1 l2 : NonEmpty A),
  NE_StronglySorted (NE_append l1 l2)
    -> NE_StronglySorted l1 && NE_StronglySorted l2.
Proof.
  move=> l1 l2 /=.
  move: l1 => [s1 H1].
  move: l2 => [s2 H2] /= H.
  apply/andP; split;
  case: s1 => // [? ?] in H1 H *;
  case: s2 => // [? ?] in H2 H *;
  by move: pairmap_cat all_cat H => /= -> -> /andP [? /= /andP [_ ?]].
Defined.

Lemma NE_StronglySorted_impl_app : forall (l1 l2 : NonEmpty A),
  NE_StronglySorted (NE_append l1 l2) -> R (NE_last l1) (NE_head l2).
Proof.
  move=> l1 l2 /=.
  move: l1 => [s1 H1].
  move: l2 => [s2 H2] /= H.
  case: s1 => // [x xs] in H1 H *;
  case: s2 => // [y ys] in H2 H *.
  move: pairmap_cat all_cat H => /= -> ->.
  by move/andP => [_ /andP [? _]].
Defined.

End Sorted.

Section Membership.

Definition NE_member {a : eqType} (z : a) (ne : NonEmpty a) : Prop :=
  let: NE xs _ := ne in z \in xs.
Arguments NE_member [a] z ne /.

Lemma NE_Forall_member_spec {a : eqType} (z : a) (ne : NonEmpty a) :
  forall f, NE_Forall f ne -> NE_member z ne -> f z.
Proof.
  move: ne => [x xs] f /= Hall Hin.
  move/allP in Hall.
  exact: Hall.
Defined.

End Membership.

Definition NE_inj : forall T (xs ys : seq T) Hxs Hys,
  xs = ys <-> NE xs Hxs = NE ys Hys.
Proof.
  move=> T xs ys Hxs Hys.
  split; last congruence.
  move=> H; move: H => -> in Hxs Hys *.
  by have ->: Hxs = Hys by exact: eq_irrelevance.
Defined.
