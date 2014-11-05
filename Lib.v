Require Export Coq.Bool.Bool.
Require Export Coq.Logic.ProofIrrelevance.
Require Export Coq.Numbers.Natural.Peano.NPeano.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Tactics.
Require Export Coq.Sorting.Sorting.
Require Export Coq.Structures.Orders.
Require Export NonEmpty.
Require Export Omega.
Require Export Tactics.

Require Export Vector.
Require Coq.Vectors.Vector.
Module V := Coq.Vectors.Vector.
Definition Vec := V.t.

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

(** The following are extensions to the Coq standard library. *)

Definition undefined {a : Type} : a. Admitted.

Definition ex_falso_quodlibet : forall {P : Type}, False -> P.
Proof. intros P. contra. Defined.

Notation "p .1" := (proj1_sig p)
  (at level 2, left associativity, format "p .1").
Notation "p .2" := (proj2_sig p)
  (at level 2, left associativity, format "p .2").
Notation "( x ; y )" := (exist _ x y).

Definition uncurry_sig {A C} {B : A -> Prop}
  (f : forall x : A, B x -> C) (p : { x : A | B x }) : C :=
  let (x,H) := p in f x H.

Definition fromMaybe {a} (d : a) (mx : option a) : a :=
  match mx with
    | Some x => x
    | None => d
  end.

Definition option_map `(f : a -> b) (x : option a) : option b :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.

Definition option_choose {a} (x y : option a) : option a :=
  match x with
  | None => y
  | Some _ => x
  end.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require String.
Open Scope string_scope.

Lemma list_cons_nonzero : forall {a x} {xs l : list a},
  l = x :: xs -> size l > 0.
Proof. by move=> a x xs l ->. Qed.

Definition exist_in_cons : forall {A : eqType} {a} {l : list A},
  {x : A | x \in l} -> {x : A | x \in a :: l}.
Proof.
  move=> A a l.
  case=> x H.
  exists x.
  rewrite in_cons.
  by apply/orP; right.
Defined.

Definition list_membership {a : eqType} (l : list a) : list { x : a | x \in l } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          exist _ x (mem_head _ xs) :: map exist_in_cons (go xs)
      end in
  go l.

Definition projTT1 {A} {P Q : A -> Type} (e : {x : A & P x & Q x}) : A :=
  let (x,_,_) := e in x.

(* Definition projTT2 {A} {P Q : A -> Type} (e : {x : A & P x & Q x}) : *)
(*   P (projTT1 e) := let (x,p,_) as x return (P (projTT1 x)) := e in p. *)

(* Definition projTT3 {A} {P Q : A -> Type} (e : {x : A & P x & Q x}) : *)
(*   Q (projTT1 e) := let (x,_,q) as x return (Q (projTT1 x)) := e in q. *)

Definition proj1_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x}) : A :=
  let (x,_,_) := e in x.

(* Definition proj2_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x}) : *)
(*   P (proj1_sigg e) := let (x,p,_) as x return (P (proj1_sigg x)) := e in p. *)

(* Definition proj3_sigg {A} {P Q : A -> Prop} (e : {x : A | P x & Q x}) : *)
(*   Q (proj1_sigg e) := let (x,_,q) as x return (Q (proj1_sigg x)) := e in q. *)

Lemma ltn_odd n m : odd n && odd m -> n < m -> n.+1 < m.
Proof.
  move/andP=> [nodd modd] Hlt.
  rewrite -subn_gt0 odd_gt0 // odd_sub // modd /= negb_involutive //.
Qed.

Lemma odd_succ_succ n : odd (n.+2) = odd n.
Proof. rewrite /= negb_involutive //. Qed.

Lemma lt_dec : forall n m, (n < m) -> (n < m)%coq_nat.
Proof. move=> n m H. destruct (@ltP n m); [ done | inv H ]. Qed.

Lemma lt_dec_iff : forall n m, (n < m) <-> (n < m)%coq_nat.
Proof.
  split. apply lt_dec.
  move=> H. destruct (@ltP n m); [ done | inv H ].
Qed.

Lemma le_dec : forall n m, (n <= m) -> (n <= m)%coq_nat.
Proof. move=> n m H. destruct (@leP n m); [ done | inv H ]. Qed.

Lemma le_dec_iff : forall n m, (n <= m) <-> (n <= m)%coq_nat.
Proof.
  split. apply le_dec.
  move=> H. destruct (@leP n m); [ done | inv H ].
Qed.

Ltac ssomega :=
  repeat match goal with
    | [ H : is_true (leq (S ?N) ?M)  |- _ ] =>
        destruct (@ltP N M); last done
    | [ H : is_true (leq ?N ?M)  |- _ ] =>
        destruct (@leP N M); last done
    | [ |- is_true (leq (S _) _) ] => apply lt_dec_iff
    | [ |- is_true (leq _ _) ] => apply le_dec_iff
  end; omega.

Lemma leq_min : forall m n p, n <= p -> minn m n <= p.
Proof. intros. rewrite geq_min. by elim: (m <= p). Qed.

Lemma ltn_min : forall m n p, n < p -> minn m n < p.
Proof. intros. rewrite gtn_min. by elim: (m < p). Qed.

Lemma ltn_max : forall m n p, p < n -> p < maxn m n.
 Proof. move=> *. by rewrite leq_max; intuition. Qed.

Lemma lt_le_shuffle : forall {x y z w}, x < y -> y <= z -> z < w -> x < w.
Proof. intros. ssomega. Qed.

Lemma le_Sn_le : forall n m : nat, n.+1 <= m -> n <= m.
Proof. intros. ssomega. Qed.

Lemma ltn_plus : forall m n, 0 < n -> m < n + m.
  elim=> [|m IHm] // n H;
    first by rewrite addn0.
  rewrite addnS; exact: IHm.
Qed.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
Proof. intros; ssomega. Qed.

Lemma ltnSSn : forall n, n < n.+2.
Proof. intros; ssomega. Qed.

Lemma fold_gt : forall a f n m (xs : list a),
  n > m -> foldl (fun n x => n + f x) n xs > m.
Proof.
  move=> a f n m xs.
  elim: xs n => // ? ? IHxs *.
  exact /IHxs /ltn_addr.
Qed.

Lemma fold_fold_lt : forall a f n m (xs : list a),
  n < m -> foldl (fun n x => n + f x) n xs <
           foldl (fun n x => n + f x) m xs.
Proof.
  move=> a f n m xs.
  elim: xs n m => // ? ? IHxs *.
  apply IHxs.
  by rewrite ltn_add2r.
Qed.

Definition safe_hd {a} (xs : list a) (H : (size xs > 0)) : a.
Proof. elim: xs H => //. Defined.

Lemma not_in_app : forall (a : eqType) x (l l' : list a),
  x \notin (l ++ l') -> x \notin l.
Proof.
  move=> a x l l'.
  rewrite mem_cat negb_orb.
  move=> /andP H. inv H.
Qed.

Lemma map_f_notin :
  forall (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) (x : T1),
  injective f -> x \notin s -> f x \notin [seq f i | i <- s].
Proof.
  move=> T1 T2 f.
  elim=> // x xs IHxs x0 Hinj.
  rewrite in_cons negb_orb => /andP [H1 H2].
  rewrite map_cons in_cons negb_orb.
  apply/andP; split.
    by rewrite inj_eq.
  exact: IHxs.
Qed.

Lemma perm_cat_cons (T : eqType) (x : T) : forall (s1 s2 : seq_predType T),
  perm_eql (x :: s1 ++ s2) (s1 ++ x :: s2).
Proof.
  move=> s1 s2.
  apply/perm_eqlP.
  rewrite perm_eq_sym perm_catC cat_cons perm_cons perm_catC.
  exact: perm_eq_refl.
Qed.

Lemma perm_rem_cons (T : eqType) (x : T) : forall (s1 s2 : seq_predType T),
  x \in s1 -> perm_eql (rem x s1 ++ x :: s2) (s1 ++ s2).
Proof.
  move=> s1 s2 Hin.
  apply/perm_eqlP.
  rewrite perm_catC cat_cons perm_cat_cons perm_catC perm_cat2r perm_eq_sym.
  exact: perm_to_rem.
Qed.

Lemma lift_bounded : forall n (x : fin n), ord_max != widen_ord (leqnSn n) x.
Proof.
  move=> n.
  case=> /= m Hlt.
  rewrite /ord_max /lift.
  apply/eqP; invert.
  move: H0 Hlt => -> H.
  abstract ssomega.
Qed.

Lemma widen_ord_inj : forall m n (H : m <= n), injective (widen_ord H).
Proof.
  move=> m n H.
  rewrite /injective => x1 x2.
  by invert; apply ord_inj.
Qed.

Fixpoint insert {a} (p : a -> bool) (z : a) (l : list a) : list a :=
  match l with
    | nil => [:: z]
    | cons x xs =>
      if p x
      then x :: insert p z xs
      else z :: x :: xs
  end.

Arguments insert {a} p z l : simpl never.

Lemma perm_cons_swap (T : eqType) (x y : T) : forall (xs : seq_predType T),
  perm_eql (x :: y :: xs) (y :: x :: xs).
Proof.
  move=> xs; apply/perm_eqlP.
  rewrite -cat1s perm_catC cat_cons perm_cons perm_catC cat1s.
  exact: perm_eq_refl.
Qed.

Lemma insert_perm (T : eqType) P (x : T) : forall (xs : seq_predType T),
  perm_eql (insert (P ^~ x) x xs) (x :: xs).
Proof.
  elim=> //= [y ys IHys]; rewrite /insert.
  case: (P y x) => //=; apply/perm_eqlP.
  rewrite perm_eq_sym perm_cons_swap perm_cons perm_eq_sym -/insert.
  exact/perm_eqlP/IHys.
Qed.

Lemma size_insert : forall (a : eqType) P (x : a) xs,
  size (insert (P ^~ x) x xs) = (size xs).+1.
Proof.
  move=> a P x xs.
  rewrite (@perm_eq_size _ _ (x :: xs)) => //.
  exact/perm_eqlP/insert_perm.
Qed.

Section Mergesort.

Variable t : Type.
Variable f : t -> nat.

Fixpoint imerge l1 l2 :=
  let fix imerge_aux l2 :=
  match l1, l2 with
  | [::], _ => l2
  | _, [::] => l1
  | a1::l1', a2::l2' =>
      if f a1 <= f a2 then a1 :: imerge l1' l2 else a2 :: imerge_aux l2'
  end
  in imerge_aux l2.

Fixpoint imerge_list_to_stack stack l :=
  match stack with
  | [::] => [:: Some l]
  | None :: stack' => Some l :: stack'
  | Some l' :: stack' => None :: imerge_list_to_stack stack' (imerge l' l)
  end.

Fixpoint imerge_stack stack :=
  match stack with
  | [::] => [::]
  | None :: stack' => imerge_stack stack'
  | Some l :: stack' => imerge l (imerge_stack stack')
  end.

Fixpoint iter_imerge stack l :=
  match l with
  | [::] => imerge_stack stack
  | a::l' => iter_imerge (imerge_list_to_stack stack [:: a]) l'
  end.

Definition isort := iter_imerge [::].

(** The proof of correctness *)

Definition lebf := fun n m => f n <= f m.

Local Notation Sorted := (LocallySorted lebf) (only parsing).

Fixpoint SortedStack stack :=
  match stack with
  | [::] => True
  | None :: stack' => SortedStack stack'
  | Some l :: stack' => Sorted l /\ SortedStack stack'
  end.

Local Ltac invert H := inversion H; subst; clear H.

Fixpoint flatten_stack (stack : list (option (list t))) :=
  match stack with
  | [::] => [::]
  | None :: stack' => flatten_stack stack'
  | Some l :: stack' => l ++ flatten_stack stack'
  end.

Theorem Sorted_imerge : forall l1 l2,
  Sorted l1 -> Sorted l2 -> Sorted (imerge l1 l2).
Proof.
  induction l1; induction l2; intros; simpl; auto.
  destruct (f a <= f a0) eqn:Heq1.
    invert H.
      simpl. constructor; trivial; rewrite Heq1; constructor.
      assert (Sorted (imerge (b::l) (a0::l2))) by (apply IHl1; auto).
      clear H0 H3 IHl1; simpl in *.
      destruct (f b <= f a0); constructor; auto || rewrite Heq1; constructor.
    assert (f a0 <= f a) by
      (case: (@leq_total (f a0) (f a)) => /orP [H'|H'];
        (trivial || (rewrite Heq1 in H'; inversion H'))).
    invert H0.
      constructor; trivial.
      assert (Sorted (imerge (a::l1) (b::l))) by auto using IHl1.
      clear IHl2; simpl in *.
      destruct (f a <= f b); constructor; auto.
Qed.

Theorem Sorted_imerge_list_to_stack : forall stack l,
  SortedStack stack -> Sorted l -> SortedStack (imerge_list_to_stack stack l).
Proof.
  induction stack as [|[|]]; intros; simpl.
    auto.
    apply IHstack. destruct H as (_,H1). fold SortedStack in H1. auto.
      apply Sorted_imerge; auto; destruct H; auto.
      auto.
Qed.

Theorem Sorted_imerge_stack : forall stack,
  SortedStack stack -> Sorted (imerge_stack stack).
Proof.
induction stack as [|[|]]; simpl; intros.
  constructor; auto.
  apply Sorted_imerge; tauto.
  auto.
Qed.

Theorem Sorted_iter_imerge : forall stack l,
  SortedStack stack -> Sorted (iter_imerge stack l).
Proof.
  intros stack l H; induction l in stack, H |- *; simpl.
    auto using Sorted_imerge_stack.
    assert (Sorted [:: a]) by constructor.
    auto using Sorted_imerge_list_to_stack.
Qed.

Theorem Sorted_isort : forall l, Sorted (isort l).
Proof.
intro; apply Sorted_iter_imerge. constructor.
Qed.

Corollary LocallySorted_isort : forall l, Sorted.Sorted lebf (isort l).
Proof. intro; eapply Sorted_LocallySorted_iff, Sorted_isort; auto. Qed.

Corollary StronglySorted_isort : forall l,
  StronglySorted lebf (isort l).
Proof.
  move=> l.
  apply Sorted_StronglySorted.
  rewrite /Relations_1.Transitive.
  move=> x y z.
  rewrite /lebf.
  intros; ssomega.
  apply LocallySorted_isort.
Qed.

Import EqNotations.
Require Import Recdef.

Lemma Forall_insert_spec : forall x xs z,
  List.Forall (lebf x) xs -> lebf x z
    -> List.Forall (lebf x) (insert (lebf^~ z) z xs).
Proof.
  move=> x.
  elim=> /= [|y ys IHys] z H Hlt.
    by constructor.
  rewrite /insert.
  case L: (lebf y z).
    constructor. by inv H.
    by apply: IHys; inv H.
  by constructor.
Qed.

Lemma StronglySorted_insert_spec (l : list t) : forall z,
  StronglySorted lebf l
    -> StronglySorted lebf (insert (fun x => lebf x z) z l).
Proof.
  move=> z.
  elim: l => /= [|x xs IHxs] Hsort.
    by constructor.
  inv Hsort. clear Hsort.
  specialize (IHxs H1).
  rewrite /insert.
  case L: (lebf x z).
    constructor. exact: IHxs.
    exact: Forall_insert_spec.
  constructor.
    by constructor.
  constructor.
    unfold lebf in *.
    apply ltnW. rewrite ltnNge.
    apply/negP/eqP. by rewrite L.
  apply List.Forall_impl with (P := (fun m : t => lebf x m)).
    rewrite /lebf.
    move=> a Hlt.
    move: L => /negP.
    rewrite /lebf.
    move=> /negP.
    rewrite -ltnNge.
    move=> L.
    ssomega.
  by [].
Qed.

End Mergesort.

Lemma Forall_leq_map : forall a f x l,
  List.Forall (fun m : a => f x <= f m) l
    -> List.Forall (fun n : nat => f x <= n) [seq f i | i <- l].
Proof.
  move=> a f x.
  elim=> [|z l IHl] H /=.
    by constructor.
  constructor. by inv H.
  apply: IHl; inv H.
Qed.

Lemma StronglySorted_leq_map : forall a f l,
  StronglySorted (fun n m : a => f n <= f m) l
    -> StronglySorted (fun m n : nat => m <= n) [seq f i | i <- l].
Proof.
  move=> a f.
  elim=> [|x l IHl] H /=.
    by constructor.
  constructor. by apply IHl; inv H.
  by apply Forall_leq_map; inv H.
Qed.

Corollary StronglySorted_isort_f : forall a (f : a -> nat) l,
  StronglySorted leq [seq f i | i <- isort f l ].
Proof.
  move=> a f l.
  pose (StronglySorted_isort f l) as Hsort.
  unfold lebf in Hsort.
  elim: l Hsort => /= [|x l IHl] Hsort.
    by constructor.
  inv Hsort. constructor.
  constructor.
    exact: StronglySorted_leq_map.
  exact: Forall_leq_map.
Qed.
