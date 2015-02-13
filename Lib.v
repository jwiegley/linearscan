Require Export LinearScan.Ssr.
Require Export LinearScan.Ltac.
Require Export LinearScan.NonEmpty.
Require Export LinearScan.Vector.

Require Export Coq.Classes.RelationClasses.
Require Export Coq.Program.Wf.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv H  := inversion H; subst; simpl; clear H.
Ltac contra := intros top; contradiction top; clear top.
Ltac invert := intros top; inversion top; clear top.

Tactic Notation "invert" "as" simple_intropattern(pat) :=
  intros top; inversion top as pat; clear top.

Definition undefined {a : Type} : a. Admitted.

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Definition flip `(f : a -> b -> c) : b -> a -> c := fun y x => f x y.

Notation "p .1" := (proj1_sig p)
  (at level 2, left associativity, format "p .1").
Notation "p .2" := (proj2_sig p)
  (at level 2, left associativity, format "p .2").
Notation "( x ; y )" := (exist _ x y).

Definition option_choose {a} (x y : option a) : option a :=
  match x with
  | None => y
  | Some _ => x
  end.

Definition maybeLast a (l : seq a) : option a :=
  let fix go res xs :=
      match xs with
      | nil => res
      | cons x xs => go (Some x) xs
      end in
  go None l.

Example maybeLast_ex1 : maybeLast ([::] : seq nat) == None.
Proof. by []. Qed.

Example maybeLast_ex2 : maybeLast [:: 1] == Some 1.
Proof. by []. Qed.

Example maybeLast_ex3 : maybeLast [:: 1; 2; 3] == Some 3.
Proof. by []. Qed.

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

Definition list_membership {a : eqType} (l : seq a) :
  seq { x : a | x \in l } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          exist _ x (mem_head _ xs) :: map exist_in_cons (go xs)
      end in
  go l.

Fixpoint init {a : Type} (x : a) (l : seq a) :=
  match l with
    | nil => nil
    | cons y nil => [:: x]
    | cons y ys => x :: init y ys
  end.

Lemma Forall_append : forall A (P : A -> Prop) xs ys,
   List.Forall P xs /\ List.Forall P ys <-> List.Forall P (xs ++ ys).
Proof.
  move=> A P.
  elim=> [|x xs IHxs] /= ys.
    split.
      by move=> [H1 H2] //=.
    move=> H.
    split=> //.
  split.
    move=> [H1 H2] //=.
    constructor.
      by inversion H1.
    apply/IHxs.
    split=> //.
    by inversion H1.
  move=> H.
  split=> //.
    constructor.
      by inversion H.
    inversion H; subst.
    by move/IHxs: H3 => [? ?].
  inversion H; subst.
  by move/IHxs: H3 => [? ?].
Qed.

Lemma Forall_rcons_inv : forall a P (x : a) xs,
  List.Forall P (rcons xs x) -> List.Forall P xs /\ P x.
Proof.
  move=> a P x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H2).
  inversion IHys.
  split=> //.
  constructor=> //.
Qed.

Require Import Coq.Sorting.Sorted.

Lemma StronglySorted_inv_app : forall a R (l1 l2 : seq a),
  StronglySorted R (l1 ++ l2)
    -> StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  move=> a R.
  elim=> [|x xs IHxs] /= l2 H.
    split=> //.
    constructor.
  inversion H.
  specialize (IHxs l2 H2).
  inversion IHxs; subst.
  split=> //.
  constructor=> //.
  by move/Forall_append: H3 => [? ?].
Qed.

Lemma StronglySorted_skip : forall a R (y : a) a0 ys,
  StronglySorted R [:: y, a0 & ys] -> StronglySorted R (y :: ys).
Proof.
  move=> a R y a0 ys H.
  elim: ys => [|z zs IHzs] in H *.
    by constructor; constructor.
  constructor.
    by constructor; inv H; inv H2; inv H1.
  by inv H; inv H3.
Qed.

Lemma StronglySorted_cat
  {A : Type} {x y : A} {xs ys : seq A} {R : A -> A -> Prop}
  `{Transitive _ R} :
  StronglySorted R (x :: xs) ->
  StronglySorted R (y :: ys)
    -> R (last x xs) y
    -> StronglySorted R (x :: xs ++ y :: ys).
Proof.
  move=> rel Hsort1 Hsort2.
  constructor.
    induction xs; simpl in *.
      induction ys; simpl in *.
        constructor.
          by constructor.
        by constructor.
      assumption.
    constructor.
      apply: IHxs.
        inv rel.
        constructor.
          by inv H2.
        by inv H3.
      induction xs; simpl in *.
        inv rel; inv H3.
        by transitivity a.
      assumption.
    induction xs; simpl in *.
      have H1: StronglySorted R [:: x]
        by constructor; constructor.
      have H2: R x y.
        inv rel; inv H4.
        by transitivity a.
      specialize (IHxs H1 H2).
      induction ys; simpl in *.
        by constructor.
      constructor=> //=.
      inv Hsort1; inv H4; inv H5.
      constructor.
        by transitivity y.
      specialize (IHys (SSorted_cons y H6 H8)
                       (StronglySorted_skip IHxs)).
      by inv IHys.
    constructor; inv rel.
      by inv H2; inv H5.
    apply: IHxs0 => /=.
    - constructor.
        exact: StronglySorted_skip.
      constructor.
        by inv H3.
      by inv H3; inv H5.
    - destruct xs. simpl in *.
        inv H2; inv H5.
        by transitivity a0.
      by [].
    - move=> H4 H5.
      destruct xs. simpl in *.
        move: (SSorted_cons x H2 H3) => H6.
        specialize (IHxs (StronglySorted_skip H6) Hsort2).
        by inv IHxs.
      move: (SSorted_cons x H2 H3) => H6.
      specialize (IHxs (StronglySorted_skip H6) Hsort2).
      by inv IHxs.
  induction xs; simpl in *.
    induction ys; simpl in *.
      by constructor.
    constructor=> //.
    inv Hsort1; inv H2; inv H3.
    constructor.
      by transitivity y.
    specialize (IHys (SSorted_cons y H4 H6)).
    by inv IHys.
  constructor; inv rel.
    by inv H3.
  apply: IHxs.
    constructor.
      by inv H2.
    by inv H3.
  inv H2; inv H3.
  induction xs; simpl in *.
    by transitivity a.
  assumption.
Qed.

Lemma StronglySorted_rcons_inv : forall a R (x : a) xs,
  StronglySorted R (rcons xs x) -> StronglySorted R xs.
Proof.
  move=> a R x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H1).
  constructor=> //.
  apply Forall_rcons_inv in H2.
  by inversion H2.
Qed.

Lemma StronglySorted_rcons_rcons_inv : forall a R (x y : a) xs,
  StronglySorted R (rcons (rcons xs x) y) -> R x y.
Proof.
  move=> a R x y.
  elim=> [|z zs IHzs] /=.
    invert.
    by inv H2.
  invert.
  exact: IHzs H1.
Qed.

Fixpoint lookup {a : eqType} {b} (dflt : b) (v : seq (a * b)) (x : a) : b :=
  if v is (k, v) :: xs
  then if k == x
       then v
       else lookup dflt xs x
  else dflt.

Fixpoint maybeLookup {a : eqType} {b} (v : seq (a * b)) (x : a) : option b :=
  if v is (k, v) :: xs
  then if k == x
       then Some v
       else maybeLookup xs x
  else None.

Fixpoint maybe_nth {a} (v : seq a) i {struct i} :=
  match v with
  | [::] => None
  | x :: s' =>
      match i with
      | 0 => Some x
      | n'.+1 => maybe_nth s' n'
      end
  end.

Fixpoint apply_nth {a} (def : a) (v : seq a) i (f : a -> a) {struct i} :=
  if v is x :: v'
  then if i is i'.+1
       then x :: apply_nth def v' i' f
       else f x :: v'
  else ncons i def [:: def].

Definition lebf {a : Type} (f : a -> nat) (n m : a) := f n <= f m.

Definition oddnum := { n : nat | odd n }.

Program Definition odd1 := exist odd 1 _.

Lemma odd_double_plus (n : nat) : odd n.*2.+1.
Proof.
  elim: n => [|n IHn] //=.
  apply/negPn.
  by rewrite odd_double.
Qed.

Lemma ltn_odd n m : odd n && odd m -> n < m -> n.+1 < m.
Proof.
  move/andP=> [nodd modd] Hlt.
  rewrite -subn_gt0 odd_gt0 // odd_sub // modd /=.
  exact/negPn.
Qed.

Definition distance (n m : nat) : nat := if n < m then m - n else n - m.

Lemma ltn_plus : forall m n, 0 < n -> m < m + n.
Proof. by elim. Qed.

Lemma leq_plus : forall m n, m <= m + n.
Proof. by elim. Qed.

Lemma leq_eqF : forall n m, (n == m) = false -> n <= m -> n < m.
Proof.
  move=> n m.
  move/eqP=> H1 H2.
  by ordered.
Qed.

Definition forFold {A B : Type} (b : B) (v : seq A) (f : B -> A -> B) : B :=
  foldl f b v.

Definition foldl_with_index
  {A B : Type} (f : nat -> B -> A -> B) (b : B) (v : seq A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => go n.+1 ys (f n z y)
      end in
  go 0 v b.

Example ex_foldl_with_index_1 :
  foldl_with_index (fun n z x => (n, x) :: z) nil [:: 1; 2; 3]
    == [:: (2, 3); (1, 2); (0, 1)].
Proof. reflexivity. Qed.

Definition foldr_with_index
  {A B : Type} (f : nat -> A -> B -> B) (b : B) (v : seq A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => f n y (go n.+1 ys z)
      end in
  go 0 v b.

Example ex_foldr_with_index_1 :
  foldr_with_index (fun n x z => (n, x) :: z) nil [:: 1; 2; 3]
    == [:: (0, 1); (1, 2); (2, 3)].
Proof. reflexivity. Qed.

Fixpoint mapAccumL {A X Y : Type} (f : A -> X -> (A * Y))
  (s : A) (v : seq X) : A * seq Y :=
  match v with
  | nil => (s, nil)
  | x :: xs =>
    let: (s', y) := f s x in
    let: (s'', ys) := mapAccumL f s' xs in
    (s'', y :: ys)
  end.

Example ex_mapAccumL_1 :
  mapAccumL (fun n x => (n.+1, x.+2)) 0 [:: 1; 2; 3] == (3, [:: 3; 4; 5]).
Proof. reflexivity. Qed.

Definition sumlist : seq nat -> nat := foldl addn 0.

Definition safe_hd {a} (xs : list a) : 0 < size xs -> a.
Proof. case: xs => //. Defined.

Arguments safe_hd [a] xs H.

Definition safe_last {a} (xs : list a) : 0 < size xs -> a.
Proof.
  case: xs => [//|y ys] /= *.
  exact: (last y ys).
Defined.

Arguments safe_last [a] xs H.

Fixpoint span {a} (p : a -> bool) (l : list a) : (list a * list a) :=
  match l with
  | nil => (nil, nil)
  | x :: xs =>
    if p x
    then let: (ys,zs) := span p xs in (x::ys,zs)
    else (nil,l)
  end.

Lemma span_cat {a} (l : list a) : forall p l1 l2,
  (l1, l2) = span p l -> l = l1 ++ l2.
Proof.
  move=> p.
  elim: l => /= [|x xs IHxs] l1 l2 Heqe.
    by inv Heqe.
  case E: (p x); rewrite E in Heqe.
    destruct (span p xs) eqn:S.
    inv Heqe.
    specialize (IHxs l l0).
    by rewrite {}IHxs.
  by inv Heqe.
Qed.

Example span_ex1 :
  span (fun x => x < 10) [:: 1; 5; 10; 15] = ([:: 1; 5], [:: 10; 15]).
Proof. reflexivity. Qed.

Program Fixpoint groupBy {a} (p : a -> a -> bool) (l : seq a)
  {measure (size l)} : seq (seq a) :=
  match l with
  | [::] => nil
  | x :: xs => let: (ys, zs) := span (p x) xs in
               (x :: ys) :: groupBy p zs
  end.
Obligation 1.
  clear groupBy.
  rename Heq_anonymous into Heqe.
  move: ys zs Heqe.
  elim: xs => [|w ws /= IHws] ys zs /=.
    by invert.
  case: (p x w) => /=; last by invert.
  case: (span (p x) ws) => [bs cs] in IHws *.
  invert; subst.
  specialize (IHws bs cs refl_equal).
  move/ltP in IHws.
  apply/ltP.
  exact/leqW.
Qed.

Example groupBy_ex1 :
  groupBy eq_op [:: 1; 3; 3; 4; 5; 5; 9; 6; 8]
    = [:: [:: 1]; [:: 3; 3]; [:: 4]; [:: 5; 5]; [:: 9]; [:: 6]; [:: 8]].
Proof. reflexivity. Qed.

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

Lemma lift_bounded : forall n (x : 'I_n), ord_max != widen_ord (leqnSn n) x.
Proof.
  move=> n.
  case=> /= m Hlt.
  rewrite /ord_max /lift.
  apply/eqP; invert.
  move: H0 Hlt => ->.
  by rewrite ltnn.
Qed.

Definition map_fst_filter_snd :
  forall (a b : eqType) (i : b) (xs : seq (a * b)),
  all (fun x => (x, i) \in xs) [seq fst x | x <- xs & snd x == i].
Proof.
  move=> a b i xs.
  apply/allP => x /mapP[[x1 y1]].
  by rewrite mem_filter => /= /andP [/eqP/=-> pIxs ->].
Qed.

Definition widen_id {n} := widen_ord (leqnSn n).
Arguments widen_id [n] i /.
Definition widen_fst {n a} p := (@widen_id n (@fst _ a p), snd p).

Lemma map_widen_fst : forall (a : eqType) n (xs : seq ('I_n * a)),
  [seq fst i | i <- [seq (@widen_fst n a) i | i <- xs]] =
  [seq (@widen_id n) i | i <- [seq fst i | i <- xs]].
Proof. move=> a n xs. by rewrite -!map_comp. Qed.

Lemma widen_ord_inj : forall m n (H : m <= n), injective (widen_ord H).
Proof.
  move=> m n H.
  rewrite /injective => x1 x2.
  by invert; apply ord_inj.
Qed.

Lemma no_ord_max : forall n (xs : seq ('I_n)),
  ord_max \notin [ seq widen_id i | i <- xs ].
Proof.
  move=> n; elim=> // [x xs IHxs] /=.
  rewrite in_cons /=.
  apply/norP; split; last assumption.
  exact: lift_bounded.
Qed.

Lemma has_size : forall (a : eqType) x (xs : seq a), x \in xs -> 0 < size xs.
Proof. move=> a x; elim=> //. Qed.

Fixpoint insert {a} (P : rel a) (z : a) (l : list a) : list a :=
  if l is x :: xs
  then if P x z
       then x :: insert P z xs
       else z :: x :: xs
  else [:: z].
Arguments insert {a} P z l : simpl never.

Fixpoint sortBy {a} (p : a -> a -> bool) (l : seq a) : seq a :=
  match l with
  | [::] => nil
  | x :: xs => insert p x (sortBy p xs)
  end.

Example sortBy_ex1 :
  sortBy ltn [:: 1; 3; 5; 7; 9; 2; 4; 6; 8] = [:: 1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. reflexivity. Qed.

Example sortBy_ex2 :
  sortBy gtn [:: 1; 3; 5; 7; 9; 2; 4; 6; 8] = [:: 9; 8; 7; 6; 5; 4; 3; 2; 1].
Proof. reflexivity. Qed.

Lemma perm_cons_swap (T : eqType) (x y : T) : forall (xs : seq_predType T),
  perm_eql (x :: y :: xs) (y :: x :: xs).
Proof.
  move=> xs; apply/perm_eqlP.
  rewrite -cat1s perm_catC cat_cons perm_cons perm_catC cat1s.
  exact: perm_eq_refl.
Qed.

Lemma insert_perm (T : eqType) P (x : T) : forall (xs : seq_predType T),
  perm_eql (insert P x xs) (x :: xs).
Proof.
  elim=> //= [y ys IHys]; rewrite /insert.
  case: (P y x) => //=; apply/perm_eqlP.
  rewrite perm_eq_sym perm_cons_swap perm_cons perm_eq_sym -/insert.
  exact/perm_eqlP/IHys.
Qed.

Lemma insert_size : forall (a : eqType) P (x : a) xs,
  size (insert P x xs) = (size xs).+1.
Proof.
  move=> a P x xs.
  rewrite (@perm_eq_size _ _ (x :: xs)) => //.
  exact/perm_eqlP/insert_perm.
Qed.

Lemma proj_rem_uniq (a b : eqType) (f : a -> b) : forall x xs,
  uniq [seq f i | i <- xs] -> uniq [seq f i | i <- rem x xs].
Proof. by move=> x xs; apply/subseq_uniq/map_subseq/rem_subseq. Qed.

Lemma in_proj : forall (a b : eqType) (x : a) (y : b) (xs : seq (a * b)),
  x \notin [seq fst i | i <- xs] ->
  y \notin [seq snd i | i <- xs] -> (x, y) \notin xs.
Proof.
  move=> a b x y.
  elim=> //= [z zs IHzs] H1 H2.
  rewrite in_cons.
  rewrite in_cons in H1.
  rewrite in_cons in H2.
  apply/norP.
  move/norP: H1 => [H3 H4].
  move/norP: H2 => [H5 H6].
  split.
    case: z => /= [j k] in H3 H5 *.
    move/eqP in H3.
    move/eqP in H5.
    apply/eqP.
    move=> Hneg.
    inversion Hneg.
    contradiction.
  apply: IHzs; by [].
Qed.

Lemma uniq_proj : forall (a b : eqType) (xs : seq (a * b)),
  uniq [seq fst i | i <- xs] ->
  uniq [seq snd i | i <- xs] -> uniq xs.
Proof.
  move=> a b.
  elim=> //= [x xs IHxs] /andP [H1 H2] /andP [H3 H4].
  case: x => /= [j k] in H1 H3 *.
  apply/andP; split; last exact: IHxs.
  exact: in_proj.
Qed.

Lemma subseq_in_cons : forall (a : eqType) x y (xs ys : seq a),
  subseq (x :: xs) (y :: ys) -> x != y -> subseq (x :: xs) ys.
Proof.
  move=> a x y xs ys Hsub Hneq.
  elim: ys => /= [|z zs IHzs] in Hsub *.
    case E: (x == y).
      move/negP: Hneq.
      by rewrite E.
    rewrite E in Hsub.
    inversion Hsub.
  case E: (x == y).
    move/negP: Hneq.
    by rewrite E.
  rewrite E in Hsub.
  assumption.
Qed.

Lemma subseq_sing : forall (a : eqType) (x : a) xs s,
  subseq (x :: xs) s -> subseq [:: x] s.
Proof.
  move=> a x xs s Hsub.
  elim: s => // [y ys IHys] in Hsub *.
  rewrite sub1seq.
  rewrite sub1seq in IHys.
  rewrite in_cons.
  apply/orP.
  case E: (x == y).
    by left.
  right.
  move/negP in E.
  move/negP in E.
  apply: IHys.
  exact: subseq_in_cons.
Qed.

Lemma in_subseq_sing : forall {E : eqType} (s : seq E) v (y : E) ys,
  v = y :: ys -> subseq v s -> y \in s.
Proof.
  move=> E s v y ys ->.
  rewrite -sub1seq.
  exact: subseq_sing.
Qed.

Fixpoint subseq_impl_cons (a : eqType) (x : a) xs s :
  subseq (x :: xs) s -> subseq xs s.
Proof.
  elim: s => //= [z zs IHzs].
  case: xs => // [y ys] in IHzs *.
  case: (x == z).
    case: (y == z).
      exact: subseq_impl_cons.
    exact.
  case: (y == z).
    move=> Hsub.
    specialize (IHzs Hsub).
    exact: subseq_impl_cons.
  exact.
Qed.

Lemma subseq_cons_add : forall (a : eqType) (x : a) xs s,
  subseq xs s -> subseq xs (x :: s).
Proof.
  move=> a x.
  elim=> // [y ys IHys] s Hsub.
  rewrite /=.
  case: (y == x).
    exact: subseq_impl_cons.
  exact.
Qed.

Lemma subseq_cons_rem : forall (a : eqType) (x : a) xs s,
  subseq (x :: xs) s -> subseq xs (rem x s).
Proof.
  move=> a x xs.
  elim=> //= [y ys IHys].
  rewrite eq_sym.
  case E: (y == x); first exact.
  move/IHys => Hsub {IHys}.
  exact: subseq_cons_add.
Qed.

Lemma widen_ord_refl : forall n (H : n <= n) x, widen_ord (m := n) H x = x.
Proof.
  move=> n H.
  case=> m Hm.
  rewrite /widen_ord /=.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma map_widen_ord_refl : forall b n (H : n <= n) (xs : seq ('I_n * b)),
  [seq (let: (xid, reg) := i in (widen_ord (m:=n) H xid, reg)) | i <- xs] = xs.
Proof.
  move=> b n H.
  elim=> //= [x xs IHxs].
  rewrite IHxs.
  case: x => [xid reg].
  congr ((_, reg) :: xs).
  exact: widen_ord_refl.
Qed.

(* This rather excessively complicated, dependent fold function is needed in
   order to walk through a list of intervals of a [ScanState] (which have a
   type dependent on that [ScanState]), while at the same time mutating the
   same [ScanState] and adjusting the type of the remainder of the interval
   list, such that it is known to still have a relationship with the new
   [ScanState].  See the function [checkActiveIntervals] in Allocate.v, which
   is the only user of this function. *)
Program Fixpoint dep_foldl_inv
  {A : Type}                    (* type of the accumulator *)
  {P : A -> Prop}               (* predicate maintained over the accumulator *)
  {R : A -> A -> Prop}          (* a relation on A that must be preserved *)
  {E : A -> eqType}             (* type of the elements we are folding over *)
  (b : A)                       (* the initial state value *)
  (Pb : P b)                    (* predicate on the initial state value *)
  (v : seq (E b))               (* list of elements from the initial state *)

  (n : nat)                     (* the length of this list (as a [nat]) *)
  (* The reason to [nat] rather than [size v] is that the type of v changes
     with each iteration of the fold, which confuses [Program Fixpoint] enough
     that it fails to compute the final proof term even after ten minutes. *)

  (Hn : n == size v)            (* witness that [length == size v] *)
  (Q : forall x : A, seq (E x)) (* function that can determine [v] from [b] *)
  (Hsub : subseq v (Q b))       (* a proof that [v] is a subseq of [Q b] *)

  (F : forall (b b' : A) (Rbb' : R b b'), E b -> E b')
                                (* transports element types between states *)

  (* The fold function [f] takes an intermediate state, a witness for the
     inductive predicate on that state, an element from the initial list which
     is known to be related to that state (and whose type has been transported
     to relate to that state), the list of remaining elements to be processed
     by the fold, and proof that this element and remaining list are at least
     a subsequence of the state.
         The expected result is a new state, proof that this new state relates
     to the incoming state in terms of [R] (which must be transitive), proof
     that the inductive predicate holds for this new state, and proof that the
     transported remainder [xs] is also a subsequence of the list determined
     by [Q] from the new state. *)
  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)),
         subseq (x :: xs) (Q z)
           -> { res : { z' : A | R z z' }
              | P res.1 & subseq (map (F z res.1 res.2) xs) (Q res.1) })

  (* The fold is done when [n] reaches zero *)
  {struct n} :
  (* The result is a final, inductively predicated state *)
  { b' : A | P b' } :=
  match (v, n) with
  | (y :: ys, S n') =>
      match f b Pb y ys Hsub with
      | exist2 (exist b' Rbb') Pb' Hsub' =>
          let ys' := map (F b b' Rbb') ys in
          @dep_foldl_inv A P R E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => exist P b Pb
  end.
Obligation 2.
  inversion Heq_anonymous.
  clear Heq_anonymous0.
  rewrite -H1 in Hn.
  rewrite -H0 in Hn.
  simpl in Hn.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.

Program Fixpoint dep_foldl_invE
  {errType : Type}              (* the short-circuiting error type *)
  {A : Type}                    (* the value being mutated through the fold *)
  {P : A -> Prop}               (* inductive predicate to be maintained on A *)
  {R : A -> A -> Prop}          (* a relation on A that must be preserved *)
  {E : A -> eqType}             (* type of the elements we are folding over *)
  (b : A)                       (* the initial state value *)
  (Pb : P b)                    (* predicate on the initial state value *)
  (v : seq (E b))               (* list of elements from the initial state *)

  (n : nat)                     (* the length of this list (as a [nat]) *)

  (Hn : n == size v)            (* witness that [length == size v] *)
  (Q : forall x : A, seq (E x)) (* function that can determine [v] from [b] *)
  (Hsub : subseq v (Q b))       (* a proof that [v] is a subseq of [Q b] *)

  (F : forall (b b' : A) (Rbb' : R b b'), E b -> E b')
                                (* transports element types between states *)

  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)),
         subseq (x :: xs) (Q z)
           -> errType +
              { res : { z' : A | R z z' }
              | P res.1 & subseq (map (F z res.1 res.2) xs) (Q res.1) })

  {struct n} :
  errType + { b' : A | P b' } :=
  match (v, n) with
  | (y :: ys, S n') =>
      match f b Pb y ys Hsub with
      | inl err => inl err
      | inr (exist2 (exist b' Rbb') Pb' Hsub') =>
          let ys' := map (F b b' Rbb') ys in
          @dep_foldl_invE errType A P R E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => inr (exist P b Pb)
  end.
Obligation 2.
  inversion Heq_anonymous.
  clear Heq_anonymous0.
  rewrite -H1 -H0 in Hn.
  simpl in Hn.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.
