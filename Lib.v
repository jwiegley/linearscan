Require Export LinearScan.IApplicative.
Require Export LinearScan.IEndo.
Require Export LinearScan.IMonad.
Require Export LinearScan.IState.
Require Export LinearScan.NonEmpty.
Require Export LinearScan.Ssr.
Require Export LinearScan.Vector.

Require Export Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv H  := inversion H; subst; simpl; auto.
Ltac contra := intros top; contradiction top; clear top.
Ltac invert := intros top; inversion top; clear top.

Tactic Notation "invert" "as" simple_intropattern(pat) :=
  intros top; inversion top as pat; clear top.

Definition undefined {a : Type} : a. Admitted.

Definition apply {A B} (f : A -> B) (x : A) := f x.

Infix "$" := apply (at level 60, right associativity, only parsing)
  : program_scope.

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

Definition all_in_list {a : eqType} (l : list a) : all (fun x => x \in l) l.
Proof. apply/allP; elim: l => //=. Qed.

Definition list_membership {a : eqType} (l : list a) : list { x : a | x \in l } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          exist _ x (mem_head _ xs) :: map exist_in_cons (go xs)
      end in
  go l.

Definition lebf {a : Type} (f : a -> nat) (n m : a) := f n <= f m.

Definition odd_1 : odd 1. done. Qed.

Lemma ltn_odd n m : odd n && odd m -> n < m -> n.+1 < m.
Proof.
  move/andP=> [nodd modd] Hlt.
  rewrite -subn_gt0 odd_gt0 // odd_sub // modd /=.
  exact/negPn.
Qed.

Lemma odd_succ_succ n : odd (n.+2) = odd n.
Proof. by rewrite /=; apply/negPn; case: (odd n). Defined.

Definition odd_add_2 {n} : odd n -> odd n.+2.
Proof. by move=> H; rewrite odd_succ_succ. Defined.

Lemma leq_min : forall m n p, n <= p -> minn m n <= p.
Proof. intros. rewrite geq_min. by elim: (m <= p). Qed.

Lemma ltn_min : forall m n p, n < p -> minn m n < p.
Proof. intros. rewrite gtn_min. by elim: (m < p). Qed.

Lemma ltn_max : forall m n p, p < n -> p < maxn m n.
 Proof. move=> *. by rewrite leq_max; intuition. Qed.

Lemma ltn_add1l : forall n m o, n + m < o -> n < o.
Proof.
  elim=> [|n IHn] m o H.
    case: o => //= in H *.
  case: o => //= [o] in H *.
  exact: (IHn m).
Qed.

Lemma le_Sn_le : forall n m : nat, n.+1 <= m -> n <= m.
Proof. exact: ltnW. Qed.

Lemma ltn_plus : forall m n, 0 < n -> m < n + m.
  elim=> [|m IHm] // n H;
    first by rewrite addn0.
  rewrite addnS; exact: IHm.
Qed.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
Proof.
  move=> n m p H1 H2.
  exact: (leq_trans H1).
Qed.

Lemma ltnSSn : forall n, n < n.+2.
Proof. move=> n. exact: ltnW. Qed.

Lemma subnn0 : forall n, n - n = 0.
Proof. by elim. Qed.

Lemma subn_leq : forall n m o, n <= m -> n - o <= m.
Proof.
  elim=> //= [n IHn] m o H.
  rewrite leq_subLR.
  by rewrite ltn_addl.
Qed.

Lemma addsubsubeq : forall n m o, n <= o -> n + m == o + m - (o - n).
Proof.
  move=> n m o H.
  rewrite [o + _]addnC.
  rewrite subnBA; last by [].
  rewrite -addnA [o + _]addnC addnA addnC -addnBA.
    by rewrite subnn0 addn0.
  exact: leqnn.
Qed.

Lemma in_notin : forall (a : eqType) (x y : a) (xs : seq a),
  x \in xs -> y \notin xs -> x != y.
Proof.
  move=> a x y xs.
  elim: xs => //= [? ? IHzs] in x y *.
  rewrite !in_cons => /orP [/eqP ->|?] /norP [? ?].
    by rewrite eq_sym.
  exact: IHzs.
Qed.

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

Lemma fold_left_plus : forall a (f : a -> nat) xs n,
   foldl (fun n x => n + f x) n xs =
   foldl (fun n x => n + f x) 0 xs + n.
Proof.
  move=> a f; elim=> // a' ? IHxs n /=.
  rewrite add0n IHxs (IHxs (f a')) [n+_]addnC addnA //.
Qed.

Lemma foldl_cons : forall a b f (z : b) (x : a) xs,
  foldl f z (x :: xs) = foldl f (f z x) xs.
Proof. move=> a b f z x; elim=> //=. Qed.

Lemma foldr_cons : forall a b f (z : b) (x : a) xs,
  foldr f z (x :: xs) = f x (foldr f z xs).
Proof. move=> a b f z x; elim=> //=. Qed.

Definition sumf {a} f : seq a -> nat := foldl (fun n x => n + f x) 0.

Definition sumlist : seq nat -> nat := foldl addn 0.

Lemma sumf_cons : forall a f xs (x : a),
  sumf f (x :: xs) = f x + sumf f xs.
Proof.
  move=> a f.
  rewrite /sumf /= => xs x.
  by rewrite fold_left_plus addnC add0n.
Qed.

Lemma sumlist_cons : forall xs (x : nat),
  sumlist (x :: xs) = x + sumlist xs.
Proof.
  rewrite /sumlist /= => xs x.
  by rewrite fold_left_plus addnC add0n.
Qed.

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

Lemma span_spec {a} (l : list a) : forall p l1 l2,
  (l1, l2) = span p l -> l = l1 ++ l2.
Proof.
  move=> p.
  elim: l => /= [|x xs IHxs] l1 l2 Heqe.
    by inv Heqe.
  case E: (p x); rewrite E in Heqe.
    destruct (span p xs) eqn:S.
    inv Heqe.
    specialize (IHxs l l0).
    rewrite {}IHxs; by reflexivity.
  inv Heqe.
Qed.

Lemma lt_size_rev : forall a (xs : seq a), 0 < size xs -> 0 < size (rev xs).
Proof.
  move=> a.
  elim=> //= [x xs IHxs] H.
  by rewrite size_rev /=.
Qed.

(* Lemma hd_last_spec : forall a (xs : seq a) (H : 0 < size xs), *)
(*   safe_hd xs H = safe_last (rev xs) (lt_size_rev H). *)
(* Proof. *)
(*   move=> a. *)
(*   case=> [//|y ys] /= H. *)

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

Lemma four_points : forall n m o p,
  (n < m < o) && (o < p) -> (m - n) + (p - o) < p - n.
Proof.
  move=> n m o p /andP [/andP [H1 H2] H3].
  rewrite -ltn_subRL -subnDA.
  apply ltn_sub2l; rewrite subnKC //;
    try exact: ltnW.
  exact: (ltn_trans H2).
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
  match l with
    | nil => [:: z]
    | cons x xs =>
      if P x z
      then x :: insert P z xs
      else z :: x :: xs
  end.

Arguments insert {a} P z l : simpl never.

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

Lemma insert_foldl :
  forall (T R : Type) (f : R -> T -> R) (z : R) P x (xs : seq T),
  (forall x y z, f (f z x) y = f (f z y) x)
    -> foldl f z (insert P x xs) = foldl f z (x :: xs).
Proof.
  move=> T R f z P x xs.
  rewrite /insert.
  elim: xs z => [|y ys IHys] //= z H.
  case E: (P y x) => //=.
  rewrite -/insert in IHys *.
  rewrite IHys /=; last by [].
  by rewrite H.
Qed.

Lemma insert_sumf : forall a f P (x : a) xs,
  sumf f (insert P x xs) = sumf f (x :: xs).
Proof.
  move=> a f P x xs.
  rewrite /sumf insert_foldl; first by [].
  move=> x0 y0 z0.
  by rewrite -addnA [f _ + f _]addnC addnA.
Qed.

Lemma sumf_sumlist : forall a f (xs : seq a),
  sumlist [seq f i | i <- xs] = sumf f xs.
Proof.
  move=> a f.
  elim=> //= [x xs IHxs].
  by rewrite sumf_cons -IHxs sumlist_cons.
Qed.

Lemma insert_f_sumlist : forall a (f : a -> nat) P (x : a) xs,
  sumlist [seq f i | i <- insert P x xs] =
  sumlist [seq f i | i <- x :: xs].
Proof.
  move=> a f P y xs.
  case: xs y => [|x xs] y //=.
  by rewrite !sumlist_cons !sumf_sumlist insert_sumf !sumf_cons.
Qed.

Lemma in_sumlist : forall (a : eqType) f (x : a) xs,
  x \in xs -> f x <= sumlist [seq f i | i <- xs].
Proof.
  move=> a f x xs H.
  elim: xs => //= [s ys IHys] in x H *.
  rewrite sumlist_cons -leq_subLR.
  move: H IHys.
  rewrite in_cons => /orP [/eqP ->|H].
    rewrite subnn0 => _.
    exact: leq0n.
  move/(_ x H) => IHys {H}.
  exact: subn_leq.
Qed.

Lemma uniq_catA : forall (T : eqType) (s1 s2 s3 : seq T),
  uniq ((s1 ++ s2) ++ s3) = uniq (s1 ++ s2 ++ s3).
Proof.
  move=> T.
  elim=> //= [x xs IHxs] s2 s3.
  rewrite IHxs.
  congr (_ && _).
  rewrite !mem_cat.
  have ->: forall a b c, (a || b || c) = [|| a, b | c].
    move=> a b c.
    by rewrite Bool.orb_assoc.
  by [].
Qed.

Lemma proj_rem_uniq (a b : eqType) (f : a -> b) : forall x xs,
  uniq [seq f i | i <- xs] -> uniq [seq f i | i <- rem x xs].
Proof. by move=> x xs; apply/subseq_uniq/map_subseq/rem_subseq. Qed.

Lemma not_in_app : forall (a : eqType) x (l l' : list a),
  x \notin (l ++ l') -> x \notin l.
Proof.
  move=> a x l l'.
  rewrite mem_cat.
  move/norP.
  move=> H. inv H.
Qed.

Lemma map_f_notin :
  forall (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) (x : T1),
  injective f -> x \notin s -> f x \notin [seq f i | i <- s].
Proof.
  move=> T1 T2 f.
  elim=> // x xs IHxs x0 Hinj.
  rewrite in_cons.
  move/norP => [H1 H2].
  rewrite map_cons in_cons.
  apply/norP; split.
    by rewrite inj_eq.
  exact: IHxs.
Qed.

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

Require Coq.Program.Wf.

(*
Program Fixpoint dep_foldl {A : Type} {B : A -> Type}
  (f : forall b' : A, B b' -> A) (b : A) (v : seq (B b))
  (P : forall b x, B b -> B (f b x)) {measure (size v)} : A :=
  match v with
  | nil => b
  | y :: ys => @dep_foldl A B f (f b y) (map (P b y) ys) _ _
  end.
Obligation 2. by rewrite size_map. Qed.
*)

Lemma cat2s : forall a (x y : a) s, [:: x; y] ++ s = (x :: y :: s).
Proof. by move=> a x y; elim=> //. Qed.

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

Lemma subseq_impl_cons : forall (a : eqType) (x : a) xs s,
  subseq (x :: xs) s -> subseq xs s.
Proof.
  move=> a x xs s Hsub.
  elim: s => // [y ys IHys] in Hsub *.
Admitted.

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

Program Fixpoint dep_foldl_inv
  {A : Type} {P : A -> Prop} {E : A -> eqType}
  (b : A) (Pb : P b) (v : seq (E b)) (n : nat) (Hn : n == size v)
  (Q : forall x : A, seq (E x)) (Hsub : subseq v (Q b))
  (F : forall b b', E b -> E b')
  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)), x \in Q z
         -> { z' : A | P z' & subseq (map (F z z') xs) (Q z') })
  {struct n} : { b' : A | P b' } :=
  match (List.destruct_list v, n) with
  | (inleft (existT y (exist ys H)), S n') =>
      match f b Pb y ys (in_subseq_sing H Hsub) with
      | exist2 b' Pb' Hsub' =>
          let ys' := map (F b b') ys in
          @dep_foldl_inv A P E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => exist P b Pb
  end.
Obligation 1.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.

Program Fixpoint dep_foldl_inv'
  {A : Type} {P : A -> Prop} {R : A -> A -> Prop} {E : A -> eqType}
  (b : A) (Pb : P b) (v : seq (E b)) (n : nat) (Hn : n == size v)
  (Q : forall x : A, seq (E x)) (Hsub : subseq v (Q b))
  (F : forall (b b' : A) (Rbb' : R b b'), E b -> E b')
  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)),
         subseq (x :: xs) (Q z)
           -> { res : { z' : A | R z z' }
              | P res.1 & subseq (map (F z res.1 res.2) xs) (Q res.1) })
  {struct n} : { b' : A | P b' } :=
  match (List.destruct_list v, n) with
  | (inleft (existT y (exist ys H)), S n') =>
      match f b Pb y ys Hsub with
      | exist2 (exist b' Rbb') Pb' Hsub' =>
          let ys' := map (F b b' Rbb') ys in
          @dep_foldl_inv' A P R E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => exist P b Pb
  end.
Obligation 2.
  inversion Heq_anonymous.
  clear Heq_anonymous0.
  rewrite -H1 in Hn.
  simpl in Hn.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.
