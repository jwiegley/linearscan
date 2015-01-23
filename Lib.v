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

Infix "$" := apply (at level 60, right associativity, only parsing).

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

Definition maybeLast a (l : seq a) : option a :=
  let fix go res xs :=
      match xs with
      | nil => res
      | cons x xs => go (Some x) xs
      end in
  go None l.

Module Trace.

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Definition trace_helper {a : Type} (msg : seq nat) (x : a) : a := x.

Definition trace {a : Type} (msg : string) (x : a) : a :=
  let fix go acc x := match x with
      | EmptyString => acc
      | String c xs => go (acc ++ [:: nat_of_bin (N_of_ascii c)]) xs
      end in
  trace_helper (go [::] msg) x.

Extract Inlined Constant trace_helper => "LinearScan.Utils.trace".

End Trace.

Example maybeLast_ex1 : maybeLast ([::] : seq nat) == None.
Proof. by []. Qed.

Example maybeLast_ex2 : maybeLast [:: 1] == Some 1.
Proof. by []. Qed.

Example maybeLast_ex3 : maybeLast [:: 1; 2; 3] == Some 3.
Proof. by []. Qed.

Lemma maybeLast_cons2 {a} (x : a) z zs :
  maybeLast [:: x, z & zs] = maybeLast (z :: zs).
Proof. elim: zs => //. Qed.

Lemma maybeLast_cons {a} (x : a) xs :
  maybeLast (x :: xs) =
  match maybeLast xs with
  | Some y => Some y
  | None   => Some x
  end.
Proof.
  elim: xs => //= [z zs IHzs] in x *.
  rewrite maybeLast_cons2 IHzs.
  case: (maybeLast zs) => //.
Qed.

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

Lemma all_pairmap_cons {a} f (x : a) w ws :
  all id (pairmap f w ws) -> f x w -> all id (pairmap f x (w :: ws)).
Proof.
  move=> Hall Hf.
  elim: ws => //= [|z zs IHzs] in Hall *; by intuition.
Qed.

Definition all_in_list {a : eqType} (l : list a) : all (fun x => x \in l) l.
Proof. apply/allP; elim: l => //=. Qed.

Definition list_membership {a : eqType} (l : seq a) :
  seq { x : a | x \in l } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          exist _ x (mem_head _ xs) :: map exist_in_cons (go xs)
      end in
  go l.

Fixpoint apply_nth {a} (def : a) (v : seq a) i (f : a -> a) {struct i} :=
  if v is x :: v'
  then if i is i'.+1
       then x :: apply_nth def v' i' f
       else f x :: v'
  else ncons i def [:: def].

Lemma size_apply_nth a (v : seq a) i def f :
  size (apply_nth def v i f) = if i < size v then size v else i.+1.
Proof.
  elim: v i => [|n v IHv] [|i] //=;
  first by rewrite size_ncons /= addn1.
  rewrite IHv; exact: fun_if.
Qed.

Lemma neq_sym : forall (A : eqType) (x y : A),
  x != y -> y != x.
Proof.
  move=> A x y Hneq.
  move/eqP in Hneq.
  apply/eqP.
  by auto.
Qed.

Definition lebf {a : Type} (f : a -> nat) (n m : a) := f n <= f m.

Definition odd_1 : odd 1. done. Qed.

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

Lemma even_odd_plus n : ~~ odd n -> odd n.+1.
Proof. case: n => //. Qed.

Lemma odd_succ_succ n : odd (n.+2) = odd n.
Proof. by rewrite /=; apply/negPn; case: (odd n). Defined.

Definition odd_add_2 {n} : odd n -> odd n.+2.
Proof. by move=> H; rewrite odd_succ_succ. Defined.

Definition distance (n m : nat) : nat := if n < m then m - n else n - m.

Lemma leq_leq : forall n m o, n <= m <= o -> n <= o.
Proof.
  move=> n m o /andP [H1 H2].
  exact: (leq_trans H1 H2).
Qed.

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

Definition mapWithIndex {a b} (f : nat -> a -> b) (l : seq a) : seq b :=
  rev (snd (foldl (fun acc x => let: (n, xs) := acc in
                                (n.+1, f n x :: xs)) (0, [::]) l)).

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

Lemma foldl_cons : forall a b f (z : b) (x : a) xs,
  foldl f (f z x) xs = foldl f z (x :: xs).
Proof. move=> a b f z x; elim=> //=. Qed.

Lemma foldr_cons : forall a b f (z : b) (x : a) xs,
  f x (foldr f z xs) = foldr f z (x :: xs).
Proof. move=> a b f z x; elim=> //=. Qed.

Lemma foldl_add : forall a (f : a -> nat) xs n,
   foldl (fun n x => n + f x) n xs =
   foldl (fun n x => n + f x) 0 xs + n.
Proof.
  move=> a f; elim=> // a' ? IHxs n /=.
  rewrite add0n IHxs (IHxs (f a')) [n+_]addnC addnA //.
Qed.

Lemma foldl_cat : forall a zs xs,
  foldl (fun acc : seq a => cons^~ acc) zs xs =
  foldl (fun acc : seq a => cons^~ acc) [::] xs ++ zs.
Proof.
  move=> a zs xs; elim: xs => // a' ? IHxs /= in zs *.
  by rewrite IHxs [in RHS]IHxs /= cats1 -cat_rcons.
Qed.

Lemma foldl_rev {a} (xs : seq a) :
  rev (foldl (fun acc : seq a => cons^~ acc) [::] xs) = xs.
Proof.
  elim: xs => //= [x xs IHxs].
  rewrite -{2}IHxs -rev_rcons.
  congr (rev _).
  rewrite -cats1.
  exact: foldl_cat.
Qed.

Definition sumf {a} f : seq a -> nat := foldl (fun n x => n + f x) 0.

Definition sumlist : seq nat -> nat := foldl addn 0.

Lemma sumf_cons : forall a f xs (x : a),
  sumf f (x :: xs) = f x + sumf f xs.
Proof.
  move=> a f.
  rewrite /sumf /= => xs x.
  by rewrite foldl_add addnC add0n.
Qed.

Lemma sumlist_cons : forall xs (x : nat),
  sumlist (x :: xs) = x + sumlist xs.
Proof.
  rewrite /sumlist /= => xs x.
  by rewrite foldl_add addnC add0n.
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

Lemma lt_size_rev : forall a (xs : seq a),
  0 < size xs -> 0 < size (rev xs).
Proof.
  move=> a.
  elim=> //= [x xs IHxs] H.
  by rewrite size_rev /=.
Qed.

(*
Lemma last_cons_rev : forall a (y : a) ys H,
  safe_last (rev (y :: ys)) H = y.
Proof.

Lemma hd_last_spec : forall a (xs : seq a) (H : 0 < size xs),
  safe_hd xs H = safe_last (rev xs) (lt_size_rev H).
Proof.
  move=> a.
  elim=> [//|y ys IHys] /= H.
  by rewrite last_cons_rev.
Qed.
*)

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

Definition map_fst_filter_snd :
  forall (a b : eqType) (i : b) (xs : seq (a * b)),
  all (fun x => (x, i) \in xs) [seq fst x | x <- xs & snd x == i].
Proof.
  move=> a b i xs.
  apply/allP => x /mapP[[x1 y1]].
  by rewrite mem_filter => /andP[/eqP/=-> pIxs ->].
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

Lemma widen_fst_inj : forall a n,
  injective (widen_fst (a:=a) (n:=n)).
Proof.
  move=> a n.
  rewrite /injective => x1 x2.
  invert.
  destruct x1.
  destruct x2.
  simpl in *. subst.
  f_equal.
  destruct o. destruct o0. subst.
  unfold nat_of_ord in *.
  rewrite H0 in i *.
  have ->: i = i0 by exact: eq_irrelevance.
  by [].
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
  {A : Type}                    (* the value being mutated through the fold *)
  {P : A -> Prop}               (* an inductive predicate to be maintained on A *)
  {R : A -> A -> Prop}          (* a relation on A that must be preserved *)
  {E : A -> eqType}             (* type of the elements we are folding over *)
  (b : A)                       (* the initial state value *)
  (Pb : P b)                    (* predicate on the initial state value *)
  (v : seq (E b))               (* the list of elements from the initial state *)

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
  {P : A -> Prop}               (* an inductive predicate to be maintained on A *)
  {R : A -> A -> Prop}          (* a relation on A that must be preserved *)
  {E : A -> eqType}             (* type of the elements we are folding over *)
  (b : A)                       (* the initial state value *)
  (Pb : P b)                    (* predicate on the initial state value *)
  (v : seq (E b))               (* the list of elements from the initial state *)

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
  rewrite -H1 in Hn.
  rewrite -H0 in Hn.
  simpl in Hn.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.
