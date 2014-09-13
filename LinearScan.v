(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf *)

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import Coq.Vectors.Fin.
Require Import Recdef.

Module Import LN := ListNotations.

Generalizable All Variables.

(****************************************************************************)

(** * Library *)

(** The following are extensions to the Coq standard library. *)

(** ** Lists *)

Section Elems.

Variable a : Set.
Variable cmp_eq_dec : forall x y : a, {x = y} + {x <> y}.

(*
Lemma not_in_list : forall x xs,
  ~ In x xs -> count_occ cmp_eq_dec xs x = 0.
Proof.
  intros. induction xs; simpl; auto.
  destruct (cmp_eq_dec a0 x); subst.
    contradiction H. constructor. reflexivity.
  apply IHxs.
  unfold not in *. intros.
  apply H. right. assumption.
Qed.
*)

(*
Lemma In_spec : forall (x : a) y xs, In x xs -> ~ In y xs -> y <> x.
Proof.
  unfold not in *. intros. subst.
  contradiction.
Qed.
*)

Function NoDup_from_list (l : list a) {measure length l} : option (NoDup l) :=
  match l with
  | nil => Some (NoDup_nil a)
  | cons x xs =>
      match in_dec cmp_eq_dec x xs with
      | left H => None
      | right H =>
          match NoDup_from_list xs with
          | None => None
          | Some l' => Some (NoDup_cons _ H l')
          end
      end
  end.
Proof. auto. Qed.

Lemma NoDup_uncons : forall (x : a) xs, NoDup (x :: xs) -> NoDup xs.
Proof.
  intros. inversion H; subst.
  assumption.
Qed.

Lemma NoDup_unapp : forall (xs ys : list a), NoDup (xs ++ ys) -> NoDup ys.
Proof.
  intros.
  induction xs. auto.
  apply IHxs.
  rewrite <- app_comm_cons in H.
  apply NoDup_uncons in H.
  assumption.
Defined.

Lemma NoDup_swap : forall (xs ys : list a), NoDup (xs ++ ys) -> NoDup (ys ++ xs).
Proof.
  intros.
(* jww (2014-09-13): NYI *)
Admitted.

Lemma NoDup_swap2 : forall (xs ys zs : list a),
  NoDup (xs ++ ys ++ zs) -> NoDup (xs ++ zs ++ ys).
Proof.
  intros.
(* jww (2014-09-13): NYI *)
Admitted.

Lemma NoDup_swap_cons : forall x (xs ys : list a),
  NoDup (x :: xs ++ ys) -> NoDup (x :: ys ++ xs).
Proof.
  intros.
  constructor.
    inversion H; subst.
    unfold not in *. intros.
    apply H2.
    apply in_app_iff.
    apply in_app_iff in H0.
    intuition.
  apply NoDup_uncons in H.
  apply NoDup_swap.
  assumption.
Defined.

Lemma NoDup_juggle : forall x (xs ys zs : list a),
  NoDup (xs ++ ys ++ zs) -> NoDup (remove cmp_eq_dec x xs ++ (x :: ys) ++ zs).
Proof.
(* jww (2014-09-13): NYI *)
Admitted.

Definition find_in (n : a) (l : list a) : {In n l} + {~ In n l}.
Proof.
  induction l as [| x xs].
    right. auto.
  destruct (cmp_eq_dec n x).
    subst. left. apply in_eq.
  inversion IHxs.
    left. apply in_cons.
    assumption.
  right. unfold not in *.
  intros. apply in_inv in H0.
  inversion H0.
     symmetry in H1. contradiction.
  contradiction.
Defined.

End Elems.

Lemma LocallySorted_uncons : forall a (R : a -> a -> Prop) (x : a) xs,
  LocallySorted R (x :: xs) -> LocallySorted R xs.
Proof. intros. inversion H; subst; [ constructor | assumption ]. Qed.

(** ** Comparisons *)

(** These definitions avoid boilerplate involved with setting up properly
    behaved comparisons between types. *)

Definition is_eq (c : comparison) : bool :=
  match c with
    | Eq => true
    | _  => false
  end.

Definition is_lt (c : comparison) : bool :=
  match c with
    | Lt => true
    | _  => false
  end.

Definition is_le (c : comparison) : bool :=
  match c with
    | Gt => false
    | _  => true
  end.

Definition is_gt (c : comparison) : bool :=
  match c with
    | Gt => true
    | _  => false
  end.

Definition is_ge (c : comparison) : bool :=
  match c with
    | Lt => false
    | _  => true
  end.

Lemma mk_compare_spec : forall {a} (x y : a)
  (cmp         : a -> a -> comparison)
  (cmp_eq_iff  : cmp x y = Eq <-> x = y)
  (cmp_gt_flip : cmp x y = Gt  -> cmp y x = Lt),
  CompSpec eq (fun x y => cmp x y = Lt) x y (cmp x y).
Proof.
  intros.
  destruct (cmp x y) eqn:Heqe.
  - apply CompEq. apply cmp_eq_iff. reflexivity.
  - apply CompLt. assumption.
  - apply CompGt. auto.
Defined.

Lemma mk_cmp_eq_dec : forall {a} (x y : a)
  (cmp        : a -> a -> comparison)
  (cmp_eq_iff : cmp x y = Eq <-> x = y),
  { x = y } + { x <> y }.
Proof.
  intros.
  destruct (cmp x y) eqn:Heqe.
  - left. apply cmp_eq_iff. reflexivity.
  - right. intuition. inversion H2.
  - right. intuition. inversion H2.
Defined.

Class CompareSpec (a : Set) := {
  cmp         : a -> a -> comparison;
  cmp_eq x y  := cmp x y = Eq;
  cmp_eq_iff  : forall x y, cmp x y = Eq <-> x = y;
  cmp_lt x y  := cmp x y = Lt;
  cmp_le x y  := cmp_lt x y \/ cmp_eq x y;
  cmp_gt x y  := cmp x y = Gt;
  cmp_ge x y  := cmp_gt x y \/ cmp_eq x y;
  cmp_gt_flip : forall x y, cmp_gt x y -> cmp_lt y x;

  cmp_spec x y : CompSpec eq cmp_lt x y (cmp x y) :=
    mk_compare_spec x y cmp (cmp_eq_iff x y) (cmp_gt_flip x y);

  cmp_eq_dec x y : { x = y } + { x <> y } :=
    mk_cmp_eq_dec x y cmp (cmp_eq_iff x y)
}.

Ltac reduce_nat_comparisons H :=
  repeat (first
    [ match goal with
      | [ |- context f [match ?X with _ => _ end] ] =>
        destruct X
      end
    | match goal with
      | [ H': context f [match ?X with _ => _ end] |- _ ] =>
        destruct X
      end

    | match goal with
      | [ H': nat_compare ?X ?Y = Eq |- _ ] =>
        apply nat_compare_eq in H'
      end
    | match goal with
      | [ |- nat_compare ?X ?Y = Eq ] =>
        apply nat_compare_eq_iff
      end

    | match goal with
      | [ H': nat_compare ?X ?Y = Lt |- _ ] =>
        apply nat_compare_lt in H'
      end
    | match goal with
      | [ |- nat_compare ?X ?Y = Lt ] =>
        apply nat_compare_lt
      end

    | match goal with
      | [ H': nat_compare ?X ?Y = Gt |- _ ] =>
        apply nat_compare_gt in H'
      end
    | match goal with
      | [ |- nat_compare ?X ?Y = Gt ] =>
        apply nat_compare_gt
      end

    | omega | inversion H; reflexivity
    ]); subst; auto.

(** ** NonEmpty lists *)

Inductive NonEmpty (a : Set) : Set :=
  | NE_Sing : a -> NonEmpty a
  | NE_Cons : a -> NonEmpty a -> NonEmpty a.

Arguments NE_Sing [_] _.
Arguments NE_Cons [_] _ _.

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => x :: nil
    | NE_Cons x xs => x :: NE_to_list xs
  end.

Definition NE_hd {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x _ => x
  end.

Fixpoint NE_tl {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x xs => NE_tl xs
  end.

Inductive NonEmptySorted {a : Set} (R : a -> a -> Prop) : NonEmpty a -> Set :=
  | NESort_Sing x : NonEmptySorted R (NE_Sing x)
  | NESort_Cons x y xs :
      NonEmptySorted R (NE_Cons y xs) -> R x y
        -> NonEmptySorted R (NE_Cons x (NE_Cons y xs)).

(** ** Finite sets *)

Definition fin := Coq.Vectors.Fin.t.

Definition from_nat (n : nat) {m} (H : n < m) : fin m := @of_nat_lt n m H.

Definition fin_to_nat {n} (f : fin n) : nat := proj1_sig (to_nat f).

Definition ultimate_Sn (n : nat) : fin (S n).
Proof. induction n; [ apply F1 | apply FS; apply IHn ]. Defined.

(** Return the last possible inhabitant of a [fin n]. *)
Definition ultimate_from_nat (n : nat) (H : n > 0) : fin n.
Proof. induction n; [ omega | apply ultimate_Sn ]. Defined.

(** Given a value [x] of type [fin n], possibly return the next lower
    inhabitant of type [y], such that y < x. *)
Definition pred_fin {n} (f : fin n) : option (fin n).
  apply to_nat in f.
  destruct f.
  destruct x. apply None.
  apply Some.
  apply Le.le_Sn_le in l.
  apply (from_nat x l).
Defined.

(** [to_nat] and [from_nat] compose to an identity module the hypothesis that
    [n < m]. *)
Lemma fin_to_from_id : forall m n (H : n < m),
  m > 0 -> @to_nat m (from_nat n H) = exist _ n H.
Proof.
  intros.
  generalize dependent n.
  induction m; intros. omega.
  destruct n; simpl.
    f_equal. apply proof_irrelevance.
  rewrite IHm.
    f_equal. apply proof_irrelevance.
  omega.
Qed.

(** The behavior of [pred_fin] is specified as follows: the predecessor of a
    successor, by way of [fin n], is a no-op. *)
Lemma pred_fin_spec : forall (n m : nat) (H : S n < m),
  pred_fin (@from_nat _ m H) = Some (from_nat n (Le.le_Sn_le _ _ H)).
Proof.
  intros. unfold pred_fin.
  rewrite fin_to_from_id.
    reflexivity.
  omega.
Qed.

(** If [pred_fin] produces a value, this value converted to [nat] is less than
    the input converted to [nat]. *)
Lemma pred_fin_lt : forall n (x y : fin n),
  @pred_fin n x = Some y -> fin_to_nat y < fin_to_nat x.
Proof.
  unfold fin_to_nat.
  destruct n; intros.
    inversion x.
  unfold pred_fin in H.
  destruct (to_nat x).
  destruct x0; inversion H.
  subst. simpl. clear H.
  destruct x0; simpl. omega.
  unfold from_nat. clear x.
  rewrite fin_to_from_id.
  simpl. omega. omega.
Qed.

(** The function [fin_to_nat] is bijective. *)
Lemma fin_to_nat_bijective : forall n (x y : fin n),
  fin_to_nat x = fin_to_nat y <-> x = y.
Proof.
  unfold fin_to_nat.
  split; intros.
  - destruct n. inversion x.
    generalize dependent y.
    induction x; intros.
      dependent destruction y.
        reflexivity.
      simpl in H.
      destruct (to_nat y).
      simpl in H. inversion H.
    dependent destruction y.
      simpl in H.
      destruct (to_nat x).
      simpl in H. inversion H.
    specialize (IHx y).
    f_equal. apply IHx.
    simpl in H.
    destruct (to_nat x).
    destruct (to_nat y).
    simpl in H.
    apply eq_add_S in H.
    subst. reflexivity.
  - f_equal. f_equal. assumption.
Qed.

(** *** Comparison of values from the same finite set. *)

(** [fin] values may be compared.  It is simply a comparison of their
    underlying naturals, owing to proof irrelevance. *)

Definition fin_compare {n} (x y : fin n) : comparison :=
  nat_compare (fin_to_nat x) (fin_to_nat y).

Lemma fin_compare_eq_iff : forall n (x y : fin n),
  fin_compare x y = Eq <-> x = y.
Proof.
  unfold fin_compare.
  split; intros;
  first [ apply nat_compare_eq_iff
        | apply nat_compare_eq in H ];
  apply fin_to_nat_bijective; assumption.
Qed.

Lemma fin_compare_gt_flip : forall n (x y : fin n),
  fin_compare x y = Gt -> fin_compare y x = Lt.
Proof.
  unfold fin_compare. intros.
  apply nat_compare_gt in H.
  apply nat_compare_lt. omega.
Qed.

Program Instance fin_CompareSpec {n} : CompareSpec (fin n) := {
  cmp         := fin_compare;
  cmp_eq_iff  := fin_compare_eq_iff n;
  cmp_gt_flip := fin_compare_gt_flip n
}.

(****************************************************************************)

(** * Core data types *)

(** ** Range *)

(** The extent of a [Range] is the set of locations it ranges over.  By
    summing the extent of a list of ranges, we have an idea of how much ground
    is left to cover, and this gives us a notion of well-founded recursion for
    iterating over intervals that may split as we examine them -- i.e., whose
    total extent must decrease after each pass. *)

Record Range : Set := {
  rstart : nat;
  rend   : nat;

  range_properly_bounded : rstart < rend
}.

(** Two ranges are equal if they start at the same location and cover the same
    extent.  Otherwise, we compare first the start position, and then the
    length of the extent. *)
Definition Rcompare (x y : Range) : comparison :=
  match x with
  | {| rstart := rstart0; rend := rend0 |} =>
      match y with
      | {| rstart := rstart1; rend := rend1 |} =>
          match nat_compare rstart0 rstart1 with
          | Lt => Lt
          | Gt => Gt
          | Eq => nat_compare rend0 rend1
          end
      end
  end.

Lemma Rcompare_eq_iff : forall x y : Range, Rcompare x y = Eq <-> x = y.
Proof.
  intros.
  destruct x. destruct y. simpl.
  split; intros;
  destruct (nat_compare rstart0 rstart1) eqn:Heqe;
  inversion H; subst;
  inversion Heqe;
  try (apply nat_compare_eq_iff; reflexivity).
    apply nat_compare_eq_iff in H1.
    apply nat_compare_eq_iff in H2.
    subst. f_equal. apply proof_irrelevance.
  rewrite Heqe.
  apply nat_compare_eq_iff. reflexivity.
Qed.

Lemma Rcompare_gt_flip : forall x y : Range,
  Rcompare x y = Gt -> Rcompare y x = Lt.
Proof.
  intros.
  unfold Rcompare in *.
  destruct x. destruct y.
  destruct (nat_compare rstart0 rstart1) eqn:Heqe;
  destruct (nat_compare rstart1 rstart0) eqn:Heqe2;
  reduce_nat_comparisons Heqe;
  try auto; inversion H.
Qed.

Program Instance Range_CompareSpec : CompareSpec Range := {
  cmp         := Rcompare;
  cmp_eq_iff  := Rcompare_eq_iff;
  cmp_gt_flip := Rcompare_gt_flip
}.

Definition in_range (loc : nat) (r : Range) : Prop :=
  rstart r <= loc /\ loc < rend r.

Definition rangesIntersect (i j : Range) : bool :=
  if rstart i <? rstart j
  then rstart j <? rend i
  else rstart i <? rend j.

Definition anyRangeIntersects (is js : NonEmpty Range) : bool :=
  fold_right
    (fun r b => orb b (existsb (rangesIntersect r) (NE_to_list js)))
    false (NE_to_list is).

(** ** RangeList *)

(** A [RangeList] encodes both the total extent of the list of ranges (the
    total span of instructions covered by all the ranges), and also the fact
    that ranges must be ordered and disjoint (non-overlapping). *)

Inductive RangeList : NonEmpty Range -> Set :=
  | RangeSing r : RangeList (NE_Sing r)
  | RangeCons r rs :
    RangeList rs -> rend r <= rstart (NE_hd rs) -> RangeList (NE_Cons r rs).

Definition rangeListStart `(RangeList xs) := rstart (NE_hd xs).
Definition rangeListEnd   `(RangeList xs) := rend (NE_tl xs).

Definition rangeListExtent `(rs : RangeList xs) :=
  rangeListEnd rs - rangeListStart rs.

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos `(RangeList ranges) : Set := {
  uloc   : nat;
  regReq : bool;

  within_range : Exists (in_range uloc) (NE_to_list ranges)
}.

(** ** Interval *)

(** A lifetime interval defines the lifetime of a variable.  It is defined as
    a list of ranges "covered" by that variable in the low-level intermediate
    representation (LIR).  Gaps in the list of ranges are called "lifetime
    holes".

    A lifetime is not necessarily only the distance that a variable is first
    and last used.  The lifetime of a variable used in a loop extends to the
    whole loop, for example, even if it is only used at the very end.  In this
    sense, coverage takes into account code flow, or what ranges would map to
    if all loops were unrolled, and then rolled back keeping track of
    coverage.

    Use positions are actual instructions where a variable is read from or
    written to, and whether it is required to be in a register at that
    point. *)

(** If for some reason we cannot assign a single register for all ranges, then
    the interval is split into two or more intervals, so each interval can be
    assigned its own register. *)

Definition IntervalId := nat.

Record Interval : Set := {
  ranges       : NonEmpty Range;
  lifetimes    : RangeList ranges;
  usePositions : NonEmpty (UsePos lifetimes)
}.

Definition intervalStart  i := rangeListStart  (lifetimes i).
Definition intervalEnd    i := rangeListEnd    (lifetimes i).
Definition intervalExtent i := rangeListExtent (lifetimes i).

Definition intervalRange (i : Interval) : Range.
  apply Build_Range
    with (rstart := intervalStart i)
         (rend   := intervalEnd i).
  unfold intervalStart, intervalEnd.
  induction (lifetimes i).
    apply range_properly_bounded.
  destruct r0;
  unfold rangeListStart, rangeListEnd in *;
  destruct r; destruct r0; simpl in *; omega.
Defined.

Definition Icompare (x y : Interval) : comparison :=
  Rcompare (NE_hd (ranges x)) (NE_hd (ranges y)).

Infix "?=" := Icompare (at level 70, no associativity).

Lemma Icompare_eq_refl : forall x, (x ?= x) = Eq.
Proof.
  intros. destruct x.
  unfold Icompare, Rcompare. simpl.
  induction ranges0; simpl; destruct a;
  destruct (nat_compare rstart0 rstart0) eqn:Heqe;
  try (apply nat_compare_eq_iff; reflexivity);
  try (apply nat_compare_lt in Heqe; omega);
  try (apply nat_compare_gt in Heqe; omega).
Qed.

Lemma Icompare_eq_iff : forall x y : Interval, x ?= y = Eq <-> x = y.
Proof.
  split; intros.
(* jww (2014-09-12): NYI *)
Admitted.

Lemma Icompare_gt_contra : forall x y : Interval,
  x ?= y = Gt -> y ?= x = Gt -> False.
Proof.
  intros. destruct x. destruct y.
  unfold Icompare, Rcompare in *.
  destruct ranges0 eqn:Heqr1; destruct r;
  destruct ranges1 eqn:Heqr2; destruct r; simpl in *;
  destruct (nat_compare rstart0 rstart1) eqn:Heqe;
  destruct (nat_compare rstart1 rstart0) eqn:Heqe2;
  try solve [ reduce_nat_comparisons H ];
  inversion H0.
Qed.

Lemma Icompare_gt_flip : forall x y : Interval, x ?= y = Gt -> y ?= x = Lt.
Proof.
(* jww (2014-09-12): NYI *)
Admitted.

Program Instance Interval_CompareSpec : CompareSpec Interval := {
  cmp         := Icompare;
  cmp_eq_iff  := Icompare_eq_iff;
  cmp_gt_flip := Icompare_gt_flip
}.

Module IntervalOrder <: TotalLeBool.
  Definition t := Interval.

  Definition leb (x y : Interval) : bool := is_le (cmp x y).
  Definition leb_true x y := is_true (leb x y).

  Theorem leb_total : forall (a1 a2 : Interval),
    leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros. unfold leb.
    destruct (cmp a1 a2) eqn:Heqe.
    - left. reflexivity.
    - left. reflexivity.
    - right. apply cmp_gt_flip in Heqe.
      rewrite Heqe. reflexivity.
  Qed.
End IntervalOrder.


Record IntervalsSortedByStart := {
  isbs : list Interval;
  isbs_unique : NoDup isbs;
  isbs_ordered : LocallySorted IntervalOrder.leb_true isbs
}.

Definition extentOfIntervals (is : IntervalsSortedByStart) : nat :=
  fold_left (fun n x => n + intervalExtent x) (isbs is) 0.

Module Import MergeSort := Sort IntervalOrder.

Lemma NoDup_sorted : forall xs, NoDup xs -> NoDup (sort xs).
Proof.
(* jww (2014-09-13): NYI *)
Admitted.

Definition sortIntervals (xs : list Interval) : option IntervalsSortedByStart.
Proof.
  pose (NoDup_from_list _ cmp_eq_dec xs).
  destruct o.
  - apply Some.
    apply Build_IntervalsSortedByStart
      with (isbs := sort xs).
    + induction n.
      * compute. apply NoDup_nil.
      * apply NoDup_sorted.
        apply NoDup_cons; assumption.
    + apply Sorted_LocallySorted_iff.
      apply LocallySorted_sort.
  - apply None.
Defined.

(****************************************************************************)

(** * Main algorithm *)

Section Allocator.

Variable maxReg : nat.          (* max number of registers *)

Hypothesis registers_exist : maxReg > 0.

Definition VirtReg := nat.
Definition PhysReg := fin maxReg.

(** ** ScanState *)

(** A [ScanState] is always relative to a current position (pos) as we move
    through the sequentialized instruction stream over which registers are
    allocated.. *)

Record ScanState := {
    unhandled : IntervalsSortedByStart;  (* starts after pos *)

    active    : list Interval;  (* ranges over pos *)
    inactive  : list Interval;  (* falls in lifetime hole *)
    handled   : list Interval;  (* ends before pos *)

    assignments : Interval -> option PhysReg;

    all_state_lists  := isbs unhandled ++ active ++ inactive ++ handled;
    lists_are_unique : NoDup all_state_lists
}.

Program Definition newScanState (xs : IntervalsSortedByStart)
  : ScanState                   := {| unhandled := xs
                  ; active      := nil
                  ; inactive    := nil
                  ; handled     := nil
                  ; assignments := fun _ => None
                  |}.
Obligation 1. destruct xs. rewrite app_nil_r. assumption. Qed.

Definition scanStateUnhandledExtent (st : ScanState) : nat :=
  extentOfIntervals (unhandled st).

Definition nextUnhandled (st : ScanState) : option (Interval * ScanState).
Proof.
  destruct st.
  destruct unhandled0.
  destruct isbs0.
    apply None.
  apply Some.
  split. apply i.
  apply {| unhandled :=
           {| isbs         := isbs0
            ; isbs_unique  := NoDup_uncons _ _ _ isbs_unique0
            ; isbs_ordered :=
                LocallySorted_uncons _ _ _ _ isbs_ordered0
            |}
         ; active           := active0
         ; inactive         := inactive0
         ; handled          := handled0
         ; assignments      := assignments0
         ; lists_are_unique := NoDup_uncons _ _ _ lists_are_unique0
         |}.
Defined.

(* jww (2014-09-13): Verify that [x] doesn't already exist in [st], which is
   something we should be able to determine. *)
Definition moveActiveToHandled (st : ScanState) (x : Interval)
  (* (H : In x (active st)) *) : ScanState.
Proof.
  destruct st.
  apply Build_ScanState
    with (unhandled   := unhandled0)
         (active      := remove cmp_eq_dec x active0)
         (inactive    := inactive0)
         (handled     := x :: handled0).
    apply assignments0.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply NoDup_swap2.
  rewrite <- app_assoc.
  apply NoDup_juggle.
  rewrite app_assoc.
  apply NoDup_swap2.
  rewrite app_assoc.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite app_assoc.
  apply NoDup_swap2.
  rewrite <- app_assoc.
  assumption.
Defined.

(* jww (2014-09-13): Verify that [x] doesn't already exist in [st], which is
   something we should be able to determine. *)
Definition moveActiveToInactive (st : ScanState) (x : Interval)
  (* (H : In x (active st)) *) : ScanState.
  destruct st.
  apply Build_ScanState
    with (unhandled := unhandled0)
         (active    := remove cmp_eq_dec x active0)
         (inactive  := x :: inactive0)
         (handled   := handled0).
    apply assignments0.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply NoDup_juggle.
  rewrite app_assoc.
  rewrite app_assoc.
  apply NoDup_swap.
  rewrite <- app_assoc.
  assumption.
Defined.

Definition addToActive (st : ScanState) (x : Interval * PhysReg)
  (* (H : ~ In x (all_state_lists st)) *) : ScanState.
Proof.
  destruct st.
  apply Build_ScanState
    with (unhandled := unhandled0)
         (active    := fst x :: active0)
         (inactive  := inactive0)
         (handled   := handled0).
    apply (fun i => if cmp_eq_dec i (fst x)
                    then Some (snd x)
                    else assignments0 i).
  unfold all_state_lists in *.
  unfold all_state_lists0 in *. simpl in *.
  apply NoDup_swap.
  rewrite <- app_comm_cons.
  apply NoDup_swap_cons.
  apply NoDup_cons.
  admit. assumption.
(* jww (2014-09-13): NYI *)
Admitted.

Definition getRegisterIndex (st : ScanState) (k : Interval -> nat)
  (z : PhysReg -> option nat) (is : list Interval) : PhysReg -> option nat :=
  fold_right
    (fun x f => fun r =>
       match assignments st x with
       | None => f r
       | Some a => if cmp_eq_dec a r
                   then Some (k x)
                   else f r
       end) z is.

(** ** Main functions *)

Definition nextIntersectionWith (i : Interval) (x : Interval) : nat.
Proof.
(* jww (2014-09-12): NYI *)
Admitted.

Function findRegister (freeUntilPos : PhysReg -> option nat) (reg : PhysReg)
  {measure fin_to_nat reg} : (PhysReg * option nat)%type :=
  match freeUntilPos reg with
  | None => (reg, None)
  | Some pos =>
      match pred_fin reg with
      | None => (reg, Some pos)
      | Some nreg =>
          match findRegister freeUntilPos nreg with
          | (reg', None) => (reg', None)
          | (reg', Some pos') =>
              if pos <? pos'
              then (reg', Some pos')
              else (reg,  Some pos)
          end
      end
  end.
Proof. intros. apply pred_fin_lt. assumption. Qed.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)

Definition tryAllocateFreeReg (st : ScanState) (current : Interval)
  : option ((Interval * PhysReg) * ScanState) :=
  (* The first part of this algorithm has been modified to be more functional:
     instead of mutating an array called [freeUntilPos] and finding the
     register with the highest value, we use a function produced by a fold,
     and iterate over the register set. *)

  (* set freeUntilPos of all physical registers to maxInt
     for each interval it in active do
       freeUntilPos[it.reg] = 0 *)
  let freeUntilPos' :=
        getRegisterIndex st (fun _ => 0) (fun r => None) (active st) in

  (* for each interval it in inactive intersecting with current do
       freeUntilPos[it.reg] = next intersection of it with current *)
  let intersectingIntervals :=
        filter (fun x =>
                  anyRangeIntersects (ranges current) (ranges x))
               (inactive st) in
  let freeUntilPos :=
        getRegisterIndex st (nextIntersectionWith current) freeUntilPos'
                         intersectingIntervals in

  (* reg = register with highest freeUntilPos *)
  let lastReg := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := findRegister freeUntilPos lastReg in
  let useReg := ((current, reg), st) in

  match mres with
  | None => Some useReg
  | Some n =>
      (* if freeUntilPos[reg] = 0 then
           // no register available without spilling
           allocation failed *)
      if beq_nat n 0
      then None
      (* else if current ends before freeUntilPos[reg] then
           // register available for the whole interval
           current.reg = reg *)
      else if ltb (intervalEnd current) n
           then Some useReg
      (* else
           // register available for the first part of the interval
           current.reg = reg
           split current before freeUntilPos[reg] *)
           else None            (* jww (2014-09-12): NYI *)
  end.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  This is why the
    type differs from [tryAllocateFreeReg], since in ever case the final state
    will be changed. *)

Definition allocateBlockedReg (st : ScanState) (current : Interval)
  : (option (Interval * PhysReg) * ScanState).
  (* set nextUsePos of all physical registers to maxInt *)

  (* for each interval it in active do
       nextUsePos[it.reg] = next use of it after start of current
     for each interval it in inactive intersecting with current do
       nextUsePos[it.reg] = next use of it after start of current *)

  (* reg = register with highest nextUsePos
     if first usage of current is after nextUsePos[reg] then
       // all other intervals are used before current, so it is best
       // to spill current itself
       assign spill slot to current
       split current before its first use position that requires a register
     else
       // spill intervals that currently block reg
       current.reg = reg
       split active interval for reg at position
       split any inactive interval for reg at the end of its lifetime hole *)

  (* // make sure that current does not intersect with
     // the fixed interval for reg
     if current intersects with the fixed interval for reg then
       splse current before this intersection *)
(* jww (2014-09-12): NYI *)
Admitted.

Definition handleInterval (current : Interval) (st0 : ScanState) : ScanState :=
  (* position = start position of current *)
  let position := intervalStart current in

  (* // check for intervals in active that are handled or inactive
     for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let go1 x st :=
    match intervalRange x with
    | Build_Range s e Hb =>
      if e <? position
      then moveActiveToHandled st x
      else if position <? s
           then moveActiveToInactive st x
           else st
    end in
  let st1 := fold_right go1 st0 (active st0) in

  (* // check for intervals in inactive that are handled or active
     for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let go2 x st := st in         (* jww (2014-09-12): NYI *)
  let st2 := fold_right go2 st1 (inactive st1) in

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg *)
  let (mres, st3) :=
      match tryAllocateFreeReg st2 current with
      | None => allocateBlockedReg st2 current
      | Some (current', st') => (Some current', st')
      end in

  (* if current has a register assigned then
       add current to active *)
  match mres with
  | None => st3
  | Some res => addToActive st3 res
  end.

Function linearScan (st : ScanState)
    {measure scanStateUnhandledExtent st} : ScanState :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match nextUnhandled st with
  | None => st
  | Some (current, p) => linearScan (handleInterval current p)
  end.
Proof.
  (* Our goal is to prove that after every call to handleInterval, the total
     scope of the remaining unhandled intervals is less than it was before,
     narrowing down to zero. *)
  intros.
  unfold scanStateUnhandledExtent.
  unfold extentOfIntervals.
  unfold nextUnhandled in teq.
  unfold handleInterval.
  (* induction (unhandled st); intros. *)
  (*   destruct isbs0 eqn:Heqe; subst; simpl in *. *)
  (*     apply S.min_elt_spec1 in Heqe. *)
  (*     specialize (H e). *)
  (*     contradiction. *)
  (*   inversion teq. *)
  (* (* At this point, we know that the list of unhandled intervals is not Empty, *)
  (*    and we must show that the result of calling handleInterval reduces the *)
  (*    total scope length. *) *)
  (* destruct p. subst. *)
  (* inversion teq0; subst. *)
(* jww (2014-09-12): NYI *)
Admitted.

End Allocator.

(****************************************************************************)

(** * Program graphs *)

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {}.

Definition determineIntervals (g : Graph VirtReg) : list Interval.
(* jww (2014-09-12): NYI *)
Admitted.

Definition allocateRegisters (maxReg : nat) (H : maxReg > 0)
  (g : Graph VirtReg) : option (ScanState maxReg) :=
  let mres := sortIntervals (determineIntervals g) in
  match mres with
  | None => None
  | Some is =>
      let st := newScanState maxReg is in
      Some (linearScan maxReg H st)
  end.
