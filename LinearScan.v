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

Lemma NoDup_swap : forall (xs ys : list a), NoDup (xs ++ ys) -> NoDup (ys ++ xs).
Proof.
  intros.
Admitted.

Lemma NoDup_swap2 : forall (xs ys zs : list a),
  NoDup (xs ++ ys ++ zs) -> NoDup (xs ++ zs ++ ys).
Proof.
  intros.
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
Admitted.

Lemma NoDup_unapp : forall (xs ys : list a), NoDup (xs ++ ys) -> NoDup ys.
Proof.
  intros.
  induction xs. auto.
  apply IHxs.
  rewrite <- app_comm_cons in H.
  apply NoDup_uncons in H.
  assumption.
Defined.

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

Lemma In_spec : forall (x : a) y xs, In x xs -> ~ In y xs -> y <> x.
Proof.
  unfold not in *. intros. subst.
  contradiction.
Qed.

Lemma Forall_uncons :
  forall {A : Type} {P : A -> Prop} {x l l0},
  Forall P l -> l = x :: l0 -> P x * Forall P l0.
Proof.
  intros.
  generalize dependent l.
  induction l0; intros.
    destruct l; inversion H0.
    inversion H; subst. auto.
  specialize (IHl0 (x :: l0)). subst.
  split; inversion H; subst; auto.
Qed.

End Elems.

Lemma LocallySorted_uncons : forall a (R : a -> a -> Prop) (x : a) xs,
  LocallySorted R (x :: xs) -> LocallySorted R xs.
Proof. intros. inversion H; subst; [ constructor | assumption ]. Qed.

Definition safe_hd {a} (xs : list a) (H : (length xs > 0)%nat) : a.
Proof.
  destruct xs.
    simpl in H.
    unfold gt in H.
    unfold Peano.lt in H.
    apply Le.le_Sn_n in H.
    inversion H.
  apply a0.
Defined.

Fixpoint safe_last {a} (xs : list a) (H : (length xs > 0)%nat) : a.
Proof.
  induction xs.
    simpl in H.
    unfold gt in H.
    unfold Peano.lt in H.
    apply Le.le_Sn_n in H.
    inversion H.
  destruct xs.
    apply a0.
  apply IHxs. simpl.
  apply Gt.gt_Sn_O.
Defined.

(** ** Comparisons *)

(** These definitions avoid boilerplate involved with setting up properly
    behaved comparisons between types. *)

Definition is_le (c : comparison) : bool :=
  match c with
    | Gt => false
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

(** ** Finite sets *)

Definition fin := Coq.Vectors.Fin.t.

Definition fin_transport (n m : nat) (H : n <= m) (f : fin n) : fin m.
Proof.
  induction f.
    induction n.
      destruct m. omega.
      constructor.
    apply IHn. omega.
  apply IHf. omega.
Defined.

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

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
  uloc   : nat;
  regReq : bool
}.

Definition UPcompare (x y : UsePos) : comparison :=
  match nat_compare (uloc x) (uloc y) with
  | Lt => Lt
  | Gt => Gt
  | Eq => if andb (regReq x) (regReq y) then Eq
          else if regReq y then Lt else Gt
  end.

Lemma UPcompare_eq_iff : forall (x y : UsePos), UPcompare x y = Eq <-> x = y.
Proof.
Admitted.

Lemma UPcompare_gt_flip : forall (x y : UsePos),
  UPcompare x y = Gt -> UPcompare y x = Lt.
Proof.
Admitted.

Program Instance UsePos_CompareSpec : CompareSpec UsePos := {
  cmp         := UPcompare;
  cmp_eq_iff  := UPcompare_eq_iff;
  cmp_gt_flip := UPcompare_gt_flip
}.

(** ** Range *)

(** The extent of a [Range] is the set of locations it ranges over.  By
    summing the extent of a list of ranges, we have an idea of how much ground
    is left to cover, and this gives us a notion of well-founded recursion for
    iterating over intervals that may split as we examine them -- i.e., whose
    total extent must decrease after each pass.

    A Range is built up from a set of use positions, and defines the inclusive
    range of those positions.  It can be extended, or split, but never shrunk.
    Also, the non-empty list of use positions is not guaranteed to be in any
    order, and overlapping use positions are accepted but only the most recent
    one "wins". *)

Record RangeDesc := {
    rbeg : nat;
    rend : nat;
    ups  : NonEmpty UsePos
}.

Inductive Range : RangeDesc -> Set :=
  | R_Sing u :
      Range {| rbeg := uloc u
             ; rend := uloc u
             ; ups  := NE_Sing u
             |}
  | R_Cons u x : Range x -> uloc u < rbeg x
      -> Range {| rbeg := rbeg x
                ; rend := rend x
                ; ups  := NE_Cons u (ups x)
                |}
  | R_Extend x b' e' : Range x
      -> Range {| rbeg := min b' (rbeg x)
                ; rend := Peano.max e' (rend x)
                ; ups  := ups x
                |}.

(*
(** Two ranges are equal if they start at the same location and cover the same
    extent.  Otherwise, we compare first the start position, and then the
    length of the extent. *)
Definition Rcompare `(x : Range xs xb xe) `(y : Range ys yb ye) : comparison.
Admitted.

Lemma Rcompare_eq_iff `(x : Range xs xb xe) `(y : Range ys yb ye)
  : Rcompare x y = Eq <-> x = y.
Admitted.
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
*)

Definition in_range (loc : nat) `(r : Range d) : Prop :=
  rbeg d <= loc /\ loc < rend d.

Definition rangesIntersect `(x : RangeDesc) `(y : RangeDesc) : bool :=
  if rbeg x <? rbeg y then rbeg y <? rend x else rbeg x <? rend y.

Definition anyRangeIntersects (is js : NonEmpty RangeDesc) : bool :=
  fold_right
    (fun r b => orb b (existsb (rangesIntersect r) (NE_to_list js)))
    false (NE_to_list is).

(*
Definition rangeListStart (xs : NonEmpty Range) := rstart (NE_hd xs).
Definition rangeListEnd   (xs : NonEmpty Range) := rend (NE_tl xs).

Definition rangeListExtent (xs : NonEmpty Range) :=
  rangeListEnd xs - rangeListStart xs.
*)

(** ** RangeList *)

(** A [RangeList] encodes both the total extent of the list of ranges (the
    total span of instructions covered by all the ranges), and also the fact
    that ranges must be ordered and disjoint (non-overlapping). *)

(*
Inductive RangeList : NonEmpty Range -> Set :=
  | RangeSing r : RangeList (NE_Sing r)
  | RangeCons r rs :
    RangeList rs -> rend r <= rstart (NE_hd rs) -> RangeList (NE_Cons r rs).
*)

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

Inductive Interval : NonEmpty RangeDesc -> Set :=
  | I_Sing : forall x, Range x -> Interval (NE_Sing x)
  | I_Cons1 : forall x y,
      Range x -> Interval (NE_Sing y) -> rend y <= rbeg y
        -> Interval (NE_Cons x (NE_Sing y))
  | I_Consn : forall x y xs,
      Range x -> Interval (NE_Cons y xs) -> rend y <= rbeg y
        -> Interval (NE_Cons x (NE_Cons y xs)).

Definition intervalStart `(i : Interval rs) : nat := rbeg (NE_hd rs).
Definition intervalEnd   `(i : Interval rs) : nat := rend (NE_tl rs).

Definition intervalExtent `(i : Interval rs) :=
  intervalEnd i - intervalStart i.

(*
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
  split; intros. destruct x. destruct y.
  unfold Icompare, Rcompare in *. simpl in *.
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

Module Import MergeSort := Sort IntervalOrder.

Lemma NoDup_sorted : forall xs, NoDup xs -> NoDup (sort xs).
Proof.
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
*)

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
    nextInterval : nat;
    IntervalId   := fin nextInterval;

    unhandled : list IntervalId;   (* starts after pos *)
    active    : list IntervalId;   (* ranges over pos *)
    inactive  : list IntervalId;   (* falls in lifetime hole *)
    handled   : list IntervalId;   (* ends before pos *)

    getInterval  : IntervalId -> { rs : NonEmpty RangeDesc & Interval rs };
    assignments  : IntervalId -> option PhysReg;

    all_state_lists  := unhandled ++ active ++ inactive ++ handled;
    lists_are_unique : NoDup all_state_lists
}.

Definition unhandledExtent (st : ScanState) : nat :=
  fold_left (fun n x => n + intervalExtent (projT2 (getInterval st x)))
            (unhandled st) 0.

Program Definition newScanState
  : ScanState := {| nextInterval := 0
                  ; unhandled    := nil
                  ; active       := nil
                  ; inactive     := nil
                  ; handled      := nil
                  ; assignments  := fun _ => None
                  |}.
Obligation 1. inversion H. Defined.
Obligation 2. constructor. Defined.

Definition nextUnhandled (st : ScanState)
  : option { st' : ScanState & IntervalId st' }.
Proof.
  destruct st.
  destruct unhandled0.
    apply None.
  apply Some.
  exists {| unhandled        := unhandled0
          ; active           := active0
          ; inactive         := inactive0
          ; handled          := handled0
          ; getInterval      := getInterval0
          ; assignments      := assignments0
          ; lists_are_unique := NoDup_uncons _ _ _ lists_are_unique0
          |}.
  apply i.
Defined.

(* jww (2014-09-14): I would like for this function to only be callable if
   proof is gives that [x] is a member of [active st], otherwise it is not a
   move and merely an insertion in [handled st].  However, attempts to do so
   have proved complicated. The real problem is that [remove] is fine with
   being requested to remove a non-member. *)
Definition moveActiveToHandled `(x : IntervalId st)
  : { st0 : ScanState | nextInterval st = nextInterval st0 }.
Proof.
  destruct st.
  eexists {| unhandled   := unhandled0
           ; active      := remove cmp_eq_dec x active0
           ; inactive    := inactive0
           ; handled     := x :: handled0
           ; getInterval := getInterval0
           ; assignments := assignments0
           |}.
    reflexivity.
    Grab Existential Variables.
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

Definition moveActiveToInactive `(x : IntervalId st)
  : { st0 : ScanState | nextInterval st = nextInterval st0 }.
Proof.
  destruct st.
  eexists {| unhandled   := unhandled0
           ; active      := remove cmp_eq_dec x active0
           ; inactive    := x :: inactive0
           ; handled     := handled0
           ; getInterval := getInterval0
           ; assignments := assignments0
           |}.
    reflexivity.
    Grab Existential Variables.
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

Record AllocateResult := {
    resultState       : ScanState;
    currentRanges     : NonEmpty RangeDesc;
    currentIntervalId : IntervalId resultState;
    currentInterval   : Interval currentRanges
}.

(* We need to know that [x] is not already a member of the [ScanState].  We
   know it was removed from the [ScanState] by [nextUnhandled], but it may
   have been split and the other parts added back to the unhandled list, so we
   need to know that it's not going to recur. *)
Definition addToActive (result : AllocateResult) (reg : PhysReg)
   (H : ~ In (currentIntervalId result)
             (all_state_lists (resultState result))) : ScanState.
Proof.
  destruct result.
  destruct resultState0.
  eapply {| unhandled   := unhandled0
          ; active      := currentIntervalId0 :: active0
          ; inactive    := inactive0
          ; handled     := handled0
          ; getInterval := getInterval0
          ; assignments := fun i =>
              if cmp_eq_dec i currentIntervalId0
              then Some reg
              else assignments0 i
          |}.
  Grab Existential Variables.
  unfold all_state_lists in *.
  unfold all_state_lists0 in *.
  unfold IntervalId, IntervalId0 in *. simpl in *.
  apply NoDup_swap.
  rewrite <- app_comm_cons.
  apply NoDup_swap_cons.
  apply NoDup_cons; assumption.
Defined.

Definition getRegisterIndex (st : ScanState) (k : IntervalId st -> nat)
  (z : PhysReg -> option nat) (is : list (IntervalId st))
  : PhysReg -> option nat :=
  fold_right
    (fun x f => fun r =>
       match assignments st x with
       | None => f r
       | Some a => if cmp_eq_dec a r then Some (k x) else f r
       end) z is.

(** ** Main functions *)

Definition nextIntersectionWith (st : ScanState)
  `(x : Interval xd) (yid : IntervalId st) : nat.
Proof.
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

Definition tryAllocateFreeReg (st : ScanState)
  (currentId : IntervalId st) `(current : Interval rs)
  : option (PhysReg * AllocateResult) :=
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
                  anyRangeIntersects rs (projT1 (getInterval st x)))
               (inactive st) in
  let freeUntilPos :=
        getRegisterIndex st (nextIntersectionWith st current) freeUntilPos'
                         intersectingIntervals in

  (* reg = register with highest freeUntilPos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := findRegister freeUntilPos lastReg in
  let useReg      := (reg, {| resultState       := st
                            ; currentRanges     := rs
                            ; currentIntervalId := currentId
                            ; currentInterval   := current
                           |}) in

  match mres with
  | None => Some useReg
  | Some n =>
      (* if freeUntilPos[reg] = 0 then
           // no register available without spilling
           allocation failed
         else if current ends before freeUntilPos[reg] then
           // register available for the whole interval
           current.reg = reg
         else
           // register available for the first part of the interval
           current.reg = reg
           split current before freeUntilPos[reg] *)
      if beq_nat n 0
      then None
      else if ltb (intervalEnd current) n
           then Some useReg
           else None            (* jww (2014-09-12): NYI *)
  end.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  This is why the
    type differs from [tryAllocateFreeReg], since in all cases the final state
    is changed. *)
Definition allocateBlockedReg (st : ScanState) `(current : Interval rs)
  : option PhysReg * AllocateResult.
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
Admitted.

Definition transportId `(H : nextInterval st <= nextInterval st')
  (x : IntervalId st) : IntervalId st'.
Proof.
  destruct st. destruct st'.
  unfold IntervalId0, IntervalId1 in *.
  unfold IntervalId in *. simpl in *.
  apply (fin_transport nextInterval0 nextInterval1 H).
  assumption.
Defined.

(* Given a starting ScanState (at which point, st = st0), walk through the
   list of active intervals and mutate st0 until it reflects the desired end
   state. *)
Fixpoint checkActiveIntervals st (is : list (IntervalId st)) pos
  : { st' : ScanState | nextInterval st = nextInterval st' } :=
  let fix go st st0 (H : nextInterval st = nextInterval st0)
             (is : list (IntervalId st)) (pos : nat) :=
    match is with
    | nil => exist _ st0 H
    | x :: xs =>
        let i := projT2 (getInterval st x) in
        let x0 := transportId (Nat.eq_le_incl _ _ H) x in
        let s := if intervalEnd i <? pos
                 then moveActiveToHandled x0
                 else if pos <? intervalStart i
                      then moveActiveToInactive x0
                      else exist _ st0 eq_refl in
        go st (proj1_sig s)
          (eq_trans H (proj2_sig s)) xs pos
    end in
  go st st eq_refl is pos.

Definition handleInterval `(currentId : IntervalId st0) : ScanState :=
  (* position = start position of current *)
  let current  := projT2 (getInterval st0 currentId) in
  let position := intervalStart current in

  (* // check for intervals in active that are handled or inactive
     for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let st1S := checkActiveIntervals st0 (active st0) position in

  (* // check for intervals in inactive that are handled or active
     for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let go2 x st := st in         (* jww (2014-09-12): NYI *)
  let st2S := fold_right go2 st1S (inactive (projT1 st1S)) in

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg *)
  let cid2 := transportId (Nat.eq_le_incl _ _ (projT2 st2S)) currentId in
  let (mreg, result) :=
      match tryAllocateFreeReg (projT1 st2S) cid2 current with
      | Some (reg, st') => (Some reg, st')
      | None => allocateBlockedReg (projT1 st2S) current
      end in

  (* if current has a register assigned then
       add current to active *)
  match mreg with
  | Some reg =>
      (* Using [find_in] here is a major weak point.  I should be able to
         determine H from the code above. *)
      match find_in _ cmp_eq_dec (currentIntervalId result)
                    (all_state_lists (resultState result)) with
      | right H => addToActive result reg H
      | left _  => resultState result
      end
  | None => resultState result
  end.

Function linearScan (st : ScanState) {measure unhandledExtent st}
  : ScanState :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match nextUnhandled st with
  | None => st
  | Some p => linearScan (handleInterval (projT2 p))
  end.
Proof.
  (* Our goal is to prove that after every call to handleInterval, the total
     scope of the remaining unhandled intervals is less than it was before,
     narrowing down to zero. *)
  intros.
  unfold unhandledExtent.
  unfold intervalExtent.
  unfold intervalStart, intervalEnd.
  induction st.
  induction unhandled0; simpl in *.
    inversion teq.
  unfold IntervalId0 in *.
  unfold all_state_lists0 in *.
  destruct p. simpl.
  specialize (IHunhandled0 (NoDup_uncons _ _ _ lists_are_unique0)).
  destruct x. inversion teq.
  unfold IntervalId1 in *.
  destruct a; simpl in *.
    destruct nextInterval1; inversion H0; simpl in *; subst.
  (* apply IHunhandled0. *)
Admitted.

(****************************************************************************)

(** * Program graphs *)

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {}.

Definition determineIntervals (g : Graph VirtReg) : ScanState.
Admitted.

Definition allocateRegisters (g : Graph VirtReg) : ScanState :=
  linearScan (determineIntervals g).

End Allocator.
