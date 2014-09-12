(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf *)

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSets.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.ProofIrrelevance.
(* Require Import FunctionalExtensionality. *)
Require Import Recdef.

Generalizable All Variables.

(****************************************************************************)

(** * Library *)

(** The following are extensions to the Coq standard library. *)

Definition no_overlap {a} (xs ys : list a) :=
  forall (x : a), ~ (In x xs) \/ ~ (In x ys).

(** * Generalized comparisons *)

(** These definitions avoid boilerplate involved with setting up properly
    behaved comparisons between types. *)

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
Qed.

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
Qed.

Class CompareSpec (a : Set) := {
  cmp         : a -> a -> comparison;
  cmp_eq_iff  : forall x y, cmp x y = Eq <-> x = y;
  cmp_lt x y  := cmp x y = Lt;
  cmp_gt x y  := cmp x y = Gt;
  cmp_gt_flip : forall x y, cmp_gt x y -> cmp_lt y x;

  cmp_spec x y : CompSpec eq cmp_lt x y (cmp x y) :=
    mk_compare_spec x y cmp (cmp_eq_iff x y) (cmp_gt_flip x y);

  cmp_eq_dec x y : { x = y } + { x <> y } :=
    mk_cmp_eq_dec x y cmp (cmp_eq_iff x y)
}.

Ltac reduce_comparisons H :=
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

    | omega | inversion H; reflexivity | subst; auto
    ]).

(** * NonEmpty lists *)

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

(** * Finite sets *)

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

(** ** Comparison of values of the same finite set type. *)

(** [fin] values may be compared.  It is simply a comparison of their
    underlying naturals, owing to proof irrelevance. *)
Definition fin_compare {n} (x y : fin n) : comparison :=
  nat_compare (fin_to_nat x) (fin_to_nat y).

(** A comparison between [fin] of [Eq] is equivalent to equality. *)
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

(** * Range *)

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
  reduce_comparisons Heqe;
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

(** * RangeList *)

(** A [RangeList] encodes both the total extent of the list of ranges (the
    total span of instructions covered by all the ranges), and also the fact
    that ranges must be ordered and disjoint (non-overlapping). *)

Inductive RangeList : NonEmpty Range -> Set :=
  | RangeSing r : RangeList (NE_Sing r)
  | RangeCons r rs :
    RangeList rs -> rend r <= rstart (NE_hd rs) -> RangeList (NE_Cons r rs).

Definition rangeListStart  `(RangeList xs) := rstart (NE_hd xs).
Definition rangeListEnd    `(RangeList xs) := rend (NE_tl xs).

Definition rangeListExtent `(rs : RangeList xs) :=
  rangeListEnd rs - rangeListStart rs.

(** * UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos `(RangeList ranges) : Set := {
  uloc   : nat;
  regReq : bool;

  within_range : Exists (in_range uloc) (NE_to_list ranges)
}.

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

Record Interval : Set := {
  ranges       : NonEmpty Range;

  (** The [intExtent] is a cached property.  It can be derived from [ranges],
      but since we refer to it often it is easier to maintain it as we
      generate new intervals. *)
  (* intExtent :=  *)

  lifetimes    : RangeList ranges;
  usePositions : NonEmpty (UsePos lifetimes)
}.

Definition intervalStart  i := rangeListStart  (lifetimes i).
Definition intervalEnd    i := rangeListEnd    (lifetimes i).
Definition intervalExtent i := rangeListExtent (lifetimes i).

Definition Icompare (x y : Interval) : comparison :=
  Rcompare (NE_hd (ranges x)) (NE_hd (ranges y)).

Infix "?=" := Icompare (at level 70, no associativity).

Lemma Icompare_eq_iff : forall x y : Interval, x ?= y = Eq <-> x = y.
Proof.
  intros x.
  induction x. destruct y.
  rewrite ?IHn; split; auto.
Admitted.

Lemma Icompare_gt_flip : forall x y : Interval, x ?= y = Gt -> y ?= x = Lt.
Proof.
Admitted.

Program Instance Interval_CompareSpec : CompareSpec Interval := {
  cmp         := Icompare;
  cmp_eq_iff  := Icompare_eq_iff;
  cmp_gt_flip := Icompare_gt_flip
}.

Module Interval_as_OT <: OrderedType.

  Definition t := Interval.
  Definition compare := Icompare.

  Definition eq := @eq Interval.
  Definition lt := fun x y => x ?= y = Lt.

  Instance eq_equiv : Equivalence eq := eq_equivalence.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - intro x. destruct x.
      unfold complement. intros.
      inversion H.
  Admitted.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof. intros x x' Hx y y' Hy; rewrite Hx, Hy; split; auto. Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof. exact cmp_spec. Qed.

  Definition eq_dec : forall x y, { eq x y } + { ~eq x y }.
  Proof. exact cmp_eq_dec. Qed.

End Interval_as_OT.

Module S := MSetAVL.Make(Interval_as_OT).
Module Import N := WPropertiesOn S.E S.

Lemma elements_spec3 : forall s x, In x (S.elements s) <-> S.In x s.
Proof.
  split; intros.
  - apply S.elements_spec1.
    apply InA_alt.
    exists x.
    split. reflexivity.
    assumption.
  - apply S.elements_spec1 in H.
    apply InA_alt in H.
    destruct H.
    inversion H.
    rewrite H0.
    assumption.
Qed.

Lemma remove_over_not : forall x e s, ~ S.In x s -> ~ S.In x (S.remove e s).
Proof.
  intros. unfold not in *. intros.
  apply H. apply S.remove_spec in H0.
  inversion H0. assumption.
Qed.

Definition intSet : Type := S.t.  (* the type of a set of intervals *)

Definition intSetExtent (is : intSet) : nat :=
  S.fold (fun x n => n + intervalExtent x) is 0.

(****************************************************************************)

Section Allocator.

Variable maxReg : nat.          (* max number of registers *)

Hypothesis registers_exist : maxReg > 0.

Definition VirtReg := nat.
Definition PhysReg := fin maxReg.

(** * AssignedInterval *)

(** [AssignedInterval] values are just a tuple of an interval and an assigned
    physical register.  Once assigned, assignments are never changed. *)

Record AssignedInterval : Set := {
  interval : Interval;
  assigned : PhysReg            (* assigned register *)
}.

Definition AIcompare (x y : AssignedInterval) : comparison.
Admitted.

Lemma AIcompare_eq_iff : forall x y : AssignedInterval,
  AIcompare x y = Eq <-> x = y.
Proof.
Admitted.

Lemma AIcompare_gt_flip : forall x y : AssignedInterval,
  AIcompare x y = Gt -> AIcompare y x = Lt.
Proof.
Admitted.

Program Instance AssignedInterval_CompareSpec
  : CompareSpec AssignedInterval := {
  cmp         := AIcompare;
  cmp_eq_iff  := AIcompare_eq_iff;
  cmp_gt_flip := AIcompare_gt_flip
}.

Definition intervalRange (i : AssignedInterval) : Range.
  apply Build_Range
    with (rstart := intervalStart (interval i))
         (rend   := intervalEnd (interval i)).
  unfold intervalStart, intervalEnd.
  induction (lifetimes (interval i)).
    apply range_properly_bounded.
  destruct r0;
  unfold rangeListStart, rangeListEnd in *;
  destruct r; destruct r0; simpl in *; omega.
Qed.

(** * ScanState *)

(** A [ScanState] is always relative to a current position (pos) as we move
    through the sequentialized instruction stream over which registers are
    allocated.. *)

Record ScanState := {
    unhandled : intSet;                 (* starts after pos *)
    active    : list AssignedInterval;  (* ranges over pos *)
    inactive  : list AssignedInterval;  (* falls in lifetime hole *)
    handled   : list AssignedInterval;  (* ends before pos *)

    intervals := map interval;

    no_overlap_in_unhandled :
      no_overlap (S.elements unhandled) (intervals active);
    no_overlap_in_actives :
      no_overlap (intervals active) (intervals inactive);
    no_overlap_in_handled :
      no_overlap (intervals active) (intervals handled)
}.

Program Definition newScanState (intervals : intSet)
  : ScanState := {| unhandled := intervals
                  ; active    := nil
                  ; inactive  := nil
                  ; handled   := nil
                  |}.
Solve All Obligations using
  (unfold no_overlap; intros; right; unfold not; intros; inversion H).

Definition scanStateUnhandledExtent (st : ScanState) : nat :=
  intSetExtent (unhandled st).

Definition nextUnhandled (st : ScanState) : option (Interval * ScanState).
Proof.
  pose (S.min_elt (unhandled st)).
  destruct o.
  - constructor.
    split.
      apply e.
    destruct st.
    apply Build_ScanState
      with (unhandled := S.remove e unhandled0)
           (active    := active0)
           (inactive  := inactive0)
           (handled   := handled0).
    + unfold no_overlap. intros.
      specialize (no_overlap_in_unhandled0 x).
      destruct no_overlap_in_unhandled0.
        left. rewrite elements_spec3.
        rewrite elements_spec3 in H.
        apply remove_over_not. assumption.
      right. assumption.
    + apply no_overlap_in_actives0.
    + apply no_overlap_in_handled0.
  - apply None.
Defined.

Definition moveActiveToHandled (st : ScanState) (x : AssignedInterval)
  : ScanState.
  apply Build_ScanState
    with (unhandled := unhandled st)
         (active    := remove cmp_eq_dec x (active st))
         (inactive  := inactive st)
         (handled   := x :: handled st).
Admitted.

Definition moveActiveToInactive (st : ScanState) (x : AssignedInterval)
  : ScanState.
  apply Build_ScanState
    with (unhandled := unhandled st)
         (active    := remove cmp_eq_dec x (active st))
         (inactive  := x :: inactive st)
         (handled   := handled st).
Admitted.

Definition addToActive (st : ScanState) (x : AssignedInterval) : ScanState.
  apply Build_ScanState
    with (unhandled := unhandled st)
         (active    := x :: active st)
         (inactive  := inactive st)
         (handled   := handled st).
Admitted.

Definition getRegisterIndex
  (k : AssignedInterval -> nat) (z : PhysReg -> option nat)
  (is : list AssignedInterval) : PhysReg -> option nat :=
  fold_right
    (fun x f => fun r =>
         if cmp_eq_dec (assigned x) r then Some (k x) else f r) z is.

Definition nextIntersectionWith (i : Interval) (x : AssignedInterval) : nat.
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

Definition tryAllocateFreeReg (st : ScanState) (current : Interval)
  : option (AssignedInterval * ScanState) :=
  (* jww: The first part of this algorithm has been modified to be functional:
     instead of mutating an array called freeUntilPos and then selecting the
     register with the highest value, we determine the register using a
     fold. *)

  (* set freeUntilPos of all physical registers to maxInt

     for each interval it in active do
       freeUntilPos[it.reg] = 0 *)
  let freeUntilPos' :=
        getRegisterIndex (fun _ => 0) (fun r => None) (active st) in

  (* for each interval it in inactive intersecting with current do
       freeUntilPos[it.reg] = next intersection of it with current *)
  let intersectingIntervals :=
        filter (fun x =>
                  anyRangeIntersects (ranges current) (ranges (interval x)))
               (inactive st) in
  let freeUntilPos :=
        getRegisterIndex (nextIntersectionWith current)
                         freeUntilPos' intersectingIntervals in

  (* reg = register with highest freeUntilPos
     if freeUntilPos[reg] = 0 then
       // no register available without spilling
       allocation failed
     else if current ends before freeUntilPos[reg] then
       // register available for the whole interval
       current.reg = reg
     else
       // register available for the first part of the interval
       current.reg = reg
       split current before freeUntilPos[reg] *)
  let lastReg := ultimate_from_nat maxReg registers_exist in
  let reg := findRegister freeUntilPos lastReg in

  (* jww (2014-09-11): NYI *)
  None.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  This is why the
    type differs from [tryAllocateFreeReg], since in ever case the final state
    will be changed. *)

Definition allocateBlockedReg (st : ScanState) (current : Interval)
  : (option AssignedInterval * ScanState).
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
  let go2 x st := st in
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
  | Some current' => addToActive st3 current'
  end.

Function linearScan (st : ScanState)
    {measure scanStateUnhandledExtent st} : ScanState :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match nextUnhandled st with
  | None => st
  | Some (current, st') => linearScan (handleInterval current st')
  end.
Proof.
  (* Our goal is to prove that after every call to handleInterval, the total
     scope of the remaining unhandled intervals is less than it was before,
     narrowing down to zero. *)
  intros.
  unfold scanStateUnhandledExtent.
  unfold intSetExtent.
  unfold nextUnhandled in teq.
  revert teq.
  unfold handleInterval.
  pattern (unhandled st).
  apply set_induction; intros.
    destruct (S.min_elt s) eqn:Heqe.
      apply S.min_elt_spec1 in Heqe.
      specialize (H e).
      contradiction.
    inversion teq.
  (* At this point, we know that the list of unhandled intervals is not Empty,
     and we must show that the result of calling handleInterval reduces the
     total scope length. *)
  destruct p. subst.
  inversion teq0; subst.
Admitted.

End Allocator.

(****************************************************************************)

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {}.

Definition determineIntervals (g : Graph VirtReg) : intSet.
Admitted.

(*
Definition allocateRegisters (g : Graph VirtReg) : intSet :=
  let st := newScanState (determineIntervals g) in
  handled (linearScan st).
*)
