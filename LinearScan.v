(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf *)

Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSets.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Recdef.

Generalizable All Variables.

(****************************************************************************)

(** * Library *)

(** The following are extensions to the Coq standard library. *)

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

Definition no_overlap {a} (xs ys : list a) :=
  forall (x : a), ~ (In x xs) \/ ~ (In x ys).

Definition fin := Coq.Vectors.Fin.t.

Definition fin_eq_dec {n} (x y : fin n) : { x = y } + { x <> y }.
Proof.
  induction x; dependent destruction y.
  - left. reflexivity.
  - right. unfold not. intros.
    inversion H.
  - right. unfold not. intros.
    inversion H.
  - destruct (IHx y).
      left. congruence.
    right. intuition.
    apply n0. apply FS_inj.
    assumption.
Defined.

Definition from_nat (n : nat) {m} (H : n < m) : fin m := @of_nat_lt n m H.

Definition ultimate_Sn (n : nat) : fin (S n).
Proof.
  induction n.
    apply F1.
  apply FS. apply IHn.
Defined.

(** Return the last possible inhabitant of a [fin n]. *)
Definition ultimate_from_nat (n : nat) (H : n > 0) : fin n.
Proof.
  induction n. omega.
  apply ultimate_Sn.
Qed.

Definition fin_to_nat {n} (f : fin n) : nat := proj1_sig (to_nat f).

Definition pred_fin {n} (f : fin n) : option (fin n).
  apply to_nat in f.
  destruct f.
  destruct x.
    apply None.
  apply Some.
  apply Le.le_Sn_le in l.
  apply (from_nat x l).
Defined.

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

Lemma pred_fin_lt : forall n x y,
  @pred_fin n x = Some y -> proj1_sig (to_nat y) < proj1_sig (to_nat x).
Proof.
  intro n.
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

Lemma pred_fin_spec : forall n m (H : S n < m),
  pred_fin (@from_nat (S n) m H) = Some (@from_nat n m (Le.le_Sn_le _ _ H)).
Proof.
  intros. unfold pred_fin.
  rewrite fin_to_from_id.
    reflexivity.
  omega.
Qed.

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

  range_properly_bounded : rstart < rend;

  rangeExtent := rend - rstart
}.

(** Two ranges are equal if they start at the same location and cover the same
    extent.  Otherwise, we compare first the start position, and then the
    length of the extent. *)
Definition Rcompare (x y : Range) : comparison :=
  match x with
  | {| rstart := rstart0; rend := rend0 |} =>
      match y with
      | {| rstart := rstart1; rend := rend1 |} =>
          let s := Compare_dec.lt_eq_lt_dec rstart0 rstart1 in
          match s with
          | inleft (left _)  => Lt
          | inright _        => Gt
          | inleft (right _) =>
              let u := Compare_dec.lt_eq_lt_dec rend0 rend1 in
              match u with
              | inleft (left _)  => Lt
              | inleft (right _) => Eq
              | inright _        => Gt
              end
          end
      end
  end.

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
    | omega | inversion H; reflexivity | auto
    ]).

Lemma Rcompare_eq_iff : forall x y : Range, Rcompare x y = Eq <-> x = y.
Proof.
  split; generalize dependent y;
  induction x; intros;
  inversion H; destruct y.
  - reduce_comparisons H1.
    subst. f_equal. apply proof_irrelevance.
  - simpl. reduce_comparisons H0.
Qed.

Definition Rcompare_lt (x y : Range) := (Rcompare x y) = Lt.
Definition Rcompare_gt (x y : Range) := (Rcompare x y) = Gt.

Lemma Rcompare_gt_flip : forall x y : Range,
  Rcompare_gt x y -> Rcompare_lt y x.
Proof.
  intros.
  unfold Rcompare_lt.
  unfold Rcompare_gt in H.
  unfold Rcompare in *.
  reduce_comparisons H.
Qed.

Lemma Rcompare_spec : forall x y, CompSpec eq Rcompare_lt x y (Rcompare x y).
Proof.
  intros.
  destruct (Rcompare x y) eqn:Heqe.
  - apply CompEq.
    apply Rcompare_eq_iff in Heqe.
    assumption.
  - apply CompLt.
    unfold Rcompare_lt. assumption.
  - apply CompGt.
    apply Rcompare_gt_flip in Heqe.
    assumption.
Qed.

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

Definition extentOfRanges `(rs : NonEmpty Range) : nat :=
  rend (NE_tl rs) - rstart (NE_hd rs).

(** * RangeList *)

(** A [RangeList] encodes both the total extent of the list of ranges (the
    total span of instructions covered by all the ranges), and also the fact
    that ranges must be ordered and disjoint (non-overlapping). *)

Inductive RangeList : nat -> NonEmpty Range -> Set :=
  | RangeSing r : RangeList (rangeExtent r) (NE_Sing r)
  | RangeCons r s n rs :
    RangeList n (NE_Cons s rs) -> rend r <= rstart s
      -> RangeList (n + (rstart s - rstart r)) (NE_Cons r rs).

Definition rangeListStart `(rs : RangeList n xs) : nat :=
  match rs with
  | RangeSing r => rstart r
  | RangeCons r _ _ _ _ _ => rstart r
  end.

Definition rangeListEnd `(rs : RangeList n xs) : nat :=
  match rs with
  | RangeSing r => rend r
  | RangeCons r _ _ _ _ _ => rstart r + n
  end.

Definition rangeListExtent `(rs : RangeList n xs) : nat := n.

(** * UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos `(RangeList extent ranges) : Set := {
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

  lifetimes    : RangeList (extentOfRanges ranges) ranges;
  usePositions : NonEmpty (UsePos lifetimes)
}.

Definition intervalStart  (i : Interval) : nat := rangeListStart (lifetimes i).
Definition intervalEnd    (i : Interval) : nat := rangeListEnd (lifetimes i).
Definition intervalExtent (i : Interval) : nat := rangeListExtent (lifetimes i).

Definition Icompare (x y : Interval) : comparison :=
  Rcompare (NE_hd (ranges x)) (NE_hd (ranges y)).

Infix "?=" := Icompare (at level 70, no associativity).

Lemma Icompare_eq_iff : forall x y : Interval, x ?= y = Eq <-> x = y.
Proof.
  intros x.
  induction x. destruct y.
  rewrite ?IHn; split; auto.
Admitted.

Definition Ilt (x y : Interval) := (x ?= y) = Lt.
Definition Igt (x y : Interval) := (x ?= y) = Gt.
Definition Ile (x y : Interval) := (x ?= y) <> Gt.
Definition Ige (x y : Interval) := (x ?= y) <> Lt.
Definition Ine (x y : Interval) :=  x <> y.

Lemma Igt_flip : forall x y : Interval, Igt x y -> Ilt y x.
Proof.
Admitted.

Lemma Ilt_not : forall x y : Interval, Ilt x y -> Ine x y.
Proof.
Admitted.

Lemma Igt_not : forall x y : Interval, Igt x y -> Ine x y.
Proof.
Admitted.

Lemma Icompare_spec : forall x y, CompSpec eq Ilt x y (x ?= y).
Proof.
  intros.
  destruct (Icompare x y) eqn:Heqe.
  - apply Icompare_eq_iff in Heqe.
    apply CompEq. assumption.
  - apply CompLt. assumption.
  - apply CompGt.
    apply Igt_flip in Heqe.
    assumption.
Qed.

Definition I_eq_dec (x y : Interval) : { x = y } + { x <> y }.
Proof.
  destruct (Icompare x y) eqn:Heqe.
  - left.  apply Icompare_eq_iff in Heqe. assumption.
  - right. apply Ilt_not in Heqe. assumption.
  - right. apply Igt_not in Heqe. assumption.
Defined.

Module Interval_as_OT <: OrderedType.

  Definition t := Interval.
  Definition compare := Icompare.

  Definition eq := @eq Interval.
  Definition lt := Ilt.

  Instance eq_equiv : Equivalence eq.
  Admitted.

  Instance lt_strorder : StrictOrder lt.
  Admitted.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof. intros x x' Hx y y' Hy; rewrite Hx, Hy; split; auto. Qed.
  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof. exact Icompare_spec. Qed.

  Definition eq_dec : forall x y, { eq x y } + { ~eq x y }.
  Proof. exact I_eq_dec. Qed.

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

Definition AI_eq_dec (x y : AssignedInterval)
  : { x = y } + { x <> y }.
Proof.
Admitted.

Definition intervalRange (i : AssignedInterval) : Range.
  apply Build_Range
    with (rstart := intervalStart (interval i))
         (rend   := intervalEnd (interval i));
  destruct i.
  unfold intervalStart, intervalEnd.
  destruct interval0.
  dependent induction lifetimes0.
    apply range_properly_bounded.
  simpl in *.
  apply range_properly_bounded.
  apply IHlifetimes0.
  destruct r. destruct s.
  unfold extentOfRanges in *. simpl in *.
  destruct rs; simpl in *.
  unfold rangeListStart, rangeListEnd.
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
         (active    := remove AI_eq_dec x (active st))
         (inactive  := inactive st)
         (handled   := x :: handled st).
Admitted.

Definition moveActiveToInactive (st : ScanState) (x : AssignedInterval)
  : ScanState.
  apply Build_ScanState
    with (unhandled := unhandled st)
         (active    := remove AI_eq_dec x (active st))
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
         if fin_eq_dec (assigned x) r then Some (k x) else f r) z is.

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
    | Build_Range s e Hp Hb =>
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
