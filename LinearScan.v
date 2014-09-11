(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSets.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Recdef.
Require Import Setoid.

Close Scope nat_scope.

Generalizable All Variables.

Section Interval.

Variable a : Set.

Record Range : Set := {
  rstart : nat;
  rend   : nat;

  range_positive : (rstart >= 0)%nat;
  range_properly_bounded : (rstart < rend)%nat;

  (** The extent of a [Range] is simply the set of locations it ranges over.
      By summing the extent of a list of ranges, we have an idea of how much
      ground is left to cover, and this gives us a notion of well-founded
      recursion for iterating over intervals that may split as we examine them
      -- i.e., whose total extent must decrease after each pass. *)
  rangeExtent := (rend - rstart)%nat
}.

Definition in_range (loc : nat) (r : Range) : Prop :=
  (rstart r <= loc)%nat /\ (loc < rend r)%nat.

(** A [RangeList] encodes both the total extent of the list of ranges (the
    total span of instructions covered by all th eranges), and also the fact
    that ranges must be ordered and disjoint (non-overlapping). *)

Inductive RangeList : nat -> list Range -> Set :=
  | RangeSing r : RangeList (rangeExtent r) (r :: nil)
  | RangeCons r s n rs :
    RangeList n (s :: rs) -> (rend r <= rstart s)%nat
      -> RangeList (n + (rstart s - rstart r))%nat (cons r rs).

Record UsePos `(RangeList extent ranges) : Set := {
  uloc   : nat;
  regReq : bool;

  uloc_positive : (uloc >= 0)%nat;
  within_range  : Exists (in_range uloc) ranges
}.

Record UsePosList `(rs : RangeList extent ranges) : Set := {
  positions : list (UsePos rs);

  has_use_positions : (length positions > 0)%nat
}.

Inductive VirtReg : Set := VR : nat -> VirtReg.
Inductive PhysReg : Set := PR : nat -> PhysReg.

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
  ranges       : list Range;
  intExtent    : nat;
  lifetimes    : RangeList intExtent ranges; (* list of disjoint ranges *)
  usePositions : UsePosList lifetimes;       (* list of use positions *)
  assigned     : option PhysReg              (* assigned register *)
}.

Definition Icompare (x y : Interval) := Eq.

Infix "?=" := Icompare (at level 70, no associativity).

Definition Ilt (x y : Interval) := (x ?= y) = Lt.
Definition Igt (x y : Interval) := (x ?= y) = Gt.
Definition Ile (x y : Interval) := (x ?= y) <> Gt.
Definition Ige (x y : Interval) := (x ?= y) <> Lt.
Definition Ine (x y : Interval) :=  x <> y.

Lemma Icompare_spec : forall n m, CompSpec eq Ilt n m (n ?= m).
Proof.
  intros.
Admitted.

Definition I_eq_dec (x y : Interval) : { x = y } + { x <> y }.
Proof.
Admitted.

End Interval.

Definition rangeListStart `(rs : RangeList n xs) : nat :=
  match rs with
  | RangeSing r => rstart r
  | RangeCons r _ _ _ _ _ => rstart r
  end.

Definition rangeListEnd `(rs : RangeList n xs) : nat :=
  match rs with
  | RangeSing r => rend r
  | RangeCons r _ _ _ _ _ => (rstart r + n)%nat
  end.

Definition rangeListExtent `(rs : RangeList n xs) : nat := n.

Definition intervalStart (i : Interval) : nat :=
  rangeListStart (lifetimes i).

Definition intervalEnd (i : Interval) : nat :=
  rangeListEnd (lifetimes i).

Definition intervalExtent (i : Interval) : nat :=
  rangeListExtent (lifetimes i).

Definition intervalRange (i : Interval) : Range.
  apply Build_Range
    with (rstart := intervalStart i)
         (rend   := intervalEnd i);
  destruct i.
  - omega.
  - unfold intervalStart, intervalEnd.
    induction lifetimes0.
      apply range_properly_bounded.
    destruct r. destruct s.
    simpl in *. omega.
Qed.

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

Module Import M := MSetAVL.Make(Interval_as_OT).
Module Import N := WPropertiesOn E M.

Definition intSet : Type := t.  (* the type of a set of intervals *)

Definition no_overlap (xs ys : intSet) := forall (x : Interval),
  ~ (In x xs) \/ ~ (In x ys).

Definition intSetExtent (is : intSet) : nat :=
  fold (fun x n => (n + intExtent x)%nat) is 0%nat.

(* Definition no_overlap (xs ys : intSet) : bool := *)
(*   fold (fun x ret => andb ret (negb (mem x ys))) xs true. *)

(* The ScanState is always relative to the current position (pos). *)
Record ScanState := {
    unhandled : intSet;         (* starts after pos *)
    active    : intSet;         (* ranges over pos, assigned to a register *)
    inactive  : intSet;         (* pos falls within a lifetime hole *)
    handled   : intSet;         (* ends before pos *)

    no_overlap_in_unhandled : no_overlap unhandled active;
    no_overlap_in_actives   : no_overlap active inactive;
    no_overlap_in_handled   : no_overlap active handled
}.

Program Definition newScanState (intervals : intSet) : ScanState :=
  {| unhandled := intervals
   ; active    := empty
   ; inactive  := empty
   ; handled   := empty
   |}.
Solve All Obligations using
  (unfold no_overlap; intros;
   right; unfold not; apply FM.empty_iff).

Lemma remove_over_not : forall x e xs, ~ In x xs -> ~ In x (remove e xs).
Proof.
  intros. unfold not in *. intros.
  apply H. apply remove_spec in H0.
  inversion H0. assumption.
Qed.

Definition nextUnhandled (st : ScanState) : option (Interval * ScanState).
  pose (min_elt (unhandled st)).
  destruct o.
  - constructor.
    split.
      apply e.
    destruct st.
    apply Build_ScanState
      with (unhandled := remove e unhandled0)
           (active    := active0)
           (inactive  := inactive0)
           (handled   := handled0).
    + unfold no_overlap. intros.
      specialize (no_overlap_in_unhandled0 x).
      destruct no_overlap_in_unhandled0.
        left. apply remove_over_not. assumption.
      right. assumption.
    + apply no_overlap_in_actives0.
    + apply no_overlap_in_handled0.
  - apply None.
Defined.

Definition moveFromActiveToHandled (x : Interval) (st : ScanState) : ScanState.
  apply Build_ScanState
    with (unhandled := unhandled st)
         (active    := remove x (active st))
         (inactive  := inactive st)
         (handled   := add x (handled st)).
Admitted.

Definition moveFromActiveToInactive (x : Interval) (st : ScanState) : ScanState.
  apply Build_ScanState
    with (unhandled := unhandled st)
         (active    := remove x (active st))
         (inactive  := add x (inactive st))
         (handled   := handled st).
Admitted.

Definition addToActive (x : Interval) (st : ScanState) : ScanState.
  apply Build_ScanState
    with (unhandled := unhandled st)
         (active    := add x (active st))
         (inactive  := inactive st)
         (handled   := handled st).
Admitted.

Definition ScanStateUnhandledExtent (st : ScanState) : nat :=
  intSetExtent (unhandled st).

(* Lemma NonEmptyScanStateScope : forall st unh x, *)
(*   unh = unhandled st -> In x unh -> *)
(*     (~ (Empty unh)) /\ (ScanStateUnhandledScope st > 0)%nat. *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)

(* TRY_ALLOCATE_FREE_REG

   set freeUntilPos of all physical registers to maxInt

   for each interval it in active do
     freeUntilPos[it.reg] = 0

   for each interval it in inactive intersecting with current do
     freeUntilPos[it.reg] = next intersection of it with current

   reg = register with highest freeUntilPos
   if freeUntilPos[reg] = 0 then
     // no register available without spilling
     allocation failed
   else if current ends before freeUntilPos[reg] then
     // register available for the whole interval
     current.reg = reg
   else
     // register available for the first part of the interval
     current.reg = reg
     split current before freeUntilPos[reg]
*)

Definition tryAllocateFreeReg (current : Interval) (st : ScanState)
  : option (Interval * ScanState).
Admitted.

(* ALLOCATE_BLOCKED_REG

   set nextUsePos of all physical registers to maxInt

   for each interval it in active do
     nextUsePos[it.reg] = next use of it after start of current
   for each interval it in inactive intersecting with current do
     nextUsePos[it.reg] = next use of it after start of current

   reg = register with highest nextUsePos
   if first usage of current is after nextUsePos[reg] then
     // all other intervals are used before current, so it is best
     // to spill current itself
     assign spill slot to current
     split current before its first use position that requires a register
   else
     // spill intervals that currently block reg
     current.reg = reg
     split active interval for reg at position
     split any inactive interval for reg at the end of its lifetime hole

   // make sure that current does not intersect with
   // the fixed interval for reg
   if current intersects with the fixed interval for reg then
     splse current before this intersection
*)

Definition allocateBlockedReg (current : Interval) (st : ScanState)
  : (Interval * ScanState).
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
      if (e <? position)%nat
      then moveFromActiveToHandled x st
      else if (position <? s)%nat
           then moveFromActiveToInactive x st
           else st
    end in
  let st1 := fold go1 (active st0) st0 in

  (* // check for intervals in inactive that are handled or active
     for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let go2 x st := st in
  let st2 := fold go2 (inactive st1) st1 in

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg *)
  let (current', st3) :=
      match tryAllocateFreeReg current st2 with
      | None => allocateBlockedReg current st2
      | Some res => res
      end in

  (* if current has a register assigned then
       add current to active *)
  if assigned current'
  then addToActive current' st3
  else st3.

(* LINEAR_SCAN

   unhandled = list of intervals sorted by increasing start positions
   active = { }; inactive = { }; handled = { }

   while unhandled /= { } do
     current = pick and remove first interval from unhandled
     HANDLE_INTERVAL (current)
*)
Function linearScan (st : ScanState)
    {measure ScanStateUnhandledExtent st} : ScanState :=
  match nextUnhandled st with
  | None => st
  | Some (current, st') => linearScan (handleInterval current st')
  end.
Proof.
  intros.
  unfold ScanStateUnhandledExtent.
  unfold intSetExtent.
  unfold nextUnhandled in teq.
  revert teq.
  unfold handleInterval.
  pattern (unhandled st).
  apply set_induction; intros.
    destruct (min_elt s) eqn:Heqe.
      apply min_elt_spec1 in Heqe.
      specialize (H e).
      contradiction.
    inversion teq.
  clear teq.
  subst. clear H.

(*
Proof.
  intros st current.
  remember (unhandled st) as unh.
  intros teq.
  (* Our goal is to prove that after every call to handleInterval, the total
     scope of the remaining unhandled intervals is less than it was before,
     narrowing down to zero. *)
  pose proof teq as H.
  apply min_elt_spec1 in H.
  pose proof H as H0.
  apply (NonEmptyScanStateScope st) in H0.
  - destruct H0 as [H1 H2].
    unfold ScanStateUnhandledScope in *.
    rewrite <- Hequnh.
    rewrite <- Hequnh in H2.
    unfold intSetScope in *.
    unfold gt in H2.
    revert Hequnh.
    revert teq.
    revert H.
    revert H1.
    revert H2.
    pattern unh.
    apply set_induction; intros.
    + contradiction.
    + (* At this point, we know that the list of unhandled intervals is not
         Empty, and we must show that the result of calling handleInterval
         reduces the total scope length. *)
      rewrite Hequnh. clear Hequnh.
      destruct st.
      subst. simpl in *.
      
  - assumption.
(*
    pattern unh'.
    apply set_induction; intros.
    + rewrite fold_1b. apply H3.
      assumption.

    + 
      remember (fold (fun (x0 : elt) (n : nat) =>
                        (n + intervalScope x0)%nat)) as f.
*)
Admitted.
*)

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