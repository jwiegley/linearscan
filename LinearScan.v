Require Import Coq.MSets.MSets.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Recdef.

Close Scope nat_scope.

(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)

Section Interval.

Variable a : Set.

Record Range : Set := {
  rstart : nat;
  rend   : nat;

  range_positive : (rstart >= 0)%nat;
  range_properly_bounded : (rstart < rend)%nat
}.

(** The scope of a [Range] is simply the number of locations that it ranges
    over.  By summing the scope of a list of ranges, we have an idea of how
    much ground is left to cover, and thus gives us a notion of well-founded
    recursion for iterating over a list of ranges that may be splitting as we
    examine them -- whose total scope must decrease after each pass. *)

Definition rangeScope (r : Range) : nat :=
  (rend r - rstart r)%nat.

Record UsePos : Set := {
  uloc   : nat;
  regReq : bool;

  uloc_positive : (uloc >= 0)%nat
}.

Inductive VirtReg : Set :=
  | VR : nat -> VirtReg.

Inductive PhysReg : Set :=
  | PR : nat -> PhysReg.

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

Fixpoint lifetimes_ordered_and_disjoint (lf : list Range) : bool :=
  match lf with
  | nil => true
  | cons x xs =>
    match xs with
    | nil => true
    | cons y ys =>
      if (rend x <? rstart y)%nat
      then lifetimes_ordered_and_disjoint xs
      else false
    end
  end.

Fixpoint check_all_lifetimes (u : UsePos) (lf : list Range) : bool :=
  match lf with
  | nil => false
  | cons l ls =>
    if andb (rstart l <=? uloc u)%nat (uloc u <? rend l)%nat
    then true
    else check_all_lifetimes u ls
  end.

Fixpoint positions_in_lifetimes (up : list UsePos) (lf : list Range) : bool :=
  match up with
  | nil => true
  | cons u us =>
    if check_all_lifetimes u lf
    then positions_in_lifetimes us lf
    else false
  end.

(** If for some reason we cannot assign a single register for all ranges, then
    the interval is split into two or more intervals, so each interval can be
    assigned its own register. *)

Record Interval : Set := {
  lifetimes    : list Range;     (* list of disjoint ranges *)
  usePositions : list UsePos;    (* list of use positions *)
  assigned     : option PhysReg; (* assigned register *)

  has_lifetimes       : (length lifetimes > 0)%nat;
  lifetimes_disjoint  : Is_true (lifetimes_ordered_and_disjoint lifetimes);
  has_use_positions   : (length usePositions > 0)%nat;
  use_positions_valid : Is_true (positions_in_lifetimes usePositions lifetimes)
}.

Fixpoint scopeOfRanges (rs : list Range) : nat :=
  match rs with
    | nil => 0%nat
    | cons x xs => (rangeScope x + scopeOfRanges xs)%nat
  end.

Definition intervalScope (i : Interval) : nat := scopeOfRanges (lifetimes i).

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

Definition intervalStart (i : Interval) : nat :=
  rstart (safe_hd (lifetimes i) (has_lifetimes i)).
Definition intervalEnd (i : Interval) : nat :=
  rend (safe_last (lifetimes i) (has_lifetimes i)).

Definition intervalTotalRange (i : Interval) : Range.
  apply Build_Range
    with (rstart := intervalStart i)
         (rend   := intervalEnd i).
  - destruct i. omega.
  - destruct i.
    unfold intervalStart, intervalEnd.
    simpl. induction lifetimes0; simpl.
      rename has_lifetimes0 into H.
      simpl in H.
      unfold gt in H.
      unfold Peano.lt in H.
      inversion H.
    admit.
Admitted.

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

Module M := MSetAVL.Make(Interval_as_OT).
Import M.

Definition intSet : Type := t.  (* the type of a set of intervals *)

Definition no_overlap (xs ys : intSet) : bool :=
  fold (fun x ret => andb ret (negb (mem x ys))) xs true.

(* The ScanState is always relative to the current position (pos). *)
Record ScanState := {
    unhandled : intSet;         (* starts after pos *)
    active    : intSet;         (* ranges over pos, assigned to a register *)
    inactive  : intSet;         (* pos falls within a lifetime hole *)
    handled   : intSet;         (* ends before pos *)

    non_overlap_in_actives : Is_true (no_overlap active inactive);
    non_overlap_in_handled : Is_true (no_overlap active handled)
}.

Program Definition newScanState (intervals : intSet) : ScanState :=
  {| unhandled := intervals
   ; active    := empty
   ; inactive  := empty
   ; handled   := empty
   |}.

(*
Definition nextUnhandled (st : ScanState) : option (Interval * ScanState) :=
  match min_elt (unhandled st) with
  | None => None
  | Some i =>
    let st' := {| unhandled := remove i (unhandled st)
                ; active    := add i (active st)
                ; inactive  := inactive st
                ; handled   := handled st
                |} in
    Some (i, st')
  end.
*)

Definition moveFromActiveToHandled (x : Interval) (st : ScanState) : ScanState.
  apply Build_ScanState
    with (active   := remove x (active st))
         (inactive := inactive st)
         (handled  := add x (handled st)).
Admitted.

Definition moveFromActiveToInactive (x : Interval) (st : ScanState) : ScanState.
  apply Build_ScanState
    with (active   := remove x (active st))
         (inactive := add x (inactive st))
         (handled  := handled st).
Admitted.

Definition intSetScope (is : intSet) : nat :=
  fold (fun x n => (n + intervalScope x)%nat) is 0%nat.

Definition ScanStateUnhandledScope (st : ScanState) : nat :=
  intSetScope (unhandled st).

(* HANDLE_INTERVAL

   position = start position of current

   // check for intervals in active that are handled or inactive
   for each interval it in active do
     if it ends before position then
       move it from active to handled
     else if it does not cover position then
       move it from active to inactive

   // check for intervals in inactive that are handled or active
   for each interval it in inactive do
     if it ends before position then
       move it from inactive to handled
     else if it covers position then
       move it from inactive to active

   // find a register for current
   tryAllocateFreeReg
   if allocation failed then
     allocateBlockedReg

   if current has a register assigned then
     add current to active
*)
Definition handleInterval (current : Interval) (st0 : ScanState) : ScanState :=
  let position := intervalStart current in

  let go1 x st' :=
    match intervalTotalRange x with
    | Build_Range s e Hp Hb =>
      if (e <? position)%nat
      then moveFromActiveToHandled x st'
      else if (position <? s)%nat
           then moveFromActiveToInactive x st'
           else st'
    end in
  let st1 := fold go1 (active st0) st0 in

  let go2 x st' := st' in
  let st2 := fold go2 (inactive st1) st1 in

  (* jww (2014-09-10): Current may get split here, which means the fold in
     linearScan is not good enough. *)
  (* match tryAllocateFreeReg current st2 with *)
  (* | None => allocateBlockedReg *)
  (* | Some (current', st3) => *)
  st2.

(* LINEAR_SCAN

   unhandled = list of intervals sorted by increasing start positions
   active = { }; inactive = { }; handled = { }

   while unhandled /= { } do
     current = pick and remove first interval from unhandled
     HANDLE_INTERVAL (current)
*)
Function linearScan (st : ScanState)
    {measure ScanStateUnhandledScope st} : ScanState :=
  match min_elt (unhandled st) with
  | None => st
  | Some current => linearScan (handleInterval current st)
  end.
Proof.
  intros.
  unfold Peano.lt.
  destruct st.
Admitted.

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

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {}.

Definition determineIntervals (g : Graph VirtReg) : intSet.
Admitted.

Definition allocateRegisters (g : Graph VirtReg) : intSet :=
  let st := newScanState (determineIntervals g) in
  handled (linearScan st).
