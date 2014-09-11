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
Require Import Coq.Vectors.Fin.
Require Import Recdef.

Generalizable All Variables.

(****************************************************************************)

Section Interval.

Record Range : Set := {
  rstart : nat;
  rend   : nat;

  range_positive : rstart >= 0;
  range_properly_bounded : rstart < rend;

  (** The extent of a [Range] is simply the set of locations it ranges over.
      By summing the extent of a list of ranges, we have an idea of how much
      ground is left to cover, and this gives us a notion of well-founded
      recursion for iterating over intervals that may split as we examine them
      -- i.e., whose total extent must decrease after each pass. *)
  rangeExtent := rend - rstart
}.

(** A [RangeList] encodes both the total extent of the list of ranges (the
    total span of instructions covered by all th eranges), and also the fact
    that ranges must be ordered and disjoint (non-overlapping). *)

Inductive RangeList : nat -> list Range -> Set :=
  | RangeSing r : RangeList (rangeExtent r) (r :: nil)
  | RangeCons r s n rs :
    RangeList n (s :: rs) -> rend r <= rstart s
      -> RangeList (n + (rstart s - rstart r)) (cons r rs).

Definition in_range (loc : nat) (r : Range) : Prop :=
  rstart r <= loc /\ loc < rend r.

Definition rangesIntersect (i j : Range) : bool :=
  if rstart i <? rstart j
  then rstart j <? rend i
  else rstart i <? rend j.

Definition anyRangeIntersects (is js : list Range) : bool :=
  fold_right
    (fun r b => orb b (existsb (rangesIntersect r) js))
    false is.

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

Record UsePos `(RangeList extent ranges) : Set := {
  uloc   : nat;
  regReq : bool;

  uloc_positive : uloc >= 0;
  within_range  : Exists (in_range uloc) ranges
}.

Record UsePosList `(rs : RangeList extent ranges) : Set := {
  positions : list (UsePos rs);

  has_use_positions : length positions > 0
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
  ranges       : list Range;
  intExtent    : nat;
  lifetimes    : RangeList intExtent ranges; (* list of disjoint ranges *)
  usePositions : UsePosList lifetimes        (* list of use positions *)
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

Definition intervalStart  (i : Interval) : nat := rangeListStart (lifetimes i).
Definition intervalEnd    (i : Interval) : nat := rangeListEnd (lifetimes i).
Definition intervalExtent (i : Interval) : nat := rangeListExtent (lifetimes i).

Definition no_overlap (xs ys : list Interval) :=
  forall (x : Interval), ~ (In x xs) \/ ~ (In x ys).

Definition intSetExtent (is : intSet) : nat :=
  S.fold (fun x n => n + intExtent x) is 0.

(****************************************************************************)

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

Definition penultimate_Sn (n : nat) : fin (S n).
Proof.
  induction n.
    apply F1.
  apply FS. apply IHn.
Defined.

(** Return the last possible inhabitant of a [fin n]. *)
Definition penultimate_from_nat (n : nat) (H : n > 0) : fin n.
Proof.
  induction n. omega.
  apply penultimate_Sn.
Qed.

Definition fin_to_nat {n} (f : fin n) : nat := proj1_sig (to_nat f).

Definition pred_fin {n} (f : fin n) : option (fin n).
  apply to_nat in f.
  destruct f.
  destruct x.
    apply None.
  apply Some.
  assert (x < n). omega.
  apply (from_nat x H).
Defined.

Lemma pred_fin_lt : forall n x y,
  @pred_fin n x = Some y -> proj1_sig (to_nat y) < proj1_sig (to_nat x).
Proof.
  intros.
Admitted.

Definition _0_lt_20 : 0 < 20. omega. Qed.
Definition _9_lt_20 : 9 < 20. omega. Qed.
Definition _8_lt_20 : 8 < 20. omega. Qed.

Example pred_fin_ex1 :
  pred_fin (@from_nat 0 20 _0_lt_20) = None.
Proof.
  unfold pred_fin, from_nat. reflexivity.
Qed.

Example pred_fin_ex2 :
  pred_fin (@from_nat 9 20 _9_lt_20) = Some (@from_nat 8 20 _8_lt_20).
Proof.
  unfold pred_fin, from_nat. reflexivity.
Qed.

Example pred_fin_ex3 : forall n m (H : S n < m),
  pred_fin (@from_nat (S n) m H) = Some (@from_nat n m (Le.le_Sn_le _ _ H)).
Proof.
  intros.
  destruct (pred_fin (from_nat (S n) H)).
  f_equal. unfold from_nat.
Admitted.

(****************************************************************************)

Section Allocator.

Variable maxReg : nat.          (* max number of registers *)

Hypothesis registers_exist : maxReg > 0.

Definition VirtReg := nat.
Definition PhysReg := fin maxReg.

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
  - omega.
  - unfold intervalStart, intervalEnd.
    simpl. destruct interval0.
    induction lifetimes0.
      apply range_properly_bounded.
    destruct r. destruct s.
    simpl in *. omega.
Qed.

(* The ScanState is always relative to the current position (pos). *)
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

Function findRegister (freeUntilPos : PhysReg -> option nat)
  (reg : PhysReg) {measure fin_to_nat reg} : (PhysReg * option nat)%type :=
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
Proof.
  intros. apply pred_fin_lt. assumption.
Qed.

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
  let lastReg := penultimate_from_nat maxReg registers_exist in
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