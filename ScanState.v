Require Export Machine.

Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import Fin.
Require Import Interval.
Require Import Lib.
Require Import NoDup.
Require Import Vector.
Require Coq.Vectors.Vector.

Module Import LN := ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MScanState (Mach : Machine).
Import Mach.

Definition maxReg := maxReg.
Definition PhysReg := fin maxReg.
Definition registers_exist := registers_exist.

Module V := Coq.Vectors.Vector.
Definition Vec := V.t.

(** ** ScanStateDesc *)

(** A [ScanStateDesc] is always relative to a current position as we move
    through the sequentialized instruction stream over which registers are
    allocated. *)

Record ScanStateDesc := {
    nextInterval : nat;
    IntervalId   := fin nextInterval;

    unhandled : list IntervalId;   (* starts after pos *)
    active    : list IntervalId;   (* ranges over pos *)
    inactive  : list IntervalId;   (* falls in lifetime hole *)

    (* jww (2014-10-01): Prove: The length of the active intervals list <
       maxReg. *)
    (* active_registers : length active < min maxReg nextInterval; *)

    (* jww (2014-10-01): The handled list is unnecessary and can be deleted
       when everything is working. *)
    handled   : list IntervalId;   (* ends before pos *)

    intervals   : Vec { d : IntervalDesc | Interval d } nextInterval;
    assignments : Vec (option PhysReg) nextInterval;

    (** Fixed Intervals

        Some machine instructions require their operands in fixed
        registers. Such constraints are already considered during the
        construction of the LIR by emitting physical register operands instead
        of virtual register operands. Although the register allocator must
        leave these operands unchanged, they must be considered during
        register allocation because they limit the number of available
        registers. Information about physical registers is collected in fixed
        intervals.

        For each physical register, one fixed interval stores where the
        register is not available for allocation. Use positions are not needed
        for fixed intervals because they are never split and spilled. Register
        constraints at method calls are also modeled using fixed intervals:
        Because all registers are destroyed when the call is executed, ranges
        of length 1 are added to all fixed intervals at the call
        site. Therefore, the allocation pass cannot assign a register to any
        interval there, and all intervals are spilled before the call. *)

    fixedIntervals :
      Vec (option { d : IntervalDesc | FixedInterval d }) maxReg;

    (* jww (2014-09-25): These restricting lemmas should be added back once
       everything is functional. *)
    (* unhandled_sorted : StronglySorted cmp_le unhandled; *)

    all_state_lists  := unhandled ++ active ++ inactive ++ handled;
    lists_are_unique : NoDup all_state_lists
}.

Definition getInterval `(i : IntervalId sd) :=
 (V.nth (intervals sd) i).2.

Definition getAssignment `(i : IntervalId sd) := V.nth (assignments sd) i.

(** Given an [IntervalId] from one [ScanStateDesc], promote it to an
    [IntervalId] within another [ScanStateDesc], provided we can demonstrate
    that the [nextInterval] is at least as large. *)
Definition transportId `(H : nextInterval sd <= nextInterval sd')
  : IntervalId sd -> IntervalId sd'.
Proof.
  case: (@leP (nextInterval sd) (nextInterval sd')) => H';
    first by apply (fin_transport H').
  contradiction H'. by apply le_dec.
Defined.

Definition unhandledExtent `(sd : ScanStateDesc) : nat :=
  match unhandled sd with
  | nil => 0
  | [i] => intervalExtent (V.nth (intervals sd) i).2
  | xs  => let f n x := n + intervalExtent (V.nth (intervals sd) x).2 in
           fold_left f xs 0
  end.

Lemma NoDup_unhandledExtent_cons
  : forall ni i (unh : list (fin ni)) ints assgn assgn' fixints
           (act act' inact inact' hnd hnd' : list (fin ni))
           (lau : NoDup (unh ++ act ++ inact ++ hnd))
           (lau' : NoDup ((i :: unh) ++ act' ++ inact' ++ hnd')),
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := unh
     ; active           := act
     ; inactive         := inact
     ; handled          := hnd
     ; intervals        := ints
     ; assignments      := assgn
     ; fixedIntervals   := fixints
     ; lists_are_unique := lau
     |} <
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := i :: unh
     ; active           := act'
     ; inactive         := inact'
     ; handled          := hnd'
     ; intervals        := ints
     ; assignments      := assgn'
     ; fixedIntervals   := fixints
     ; lists_are_unique := lau'
     |}.
Proof.
  intros.
  induction unh; unfold unhandledExtent; simpl;
  pose (Interval_extent_nonzero (V.nth ints i).2). auto.
  destruct unh; simpl;
    first by (rewrite add0n; apply ltn_plus).
  apply fold_fold_lt; rewrite 2!add0n -addnA.
  by apply ltn_plus.
Qed.

Lemma move_unhandled_to_active : forall n (x : fin n) unh act inact hnd,
  NoDup ((x :: unh) ++ act ++ inact ++ hnd)
    -> NoDup (unh ++ (x :: act) ++ inact ++ hnd).
Proof.
  intros. rewrite <- app_comm_cons.
  apply NoDup_app_cons. assumption.
Qed.

Lemma move_active_to_inactive : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (active sd)
    -> NoDup (unhandled sd ++ remove cmp_eq_dec x (active sd) ++
              (x :: inactive sd) ++ handled sd).
Proof.
  intros.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply NoDup_juggle.
  rewrite app_assoc.
  rewrite app_assoc.
  apply NoDup_swap.
  rewrite <- app_assoc.
  assumption.
  apply H0.
Qed.

Lemma move_active_to_handled : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (active sd)
    -> NoDup (unhandled sd ++ remove cmp_eq_dec x (active sd) ++
              inactive sd ++ x :: handled sd).
Proof.
  intros.
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
  apply H0.
Qed.

Lemma move_inactive_to_active : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (inactive sd)
    -> NoDup (unhandled sd ++ x :: active sd ++
              remove cmp_eq_dec x (inactive sd) ++ handled sd).
Proof.
  intros.
  rewrite app_comm_cons.
  apply NoDup_swap.
  rewrite <- app_assoc.
  apply NoDup_swap.
  repeat rewrite <- app_assoc.
  rewrite (app_assoc (handled sd)).
  apply NoDup_swap2.
  apply NoDup_juggle.
  repeat rewrite app_assoc.
  apply NoDup_swap.
  rewrite <- app_assoc.
  apply NoDup_swap2.
  rewrite <- app_assoc.
  rewrite app_assoc.
  apply NoDup_swap2.
  rewrite <- app_assoc.
  assumption.
  apply H0.
Qed.

Lemma move_inactive_to_handled : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (inactive sd)
    -> NoDup (unhandled sd ++ active sd ++
              remove cmp_eq_dec x (inactive sd) ++ x :: handled sd).
Proof.
  intros.
  rewrite (app_assoc (unhandled sd)).
  apply NoDup_swap.
  repeat rewrite <- app_assoc.
  apply NoDup_juggle.
  rewrite (app_assoc (inactive sd)).
  apply NoDup_swap.
  repeat rewrite <- app_assoc.
  assumption.
  apply H0.
Qed.

(** Given a vector of optional positions associated with register, return the
    first register (counting downwards) which is either [None], or the highest
    of [Some] value.

    The worst case scenario is that every register has [Some n] with the same
    n, in which case register 0 is selected. *)

Definition registerWithHighestPos
  : Vec (option nat) maxReg -> fin maxReg * option nat :=
  fold_left_with_index
    (fun reg (res : fin maxReg * option nat) x =>
       match (res, x) with
       | ((r, None), _) => (r, None)
       | (_, None) => (reg, None)
       | ((r, Some n), Some m) =>
         if n < m then (reg, Some m) else (r, Some n)
       end) (from_nat 0 registers_exist, Some 0).

(** Given a vector from registers to values, find the slot corresponding to
    the register assigned to [i] and replace it with [x]. *)

Definition atIntervalReg {sd : ScanStateDesc} (i : IntervalId sd)
  {a} (v : Vec a maxReg) (x : a) :=
  match V.nth (assignments sd) i with
  | None => v
  | Some r => V.replace v r x
  end.

(** ** ScanState *)

(** The [ScanState] inductive data type describes the allowable state
    transitions that can be applied to a [ScanStateDesc] value.

    In essence there are five mutating operations:

    1. Create a new unhandled interval.  This can occur for two reasons:

       a. Adding a new interval to be considered before the linear scan
          algorithm has started.
       b. Splitting the current interval, which pushes back its "pieces" as
          new unhandled intervals.

    2. Remove the first unhandled interval.  This happens when we remove it in
       order to make it the new current interval.

    3. Add the current interval to the active list.

    4. Move an item from the active list to the inactive or handled lists.

    5. Move an item from the inactive list to the active or handled lists. *)

Inductive ScanState : ScanStateDesc -> Prop :=
  | ScanState_nil :
    ScanState
      {| nextInterval     := 0
       ; unhandled        := nil
       ; active           := nil
       ; inactive         := nil
       ; handled          := nil
       ; intervals        := V.nil _
       ; assignments      := V.nil _
       ; fixedIntervals   := V.const None _
       (* ; unhandled_sorted := LSorted_nil _ *)
       ; lists_are_unique := NoDup_nil _
       |}

  | ScanState_newUnhandled
      ni unh (* unhsort *) act inact hnd ints assgn fixints lau :
    forall `(i : Interval d),
    ScanState
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; assignments      := assgn
       ; fixedIntervals   := fixints
       (* ; unhandled_sorted := unhsort *)
       ; lists_are_unique := lau
       |} ->
    forall newi (H : newi = last_fin_from_nat ni),
    ScanState
      {| nextInterval     := S ni
       ; unhandled        := newi :: map fin_expand unh
       ; active           := map fin_expand act
       ; inactive         := map fin_expand inact
       ; handled          := map fin_expand hnd
       ; intervals        := V.shiftin (d; i) ints
       ; assignments      := V.shiftin None assgn
       ; fixedIntervals   := fixints
       (* ; unhandled_sorted := unhsort *)
       ; lists_are_unique := map_fin_expand_rewrite (NoDup_fin_cons _ _ lau H)
       |}

  | ScanState_moveUnhandledToActive
      ni unh (* unhsort *) act inact hnd ints assgn fixints x reg :
    forall lau : NoDup ((x :: unh) ++ act ++ inact ++ hnd),
    ScanState
      {| nextInterval     := ni
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; assignments      := assgn
       ; fixedIntervals   := fixints
       (* ; unhandled_sorted := unhandled_sorted sd *)
       ; lists_are_unique := lau
       |} ->
    ScanState
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := x :: act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       (* jww (2014-10-01): Prove: It was None before this call *)
       ; assignments      := V.replace assgn x (Some reg)
       ; fixedIntervals   := fixints
       (* ; unhandled_sorted := unhandled_sorted sd *)
       ; lists_are_unique := move_unhandled_to_active lau
       |}

  | ScanState_moveActiveToInactive sd x :
    ScanState sd -> forall (H : In x (active sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := remove cmp_eq_dec x (active sd)
       ; inactive         := x :: inactive sd
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       ; lists_are_unique := move_active_to_inactive (lists_are_unique sd) H
       |}

  | ScanState_moveActiveToHandled sd x :
    ScanState sd -> forall (H : In x (active sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := remove cmp_eq_dec x (active sd)
       ; inactive         := inactive sd
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       ; lists_are_unique := move_active_to_handled (lists_are_unique sd) H
       |}

  | ScanState_moveInactiveToActive sd x :
    ScanState sd -> forall (H : In x (inactive sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := x :: active sd
       ; inactive         := remove cmp_eq_dec x (inactive sd)
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       ; lists_are_unique := move_inactive_to_active (lists_are_unique sd) H
       |}

  | ScanState_moveInactiveToHandled sd x :
    ScanState sd -> forall (H : In x (inactive sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := remove cmp_eq_dec x (inactive sd)
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       ; lists_are_unique :=
         move_inactive_to_handled (lists_are_unique sd) H
       |}.

Tactic Notation "ScanState_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ScanState_nil"
  | Case_aux c "ScanState_newUnhandled"
  | Case_aux c "ScanState_moveUnhandledToActive"
  | Case_aux c "ScanState_moveActiveToInactive"
  | Case_aux c "ScanState_moveActiveToHandled"
  | Case_aux c "ScanState_moveInactiveToActive"
  | Case_aux c "ScanState_moveInactiveToHandled"
  ].

Definition scanStateDesc `(st : ScanState sd) := sd.

(** [ScanState_unhandledExtent] relates the [unhandledExtent] of a [ScanState]
    with the [intervalExtent] of the first member of its [unhandled] list. *)
Theorem ScanState_unhandledExtent `(st : ScanState sd) :
  let ue := unhandledExtent sd in
  match unhandled sd with
  | nil    => ue = 0
  | [i]    => ue = intervalExtent (V.nth (intervals sd) i).2
  | i :: _ => ue > intervalExtent (V.nth (intervals sd) i).2
  end.
Proof.
  destruct sd.
  destruct unhandled0 eqn:Heqe;
  unfold unhandledExtent; simpl. reflexivity.
  destruct l eqn:Heqe2; simpl. reflexivity.
  apply fold_gt.
  pose (Interval_extent_nonzero (V.nth intervals0 i0).2).
  by rewrite add0n addnC ltn_plus.
Qed.

(** ** ScanStateCursor *)

(** A [ScannStateCursor] gives us a view of the first unhandled element within
    a [ScanState].  The cursor is only valid if such an unhandled element
    exists, so it combines that assertion with a view onto that element. *)

Record ScanStateCursor (sd : ScanStateDesc) : Prop := {
    curState  : ScanState sd;
    curExists : length (unhandled sd) > 0;

    curId         := safe_hd curExists;
    curIntDetails := V.nth (intervals sd) curId
}.

Arguments curState {sd} _.
Arguments curExists {sd} _.
Arguments curId {sd} _.
Arguments curIntDetails {sd} _.

Definition curStateDesc `(cur : ScanStateCursor sd) := sd.
Definition curIntDesc   `(cur : ScanStateCursor sd) := (curIntDetails cur).1.
Definition curInterval  `(cur : ScanStateCursor sd) := (curIntDetails cur).2.

Definition curPosition `(cur : ScanStateCursor sd) :=
  intervalStart (curInterval cur).

(** ** NextScanState *)

(** A [NextScanState] is a [ScanState] produced by mutating a prior
    [ScanState], while respecting the given predicate on the newly generated
    version.  This allows us to define well-founded recursion easily on the
    composition a series of [ScanState] mutations. *)

Record NextScanState (P : ScanStateDesc -> Prop) : Type := {
    nextDesc   : ScanStateDesc;
    nextState  : ScanState nextDesc;
    morphProof : P nextDesc
}.

Arguments Build_NextScanState [P] _ _ _.

Arguments nextDesc   [P] _.
Arguments nextState  [P] _.
Arguments morphProof [P] _.

Definition NextState `(cur : ScanStateCursor sd) P := NextScanState (P sd).

Definition NextStateDep  `(cur : ScanStateCursor sd) P Q :=
  { x : NextScanState (P sd) | Q x }.

Definition NextStateWith `(cur : ScanStateCursor sd) P A :=
  (A * NextScanState (P sd))%type.

Definition NSS_transport
  (P Q : ScanStateDesc -> ScanStateDesc -> Prop)
  {sd : ScanStateDesc} `(n : NextScanState (P sd'))
  (f : P sd' (nextDesc n) -> Q sd (nextDesc n)) : NextScanState (Q sd) :=
  {| nextDesc   := nextDesc n
   ; nextState  := nextState n
   ; morphProof := f (morphProof n)
   |}.

End MScanState.