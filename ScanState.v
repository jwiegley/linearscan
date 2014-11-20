Require Import LinearScan.Lib.

Require Export LinearScan.Machine.
Require Export LinearScan.Interval.
Require Export LinearScan.Ops.
Require Export LinearScan.Vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MScanState (Mach : Machine).

Include Mach.

(** ** ScanStateDesc *)

(** A [ScanStateDesc] is always relative to a current position as we move
    through the sequentialized instruction stream over which registers are
    allocated. *)

Definition fixedIntervalsType :=
  Vec (option { d : IntervalDesc | FixedInterval d }) maxReg.

Record ScanStateDesc : Type := {
    nextInterval : nat;
    IntervalId := 'I_nextInterval;

    intervals : Vec { d : IntervalDesc | Interval d } nextInterval;
    fixedIntervals : fixedIntervalsType;

    unhandled : list (IntervalId * nat);     (* starts after pos *)
    active    : list (IntervalId * PhysReg); (* ranges over pos *)
    inactive  : list (IntervalId * PhysReg); (* falls in lifetime hole *)
    handled   : list (IntervalId * PhysReg); (* ends before pos *)

    unhandledIds := [seq fst i | i <- unhandled];
    activeIds    := [seq fst i | i <- active];
    inactiveIds  := [seq fst i | i <- inactive];
    handledIds   := [seq fst i | i <- handled];

    all_state_lists := unhandledIds ++ activeIds ++ inactiveIds ++ handledIds
}.

Arguments IntervalId /.
Arguments unhandledIds /.
Arguments activeIds /.
Arguments inactiveIds /.
Arguments handledIds /.

Definition getInterval `(i : IntervalId sd) := (vnth (intervals sd) i).2.
Arguments getInterval [sd] i /.

Definition totalExtent `(xs : seq (IntervalId sd)) : nat :=
  sumlist [seq (intervalExtent (getInterval i)) | i <- xs].
Arguments totalExtent [sd] _ /.

Definition unhandledExtent (sd : ScanStateDesc) : nat :=
  totalExtent [seq fst i | i <- unhandled sd].

Definition intervals_for_reg {sd : ScanStateDesc}
  (xs : seq (IntervalId sd * PhysReg)) (reg : PhysReg) : seq (IntervalId sd) :=
  foldl (fun acc x =>
           let: (xid, r) := x in
           if r == reg
           then xid :: acc
           else acc) nil xs.

(** Given a vector of optional positions associated with register, return the
    first register (counting downwards) which is either [None], or the highest
    of [Some] value.

    The worst case scenario is that every register has [Some n] with the same
    n, in which case register 0 is selected. *)

Definition registerWithHighestPos :
  Vec (option nat) maxReg -> 'I_maxReg * option nat :=
  vfoldl_with_index
    (fun reg (res : 'I_maxReg * option nat) x =>
       match (res, x) with
       | ((r, None), _) => (r, None)
       | (_, None) => (reg, None)
       | ((r, Some n), Some m) =>
         if n < m then (reg, Some m) else (r, Some n)
       end) (Ordinal registers_exist, Some 0).

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
       ; intervals        := vnil _
       ; fixedIntervals   := vconst None
       |}

  | ScanState_newUnhandled sd :
    ScanState sd -> forall `(i : Interval d),
    let n   := (ord_max, ibeg d) in
    let unh := map widen_fst (unhandled sd) in
    ScanState
      {| nextInterval     := (nextInterval sd).+1
       ; unhandled        := insert (lebf (@snd _ _)) n unh
       ; active           := map widen_fst (active sd)
       ; inactive         := map widen_fst (inactive sd)
       ; handled          := map widen_fst (handled sd)
       ; intervals        := vshiftin (intervals sd) (d; i)
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_newInactive sd reg :
    ScanState sd -> forall `(i : Interval d),
    let inact := map widen_fst (inactive sd) in
    ScanState
      {| nextInterval     := (nextInterval sd).+1
       ; unhandled        := map widen_fst (unhandled sd)
       ; active           := map widen_fst (active sd)
       ; inactive         := (ord_max, reg) :: inact
       ; handled          := map widen_fst (handled sd)
       ; intervals        := vshiftin (intervals sd) (d; i)
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_setInterval sd :
    ScanState sd -> forall xid `(i : Interval d),
    let xi := (vnth (intervals sd) xid).2 in
    intervalExtent i < intervalExtent xi ->
    intervalStart i == intervalStart xi ->
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := inactive sd
       ; handled          := handled sd
       ; intervals        := vreplace (intervals sd) xid (d; i)
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_setFixedIntervals sd :
    ScanState sd -> forall (regs : fixedIntervalsType),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := inactive sd
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := regs
       |}

  | ScanState_moveUnhandledToActive
      ni unh act inact hnd ints fixints x reg :
    ScanState
      {| nextInterval     := ni
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; fixedIntervals   := fixints
       |} ->
    (* jww (2014-11-05): NYI *)
    (* reg \notin [seq snd i | i <- act ++ inact] -> *)
    ScanState
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := (fst x, reg) :: act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; fixedIntervals   := fixints
       |}

  | ScanState_moveActiveToInactive sd :
    ScanState sd -> forall x, x \in active sd ->
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := x :: inactive sd
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveActiveToHandled sd :
    ScanState sd -> forall x, x \in active sd ->
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := inactive sd
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveInactiveToActive sd :
    ScanState sd -> forall x, x \in inactive sd ->
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := x :: active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveInactiveToHandled sd :
    ScanState sd -> forall x, x \in inactive sd ->
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}.

Tactic Notation "ScanState_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ScanState_nil"
  | Case_aux c "ScanState_newUnhandled"
  | Case_aux c "ScanState_newInactive"
  | Case_aux c "ScanState_setInterval"
  | Case_aux c "ScanState_setFixedIntervals"
  | Case_aux c "ScanState_moveUnhandledToActive"
  | Case_aux c "ScanState_moveActiveToInactive"
  | Case_aux c "ScanState_moveActiveToHandled"
  | Case_aux c "ScanState_moveInactiveToActive"
  | Case_aux c "ScanState_moveInactiveToHandled"
  ].

Notation ScanStateSig := { sd : ScanStateDesc | ScanState sd }.

Definition getScanStateDesc `(st : ScanState sd) := sd.
Arguments getScanStateDesc [sd] st /.

Definition packScanState `(st : ScanState sd) := exist ScanState sd st.
Arguments packScanState [sd] st /.

(** ** ScanStateCursor *)

(** A [ScannStateCursor] gives us a view of the first unhandled element within
    a [ScanState].  The cursor is only valid if such an unhandled element
    exists, so it combines that assertion with a view onto that element. *)

Record ScanStateCursor (sd : ScanStateDesc) : Prop := {
    curState  : ScanState sd;
    curExists : size (unhandled sd) > 0;

    curId := safe_hd _ curExists;
    curIntDetails := vnth (intervals sd) (fst curId)
}.

Arguments curState {sd} _.
Arguments curExists {sd} _.
Arguments curId {sd} _.
Arguments curIntDetails {sd} _.

Definition curInterval `(cur : ScanStateCursor sd) := (curIntDetails cur).2.
Arguments curInterval [sd] cur /.
Definition curPosition `(cur : ScanStateCursor sd) :=
  intervalStart (curInterval cur).
Arguments curPosition [sd] cur /.

End MScanState.