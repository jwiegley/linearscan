Require Import LinearScan.Lib.

Require Export LinearScan.Machine.
Require Export LinearScan.Interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MScanState (Mach : Machine).

Include Mach.

Inductive SSError : Set :=
  | ECannotSplitSingleton : nat -> SSError
  | ECannotSplitAssignedSingleton : nat -> SSError
  | ENoIntervalsToSplit
  | ERegisterAlreadyAssigned : nat -> SSError
  | ERegisterAssignmentsOverlap : nat -> SSError
  | EFuelExhausted : SSError.

Definition stbind {P Q R a b}
  (f : (a -> IState SSError Q R b)) (x : IState SSError P Q a) :
  IState SSError P R b :=
  @ijoin (IState SSError) _ P Q R b (@imap _ _ P Q _ _ f x).

Notation "m >>>= f" := (stbind f m) (at level 25, left associativity).

Notation "X <<- A ;; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

Notation "A ;;; B" := (_ <<- A ;; B)
  (right associativity, at level 84, A1 at next level).

Definition error_ {I X} err := mkIState SSError I I X (fun _ => inl err).
Definition return_ {I X} := @ipure (IState SSError) _ I X.

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

    (* The [nat] in this member indicates the beginning position of the
       interval. *)
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

(** Given a vector of optional positions associated with a register, return
    the first register (counting upwards) which is either [None], or the
    highest of [Some] value.

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

Inductive ScanStateStatus := Pending | InUse.

Inductive ScanState : ScanStateStatus -> ScanStateDesc -> Prop :=
  | ScanState_nil :
    ScanState Pending
      {| nextInterval     := 0
       ; unhandled        := nil
       ; active           := nil
       ; inactive         := nil
       ; handled          := nil
       ; intervals        := vnil _
       ; fixedIntervals   := vconst None
       |}

  (* This is the only constructor which may add work to the scan state. *)
  | ScanState_newUnhandled b sd :
    ScanState b sd -> forall `(i : Interval d),
    let n   := (ord_max, ibeg d) in
    let unh := map widen_fst (unhandled sd) in
    (if b is Pending
     then (* While a [ScanState] is [Pending], unhandled intervals may be
             added at any position.  Once it is finalized and [InUse],
             unhandled intervals (arising from splits) may only be added after
             the current position. *)
          True
     else if unhandled sd is (_, u) :: _
          then u < ibeg d
          else False) ->
    ScanState b
      {| nextInterval     := (nextInterval sd).+1
       ; unhandled        := insert (lebf (@snd _ _)) n unh
       ; active           := map widen_fst (active sd)
       ; inactive         := map widen_fst (inactive sd)
       ; handled          := map widen_fst (handled sd)
       ; intervals        := vshiftin (intervals sd) (d; i)
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_finalize sd :
      ScanState Pending sd -> ScanState InUse sd

  | ScanState_setInterval sd :
    ScanState InUse sd -> forall xid `(i : Interval d),
    let xi := (vnth (intervals sd) xid).2 in
    intervalStart i == intervalStart xi ->
    ScanState InUse
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := inactive sd
       ; handled          := handled sd
       ; intervals        := vreplace (intervals sd) xid (d; i)
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_setFixedIntervals sd :
    ScanState Pending sd -> forall (regs : fixedIntervalsType),
    ScanState Pending
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
    ScanState InUse
      {| nextInterval     := ni
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; fixedIntervals   := fixints
       |} ->
    reg \notin [seq snd i | i <- act] ->
    ScanState InUse
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := (fst x, reg) :: act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; fixedIntervals   := fixints
       |}

  | ScanState_moveActiveToInactive sd :
    ScanState InUse sd -> forall x, x \in active sd ->
    ScanState InUse
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := x :: inactive sd
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveActiveToHandled sd :
    ScanState InUse sd -> forall x, x \in active sd ->
    ScanState InUse
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := inactive sd
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveInactiveToActive sd :
    ScanState InUse sd -> forall x, x \in inactive sd ->
    snd x \notin [seq snd i | i <- active sd] ->
    ScanState InUse
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := x :: active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveInactiveToHandled sd :
    ScanState InUse sd -> forall x, x \in inactive sd ->
    ScanState InUse
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
  | Case_aux c "ScanState_finalize"
  | Case_aux c "ScanState_setInterval"
  | Case_aux c "ScanState_setFixedIntervals"
  | Case_aux c "ScanState_moveUnhandledToActive"
  | Case_aux c "ScanState_moveActiveToInactive"
  | Case_aux c "ScanState_moveActiveToHandled"
  | Case_aux c "ScanState_moveInactiveToActive"
  | Case_aux c "ScanState_moveInactiveToHandled"
  ].

Definition ScanStateSig (b : ScanStateStatus) :=
  { sd : ScanStateDesc | ScanState b sd }.

Definition getScanStateDesc `(st : ScanState InUse sd) := sd.
Arguments getScanStateDesc [sd] st /.

Definition packScanState `(st : ScanState b sd) := exist (ScanState b) sd st.
Arguments packScanState [b sd] st /.

(** ** ScanStateCursor *)

(** A [ScannStateCursor] gives us a view of the first unhandled element within
    a [ScanState].  The cursor is only valid if such an unhandled element
    exists, so it combines that assertion with a view onto that element. *)

Record ScanStateCursor (sd : ScanStateDesc) : Prop := {
    curState  : ScanState InUse sd;
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