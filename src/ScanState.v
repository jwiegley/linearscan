Require Import LinearScan.Lib.
Require Import LinearScan.Interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section ScanState.

Variable maxReg : nat.          (* max number of registers *)
Hypothesis registers_exist : maxReg > 0.
Definition PhysReg := 'I_maxReg.

(** ** ScanStateDesc *)

(** A [ScanStateDesc] is always relative to a current position as we move
    through the sequentialized instruction stream over which registers are
    allocated. *)

Definition FixedIntervalsType := Vec (option IntervalSig) maxReg.

Record ScanStateDesc : Type := {
    nextInterval : nat;
    IntervalId := 'I_nextInterval;

    intervals : Vec IntervalSig nextInterval;
    fixedIntervals : FixedIntervalsType;

    (* The [nat] in this member indicates the beginning position of the
       interval. *)
    unhandled : seq (IntervalId * nat);     (* starts after pos *)
    active    : seq (IntervalId * PhysReg); (* ranges over pos *)
    inactive  : seq (IntervalId * PhysReg); (* falls in lifetime hole *)
    handled   : seq (IntervalId * option PhysReg); (* ends before pos *)

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
  Vec (option oddnum) maxReg -> 'I_maxReg * option oddnum :=
  vfoldl_with_index
    (fun reg (res : 'I_maxReg * option oddnum) x =>
       match (res, x) with
       | ((r, None), _) => (r, None)
       | (_, None) => (reg, None)
       | ((r, Some n), Some m) =>
         if n.1 < m.1 then (reg, Some m) else (r, Some n)
       end) (Ordinal registers_exist, Some odd1).

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
             unhandled intervals (arising from splits) may only be added
             after the current position. *)
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

  | ScanState_newHandled sd :
    ScanState InUse sd -> forall `(i : Interval d),
    firstUseReqReg i == None ->
    ScanState InUse
      {| nextInterval     := (nextInterval sd).+1
       ; unhandled        := map widen_fst (unhandled sd)
       ; active           := map widen_fst (active sd)
       ; inactive         := map widen_fst (inactive sd)
       ; handled          := (ord_max, None) :: map widen_fst (handled sd)
       ; intervals        := vshiftin (intervals sd) (d; i)
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_setInterval sd :
    ScanState InUse sd -> forall xid `(i : Interval d),
    let xi := (vnth (intervals sd) xid).2 in
    intervalStart i == intervalStart xi ->
    intervalEnd i   <= intervalEnd   xi ->
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
    ScanState Pending sd -> forall (regs : FixedIntervalsType),
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

  | ScanState_moveUnhandledToHandled (* allocate a spill slot *)
      ni unh act inact hnd ints fixints x :
    ScanState InUse
      {| nextInterval     := ni
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; fixedIntervals   := fixints
       |} ->
    firstUseReqReg (vnth ints (fst x)).2 == None ->
    ScanState InUse
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := act
       ; inactive         := inact
       ; handled          := (fst x, None) :: hnd
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

  | ScanState_moveActiveToHandled sd spilled :
    ScanState InUse sd -> forall x, x \in active sd ->
    (if spilled
     then firstUseReqReg (getInterval (fst x)) == None
     else true) ->
    ScanState InUse
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := inactive sd
       ; handled          := (fst x, if spilled
                                     then None
                                     else Some (snd x)) :: handled sd
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

  | ScanState_moveInactiveToHandled sd spilled :
    ScanState InUse sd -> forall x, x \in inactive sd ->
    (if spilled
     then firstUseReqReg (getInterval (fst x)) == None
     else true) ->
    ScanState InUse
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := (fst x, if spilled
                                     then None
                                     else Some (snd x)) :: handled sd
       ; intervals        := intervals sd
       ; fixedIntervals   := fixedIntervals sd
       |}.

Definition ScanStateSig (b : ScanStateStatus) :=
  { sd : ScanStateDesc | ScanState b sd }.

Definition getScanStateDesc `(st : ScanState InUse sd) := sd.
Arguments getScanStateDesc [sd] st /.

Definition packScanState `(st : ScanState b sd) := exist (ScanState b) sd st.
Arguments packScanState [b sd] st /.

End ScanState.

Tactic Notation "ScanState_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ScanState_nil"
  | Case_aux c "ScanState_newUnhandled"
  | Case_aux c "ScanState_finalize"
  | Case_aux c "ScanState_newHandled"
  | Case_aux c "ScanState_setInterval"
  | Case_aux c "ScanState_setFixedIntervals"
  | Case_aux c "ScanState_moveUnhandledToActive"
  | Case_aux c "ScanState_moveUnhandledToHandled"
  | Case_aux c "ScanState_moveActiveToInactive"
  | Case_aux c "ScanState_moveActiveToHandled"
  | Case_aux c "ScanState_moveInactiveToActive"
  | Case_aux c "ScanState_moveInactiveToHandled"
  ].
