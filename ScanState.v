Require Import Lib.

Require Export Machine.
Require Export Interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MScanState (Mach : Machine).
Import Mach.

Import EqNotations.

Definition maxReg := maxReg.
Definition PhysReg := fin maxReg.
Definition registers_exist := registers_exist.

(** ** ScanStateDesc *)

(** A [ScanStateDesc] is always relative to a current position as we move
    through the sequentialized instruction stream over which registers are
    allocated. *)

Definition fixedIntervalsType :=
  Vec (option { d : IntervalDesc | FixedInterval d }) maxReg.

Record ScanStateDesc : Type := {
    nextInterval : nat;
    IntervalId := fin nextInterval;

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

Definition widen_id {n} := widen_ord (leqnSn n).
Arguments widen_id [n] i /.
Definition widen_fst {n a} p := (@widen_id n (@fst _ a p), snd p).

Lemma map_widen_fst : forall (a : eqType) n (xs : seq (fin n * a)),
  [seq fst i | i <- [seq (@widen_fst n a) i | i <- xs]] =
  [seq (@widen_id n) i | i <- [seq fst i | i <- xs]].
Proof. move=> a n xs. by rewrite -!map_comp. Qed.

Definition getInterval `(i : IntervalId sd) := (vnth (intervals sd) i).2.
Arguments getInterval [sd] i /.

Definition unhandledExtent `(sd : ScanStateDesc) : nat :=
  match unhandledIds sd with
  | nil => 0
  | [:: i] => intervalExtent (vnth (intervals sd) i).2
  | xs  =>
    let f n x := n + intervalExtent (vnth (intervals sd) x).2 in
    foldl f 0 xs
  end.

(** Given a vector of optional positions associated with register, return the
    first register (counting downwards) which is either [None], or the highest
    of [Some] value.

    The worst case scenario is that every register has [Some n] with the same
    n, in which case register 0 is selected. *)

Definition registerWithHighestPos :
  Vec (option nat) maxReg -> fin maxReg * option nat :=
  fold_left_with_index
    (fun reg (res : fin maxReg * option nat) x =>
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
       ; intervals        := V.nil _
       ; fixedIntervals   := V.const None _
       |}

  | ScanState_newUnhandled sd :
    ScanState sd -> forall `(i : Interval d),
    let n   := (ord_max, ibeg d) in
    let unh := map widen_fst (unhandled sd) in
    ScanState
      {| nextInterval     := (nextInterval sd).+1
       ; unhandled        := insert (lebf snd ^~ n) n unh
       ; active           := map widen_fst (active sd)
       ; inactive         := map widen_fst (inactive sd)
       ; handled          := map widen_fst (handled sd)
       ; intervals        := V.shiftin (d; i) (intervals sd)
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
       ; intervals        := replace (intervals sd) xid (d; i)
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

(** [ScanState_unhandledExtent] relates the [unhandledExtent] of a [ScanState]
    with the [intervalExtent] of the first member of its [unhandled] list. *)
Theorem ScanState_unhandledExtent `(st : ScanState sd) :
  let ue := unhandledExtent sd in
  match unhandled sd with
  | nil    => ue == 0
  | [:: i] => ue == intervalExtent (vnth (intervals sd) (fst i)).2
  | i :: _ => ue > intervalExtent (vnth (intervals sd) (fst i)).2
  end.
Proof.
  destruct sd.
  destruct unhandled0 eqn:Heqe;
  unfold unhandledExtent; simpl. by [].
  destruct l eqn:Heqe2; simpl. by [].
  apply fold_gt.
  destruct p0.
  pose (Interval_extent_nonzero (vnth intervals0 i).2).
  by rewrite add0n addnC ltn_plus.
Qed.

Theorem ScanState_newUnhandled_spec `(st : ScanState sd) : forall d i,
  let st' := @ScanState_newUnhandled _ st d i in
  let sd' := getScanStateDesc st' in
    unhandledExtent sd' == unhandledExtent sd + intervalExtent i.
Admitted.

Theorem ScanState_setInterval_spec `(st : ScanState sd) : forall xid d i H1 H2,
  let st' := @ScanState_setInterval _ st xid d i H1 H2 in
  let sd' := getScanStateDesc st' in
    unhandledExtent sd'
      == (unhandledExtent sd - intervalExtent (vnth (intervals sd) xid).2) +
         intervalExtent i.
Admitted.

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