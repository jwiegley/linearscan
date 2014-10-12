Require Import Coq.Structures.Orders.
Require Import Range.
Require Import Interval.
Require Import Lib.
Require Import ScanState.
Require Import SSMorph.
Require Import Hask.IApplicative.
Require Import Hask.IMonad.
Require Import Hask.IState.

Open Scope nat_scope.
Open Scope program_scope.

Generalizable All Variables.

Module MAllocate (M : Machine).
Include MSSMorph M.

Definition splitCurrentInterval {pre P} `{HasWork P} (before : option nat)
  : SState pre P SSMorphStHasLen unit.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition splitActiveIntervalForReg {pre P} (reg : PhysReg) (position : nat)
  : SState pre P P unit.
  (* jww (2014-10-01): NYI *)
Admitted.

Definition splitAnyInactiveIntervalForReg {pre P} (reg : PhysReg)
  : SState pre P P unit.
  (* jww (2014-10-01): NYI *)
Admitted.

Definition intersectsWithFixedInterval {pre P} `{HasWork P} (reg : PhysReg)
  (* jww (2014-10-02): This needs to say "it has to have Len in it" *)
  : SState pre P P (option nat).
  (* jww (2014-10-01): NYI *)
Admitted.

Definition assignSpillSlotToCurrent {pre P} `{HasWork P}
  : SState pre P P unit.
  (* jww (2014-09-26): NYI *)
Admitted.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg {pre P} `{W : HasWork P}
  : SState pre P P (option (SState pre P SSMorphSt PhysReg)) :=
  withCursor $ fun sd cur =>
    let current := curInterval cur in
    let sd := curStateDesc cur in

    (* set freeUntilPos of all physical registers to maxInt
       for each interval it in active do
         freeUntilPos[it.reg] = 0
       for each interval it in inactive intersecting with current do
         freeUntilPos[it.reg] = next intersection of it with current *)
    let go n := fold_left (fun v i => atIntervalReg i v (n i)) in
    let freeUntilPos' := go (fun _ => Some 0)
                            (active sd) (V.const None maxReg) in
    let intersectingIntervals :=
        filter (fun x => intervalsIntersect current (getInterval x))
               (inactive sd) in
    let freeUntilPos :=
        go (fun i => intervalIntersectionPoint (getInterval i) current)
           intersectingIntervals freeUntilPos' in

    (* reg = register with highest freeUntilPos *)
    (* mres = highest use position of the found register *)
    let (reg, mres) := registerWithHighestPos freeUntilPos in

    (** [moveUnhandledToActive] not only moves an [IntervalId] from the
        [unhandled] list to the [active] list in the current [ScanStateDesc], it
        also assignments a register to that newly active interval, which can be
        accessed by calling [getAssignment]. *)

    let success := moveUnhandledToActive reg ;;; return_ reg in
    let maction :=
        match mres with
        | None => Some success
        | Some n =>
          (* if freeUntilPos[reg] = 0 then
               // no register available without spilling
               allocation failed
             else if current ends before freeUntilPos[reg] then
               // register available for the whole interval
               current.reg = reg
             else
               // register available for the first part of the interval
               current.reg = reg
               split current before freeUntilPos[reg] *)
          if beq_nat n 0
          then None
          else Some (if intervalEnd current <? n
                     then success
                     else splitCurrentInterval (Some n) ;;;
                          moveUnhandledToActive reg ;;;
                          return_ reg)
        end in
    return_ maction.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  In either case,
    the change to the [ScanState] must be a productive one. *)
Definition allocateBlockedReg {pre P} `{HasWork P}
  : SState pre P SSMorphSt (option PhysReg) :=
  withCursor $ fun sd cur =>
    let st      := curState cur in
    let current := curInterval cur in
    let start   := intervalStart current in
    let pos     := curPosition cur in

    (* set nextUsePos of all physical registers to maxInt
       for each interval it in active do
         nextUsePos[it.reg] = next use of it after start of current
       for each interval it in inactive intersecting with current do
         nextUsePos[it.reg] = next use of it after start of current *)
    let go := fold_left (fun v i =>
                atIntervalReg i v (nextUseAfter (getInterval i) start)) in
    let nextUsePos' := go (active sd) (V.const None maxReg) in
    let intersectingIntervals :=
        filter (fun x => intervalsIntersect current (getInterval x))
               (inactive sd) in
    let nextUsePos := go intersectingIntervals nextUsePos' in

    (* reg = register with highest nextUsePos *)
    (* mres = highest use position of the found register *)
    let (reg, mres) := registerWithHighestPos nextUsePos in

    (* if first usage of current is after nextUsePos[reg] then
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
         split current before this intersection *)
    if (match mres with
        | None   => false
        | Some n => n <? start
        end)
    then
      assignSpillSlotToCurrent ;;;
      splitCurrentInterval (firstUseReqReg current) ;;;

      mloc <<- intersectsWithFixedInterval reg ;;
      match mloc with
      | Some n => splitCurrentInterval (Some n)
      | None   => return_ tt
      end ;;;
      weakenStHasLenToSt ;;;
      return_ None
    else
      splitActiveIntervalForReg reg pos ;;;
      splitAnyInactiveIntervalForReg reg ;;;

      mloc <<- intersectsWithFixedInterval reg ;;
      match mloc
      with
      | Some n => splitCurrentInterval (Some n) ;;;
                  moveUnhandledToActive reg
      | None   => moveUnhandledToActive reg
      end ;;;
      return_ (Some reg).

Definition checkActiveIntervals {pre} (pos : nat)
  : SState pre SSMorphLen SSMorphLen unit :=
  let fix go sd (st : ScanState sd) ss ints :=
    match ints with
    | nil => ss
    | x :: xs =>
        (* for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it does not cover position then
               move it from active to inactive *)
        let i := getInterval x.1 in
        let st1 :=
            if intervalEnd i <? pos
            then uncurry_sig (moveActiveToHandled st) x
            else if negb (intervalCoversPos i pos)
                 then uncurry_sig (moveActiveToInactive st) x
                 else ss in
        go sd st st1 xs
    end in
  withScanStatePO $ fun sd (st : ScanState sd) =>
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let (sd',st',H) := go sd st unchanged (list_membership (active sd)) in
    iput {| thisDesc  := sd'
          ; thisHolds := H
          ; thisState := st'
          |}.

Definition checkInactiveIntervals {pre} (pos : nat)
  : SState pre SSMorphLen SSMorphLen unit :=
  let fix go sd (st : ScanState sd) ss ints :=
    match ints with
    | nil => ss
    | x :: xs =>
        (* for each interval it in inactive do
             if it ends before position then
               move it from inactive to handled
             else if it covers position then
               move it from inactive to active *)
        let i := getInterval x.1 in
        let st1 :=
            if intervalEnd i <? pos
            then uncurry_sig (moveInactiveToHandled st) x
            else if intervalCoversPos i pos
                 then uncurry_sig (moveInactiveToActive st) x
                 else ss in
        go sd st st1 xs
    end in
  withScanStatePO $ fun sd (st : ScanState sd) =>
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let (sd',st',H) := go sd st unchanged (list_membership (inactive sd)) in
    iput {| thisDesc  := sd'
          ; thisHolds := H
          ; thisState := st'
          |}.

Definition handleInterval {pre}
  : SState pre SSMorphHasLen SSMorphSt (option PhysReg) :=
  (* position = start position of current *)
  withCursor $ fun _ cur =>
    let position := curPosition cur in

    (* // check for intervals in active that are handled or inactive *)
    liftLen $ checkActiveIntervals position ;;;
    (* // check for intervals in inactive that are handled or active *)
    liftLen $ checkInactiveIntervals position ;;;

    (* // find a register for current
       tryAllocateFreeReg
       if allocation failed then
         allocateBlockedReg
       if current has a register assigned then
         add current to active (done by the helper functions) *)
    mres <<- tryAllocateFreeReg ;;
    match mres with
    | Some x => imap (@Some _) x
    | None   => allocateBlockedReg
    end.

Function linearScan (sd : ScanStateDesc) (st : ScanState sd)
  {measure unhandledExtent sd} : { sd' : ScanStateDesc | ScanState sd' } :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match destruct_list (unhandled sd) with
  | inleft (existT x (exist xs H)) =>
    let ssinfo := {| thisDesc  := sd
                   ; thisHolds := newSSMorphHasLen (list_cons_nonzero H)
                   ; thisState := st
                   |} in
    match runIState handleInterval ssinfo with
      (_, ssinfo') =>
        linearScan (thisDesc ssinfo') (thisState ssinfo')
    end
  | inright _ => (sd; st)
  end.
(* We must prove that after every call to handleInterval, the total extent
   of the remaining unhandled intervals is less than it was before. *)
Proof. destruct ssinfo'; destruct thisHolds0; auto. Qed.

End MAllocate.