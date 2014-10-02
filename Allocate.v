Require Import Coq.Structures.Orders.
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

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], then splitting is done before the
    first use position that does not require a register.

    The resulting intervals are sorted back into the unhandled
    list, so that the next interval to be processed may not be the remainder
    of the split interval.

    jww (2014-10-01): Prove that it always succeeds. *)

Definition splitCurrentInterval {P} (before : option nat)
  : SState HasUnhandled HasUnhandled P SSMorphStLen unit.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition splitActiveIntervalForReg {H P} (reg : PhysReg) (position : nat)
  : SState H H P P unit.
  (* jww (2014-10-01): NYI *)
Admitted.

Definition splitAnyInactiveIntervalForReg {H P} (reg : PhysReg)
  : SState H H P P unit.
  (* jww (2014-10-01): NYI *)
Admitted.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg
  : SState HasUnhandled HasUnhandled SSMorphLen SSMorphLen
           (option (SState HasUnhandled MaybeHasUnhandled
                           SSMorphLen SSMorphSt PhysReg)) :=
  withLenCursor $ fun sd cur =>
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
      filter (fun x => anyRangeIntersects current (getInterval x))
             (inactive sd) in
  let freeUntilPos :=
      go (fun i => firstIntersectionPoint (getInterval i) current)
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
                        weakenStLenToLen ;;;
                        moveUnhandledToActive reg ;;;
                        return_ reg)
      end in
  return_ maction.

Definition nextUseAfter `(curId : Interval desc) (pos : nat) : option nat.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition firstUseReqReg `(curId : Interval desc) : option nat.
  (* jww (2014-10-01): NYI *)
Admitted.

Definition assignSpillSlotToCurrent {P}
  : SState HasUnhandled HasUnhandled P P unit.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition intersectsWithFixedInterval {P} (reg : PhysReg)
  : SState HasUnhandled HasUnhandled P P (option nat).
  (* jww (2014-10-01): NYI *)
Admitted.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  In either case,
    the change to the [ScanState] must be a productive one. *)
Definition allocateBlockedReg
  : SState HasUnhandled MaybeHasUnhandled SSMorphLen SSMorphSt (option PhysReg) :=
  withLenCursor $ fun sd cur =>
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
      filter (fun x => anyRangeIntersects current (getInterval x))
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

    mloc <<- intersectsWithFixedInterval reg ;
    match mloc with
    | Some n => splitCurrentInterval (Some n)
    | None   => return_ tt
    end ;;;
    weakenStLenToSt ;;;
    weakenHasUnhandled ;;;
    return_ None
  else
    splitActiveIntervalForReg reg pos ;;;
    splitAnyInactiveIntervalForReg reg ;;;

    mloc <<- intersectsWithFixedInterval reg ;
    match mloc with
    | Some n => splitCurrentInterval (Some n) ;;;
                weakenStLenToLen
    | None   => return_ tt
    end ;;;

    moveUnhandledToActive reg ;;;
    return_ (Some reg).

Definition checkActiveIntervals {H} : SState H H SSMorphLen SSMorphLen unit :=
  let fix go is pos :=
    match is with
    | nil => return_ tt
    | x :: xs =>
        (* for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it does not cover position then
               move it from active to inactive *)
        let i := getInterval (proj1_sig x) in
        let act :=
            if intervalEnd i <? pos
            then uncurry_sig moveActiveToHandled x
            else if negb (intervalCoversPos i pos)
                 then uncurry_sig moveActiveToInactive x
                 else return_ tt in
        act ;;; go xs pos
    end in
  withScanState $ fun sd (st : ScanState sd) =>
    withLenCursor $ fun cur =>
    let pos := curPosition cur in
    go (list_membership (active sd)) pos.

Definition checkInactiveIntervals : SState SSMorphLen SSMorphLen unit :=
  let fix go sd (st : ScanState sd) is pos :=
    match is with
    | nil => return_ tt
    | x :: xs =>
        (* for each interval it in inactive do
             if it ends before position then
               move it from inactive to handled
             else if it covers position then
               move it from inactive to active *)
        let i := getInterval (proj1_sig x) in
        let act :=
            if intervalEnd i <? pos
            then step (uncurry_sig (moveInactiveToHandled st) x)
            else if intervalCoversPos i pos
                 then step (uncurry_sig (moveInactiveToActive st) x)
                 else return_ tt in
        act ;;; go sd st xs pos
    end in
  withScanState $ fun sd (st : ScanState sd) =>
    pos <<- cursor (@curPosition) ;
    go sd st (list_membership (inactive sd)) pos.

Definition handleInterval : SState SSMorphLen SSMorphSt (option PhysReg) :=
  (* position = start position of current *)
  (* // check for intervals in active that are handled or inactive *)
  checkActiveIntervals ;;;
  (* // check for intervals in inactive that are handled or active *)
  checkInactiveIntervals ;;;

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg
     if current has a register assigned then
       add current to active (done by the helper functions) *)
  mres <<- tryAllocateFreeReg ;
  match mres with
  | Some x => reg <<- x ;
              return_ (Some reg)
  | None   => allocateBlockedReg
  end.

Function linearScan (sd : ScanStateDesc) (st : ScanState sd)
  {measure unhandledExtent sd} : { sd' : ScanStateDesc | ScanState sd' } :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match destruct_list (unhandled sd) with
  | inleft (existT x (exist xs H)) =>
    let cursor := {| curState  := st
                   ; curExists := list_cons_nonzero H |} in
    let next   := {| nextDesc   := sd
                   ; nextState  := st
                   ; morphProof := newSSMorphLen sd
                   |} in
    let istate := {| startDesc   := sd
                   ; startCursor := cursor
                   ; bridgeState := next

                   ; thisDesc    := sd
                   ; thisCursor  := cursor
                   ; resultState := next
                   |} in
    match runIState handleInterval istate with
      (_, istate') =>
        let next' := resultState istate' in
        linearScan (nextDesc next') (nextState next')
    end
  | inright _ => exist _ sd st
  end.
(* We must prove that after every call to handleInterval, the total extent
   of the remaining unhandled intervals is less than it was before. *)
Proof.
  intros.
  subst. clear H teq teq2 x xs.
  destruct istate'. simpl.
  destruct bridgeState0. simpl.
  destruct morphProof0.
  crush. assumption.
  assumption.
 intros; inversion smorph2; assumption. Defined.

End MAllocate.