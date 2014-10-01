Require Import Coq.Program.Basics.
Require Import Coq.Structures.Orders.
Require Import Coq.Vectors.Vector.
Require Import Compare.
Require Import Fin.
Require Import Interval.
Require Import Lib.
Require Import ScanState.
Require Import Vector.
Require Import SSMorph.

Open Scope program_scope.

Generalizable All Variables.

Module MAllocate (M : Machine).
Include MSSMorph M.

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
         if n <? m then (reg, Some m) else (r, Some n)
       end) (from_nat 0 registers_exist, Some 0).

(** Given a vector from registers to values, find the slot corresponding to
    the register assigned to [i] and replace it with [x]. *)

Definition atIntervalReg {sd : ScanStateDesc} (i : IntervalId sd)
  {a} (v : Vec a maxReg) (x : a) :=
  match V.nth (assignments sd) i with
  | None => v
  | Some r => replace v r x
  end.

(** Split the current interval before the position [before].  This must
    succeed, which means there must be use positions within the interval prior
    to [before].  If [before] is [None], then splitting is done before the
    first use position that does not require a register.

    The resulting intervals are sorted back into the unhandled
    list, so that the next interval to be processed may not be the remainder
    of the split interval.

    jww (2014-10-01): Prove that it always succeeds. *)

Definition splitInterval `(cur : ScanStateCursor sd) (before : option nat)
  : NextState cur SSMorphStLen :=
  (* jww (2014-09-26): NYI *)
  Build_NextScanState sd (curState cur) undefined.

Definition getInterval `(i : IntervalId sd) :=
  proj2_sig (V.nth (intervals sd) i).

Definition getAssignment `(i : IntervalId sd) :=
  V.nth (assignments sd) i.

Definition assignRegister `(cur : ScanStateCursor sd)
  (reg : PhysReg) : NextState cur SSMorphLen.
  (* jww (2014-10-01): NYI *)
Admitted.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg `(cur : ScanStateCursor sd)
  : option (NextState cur SSMorphSt) :=
  let current := curInterval cur in

  (* set freeUntilPos of all physical registers to maxInt
     for each interval it in active do
       freeUntilPos[it.reg] = 0
     for each interval it in inactive intersecting with current do
       freeUntilPos[it.reg] = next intersection of it with current *)
  let go n := fold_left (fun v i => atIntervalReg i v (n i)) in
  let freeUntilPos' := go (fun _ => Some 0)
                          (active sd) (const None maxReg) in
  let intersectingIntervals :=
      filter (fun x => anyRangeIntersects current (getInterval x))
             (inactive sd) in
  let freeUntilPos :=
      go (fun i => firstIntersectionPoint (getInterval i) current)
         intersectingIntervals freeUntilPos' in

  (* reg = register with highest freeUntilPos *)
  (* mres = highest use position of the found register *)
  let (reg, mres) := registerWithHighestPos freeUntilPos in

  let success := moveUnhandledToActive cur reg in
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
               else let spl    := splitInterval cur (Some n) in
                    let cur'   := cursorFromMorphStLen cur spl in
                    moveUnhandledToActive cur' reg)
  end.

Definition nextUseAfter `(curId : Interval desc) (pos : nat) : option nat.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition assignSpillSlotToCurrent `(cur : ScanStateCursor sd)
  : NextScanState (SSMorphLen sd).
  (* jww (2014-09-26): NYI *)
Admitted.

Definition intersectsWithFixedInternal `(cur : ScanStateCursor sd)
  (reg : PhysReg) : bool.
  (* jww (2014-10-01): NYI *)
Admitted.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  In either case,
    the change to the [ScanState] must be a productive one. *)
Definition allocateBlockedReg `(cur : ScanStateCursor sd)
  : NextState cur SSMorphSt :=
  let current := curInterval cur in
  let start   := intervalStart current in
  let pos     := curPosition cur in

  (* set nextUsePos of all physical registers to maxInt
     for each interval it in active do
       nextUsePos[it.reg] = next use of it after start of current
     for each interval it in inactive intersecting with current do
       nextUsePos[it.reg] = next use of it after start of current *)
  let go :=
      fold_left (fun v i =>
                   atIntervalReg i v (nextUseAfter (getInterval i) start)) in
  let nextUsePos' := go (active sd) (const None maxReg) in
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
  let firstUse := undefined in
  let next :=
      if (match mres with
          | None   => false
          | Some n => n <? firstUse
          end)
      then let next := assignSpillSlotToCurrent cur in
           let firstUseReqReg := undefined in
           splitInterval cur (Some firstUseReqReg)
      else undefined in

  (* // make sure that current does not intersect with
     // the fixed interval for reg
     if current intersects with the fixed interval for reg then
       split current before this intersection *)
  let cursor := cursorFromMorphStLen cur next in
  if intersectsWithFixedInternal cursor reg
  (* then moveUnhandledToActive *)
  (*          (cursorFromMorphStLen cursor (splitInterval cursor undefined)) reg *)
  (* else next. *)
  then undefined
  else undefined.

Fixpoint checkActiveIntervals `(st : ScanState sd) pos
  : NextScanState (SSMorphLen sd) :=
  let fix go sd (st : ScanState sd) ss is pos :=
    match is with
    | nil => ss
    | x :: xs =>
        (* for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it does not cover position then
               move it from active to inactive *)
        let i := getInterval (proj1_sig x) in
        let st1 := if intervalEnd i <? pos
                   then uncurry_sig (moveActiveToHandled st) x
                   else if negb (intervalCoversPos i pos)
                        then uncurry_sig (moveActiveToInactive st) x
                        else ss in
        go sd st st1 xs pos
    end in
  go sd st (Build_NextScanState sd st (newSSMorphLen sd))
     (list_membership (active sd)) pos.

Fixpoint checkInactiveIntervals `(st : ScanState sd) pos
  : NextScanState (SSMorphLen sd) :=
  let fix go sd (st : ScanState sd) ss is pos :=
    match is with
    | nil => ss
    | x :: xs =>
        (* for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it covers position then
               move it from active to inactive *)
        let i := getInterval (proj1_sig x) in
        let st1 := if intervalEnd i <? pos
                   then uncurry_sig (moveInactiveToHandled st) x
                   else if intervalCoversPos i pos
                        then uncurry_sig (moveInactiveToActive st) x
                        else ss in
        go sd st st1 xs pos
    end in
  go sd st (Build_NextScanState sd st (newSSMorphLen sd))
     (list_membership (inactive sd)) pos.

Definition handleInterval `(cur : ScanStateCursor sd)
  : NextState cur SSMorphSt :=
  (* position = start position of current *)
  let position := curPosition cur in

  (* // check for intervals in active that are handled or inactive *)
  let sp1  := checkActiveIntervals (curState cur) position in
  let Hlt1 := unhandled_nonempty sd (nextDesc sp1) (morphProof sp1)
                                 (curExists cur) in
  let H1   := next_interval_increases (morphProof sp1) in
  let cid1 := transportId H1 (curId cur) in

  (* jww (2014-10-01): OPTIONAL Prove: length active <=. *)

  (* // check for intervals in inactive that are handled or active *)
  let sp2  := checkInactiveIntervals (nextState sp1) position in
  let Hlt2 := unhandled_nonempty (nextDesc sp1) (nextDesc sp2)
                                 (morphProof sp2) Hlt1 in
  let H2   := next_interval_increases (morphProof sp2) in
  let cid2 := transportId H2 cid1 in

  (* jww (2014-10-01): OPTIONAL Prove: length inactive <=. *)

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg
     if current has a register assigned then
       add current to active (done by the helper functions) *)
  let cursor := {| curState  := nextState sp2
                 ; curExists := Hlt2
                 |} in
  let result := fromMaybe (allocateBlockedReg cursor)
                          (tryAllocateFreeReg cursor) in
  {| nextDesc   := nextDesc result
   ; nextState  := nextState result
   ; morphProof :=
       SSMorphLenLenSt_transitivity (morphProof sp1) (morphProof sp2)
                                    (morphProof result)
   |}.

Function linearScan (sd : ScanStateDesc) (st : ScanState sd)
  {measure unhandledExtent sd} : { sd' : ScanStateDesc | ScanState sd' } :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match destruct_list (unhandled sd) with
  | inleft (existT x (exist xs H)) =>
    let cursor := {| curState  := st
                   ; curExists := list_cons_nonzero H
                   |} in
    match handleInterval cursor with
      Build_NextScanState sd2 st2 smorph2 => linearScan sd2 st2
    end
  | inright _ => exist _ sd st
  end.
(* We must prove that after every call to handleInterval, the total extent
   of the remaining unhandled intervals is less than it was before. *)
Proof. intros; inversion smorph2; assumption. Defined.

End MAllocate.