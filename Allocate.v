Require Import Coq.Program.Basics.
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

(** Split the current interval before position [before].  This must succeed,
    which means there must be use positions within the interval prior to
    [before].  If [before] is [None], then splitting is done before the first
    use position that does not require a register.

    The resulting intervals are sorted back into the unhandled
    list, so that the next interval to be processed may not be the remainder
    of the split interval. *)

Definition splitInterval `(cur : ScanStateCursor sd) (before : option nat)
  : NextState cur SSMorphStLen :=
  (* jww (2014-09-26): NYI *)
  Build_NextScanState sd (curState cur) undefined.

Definition atRegister (sd : ScanStateDesc)
  {a} (x : IntervalId sd -> a) (v : Vec a maxReg) (i : IntervalId sd) :=
  match V.nth (assignments sd) i with
  | None => v
  | Some r => replace v r (x i)
  end.

Definition registerWithHighestPos :=
  fold_left_with_index
    (fun reg (res : fin maxReg * option nat) x =>
       match (res, x) with
       | ((r, None), _) => (r, None)
       | (_, None) => (reg, None)
       | ((r, Some n), Some m) =>
         if n <? m then (reg, Some m) else (r, Some n)
       end) (from_nat 0 registers_exist, Some 0).

Definition nextIntersectionWith
  `(i : Interval d) `(jid : IntervalId sd) : option nat :=
  firstIntersectionPoint (proj2_sig (V.nth (intervals sd) jid)) i.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg `(cur : ScanStateCursor sd)
  : option (NextState cur SSMorphSt) :=
  (* The first part of this algorithm has been modified to be more functional:
     instead of mutating an array called [freeUntilPos] and finding the
     register with the highest value, we use a function produced by a fold,
     and iterate over the register set. *)

  (* set freeUntilPos of all physical registers to maxInt
     for each interval it in active do
       freeUntilPos[it.reg] = 0
     for each interval it in inactive intersecting with current do
       freeUntilPos[it.reg] = next intersection of it with current *)
  let st             := curState cur in
  let current        := curInterval cur in
  let freeUntilPos'' := const None maxReg in
  let freeUntilPos'  :=
      fold_left (atRegister sd (fun _ => Some 0)) (active sd)
                freeUntilPos'' in

  let intersectingIntervals :=
      filter (fun x => anyRangeIntersects current
                         (proj2_sig (V.nth (intervals sd) x)))
             (inactive sd) in
  let freeUntilPos :=
      fold_left (atRegister sd (nextIntersectionWith current))
                intersectingIntervals freeUntilPos' in

  (* reg = register with highest freeUntilPos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := registerWithHighestPos freeUntilPos in
  let default     := moveUnhandledToActive cur reg in

  (* [mres] indicates the highest use position of the found register *)
  match mres with
  | None => Some default
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
    else Some
      (if ltb (intervalEnd current) n
       then default
       else moveUnhandledToActive
              (cursorFromMorphStLen cur (splitInterval cur (Some n))) reg)
  end.

Definition nextUseAfter (pos : nat) `(curId : IntervalId desc) : option nat.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition assignSpillSlotToCurrent `(cur : ScanStateCursor sd)
  : NextScanState (SSMorphLen sd).
  (* jww (2014-09-26): NYI *)
Admitted.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  In either case,
    the change to the [ScanState] must be a productive one. *)
Definition allocateBlockedReg `(cur : ScanStateCursor sd)
  : NextState cur SSMorphSt :=
  let st      := curState cur in
  let current := curInterval cur in
  let pos     := curPosition cur in

  (* set nextUsePos of all physical registers to maxInt
     for each interval it in active do
       nextUsePos[it.reg] = next use of it after start of current
     for each interval it in inactive intersecting with current do
       nextUsePos[it.reg] = next use of it after start of current *)
  let nextUsePos'' := const None maxReg in
  let nextUsePos' :=
      fold_left (atRegister sd (nextUseAfter pos)) (active sd)
                nextUsePos'' in
  let intersectingIntervals :=
      filter (fun x => anyRangeIntersects current
                         (proj2_sig (V.nth (intervals sd) x)))
             (inactive sd) in
  let nextUsePos :=
      fold_left (atRegister sd (nextUseAfter pos))
                intersectingIntervals nextUsePos' in

  (* reg = register with highest nextUsePos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
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
  let next :=
      if (match mres with
          | None   => false
          | Some n => n <? pos
          end)
      then let next := assignSpillSlotToCurrent cur in
           splitInterval cur undefined
      else undefined in

  (* // make sure that current does not intersect with
     // the fixed interval for reg
     if current intersects with the fixed interval for reg then
       split current before this intersection *)
  let cursor := cursorFromMorphStLen cur next in
  if true
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
        let i := proj2_sig (V.nth (intervals sd) (proj1_sig x)) in
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
        let i := proj2_sig (V.nth (intervals sd) (proj1_sig x)) in
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