Require Import Coq.Program.Tactics.
Require Import Compare.
Require Import Fin.
Require Import Interval.
Require Import Lib.
Require Import Range.
Require Import ScanState.
Require Import SSMorph.

Generalizable All Variables.

Module MAllocate (M : Machine).
Include MSSMorph M.

(** * Helper functions *)

Definition nextIntersectionWith
  `(i : Interval d) `(jid : IntervalId sd) : option nat :=
  firstIntersectionPoint (projT2 (getInterval sd jid)) i.

(** Given a function from intervals to indices ([intervalIndex]), and a
    default function from registers to indices ([registerIndex]), build a
    complete function from registers to indices by looking up the given
    register in the list of assignments, finding the first interval it has
    been assigned to, and then using [intervalIndex] to find the index, if
    any. *)

Definition getRegisterIndex `(st : ScanState sd)
  (intervalIndex : IntervalId sd -> option nat)
  (registerIndex : PhysReg -> option nat)
  (intervals : list (IntervalId sd)) : PhysReg -> option nat :=
  fold_right
    (fun x f => fun r =>
       match assignments sd x with
       | None => f r
       | Some a => if cmp_eq_dec a r then intervalIndex x else f r
       end) registerIndex intervals.

(** Given a function from registers to indices ([registerIndex]), and a
    starting register [start] (the highest register to be considered), look
    through the registers from highest to lowest to find the one with the
    highest associated index, where [None] counts as infinitely high (i.e.,
    unassociated). *)

Function findRegister (registerIndex : PhysReg -> option nat)
  (start : PhysReg) {measure fin_to_nat start}
  : (PhysReg * option nat)%type :=
  match registerIndex start with
  | None => (start, None)
  | Some pos =>
      match pred_fin start with
      | None => (start, Some pos)
      | Some nreg =>
          match findRegister registerIndex nreg with
          | (reg, None) => (reg, None)
          | (reg, Some pos') =>
              if pos <? pos'
              then (reg, Some pos')
              else (reg, Some pos)
          end
      end
  end.
Proof. intros; apply pred_fin_lt; assumption. Qed.

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

Definition cursorFromMorphLen `(cur : ScanStateCursor sd)
  `(n : NextState cur SSMorphLen) : ScanStateCursor (nextDesc n).
Proof.
  destruct sd. destruct cur. simpl in *.
  rapply Build_ScanStateCursor;
  destruct n; simpl in *.
  - apply nextState0.
  - destruct morphProof0.
    destruct nextDesc0.
    simpl in *. omega.
  - auto.
Defined.

Definition cursorFromMorphStLen `(cur : ScanStateCursor sd)
  `(n : NextState cur SSMorphStLen) : ScanStateCursor (nextDesc n) :=
  cursorFromMorphLen cur
    {| nextDesc   := nextDesc n
     ; nextState  := nextState n
     ; morphProof := stlen_is_SSMorphLen _ _ (morphProof n)
     |}.

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
  let st      := curState cur in
  let current := curInterval cur in

  let freeUntilPos' :=
      getRegisterIndex st (fun _ => Some 0) (fun _ => None) (active sd) in
  let intersectingIntervals :=
        filter (fun x => anyRangeIntersects current
                           (projT2 (getInterval sd x)))
               (inactive sd) in
  let freeUntilPos :=
      getRegisterIndex st (nextIntersectionWith current) freeUntilPos'
                       intersectingIntervals in

  (* reg = register with highest freeUntilPos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := findRegister freeUntilPos lastReg in
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
  (* set nextUsePos of all physical registers to maxInt
     for each interval it in active do
       nextUsePos[it.reg] = next use of it after start of current
     for each interval it in inactive intersecting with current do
       nextUsePos[it.reg] = next use of it after start of current *)
  let st      := curState cur in
  let current := curInterval cur in
  let pos     := curPosition cur in

  let nextUsePos' :=
      getRegisterIndex st (nextUseAfter pos) (fun _ => None) (active sd) in
  let intersectingIntervals :=
        filter (fun x => anyRangeIntersects current
                           (projT2 (getInterval sd x)))
               (inactive sd) in
  let nextUsePos :=
      getRegisterIndex st (nextUseAfter pos)
                       nextUsePos' intersectingIntervals in

  (* reg = register with highest nextUsePos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := findRegister nextUsePos lastReg in

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
  let fix go (sd : ScanStateDesc) (st : ScanState sd) ss is pos :=
    match is with
    | nil => ss
    | x :: xs =>
        (* // check for intervals in active that are handled or inactive
           for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it does not cover position then
               move it from active to inactive *)
        let i := projT2 (getInterval sd (projT1 x)) in
        let st1 := if intervalEnd i <? pos
                   then moveActiveToHandled st (projT1 x) (projT2 x)
                   else if negb (intervalCoversPos i pos)
                        then moveActiveToInactive st (projT1 x) (projT2 x)
                        else ss in
        go sd st st1 xs pos
    end in
  go sd st (Build_NextScanState sd st (newSSMorphLen sd))
     (list_membership (active sd)) pos.

Fixpoint checkInactiveIntervals `(st : ScanState sd) pos
  : NextScanState (SSMorphLen sd) :=
  let fix go (sd : ScanStateDesc) (st : ScanState sd) ss is pos :=
    match is with
    | nil => ss
    | x :: xs =>
        (* // check for intervals in inactive that are handled or active
           for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it covers position then
               move it from active to inactive *)
        let i := projT2 (getInterval sd (projT1 x)) in
        let st1 := if intervalEnd i <? pos
                   then moveInactiveToHandled st (projT1 x) (projT2 x)
                   else if intervalCoversPos i pos
                        then moveInactiveToActive st (projT1 x) (projT2 x)
                        else ss in
        go sd st st1 xs pos
    end in
  go sd st (Build_NextScanState sd st (newSSMorphLen sd))
     (list_membership (inactive sd)) pos.

Lemma SSMorphLenLenSt_transitivity
  `( i : SSMorphLen sd0 sd1)
  `( j : SSMorphLen sd1 sd2)
  `( k : SSMorphSt  sd2 sd3) : SSMorphSt sd0 sd3.
Proof.
  constructor;
  destruct i;
  destruct j;
  destruct k.
    transitivity sd1; auto.
    transitivity sd2; auto.
  intuition.
Qed.

Definition handleInterval `(cur : ScanStateCursor sd) : NextState cur SSMorphSt :=
  (* position = start position of current *)
  let position  := curPosition cur in

  (* // check for intervals in active that are handled or inactive
     for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let sp1  := checkActiveIntervals (curState cur) position in
  let Hlt1 := unhandled_nonempty sd (nextDesc sp1) (morphProof sp1)
                                 (curExists cur) in
  let H1   := next_interval_increases (morphProof sp1) in
  let cid1 := transportId H1 (curId cur) in

  (* // check for intervals in inactive that are handled or active
     for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let sp2  := checkInactiveIntervals (nextState sp1) position in
  let Hlt2 := unhandled_nonempty (nextDesc sp1) (nextDesc sp2)
                                 (morphProof sp2) Hlt1 in
  let H2   := next_interval_increases (morphProof sp2) in
  let cid2 := transportId H2 cid1 in

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg
     if current has a register assigned then
       add current to active (done by the helper functions) *)
  let cursor := {| curState   := nextState sp2
                 ; curExists  := Hlt2
                 ; curIntDesc := curIntDesc cur
                 |} in
  let result := fromMaybe (allocateBlockedReg cursor)
                          (tryAllocateFreeReg cursor) in
  {| nextDesc   := nextDesc result
   ; nextState  := nextState result
   ; morphProof :=
       SSMorphLenLenSt_transitivity (morphProof sp1) (morphProof sp2)
                                    (morphProof result)
   |}.

Lemma list_cons_nonzero : forall {a x} {xs l : list a},
  l = x :: xs -> length l > 0.
Proof. intros. rewrite H. simpl. omega. Qed.

(* while unhandled /= { } do
     current = pick and remove first interval from unhandled
     HANDLE_INTERVAL (current) *)

Function linearScan (sd : ScanStateDesc) (st : ScanState sd)
  {measure unhandledExtent sd} : { sd' : ScanStateDesc & ScanState sd' } :=
  match destruct_list (unhandled sd) with
  | inleft (existT x (exist xs H)) =>
    let cursor := {| curState   := st
                   ; curExists  := list_cons_nonzero H
                   ; curIntDesc := projT1 (getInterval sd x)
                   |} in
    match handleInterval cursor with
    | Build_NextScanState sd2 st2 smorph2 => linearScan sd2 st2
    end
  | inright _ => existT _ sd st
  end.
(* We must prove that after every call to handleInterval, the total extent
   of the remaining unhandled intervals is less than it was before. *)
Proof. intros; inversion smorph2; assumption. Defined.

(** * Program graphs *)

Definition VirtReg := nat.

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {
    postOrderTraversal : a
}.

Definition determineIntervals (g : Graph VirtReg)
  : { sd : ScanStateDesc & ScanState sd }.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition allocateRegisters (g : Graph VirtReg) : ScanStateDesc :=
  let (sd,st) := determineIntervals g in projT1 (linearScan sd st).

End MAllocate.