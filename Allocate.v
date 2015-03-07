Require Import LinearScan.Lib.
Require Import LinearScan.IState.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.ScanState.
Require Import LinearScan.Morph.
Require Import LinearScan.Cursor.
Require Import LinearScan.Spec.
Require Import LinearScan.Split.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Allocate.

Variable maxReg : nat.          (* max number of registers *)
Hypothesis registers_exist : maxReg > 0.
Definition PhysReg : predArgType := 'I_maxReg.

Open Scope program_scope.

Definition intersectsWithFixedInterval {pre} (reg : PhysReg) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) (option oddnum) :=
  withCursor (maxReg:=maxReg) $ fun sd cur =>
    let int := curIntDetails cur in
    return_ $ vfoldl (fun mx v =>
      option_choose mx
        (if v is Some i
         then intervalIntersectionPoint int.2 i.2
         else None)) None (fixedIntervals sd).

Definition updateRegisterPos {n : nat} (v : Vec (option oddnum) n)
  (r : 'I_n) (p : option oddnum) : Vec (option oddnum) n :=
  match p with
  | None => v
  | Some x =>
      vreplace v r
        (Some (match vnth v r with
               | Some n => if n.1 < x.1 then n else x
               | None   => x
               end))
  end.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg {pre} :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg)
    (option (SState pre (@SSMorphHasLen maxReg) (@SSMorph maxReg) PhysReg)) :=
  withCursor (maxReg:=maxReg) $ fun sd cur =>
    let current := curInterval cur in
    let pos     := curPosition cur in

    (* set freeUntilPos of all physical registers to maxInt
       for each interval it in active do
         freeUntilPos[it.reg] = 0
       for each interval it in inactive intersecting with current do
         freeUntilPos[it.reg] = next intersection of it with current *)
    let go f v p := let: (i, r) := p in updateRegisterPos v r (f i) in
    let freeUntilPos' :=
        foldl (go (fun _ => Some odd1)) (vconst None) (active sd) in
    let intersectingIntervals :=
        filter (fun x => intervalsIntersect current (getInterval (fst x)))
               (inactive sd) in
    let freeUntilPos'' :=
        foldl (go (fun i => intervalIntersectionPoint (getInterval i) current))
          freeUntilPos' intersectingIntervals in
    let freeUntilPos :=
        vfoldl_with_index (fun reg acc (mint : option IntervalSig) =>
          if mint is Some int
          then updateRegisterPos acc reg
                 (intervalIntersectionPoint int.2 current)
          else acc) freeUntilPos'' (fixedIntervals sd) in

    (* reg = register with highest freeUntilPos *)
    (* mres = highest use position of the found register *)
    let (reg, mres) := registerWithHighestPos registers_exist freeUntilPos in

    (** [moveUnhandledToActive] not only moves an [IntervalId] from the
        [unhandled] list to the [active] list in the current [ScanStateDesc],
        it also assigns a register to the newly active interval that can be
        accessed by calling [getAssignment]. *)
    let success := moveUnhandledToActive reg ;;; return_ reg in

    return_ $
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
        if n.1 <= pos
        then None
        else @Some _ $
          if intervalEnd current < n.1
          then success
          else splitCurrentInterval (BeforePos n) ;;;
               success
      end.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  In either case,
    the change to the [ScanState] must be a productive one. *)
Definition allocateBlockedReg {pre} :
  SState pre (@SSMorphHasLen maxReg) (@SSMorph maxReg) (option PhysReg) :=
  withCursor (maxReg:=maxReg) $ fun sd cur =>
    let current := curInterval cur in
    let start   := intervalStart current in
    let pos     := curPosition cur in
    let posOdd  := curPosition_odd cur in

    (* set nextUsePos of all physical registers to maxInt
       for each interval it in active do
         nextUsePos[it.reg] = next use of it after start of current
       for each interval it in inactive intersecting with current do
         nextUsePos[it.reg] = next use of it after start of current *)
    let go {n : nat} (v : Vec (option oddnum) n) (p : IntervalSig * 'I_n) :=
        let: (int, r) := p in
        let atPos u := pos == uloc u in
        let pos' :=
            (* In calculating the highest use position of this register, if we
               know that it is being used at the current position, then it
               cannot be spilled there, and so we try to take it out of the
               running by returning one. *)
            match findIntervalUsePos int.2 atPos with
            | Some _ => Some odd1
            | None   => nextUseAfter int.2 start
            end in
        updateRegisterPos v r pos' in

    let resolve xs := [seq (packInterval (getInterval (fst i)), snd i)
                      | i <- xs] in
    let nextUsePos' := foldl go (vconst None) (resolve (active sd)) in
    let intersectingIntervals : seq (IntervalSig * PhysReg) :=
        filter (fun x => intervalsIntersect current (fst x).2)
               (resolve (inactive sd)) ++
        vfoldl_with_index (fun reg acc mint =>
          if mint is Some int
          then if intervalsIntersect current int.2
               then (int, reg) :: acc
               else acc
          else acc) [::] (fixedIntervals sd) in
    let nextUsePos := foldl go nextUsePos' intersectingIntervals in

    (* reg = register with highest nextUsePos *)
    (* mres = highest use position of the found register *)
    let (reg, mres) := registerWithHighestPos registers_exist nextUsePos in

    if (match mres with
        | None   => false
        | Some n =>
            n.1 < if lookupUsePos current (fun u => pos <= uloc u)
                    is Some (nextUse; _)
                  then nextUse.1
                  else intervalEnd current
        end)
    then
      (* if first usage of current is after nextUsePos[reg] then
           // all other intervals are used before current, so it is best
           // to spill current itself
           assign spill slot to current
           split current before its first use position that requires a
             register *)
      let p := firstUseReqRegOrEnd current in
      splitCurrentInterval (BeforePos p) ;;;

      (* // make sure that current does not intersect with
         // the fixed interval for reg
         if current intersects with the fixed interval for reg then
           split current before this intersection *)
      (* mloc <<- intersectsWithFixedInterval reg ;; *)
      (* match mloc with *)
      (* | Some n => splitCurrentInterval (BeforePos n) (Some reg) *)
      (* | None   => return_ tt *)
      (* end ;;; *)

      (* The allocation failed, so we had to spill some part of the current
         interval instead. *)
      @moveUnhandledToHandled maxReg pre ;;;
      return_ None
    else
      (* // spill intervals that currently block reg
         current.reg = reg
         split active interval for reg at position
         split any inactive interval for reg at the end of its lifetime hole *)
      let oddpos := (pos; posOdd) in
      splitAnyInactiveIntervalForReg reg oddpos ;;;
      splitActiveIntervalForReg reg oddpos ;;;

      (* The remaining part of these active and inactive intervals go back
         onto the unhandled list; the former part goes onto the inact list. *)

      (* // make sure that current does not intersect with
         // the fixed interval for reg
         if current intersects with the fixed interval for reg then
           split current before this intersection *)
      (* jww (2015-01-30): What if the fixed interval begins at the current
         position? *)
      mloc <<- intersectsWithFixedInterval reg ;;
      match mloc with
      | Some n => splitCurrentInterval (BeforePos n)
      | None   => return_ tt
      end ;;;

      moveUnhandledToActive reg ;;;
      return_ $ Some reg.

Definition morphlen_transport {b b'} :
  @SSMorphLen maxReg b b' -> IntervalId b -> IntervalId b'.
Proof.
  case. case=> ? ?.
  exact: (widen_ord _).
Defined.

Definition mt_fst b b' (sslen : SSMorphLen b b')
  (x : IntervalId b * PhysReg) :=
  let: (xid, reg) := x in (morphlen_transport sslen xid, reg).

Notation int_reg sd := (@IntervalId maxReg sd * PhysReg)%type.
Definition int_reg_seq sd := seq (int_reg sd).

Definition intermediate_result (sd z : ScanStateDesc maxReg)
  (xs : int_reg_seq z)
  (f : forall sd' : ScanStateDesc maxReg, int_reg_seq sd') :=
  { res : {z' : ScanStateDesc maxReg | SSMorphLen z z'}
  | (ScanState InUse res.1 /\ SSMorphLen sd res.1)
  & subseq [seq mt_fst res.2 i | i <- xs] (f res.1) }.

Program Definition goActive (pos : nat) (sd z : ScanStateDesc maxReg)
  (Pz : ScanState InUse z /\ SSMorphLen sd z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (active z)) :
  intermediate_result sd xs (@active maxReg) :=
  (* for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let: conj st sslen := Pz in
  let go i : intermediate_result sd xs (@active maxReg) :=
    let Hin : x \in active z := @in_subseq_sing _ _ _ x xs _ Hsub in
    let ss := if intervalEnd i < pos
              then moveActiveToHandled st Hin
              else if ~~ posWithinInterval i pos
                   then moveActiveToInactive st Hin
                   else exist2 _ _ z st (newSSMorphLen z) in
    match ss with
    | exist2 sd' st' sslen' =>
        exist2 _ _ (sd'; sslen') (conj st' (transitivity sslen sslen')) _
    end in
  go (getInterval (fst x)).
Obligation 2.
  move: Heq_ss.

  case: (iend (vnth (intervals z) i0).1 < pos).
    rewrite /moveActiveToHandled /=.
    invert as [H1]; subst; simpl.
    rewrite /mt_fst /morphlen_transport /=.
    case: sslen'.
    case=> [? _].
    rewrite map_widen_ord_refl.
    exact: subseq_cons_rem.

  case: (~~ (ibeg (vnth (intervals z) i0).1 <=
             pos < iend (vnth (intervals z) i0).1)).
    rewrite /moveActiveToInactive /=.
    invert as [H1]; subst; simpl.
    rewrite /mt_fst /morphlen_transport /=.
    case: sslen'.
    case=> [? _].
    rewrite map_widen_ord_refl.
    exact: subseq_cons_rem.

  invert as [H1]; subst; simpl.
  rewrite /mt_fst /morphlen_transport /=.
  case: sslen'.
  case=> [? _].
  rewrite map_widen_ord_refl.
  exact: subseq_impl_cons.
Qed.

Definition checkActiveIntervals {pre} (pos : nat) :
  SState pre (@SSMorphLen maxReg) (@SSMorphLen maxReg) unit :=
  withScanStatePO (maxReg:=maxReg) $ fun sd (st : ScanState InUse sd) =>
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let res : { sd' : ScanStateDesc maxReg
              | ScanState InUse sd' /\ SSMorphLen sd sd' } :=
        @dep_foldl_inv (ScanStateDesc maxReg)
          (fun sd' => ScanState InUse sd' /\ SSMorphLen sd sd')
          (@SSMorphLen maxReg) _ sd (conj st (newSSMorphLen sd))
          (active sd) (size (active sd)) (eq_refl _)
          (@active maxReg) (subseq_refl _) mt_fst (@goActive pos sd) in
    let: exist sd' (conj st' H) := res in
    IState.iput SSError {| thisDesc  := sd'
                         ; thisHolds := H
                         ; thisState := st' |}.

Program Definition moveInactiveToActive' `(st : ScanState InUse z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (inactive z))
  (Hin : x \in inactive z) :
  SSError +
  { sd' : ScanStateDesc maxReg | ScanState InUse sd'
  & { sslen : SSMorphLen z sd'
    | subseq [seq mt_fst sslen i | i <- xs] (inactive sd')
    }
  } :=
  match snd x \notin [seq snd i | i <- active z] with
  | true  =>
      match moveInactiveToActive st Hin _ with
      | exist2 sd' st' sslen' =>
          inr (exist2 _ _ sd' st' (sslen'; _))
      end
  | false => inl (ERegisterAssignmentsOverlap (snd x : PhysReg))
  end.
Obligation 2.
  rewrite /moveActiveToInactive /mt_fst /morphlen_transport /=.
  case: sslen'; case=> [? _].
  rewrite map_widen_ord_refl.
  exact: subseq_cons_rem.
Defined.

Program Definition goInactive (pos : nat) (sd z : ScanStateDesc maxReg)
  (Pz : ScanState InUse z /\ SSMorphLen sd z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (inactive z)) :
  SSError + intermediate_result sd xs (@inactive maxReg) :=
  (* for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let: conj st sslen := Pz in
  match getInterval (fst x)
  return SSError + intermediate_result sd xs (@inactive maxReg) with
  | i =>
    let Hin : x \in inactive z :=
        @in_subseq_sing _ _ _ x xs _ Hsub in
    let f (sd'    : ScanStateDesc maxReg)
          (st'    : ScanState InUse sd')
          (sslen' : SSMorphLen z sd')
          (Hsub'  : subseq [seq mt_fst sslen' i | i <- xs]
                           (inactive sd')) :=
        inr (exist2 _ _ (sd'; sslen')
                    (conj st' (transitivity sslen sslen')) Hsub') in
    if intervalEnd i < pos
    then match moveInactiveToHandled st Hin with
         | exist2 sd' st' sslen' =>
             f sd' st' sslen' _
         end
    else if posWithinInterval i pos
         then match moveInactiveToActive' st Hsub Hin with
              | inl err => inl err
              | inr (exist2 sd' st' (exist sslen' Hsub')) =>
                  f sd' st' sslen' Hsub'
              end
         else f z st (newSSMorphLen z) _
  end.
Obligation 2.
  rewrite /mt_fst /morphlen_transport /=.
  case: sslen'.
  case=> [? _].
  rewrite map_widen_ord_refl.
  exact: subseq_cons_rem.
Defined.
Obligation 3.
  rewrite /mt_fst /morphlen_transport /=.
  rewrite map_widen_ord_refl.
  exact: subseq_impl_cons.
Defined.

Definition checkInactiveIntervals {pre} (pos : nat) :
  SState pre (@SSMorphLen maxReg) (@SSMorphLen maxReg) unit :=
  withScanStatePO (maxReg:=maxReg) $ fun sd (st : ScanState InUse sd) =>
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let eres : SSError + {sd' : ScanStateDesc maxReg
                         | ScanState InUse sd' /\ SSMorphLen sd sd'} :=
        @dep_foldl_invE SSError (ScanStateDesc maxReg)
          (fun sd' => ScanState InUse sd' /\ SSMorphLen sd sd')
          (@SSMorphLen maxReg) _ sd (conj st (newSSMorphLen sd))
          (inactive sd) (size (inactive sd)) (eq_refl _)
          (@inactive maxReg) (subseq_refl _) mt_fst (@goInactive pos sd) in
    match eres with
    | inl err => error_ err
    | inr (exist sd' (conj st' H)) =>
        IState.iput SSError {| thisDesc  := sd'
                             ; thisHolds := H
                             ; thisState := st' |}
    end.

Definition handleInterval {pre} :
  SState pre (@SSMorphHasLen maxReg) (@SSMorph maxReg) (option PhysReg) :=
  (* position = start position of current *)
  withCursor (maxReg:=maxReg) $ fun _ cur =>
    let current  := curInterval cur in
    let position := curPosition cur in

    (* Remove any empty intervals from the unhandled list *)
    if firstUsePos current is None
    then @moveUnhandledToHandled maxReg pre ;;; return_ None
    else
      (* // check for intervals in active that are handled or inactive *)
      liftLen (fun sd => @checkActiveIntervals sd position) ;;;
      (* // check for intervals in inactive that are handled or active *)
      liftLen (fun sd => @checkInactiveIntervals sd position) ;;;

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

Definition finalizeScanState `(st : ScanState InUse sd) (finalPos : nat) :
  ScanStateDesc maxReg :=
  match (checkActiveIntervals   finalPos ;;;
         checkInactiveIntervals finalPos)
          {| thisDesc  := sd
           ; thisHolds := newSSMorphLen sd
           ; thisState := st |} with
  | inl _ => sd
  | inr (tt, ss) => thisDesc ss
  end.

Require Import Coq.Program.Wf.
(* Include Trace. *)

(* Walk through all the intervals which had been defined previously as the
   [unhandled] list, and use those to determine register allocations.  The
   final result will be a [ScanState] whose [handled] list represents the
   final allocations for each interval. *)
Fixpoint walkIntervals `(st : ScanState InUse sd) (positions : nat) :
  (SSError * ScanStateSig maxReg InUse) + ScanStateSig maxReg InUse :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  if positions is S n
  then let fix go count ss :=
    (* trace "walkIntervals: go" $ *)
    if count is S cnt
    then
      (* trace "walkIntervals: count > 0" $ *)
      match handleInterval ss with
      | inl err => inl (err, packScanState (thisState ss))
      | inr (_, ss') =>
        (* A [ScanState InUse] may not insert new unhandled intervals at the
           same position as [curPos], and so even though [unhandled sd] may
           have been changed by the call to [handleInterval], it will not
           have changed it with respect to subsequent intervals at the same
           position.  Thus, we may safely make the assumption that if
           another interval at the same position exists in [xs], then it
           will also be there in [unhandled sd] when [go] is next
           evaluated. *)
        match strengthenHasLen (thisHolds ss') with
        | None => if cnt is S _
                  then inl (EUnexpectedNoMoreUnhandled,
                            packScanState (thisState ss'))
                  else inr ss'
        | Some holds' =>
            go cnt {| thisDesc  := thisDesc ss'
                    ; thisHolds := holds'
                    ; thisState := thisState ss' |}
        end
      end
    else inr {| thisDesc  := thisDesc ss
              ; thisHolds := weakenHasLen (thisHolds ss)
              ; thisState := thisState ss |} in

    (* trace "walkIntervals: destructing list" $ *)
    match List.destruct_list (unhandled sd) with
    | inright _ => inr (packScanState st)
    | inleft (existT (_, pos) (_; H)) =>
        (* trace "walkIntervals: found item" $ *)
        match go (count (fun x => snd x == pos) (unhandled sd))
                 {| thisDesc  := sd
                  ; thisHolds := newSSMorphHasLen (list_cons_nonzero H)
                  ; thisState := st |} with
        | inl err => inl err
        | inr ss  => walkIntervals (thisState ss) n
        end
    end

  (* jww (2015-01-20): Should be provably impossible *)
  else inl (EFuelExhausted, packScanState st).

End Allocate.