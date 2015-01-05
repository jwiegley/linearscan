Require Import LinearScan.Blocks.
Require Import LinearScan.Lib.

Require Export LinearScan.SSMorph.

Generalizable All Variables.

Require LinearScan.Spec.

Module MAllocate (Mach : Machine).

Include MSSMorph Mach.

Open Scope program_scope.

Definition intersectsWithFixedInterval {pre P} `{HasWork P} (reg : PhysReg) :
  SState pre P P (option nat) :=
  withCursor $ fun sd cur =>
    let int := curIntDetails cur in
    return_ $ vfoldl (fun mx v =>
      option_choose mx
        (if v is Some i
         then intervalIntersectionPoint int.2 i.2
         else None)) None (fixedIntervals sd).

(* Definition assignSpillSlotToCurrent {pre P} `{HasWork P} : *)
(*   SState pre P P unit. *)

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg {pre P} `{W : HasWork P} :
  SState pre P P (option (SState pre P SSMorphSt PhysReg)) :=
  withCursor $ fun sd cur =>
    let current := curInterval cur in

    (* set freeUntilPos of all physical registers to maxInt
       for each interval it in active do
         freeUntilPos[it.reg] = 0
       for each interval it in inactive intersecting with current do
         freeUntilPos[it.reg] = next intersection of it with current *)
    let go n := foldl (fun v p => let: (i, r) := p in vreplace v r (n i)) in
    let freeUntilPos' := go (fun _ => Some 0) (vconst None) (active sd) in
    let intersectingIntervals :=
        filter (fun x => intervalsIntersect current (getInterval (fst x)))
               (inactive sd) in
    let freeUntilPos :=
        go (fun i => intervalIntersectionPoint (getInterval i) current)
           freeUntilPos' intersectingIntervals in

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
          if n == 0
          then None
          else Some (if intervalEnd current < n
                     then success
                     else splitCurrentInterval (Some n) ;;;
                          moveUnhandledToActive reg ;;;
                          return_ reg)
        end in
    return_ maction.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  In either case,
    the change to the [ScanState] must be a productive one. *)
Definition allocateBlockedReg {pre P} `{HasWork P} :
  SState pre P SSMorphSt (option PhysReg) :=
  withCursor $ fun sd cur =>
    let current := curInterval cur in
    let start   := intervalStart current in
    let pos     := curPosition cur in

    (* set nextUsePos of all physical registers to maxInt
       for each interval it in active do
         nextUsePos[it.reg] = next use of it after start of current
       for each interval it in inactive intersecting with current do
         nextUsePos[it.reg] = next use of it after start of current *)
    let go v p := let: (i, r) := p in
        let int := getInterval i in
        let atPos u := pos == uloc u in
        let pos' :=
            match findIntervalUsePos int atPos with
            | Some _ => Some 0
            | None   => nextUseAfter int start
            end in
        vreplace v r pos' in
    let nextUsePos' := foldl go (vconst None) (active sd) in
    let intersectingIntervals :=
        filter (fun x => intervalsIntersect current (getInterval (fst x)))
               (inactive sd) in
    let nextUsePos := foldl go nextUsePos' intersectingIntervals in

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
        | Some n => n < start
        end)
    then
      (* jww (2014-12-01): Need to determine what should happen here. *)
      (* assignSpillSlotToCurrent ;;; *)
      splitCurrentInterval (firstUseReqReg current) ;;;

      mloc <<- intersectsWithFixedInterval reg ;;
      match mloc with
      | Some n => splitCurrentInterval (Some n)
      | None   => return_ tt
      end ;;;
      weakenStHasLenToSt ;;;
      return_ None
    else
      splitAnyInactiveIntervalForReg reg ;;;
      splitActiveIntervalForReg reg pos ;;;

      mloc <<- intersectsWithFixedInterval reg ;;
      match mloc
      with
      | Some n => splitCurrentInterval (Some n) ;;;
                  moveUnhandledToActive reg
      | None   => moveUnhandledToActive reg
      end ;;;
      return_ (Some reg).

Definition morphlen_transport : forall b b',
  SSMorphLen b b' -> IntervalId b -> IntervalId b'.
Proof.
  move=> b b'.
  case. case=> Hdec ? ? /= _.
  exact: (widen_ord _).
Defined.

Definition mt_fst b b' (sslen : SSMorphLen b b')
  (x : IntervalId b * PhysReg) :=
  match x with
  | (xid, reg) => (morphlen_transport b b' sslen xid, reg)
  end.

Notation int_reg sd       := (IntervalId sd * PhysReg)%type.
Definition int_reg_seq sd := seq (int_reg sd).

Definition intermediate_result (sd z : ScanStateDesc) (xs : int_reg_seq z)
  (f : forall sd' : ScanStateDesc, int_reg_seq sd') :=
  { res : {z' : ScanStateDesc | SSMorphLen z z'}
  | (ScanState res.1 /\ SSMorphLen sd res.1)
  & subseq [seq mt_fst z res.1 res.2 i | i <- xs] (f res.1) }.

Program Definition goActive (pos : nat) (sd z : ScanStateDesc)
  (Pz : ScanState z /\ SSMorphLen sd z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (active z)) :
  intermediate_result sd z xs active :=
  (* for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let: conj st sslen := Pz in
  let go i : intermediate_result sd z xs active :=
    let Hin : x \in active z := @in_subseq_sing _ _ _ x xs _ Hsub in
    let ss := if intervalEnd i < pos
              then moveActiveToHandled st Hin
              else if ~~ intervalCoversPos i pos
                   then moveActiveToInactive st Hin
                   else exist2 _ _ z st (newSSMorphLen z) in
    match ss with
    | exist2 sd' st' sslen' =>
        exist2 _ _ (exist _ sd' sslen')
               (conj st' (transitivity sslen sslen')) _
    end in
  go (getInterval (fst x)).
Obligation 2.
  move: Heq_ss.
  case: (iend (vnth (intervals z) o).1 < pos).
    rewrite /moveActiveToHandled /=.
    invert as [H1]; subst; simpl.
    rewrite /mt_fst /morphlen_transport /=.
    case: sslen'.
    case=> [Hinc _ _ _ _].
    rewrite map_widen_ord_refl.
    exact: subseq_cons_rem.
  case: (~~ (ibeg (vnth (intervals z) o).1 <=
             pos < iend (vnth (intervals z) o).1)).
    rewrite /moveActiveToInactive /=.
    invert as [H1]; subst; simpl.
    rewrite /mt_fst /morphlen_transport /=.
    case: sslen'.
    case=> [Hinc _ _ _ _].
    rewrite map_widen_ord_refl.
    exact: subseq_cons_rem.
  invert as [H1]; subst; simpl.
  rewrite /mt_fst /morphlen_transport /=.
  case: sslen'.
  case=> [Hinc _ _ _ _].
  rewrite map_widen_ord_refl.
  exact: subseq_impl_cons.
Qed.

Definition checkActiveIntervals {pre} (pos : nat) :
  SState pre SSMorphLen SSMorphLen unit :=
  withScanStatePO $ fun sd (st : ScanState sd) =>
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let res : {sd' : ScanStateDesc | ScanState sd' /\ SSMorphLen sd sd'} :=
        @dep_foldl_inv
          ScanStateDesc (fun sd' => ScanState sd' /\ SSMorphLen sd sd')
          SSMorphLen _ sd (conj st (newSSMorphLen sd))
          (active sd) (size (active sd)) (eq_refl _)
          active (subseq_refl _) mt_fst (goActive pos sd) in
    let: exist sd' (conj st' H) := res in
    IState.iput SSError {| thisDesc  := sd'
                         ; thisHolds := H
                         ; thisState := st' |}.

Program Definition moveInactiveToActive' `(st : ScanState z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (inactive z))
  (Hin : x \in inactive z) :
  SSError +
  { sd' : ScanStateDesc | ScanState sd'
  & { sslen : SSMorphLen z sd'
    | subseq [seq mt_fst z sd' sslen i | i <- xs]
             (inactive sd')
    }
  } :=
  match snd x \notin [seq snd i | i <- active z] with
  | true  =>
      match moveInactiveToActive st Hin _ with
      | exist2 sd' st' sslen' =>
          inr (exist2 _ _ sd' st' (exist _ sslen' _))
      end
  | false => inl (ERegisterAssignmentsOverlap (snd x : PhysReg))
  end.
Obligation 2.
  rewrite /moveActiveToInactive /mt_fst /morphlen_transport /=.
  case: sslen'; case=> [Hinc _ _ _ _].
  rewrite map_widen_ord_refl.
  exact: subseq_cons_rem.
Defined.

Program Definition goInactive (pos : nat) (sd z : ScanStateDesc)
  (Pz : ScanState z /\ SSMorphLen sd z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (inactive z)) :
  SSError + intermediate_result sd z xs inactive :=
  (* for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let: conj st sslen := Pz in
  match getInterval (fst x)
  return SSError + intermediate_result sd z xs inactive with
  | i =>
    let Hin : x \in inactive z :=
        @in_subseq_sing _ _ _ x xs _ Hsub in
    let f (sd'    : ScanStateDesc)
          (st'    : ScanState sd')
          (sslen' : SSMorphLen z sd')
          (Hsub'  : subseq [seq mt_fst z sd' sslen' i | i <- xs]
                           (inactive sd')) :=
        inr (exist2 _ _ (exist _ sd' sslen')
                    (conj st' (transitivity sslen sslen')) Hsub') in
    if intervalEnd i < pos
    then match moveInactiveToHandled st Hin with
         | exist2 sd' st' sslen' =>
             f sd' st' sslen' _
         end
    else if intervalCoversPos i pos
         then match moveInactiveToActive' st x xs Hsub Hin with
              | inl err => inl err
              | inr (exist2 sd' st' (exist sslen' Hsub')) =>
                  f sd' st' sslen' Hsub'
              end
         else f z st (newSSMorphLen z) _
  end.
Obligation 2.
  rewrite /mt_fst /morphlen_transport /=.
  case: sslen'.
  case=> [Hinc _ _ _ _].
  rewrite map_widen_ord_refl.
  exact: subseq_cons_rem.
Defined.
Obligation 3.
  rewrite /mt_fst /morphlen_transport /=.
  rewrite map_widen_ord_refl.
  exact: subseq_impl_cons.
Defined.

Definition checkInactiveIntervals {pre} (pos : nat) :
  SState pre SSMorphLen SSMorphLen unit :=
  withScanStatePO $ fun sd (st : ScanState sd) =>
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let eres : SSError + {sd' : ScanStateDesc | ScanState sd' /\ SSMorphLen sd sd'} :=
        @dep_foldl_invE SSError
          ScanStateDesc (fun sd' => ScanState sd' /\ SSMorphLen sd sd')
          SSMorphLen _ sd (conj st (newSSMorphLen sd))
          (inactive sd) (size (inactive sd)) (eq_refl _)
          inactive (subseq_refl _) mt_fst (goInactive pos sd) in
    match eres with
    | inl err => IState.ierr SSError err
    | inr (exist sd' (conj st' H)) =>
        IState.iput SSError {| thisDesc  := sd'
                             ; thisHolds := H
                             ; thisState := st' |}
    end.

Definition handleInterval {pre} :
  SState pre SSMorphHasLen SSMorphSt (option PhysReg) :=
  (* position = start position of current *)
  withCursor $ fun _ cur =>
    let position := curPosition cur in
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
    | Some x => IEndo.imap (@Some _) x
    | None   => allocateBlockedReg
    end.

Require Import Coq.Program.Wf.

(* Walk through all the intervals which had been defined previously as the
   [unhandled] list, and use those to determine register allocations.  The
   final result will be a [ScanState] whose [handled] list represents the
   final allocations for each interval. *)
Program Fixpoint walkIntervals {sd : ScanStateDesc} (st : ScanState sd)
  {measure (unhandledExtent sd)} : SSError + ScanStateSig :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match List.destruct_list (unhandled sd) with
  | inleft (existT x (exist xs H)) =>
    let ssinfo := {| thisDesc  := sd
                   ; thisHolds := newSSMorphHasLen (list_cons_nonzero H)
                   ; thisState := st
                   |} in
    match IState.runIState SSError handleInterval ssinfo with
    | inl err => inl err
    | inr (_, ssinfo') => walkIntervals (thisState ssinfo')
    end
  | inright _ => inr (packScanState st)
  end.
Obligation 1.
  (* We must prove that after every call to [handleInterval], the total extent
     of the remaining unhandled intervals is less than it was before. *)
  by intros; clear; case: ssinfo' => ? /= [? /ltP].
Qed.

End MAllocate.