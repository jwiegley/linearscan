Set Warnings "-notation-overridden".
Set Warnings "-spurious-ssr-injection".

Require Import LinearScan.Lib.
Require Import LinearScan.Context.
Require Import LinearScan.UsePos.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.ScanState.
Require Import LinearScan.Morph.
Require Import LinearScan.Cursor.
Require Import LinearScan.Spec.
Require Import LinearScan.Spill.
Require Import LinearScan.Split.
Require Import Coq.Program.Wf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Allocate.

Variable maxReg : nat.          (* max number of registers *)
Hypothesis registers_exist : maxReg > 0.
Definition PhysReg := 'I_maxReg.

Open Scope program_scope.

Definition intersectsWithFixedInterval {pre} (reg : PhysReg) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) (option nat) :=
  withCursor (maxReg:=maxReg) $ fun sd cur =>
    ipure $ if vnth (fixedIntervals sd) reg is Some i
            then intervalIntersectsWithSubrange (curIntDetails cur).1 i.1
            else None.

Definition updateRegisterPos (v : Vec (option nat) maxReg)
  (r : PhysReg) (p : option nat) : Vec (option nat) maxReg :=
  match p with
  | None => v
  | Some x => vreplace v r (Some (match vnth v r with
                                  | Some n => if n < x then n else x
                                  | None   => x
                                  end))
  end.

Definition findEligibleRegister (sd : ScanStateDesc maxReg)
  `(current : Interval d) xs : PhysReg * option nat :=
  (* Make sure that if there's a fixed interval that intersection with the
     current interval, that we indicate that the register is only free up
     until that point. *)
  let: (xs, fixedAndIntersects) :=
    vfoldl_with_index (fun reg acc (mint : option IntervalSig) =>
      let: (fup, fai) := acc in
      if mint is Some int
      then let op := intervalIntersectsWithSubrange current int.2 in
           (updateRegisterPos fup reg op, vreplace fai reg (isSome op))
      else acc) (xs, vconst false) (fixedIntervals sd) in
  registerWithHighestPos registers_exist fixedAndIntersects xs.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg {pre} :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg)
    (option (SState pre (@SSMorphHasLen maxReg) (@SSMorph maxReg) PhysReg)) :=
  withCursor (maxReg:=maxReg) $ fun sd cur =>
    let current := curInterval cur in

    (* set freeUntilPos of all physical registers to maxInt
       for each interval it in active do
         freeUntilPos[it.reg] = 0
       for each interval it in inactive intersecting with current do
         freeUntilPos[it.reg] = next intersection of it with current *)
    let go f v p := let: (i, r) := p in updateRegisterPos v r (f i) in
    let actives := foldl (go (fun _ => Some 0)) (vconst None) (active sd) in
    let freeUntilPos :=
        foldl (go (fun i => intervalsIntersect current (getInterval i)))
          actives (inactive sd) in

    (* reg = register with highest freeUntilPos *)
    (* mres = highest use position of the found register *)
    let (reg, mres) := findEligibleRegister sd current freeUntilPos in

    (** [moveUnhandledToActive] not only moves an [IntervalId] from the
        [unhandled] list to the [active] list in the current [ScanStateDesc],
        it also assigns a register to the newly active interval that can be
        accessed by calling [getAssignment]. *)
    let success := moveUnhandledToActive reg ;;; ipure reg in

    let cid := curId cur in
    context (ETryAllocateFreeReg reg mres (fst cid)) $
      ipure $
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
          if n <= intervalStart current
          then None
          else @Some _ $
            if intervalEnd current < n
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
    let pos     := intervalStart current in

    (* set nextUsePos of all physical registers to maxInt
       for each interval it in active do
         nextUsePos[it.reg] = next use of it after start of current
       for each interval it in inactive intersecting with current do
         nextUsePos[it.reg] = next use of it after start of current *)
    let go (v : Vec (option nat) maxReg) (p : IntervalSig * PhysReg) :=
        let: (int, reg) := p in
        let atPos u := (pos == uloc u) && regReq u in
        let pos' :=
            (* In calculating the highest use position of this register, if we
               know that it is being used at the current position, then it
               cannot be spilled there, and so we try to take it out of the
               running by returning one. *)
            match findIntervalUsePos int.2 atPos with
            | Some _ => Some 0
            | None   => nextUseAfter int.2 pos
            end in
        updateRegisterPos v reg pos' in

    let resolve xs :=
        [seq (packInterval (getInterval (fst i)), snd i) | i <- xs] in
    let actives := foldl go (vconst None) (resolve (active sd)) in
    let nextUsePos'' :=
        foldl go actives (filter (fun x => intervalsIntersect current (fst x).1)
                                 (resolve (inactive sd))) in

    (* reg = register with highest nextUsePos *)
    (* mres = highest use position of the found register *)
    let (reg, mres) := findEligibleRegister sd current nextUsePos'' in

    let cid := curId cur in
    context (EAllocateBlockedReg reg mres (fst cid)) $
      if (match mres with
          | None   => false
          | Some n =>
              n < if lookupUsePos current (fun u => pos <= uloc u)
                       is Some (nextUse; _)
                  then nextUse
                  else intervalEnd current
          end)
      then
        (* if first usage of current is after nextUsePos[reg] then
             // all other intervals are used before current, so it is best
             // to spill current itself
             assign spill slot to current
             split current before its first use position that requires a
               register *)
        @spillCurrentInterval maxReg pre ;;;

        (* // make sure that current does not intersect with
           // the fixed interval for reg
           if current intersects with the fixed interval for reg then
             split current before this intersection *)

        (* The allocation failed, so we had to spill some part of the current
           interval instead. *)
        ipure None
      else
        (* // spill intervals that currently block reg
           current.reg = reg
           split active interval for reg at position
           split any inactive interval for reg at the end of its lifetime
             hole *)
        splitAnyInactiveIntervalForReg reg pos ;;;
        splitActiveIntervalForReg reg pos ;;;

        (* The remaining part of these active and inactive intervals go back
           onto the unhandled list; the former part goes onto the inact list. *)

        (* // make sure that current does not intersect with
           // the fixed interval for reg
           if current intersects with the fixed interval for reg then
             split current before this intersection *)
        mloc <<- intersectsWithFixedInterval reg ;;;
        match mloc with
        | Some n => context (EIntersectsWithFixedInterval n reg) $
                      splitCurrentInterval (BeforePos n)
        | None   => ipure tt
        end ;;;

        moveUnhandledToActive reg ;;;
        ipure $ Some reg.

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

Program Definition goActive (pos : nat) (sd : ScanStateDesc maxReg)
  (e : seq SSTrace) (z : ScanStateDesc maxReg)
  (Pz : ScanState InUse z /\ SSMorphLen sd z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (active z)) :
  seq SSTrace + intermediate_result sd xs (@active maxReg) :=
  (* for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let: conj st sslen := Pz in
  let i := getInterval (fst x) in
  let Hin : x \in active z := @in_subseq_sing _ _ _ x xs _ Hsub in
  let eres :=
    if intervalEnd i < pos
    then
      if prop (verifyNewHandled z i (snd x)) isn't Some Hreq
      then let: (p1, p2) := x in
           inl (ERegisterAssignmentsOverlap p2 p1 1 :: e)
      else let: exist2 x H1 H2 :=
             moveActiveToHandled st Hin Hreq (spilled:=false) in
           inr (exist2 _ _ x H1 (proj1 H2))
    else inr $ if ~~ posWithinInterval i pos
               then moveActiveToInactive st Hin
               else exist2 _ _ z st (newSSMorphLen z) in
  match eres with
  | inl err => inl err
  | inr (exist2 sd' st' sslen') =>
      inr (exist2 _ _ (sd'; sslen')
                  (conj st' (transitivity sslen sslen')) _)
  end.
Next Obligation.
  move: Heq_eres.

  case: (iend (vnth (intervals z) i).1 < pos);
  case: (prop (verifyNewHandled z (vnth (intervals z) i).1 p)) => a;
  try discriminate.

  - rewrite /moveActiveToHandled /=.
    invert as [H1]; subst; simpl.
    rewrite /mt_fst /morphlen_transport /=.
    case: sslen'.
    case=> [[?] _].
    rewrite map_widen_ord_refl.
    exact: subseq_cons_rem.

  - case: (~~ (ibeg (vnth (intervals z) i).1
             <= pos < iend (vnth (intervals z) i).1)).
      rewrite /moveActiveToInactive /=.
      invert as [H1]; subst; simpl.
      rewrite /mt_fst /morphlen_transport /=.
      case: sslen'.
      case=> [[?] _].
      rewrite map_widen_ord_refl.
      exact: subseq_cons_rem.

    invert as [H1]; subst; simpl.
    rewrite /mt_fst /morphlen_transport /=.
    case: sslen'.
    case=> [[?] _].
    rewrite map_widen_ord_refl.
    apply: subseq_impl_cons.
    exact Hsub.

  - case: (~~ (ibeg (vnth (intervals z) i).1
             <= pos < iend (vnth (intervals z) i).1)) in a *.
      inv a.
      rewrite /mt_fst /morphlen_transport /=.
      case: sslen'.
      case=> [[?] _].
      rewrite map_widen_ord_refl.
      exact: subseq_cons_rem.
    inv a.
    rewrite /mt_fst /morphlen_transport /=.
    case: sslen'.
    case=> [[?] _].
    rewrite map_widen_ord_refl.
    apply: subseq_impl_cons.
    exact Hsub.
Qed.

(* This rather excessively complicated, dependent fold function is needed in
   order to walk through a list of intervals of a [ScanState] (which have a
   type dependent on that [ScanState]), while at the same time mutating the
   same [ScanState] and adjusting the type of the remainder of the interval
   list, such that it is known to still have a relationship with the new
   [ScanState]. *)
Program Fixpoint dep_foldl_invE
  {errType : Type}              (* the short-circuiting error type *)
  {A : Type}                    (* the value being mutated through the fold *)
  {P : A -> Prop}               (* inductive predicate to be maintained on A *)
  {R : A -> A -> Prop}          (* a relation on A that must be preserved *)
  {E : A -> eqType}             (* type of the elements we are folding over *)
  (b : A)                       (* the initial state value *)
  (Pb : P b)                    (* predicate on the initial state value *)
  (v : seq (E b))               (* list of elements from the initial state *)

  (n : nat)                     (* the length of this list (as a [nat]) *)
  (* The reason to [nat] rather than [size v] is that the type of v changes
     with each iteration of the fold, which confuses [Program Fixpoint] enough
     that it fails to compute the final proof term even after ten minutes. *)

  (Hn : n == size v)            (* witness that [length == size v] *)
  (Q : forall x : A, seq (E x)) (* function that can determine [v] from [b] *)
  (Hsub : subseq v (Q b))       (* a proof that [v] is a subseq of [Q b] *)

  (F : forall (b b' : A) (Rbb' : R b b'), E b -> E b')
                                (* transports element types between states *)

  (* The fold function [f] takes an intermediate state, a witness for the
     inductive predicate on that state, an element from the initial list which
     is known to be related to that state (and whose type has been transported
     to relate to that state), the list of remaining elements to be processed
     by the fold, and proof that this element and remaining list are at least
     a subsequence of the state.
         The expected result is a new state, proof that this new state relates
     to the incoming state in terms of [R] (which must be transitive), proof
     that the inductive predicate holds for this new state, and proof that the
     transported remainder [xs] is also a subsequence of the list determined
     by [Q] from the new state. *)
  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)),
         subseq (x :: xs) (Q z)
           -> errType +
              { res : { z' : A | R z z' }
              | P res.1 & subseq (map (F z res.1 res.2) xs) (Q res.1) })

  (* The fold is done when [n] reaches zero *)
  {struct n} :
  (* The result is a final, inductively predicated state *)
  errType + { b' : A | P b' } :=
  match (v, n) with
  | (y :: ys, S n') =>
      match f b Pb y ys Hsub with
      | inl err => inl err
      | inr (exist2 (exist b' Rbb') Pb' Hsub') =>
          let ys' := map (F b b' Rbb') ys in
          @dep_foldl_invE errType A P R E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => inr (exist P b Pb)
  end.
Obligation 2.
  first [ inversion Heq_anonymous;
          subst;
          clear Heq_anonymous0;
          move: eqSS Hn => /= -> /eqP ->;
          by rewrite size_map
        | inversion Heq_anonymous0;
          subst;
          clear Heq_anonymous;
          move: eqSS Hn => /= -> /eqP ->;
          by rewrite size_map ].
Qed.

Definition checkActiveIntervals {pre} (pos : nat) :
  SState pre (@SSMorphLen maxReg) (@SSMorphLen maxReg) unit :=
  withScanStatePO (maxReg:=maxReg) $ fun sd (st : ScanState InUse sd) =>
    e <<- Context.iask ;;;
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let eres : seq SSTrace + { sd' : ScanStateDesc maxReg
                             | ScanState InUse sd' /\ SSMorphLen sd sd' } :=
        @dep_foldl_invE (seq SSTrace) (ScanStateDesc maxReg)
          (fun sd' => ScanState InUse sd' /\ SSMorphLen sd sd')
          (@SSMorphLen maxReg) _ sd (conj st (newSSMorphLen sd))
          (active sd) (size (active sd)) (eq_refl _)
          (@active maxReg) (subseq_refl _) mt_fst (@goActive pos sd e) in
    match eres with
    | inl err => error_ err
    | inr (exist sd' (conj st' H)) =>
        Context.iput {| thisDesc  := sd'
                      ; thisHolds := H
                      ; thisState := st' |}
    end.

Program Definition moveInactiveToActive' `(st : ScanState InUse z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (inactive z))
  (Hin : x \in inactive z) (e : seq SSTrace) :
  seq SSTrace +
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
  | false =>
      let: (p1, p2) := x in
      inl (ERegisterAssignmentsOverlap p2 p1 2 :: e)
  end.
Next Obligation.
  rewrite /moveActiveToInactive /mt_fst /morphlen_transport /=.
  case: sslen'; case=> [[?] _].
  rewrite map_widen_ord_refl.
  exact: subseq_cons_rem.
Defined.

Program Definition goInactive (pos : nat) (sd : ScanStateDesc maxReg)
  (e : seq SSTrace) (z : ScanStateDesc maxReg)
  (Pz : ScanState InUse z /\ SSMorphLen sd z)
  (x : int_reg z) (xs : int_reg_seq z)
  (Hsub : subseq (x :: xs) (inactive z)) :
  seq SSTrace + intermediate_result sd xs (@inactive maxReg) :=
  (* for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let: conj st sslen := Pz in
  match getInterval (fst x)
  return seq SSTrace + intermediate_result sd xs (@inactive maxReg) with
  | i =>
    let Hin : x \in inactive z := @in_subseq_sing _ _ _ x xs _ Hsub in
    let f (sd'    : ScanStateDesc maxReg)
          (st'    : ScanState InUse sd')
          (sslen' : SSMorphLen z sd')
          (Hsub'  : subseq [seq mt_fst sslen' i | i <- xs]
                           (inactive sd')) :=
        inr (exist2 _ _ (sd'; sslen')
                    (conj st' (transitivity sslen sslen')) Hsub') in
    if intervalEnd i < pos
    then
      if prop (verifyNewHandled z i (snd x)) isn't Some Hreq
      then let: (p1, p2) := x in
           inl (ERegisterAssignmentsOverlap p2 p1 3 :: e)
      else
        match moveInactiveToHandled st Hin Hreq (spilled:=false) with
        | exist2 sd' st' (conj sslen' _) =>
            f sd' st' sslen' _
        end
    else
      if posWithinInterval i pos
      then match moveInactiveToActive' st Hsub Hin e with
           | inl err => inl err
           | inr (exist2 sd' st' (exist sslen' Hsub')) =>
               f sd' st' sslen' Hsub'
           end
      else f z st (newSSMorphLen z) _
  end.
Next Obligation.
  rewrite /mt_fst /morphlen_transport /=.
  case: sslen'.
  case=> [[?] _].
  rewrite map_widen_ord_refl.
  exact: subseq_cons_rem.
Defined.
Next Obligation.
  rewrite /mt_fst /morphlen_transport /=.
  rewrite map_widen_ord_refl.
  apply: subseq_impl_cons.
  exact Hsub.
Defined.

Definition checkInactiveIntervals {pre} (pos : nat) :
  SState pre (@SSMorphLen maxReg) (@SSMorphLen maxReg) unit :=
  withScanStatePO (maxReg:=maxReg) $ fun sd (st : ScanState InUse sd) =>
    e <<- Context.iask ;;;
    let unchanged := exist2 _ _ sd st (newSSMorphLen sd) in
    let eres : seq SSTrace + { sd' : ScanStateDesc maxReg
                             | ScanState InUse sd' /\ SSMorphLen sd sd'} :=
        @dep_foldl_invE (seq SSTrace) (ScanStateDesc maxReg)
          (fun sd' => ScanState InUse sd' /\ SSMorphLen sd sd')
          (@SSMorphLen maxReg) _ sd (conj st (newSSMorphLen sd))
          (inactive sd) (size (inactive sd)) (eq_refl _)
          (@inactive maxReg) (subseq_refl _) mt_fst (@goInactive pos sd e) in
    match eres with
    | inl err => error_ err
    | inr (exist sd' (conj st' H)) =>
        Context.iput {| thisDesc  := sd'
                      ; thisHolds := H
                      ; thisState := st' |}
    end.

Definition handleInterval {pre} :
  SState pre (@SSMorphHasLen maxReg) (@SSMorph maxReg) (option PhysReg) :=
  (* position = start position of current *)
  withCursor (maxReg:=maxReg) $ fun _ cur =>
    let current := curInterval cur in
    let pos     := intervalStart current in
    let cid     := curId cur in

    (* Remove any empty intervals from the unhandled list *)
    if firstUsePos current is None
    then @moveUnhandledToHandled maxReg pre ;;; ipure None
    else
      (* // check for intervals in active that are handled or inactive *)
      liftLen (fun sd => @checkActiveIntervals sd pos) ;;;
      (* // check for intervals in inactive that are handled or active *)
      liftLen (fun sd => @checkInactiveIntervals sd pos) ;;;

      (* // find a register for current
         tryAllocateFreeReg
         if allocation failed then
           allocateBlockedReg
         if current has a register assigned then
           add current to active (done by the helper functions) *)
      mres <<- tryAllocateFreeReg ;;;
      match mres with
      | Some x => imap (@Some _) x
      | None   => allocateBlockedReg
      end.

Program Definition finalizeScanState
  `(st : ScanState InUse sd) (finalPos : nat) :
  seq SSTrace +
  { sd' : ScanStateDesc maxReg
  | [&& size (unhandled sd') == 0
    ,   size (active sd') == 0
    &   size (inactive sd') == 0 ] } :=
  match (checkActiveIntervals   finalPos ;;;
         checkInactiveIntervals finalPos) [::]
          {| thisDesc  := sd
           ; thisHolds := newSSMorphLen sd
           ; thisState := st |} with
  | inl errs => inl errs
  | inr (tt, ss) => _
  end.
Next Obligation.
  destruct ss.
  case H1: (size (unhandled thisDesc) == 0).
    case H2: (size (active thisDesc) == 0).
      case H3: (size (inactive thisDesc) == 0).
        apply: inr _.
        exists thisDesc.
        apply/andP; split => //.
        apply/andP; split => //.
      exact: inl [:: EInactiveIntervalsRemain].
    exact: inl [:: EActiveIntervalsRemain].
  exact: inl [:: EUnhandledIntervalsRemain].
Qed.

(* Walk through all the intervals which had been defined previously as the
   [unhandled] list, and use those to determine register allocations.  The
   final result will be a [ScanState] whose [handled] list represents the
   final allocations for each interval. *)
Fixpoint walkIntervals `(st : ScanState InUse sd) (positions : nat) :
  (seq SSTrace * ScanStateSig maxReg InUse) + ScanStateSig maxReg InUse :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  if positions isn't S n
  then inl ([:: EFuelExhausted], packScanState st)
  else let fix go count ss :=
    if count is S cnt
    then
      match handleInterval [::] ss with
      | inl err => inl (err, packScanState (thisState ss))
      | inr (_, ss') =>
        (* A [ScanState InUse] may not insert new unhandled intervals at the
           same position as [curPos], and so even though [unhandled sd] may
           have been changed by the call to [handleInterval], it will not
           have changed it with respect to subsequent intervals at the same
           position. *)
        match strengthenHasLen (thisHolds ss') with
        | None => inr ss'
        | Some holds' =>
            go cnt {| thisDesc  := thisDesc ss'
                    ; thisHolds := holds'
                    ; thisState := thisState ss' |}
        end
      end
    else inr {| thisDesc  := thisDesc ss
              ; thisHolds := weakenHasLen (thisHolds ss)
              ; thisState := thisState ss |} in

    match List.destruct_list (unhandled sd) with
    | inright _ => inr (packScanState st)
    | inleft (existT (_, pos) (_; H)) =>
        match go (count (fun x => snd x == pos) (unhandled sd))
                 {| thisDesc  := sd
                  ; thisHolds := newSSMorphHasLen (list_cons_nonzero H)
                  ; thisState := st |} with
        | inl err => inl err
        | inr ss  => walkIntervals (thisState ss) n
        end
    end.

Record Allocation := {
  intId  : nat;                 (* the interval ident *)
  intVal : IntervalDesc;        (* the interval description data *)
  intReg : option PhysReg       (* None if it was spilled to the stack *)
}.

Definition determineAllocations (sd : @ScanStateDesc maxReg) : seq Allocation :=
  [seq {| intId  := nat_of_ord (fst x)
        ; intVal := getIntervalDesc (getInterval (fst x))
        ; intReg := snd x |} | x <- handled sd].

End Allocate.
