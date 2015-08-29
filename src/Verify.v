Require Import LinearScan.Lib.
Require Import Hask.Control.Monad.Trans.State.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.Resolve.
Require Import LinearScan.Allocate.
Require Import LinearScan.Loops.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Verify.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Variables opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable oinfo : OpInfo maxReg opType1 opType2.

Inductive UseVerifier := VerifyDisabled | VerifyEnabled | VerifyEnabledStrict.

Definition RegAllocations := Vec (option VarId * option VarId) maxReg.

Record RegStateDesc := {
  rsAllocs : RegAllocations;
  rsStack  : IntSet
}.

Record RegStateDescSet := {
  _rsAllocs : seq (option VarId * option VarId);
  _rsStack  : IntSet
}.

Definition fromRegStateDesc (x : RegStateDesc) : RegStateDescSet :=
  {| _rsAllocs := vec_to_seq (rsAllocs x)
   ; _rsStack  := rsStack x |}.

Definition residency :
  Lens' (option VarId * option VarId) (option VarId) := _1.
Definition reservation :
  Lens' (option VarId * option VarId) (option VarId) := _2.

Definition newRegStateDesc : RegStateDesc :=
  {| rsAllocs := vconst (None, None)
   ; rsStack  := emptyIntSet |}.

(* The pattern is: actual, actual, expected *)
Inductive AllocError :=
  | VarNotAllocated of VarId
  | VarNotResident of VarId
  | VarNotResidentForReg of VarId & nat & option VarId & nat
  | VarNotReservedForReg of VarId & nat & option VarId & nat
  | StackNotAllocatedForVar of VarId
  | StackAlreadyAllocatedForVar of VarId
  | PhysRegAlreadyReservedForVar of nat & VarId
  | RegAlreadyReservedToVar of nat & VarId & VarId
  | BlockWithoutPredecessors of BlockId
  | AllocationDoesNotMatch of VarId & option (option nat)
                                    & option (option nat) & nat & nat
  | UnknownPredecessorBlock of BlockId & BlockId
  | LoopInResolvingMoves of ResolvingMoveSet.

Inductive RegState : RegStateDesc -> Prop :=
  | StartState : RegState newRegStateDesc

  | ReserveRegS st r v :
    vnth (rsAllocs st) r ^_ reservation == None ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (reservation .~ Some v)
       ; rsStack  := rsStack st |}

  | ReleaseRegS st r v :
    vnth (rsAllocs st) r ^_ reservation == Some v ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (reservation .~ None)
       ; rsStack  := rsStack st |}

  | AssignRegS st r v :
    vnth (rsAllocs st) r ^_ reservation == Some v ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (residency .~ Some v)
       ; rsStack  := rsStack st |}

  | ClearRegS st r v :
    vnth (rsAllocs st) r ^_ residency == Some v ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (residency .~ None)
       ; rsStack  := rsStack st |}

  | AllocStackS st v :
    ~~ IntSet_member v (rsStack st) ->
    RegState
      {| rsAllocs := rsAllocs st
       ; rsStack  := IntSet_insert v (rsStack st) |}

  | FreeStackS st v :
    IntSet_member v (rsStack st) ->
    RegState
      {| rsAllocs := rsAllocs st
       ; rsStack  := IntSet_delete v (rsStack st) |}.

Definition RegStateSig := { rd : RegStateDesc | RegState rd }.

Definition getRegStateDesc `(st : RegState rd) := rd.
Arguments getRegStateDesc [rd] st /.

Definition packRegState `(st : RegState rd) := exist RegState rd st.
Arguments packRegState [rd] st /.

Variable A : Type.

Record VerifiedSig := {
  verDesc   : RegStateDesc;
  verState  : RegState verDesc;
  (* [verBlocks] gives the final allocation state for every handled block *)
  verInit   : IntMap RegStateSig;
  verFinal  : IntMap RegStateSig;
  verMoves  : IntMap (seq ResolvingMoveSet);
  verErrors : IntMap (RegStateDescSet * seq AllocError);
  verExt    : A
}.

Definition newVerifiedSig (i : A) :=
  {| verDesc   := newRegStateDesc
   ; verState  := StartState
   ; verInit   := emptyIntMap
   ; verFinal  := emptyIntMap
   ; verMoves  := emptyIntMap
   ; verErrors := emptyIntMap
   ; verExt    := i |}.

Definition _verDesc : Getter VerifiedSig RegStateDesc := fun _ _ _ f s =>
  fmap (const s) (f (verDesc s)).

Definition _verState :
  Lens' VerifiedSig { rd : RegStateDesc | RegState rd } := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := x.1
     ; verState  := x.2
     ; verInit   := verInit s
     ; verFinal  := verFinal s
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verDesc s; verState s)).

Definition _verInit : Lens' VerifiedSig (IntMap RegStateSig) :=
  fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verInit   := x
     ; verFinal  := verFinal s
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verInit s)).

Definition _verFinal : Lens' VerifiedSig (IntMap RegStateSig) :=
  fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verInit   := verInit s
     ; verFinal  := x
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verFinal s)).

Definition _verMoves :
  Lens' VerifiedSig (IntMap (seq ResolvingMoveSet)) := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verInit   := verInit s
     ; verFinal  := verFinal s
     ; verMoves  := x
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verMoves s)).

Definition _verErrors :
  Lens' VerifiedSig (IntMap (RegStateDescSet * seq AllocError)) :=
  fun _ _ f s =>
      fmap (fun x =>
        {| verDesc   := verDesc s
         ; verState  := verState s
         ; verInit   := verInit s
         ; verFinal  := verFinal s
         ; verMoves  := verMoves s
         ; verErrors := x
         ; verExt    := verExt s
         |}) (f (verErrors s)).

Definition _verExt : Lens' VerifiedSig A := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verInit   := verInit s
     ; verFinal  := verFinal s
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := x
     |}) (f (verExt s)).

Definition Verified := StateT VerifiedSig mType.

Variable pc : OpId.
Variable intervals : seq (Allocation maxReg).
Variable useVerifier : UseVerifier.

Definition errorsT (errs : seq AllocError) : Verified unit :=
  st <-- use _verDesc ;;
  _verErrors %= fun m =>
    flip (IntMap_insert pc) m $
      if IntMap_lookup pc m is Some (d, prevErrs)
      then (d, prevErrs ++ errs)
      else (fromRegStateDesc st, errs).

Definition errorT (err : AllocError) : Verified unit := errorsT [:: err].

Definition addMove (mv : ResolvingMoveSet) : Verified unit :=
  _verMoves %= IntMap_alter (fun mxs => @Some _ $ if mxs is Some xs
                                                  then rcons xs mv
                                                  else [:: mv]) pc.

Definition allocationFor (var : VarId) (pos : nat) : option (option PhysReg) :=
  match [seq i <- intervals
             | let int := intVal i in
               [&& ivar int == var
               &   ibeg int <= pos < iend int ]] with
  | [::]   => None                (* not allocated here *)
  | [:: a] => (Some (intReg a))   (* allocated in reg or on stack *)
  | _      => None                (* over-allocated! but see the Theorem
                                     no_allocations_overlap in Spec.v *)
  end.

Definition variablesAtPos (pos : nat) : seq (VarId * option PhysReg) :=
  [seq (ivar (intVal i), intReg i) | i <- intervals
                                   & let int := intVal i in
                                     ibeg int <= pos < iend int].

Definition checkAllocation
  (reg : option (option PhysReg)) (var : VarId) (pos idx : nat) :
  Verified unit :=
  let alloc := allocationFor var pos in
  if alloc != reg
  then errorT $ AllocationDoesNotMatch var
                  (option_map (option_map (@nat_of_ord maxReg)) reg)
                  (option_map (option_map (@nat_of_ord maxReg)) alloc)
                  pos idx
  else pure tt.

Definition reserveReg (reg : PhysReg) (var : VarId) (fromSplit : bool) :
  Verified unit :=
  addMove $ RSAllocReg var reg fromSplit ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ reservation == None) is Some H
  then _verState .= packRegState (ReserveRegS var H)
  else if vnth (rsAllocs st) reg ^_ reservation is Some v
       then when (v != var) $
              errorT $ RegAlreadyReservedToVar reg v var
       else pure tt.

Definition isReserved (reg : PhysReg) : Verified (option VarId) :=
  st <-- use _verDesc ;;
  pure (vnth (rsAllocs st) reg ^_ reservation).

Definition checkReservation (reg : PhysReg) (var : VarId) : Verified unit :=
  st <-- use _verDesc ;;
  let err := errorT $ VarNotReservedForReg var reg
                        (vnth (rsAllocs st) reg ^_ reservation) 1 in
  res <-- isReserved reg ;;
  if res is Some var'
  then unless (var == var') err
  else if useVerifier is VerifyEnabledStrict
       then err
       else pure tt.

Definition releaseReg (reg : PhysReg) (var : VarId) (fromSplit : bool) :
  Verified unit :=
  addMove $ RSFreeReg reg var fromSplit ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ reservation == Some var) is Some H
  then _verState .= packRegState (ReleaseRegS H)
  else let err := errorT $ VarNotReservedForReg var reg
                             (vnth (rsAllocs st) reg ^_ reservation) 2 in
       if useVerifier is VerifyEnabledStrict
       then err
       else if vnth (rsAllocs st) reg ^_ reservation is None
            then pure tt
            else err.

Definition assignReg (reg : PhysReg) (var : VarId) : Verified unit :=
  addMove $ RSAssignReg var reg ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ reservation == Some var) is Some H
  then _verState .= packRegState (AssignRegS H)
  else let err := errorT $ VarNotReservedForReg var reg
                         (vnth (rsAllocs st) reg ^_ reservation) 3 in
       if useVerifier is VerifyEnabledStrict
       then err
       else if vnth (rsAllocs st) reg ^_ reservation is None
            then pure tt
            else err.

Definition isResident (reg : PhysReg) : Verified (option VarId) :=
  st <-- use _verDesc ;;
  pure (vnth (rsAllocs st) reg ^_ residency).

Definition checkResidency (reg : PhysReg) (var : VarId) : Verified unit :=
  st <-- use _verDesc ;;
  res <-- isResident reg ;;
  let err := errorT $ VarNotResidentForReg var reg res 1 in
  if useVerifier is VerifyEnabledStrict
  then if res is Some var'
       then unless (var == var') err
       else err
  else pure tt.

Definition clearReg (reg : PhysReg) (var : VarId) : Verified unit :=
  addMove $ RSClearReg reg var ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ residency == Some var) is Some H
  then _verState .= packRegState (ClearRegS H)
  else let err := errorT $ VarNotResidentForReg var reg
                             (vnth (rsAllocs st) reg ^_ residency) 2 in
       if useVerifier is VerifyEnabledStrict
       then err
       else if vnth (rsAllocs st) reg ^_ residency is None
            then pure tt
            else err.

Definition isStackAllocated (var : VarId) : Verified bool :=
  st <-- use _verDesc ;;
  pure (IntSet_member var (rsStack st)).

Definition checkStack (var : VarId) : Verified unit :=
  st  <-- use _verDesc ;;
  res <-- isStackAllocated var ;;
  let err := errorT $ StackNotAllocatedForVar var in
  if useVerifier is VerifyEnabledStrict
  then unless res err
  else pure tt.

Definition allocStack (var : VarId) : Verified unit :=
  addMove $ RSAllocStack var ;;
  st <-- use _verDesc ;;
  if prop (~~ IntSet_member var (rsStack st)) is Some H
  then _verState .= packRegState (AllocStackS H)
  else let err := errorT $ StackAlreadyAllocatedForVar var in
       if useVerifier is VerifyEnabledStrict
       then err
       else pure tt.

Definition freeStack (var : VarId) : Verified unit :=
  addMove $ RSFreeStack var ;;
  st <-- use _verDesc ;;
  if prop (IntSet_member var (rsStack st)) is Some H
  then _verState .= packRegState (FreeStackS H)
  else let err := errorT $ StackNotAllocatedForVar var in
       if useVerifier is VerifyEnabledStrict
       then err
       else pure tt.

Definition checkLiveness (vars : IntSet) : Verified unit :=
  if useVerifier isn't VerifyEnabledStrict then pure tt else
  st <-- use _verDesc ;;
  (forM_ (IntSet_toList vars) $ fun var =>
     unless (vfoldl_with_index (fun reg b p =>
       b || if p ^_ residency is Some var then true else false)
                               false (rsAllocs st)) $
       errorT $ VarNotResident var) (* ;;

  (* Clear out any resident registers which liveness tells us are not set.
     That is, even though there may be contents "left over", we don't want to
     rely on that, but only on the liveness information. *)
  vfoldl_with_index (fun reg act p => act >>
                       if p ^_ residency is Some v
                       then unless (IntSet_member v vars) $
                              clearReg reg v
                       else pure tt)
                    (pure tt) (rsAllocs st) *).

Definition verifyBlockBegin (bid : nat) (liveIns : IntSet) (loops : LoopState) :
  Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
  (if IntMap_lookup bid (forwardBranches loops) is Some fwds
   then
     forM_ (IntSet_toList fwds) (fun pred =>
       exits <-- use _verFinal ;;
       if IntMap_lookup pred exits isn't Some allocs
       then errorT $ UnknownPredecessorBlock bid pred
       else _verState .= allocs)
   else
    (if useVerifier is VerifyEnabledStrict
     then
        when (IntSet_size liveIns > 0) $
          errorT $ BlockWithoutPredecessors bid
     else pure tt)) ;;

  checkLiveness liveIns ;;

  allocs <-- use _verState ;;
  _verInit %= IntMap_insert bid allocs.

Definition verifyBlockEnd (bid : nat) (liveOuts : IntSet) : Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
  (* Check to ensure that all "live out" variables are resident in registers
     at the end of the block. *)
  checkLiveness liveOuts ;;

  (* Clear out all known allocations, saving them for this block. *)
  allocs <-- use _verState ;;
  _verFinal %= IntMap_insert bid allocs ;;

  _verState .= packRegState StartState.

Definition verifyAllocs (op : opType1)
  (allocs : seq ((VarId * VarKind) * PhysReg)) : Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
  forM_ (opRefs oinfo op) $ fun ref =>
    (* Determine which register this variable has been associated with by the
       allocation for this operation. *)
    match varId ref with
    | inl reg =>
      (* Direct register references are mostly left alone; we just check to
         make sure that it's not overwriting a variable in a register. *)

      (* st <-- use _verDesc ;; *)
      (* if varKind ref is Input *)
      (* then pure tt *)
      (* else if vnth (rsAllocs st) reg is (_, Some v) *)
      (*      then errorT $ PhysRegAlreadyReservedForVar reg v *)
      (*      else pure tt *)

      (* jww (2015-08-19): The above check doesn't fully work yet *)
      pure tt

    | inr var =>
        if maybeLookup allocs (var, varKind ref) isn't Some reg
        then errorT $ VarNotAllocated var
        else
          (* We decrement the pc by 2 or 1 to offset what
             [Assign.setAllocations] had added. *)
          match varKind ref with
          | Input  =>
            (* jww (2015-08-29): It only needs to be resident at this point,
               not necessarily allocated to a register. Some other variable
               could be allocated, pending an upcoming write after the
               resident value is used as an input. *)
            (* checkAllocation (Some (Some reg)) var pc.-2 1 ;; *)
            checkResidency reg var
          | Temp   =>
            checkAllocation (Some (Some reg)) var pc.-1 2 ;;
            checkReservation reg var
          | Output =>
            checkAllocation (Some (Some reg)) var pc.-1 3 ;;
            assignReg reg var
          end
    end.

Definition verifyResolutions (moves : seq (@ResolvingMove maxReg)) :
  Verified (seq (ResolvingMove maxReg)) :=
  if useVerifier is VerifyDisabled
  then pure moves else
  forFoldM [::] moves $ fun acc mv =>
    st <-- use _verDesc ;;
    match mv with
    | Move fromReg fromVar toReg =>
      unless (fromReg == toReg) $
        releaseReg fromReg fromVar false ;;
        reserveReg toReg fromVar false ;;
        addMove (weakenResolvingMove mv) ;;
        check <-- isResident fromReg ;;
        (* jww (2015-08-27): This logic is a little screwy... *)
        (if useVerifier is VerifyEnabledStrict
         then when (isJust check) $
                checkResidency fromReg fromVar ;;
                assignReg toReg fromVar
         else assignReg toReg fromVar) ;;
        pure $ rcons acc mv

    | Transfer fromReg fromVar toReg =>
      unless (fromReg == toReg) $
        releaseReg fromReg fromVar false ;;
        reserveReg toReg fromVar false ;;
        pure acc

    | Spill fromReg toSpillSlot fromSplit =>
      releaseReg fromReg toSpillSlot fromSplit ;;
      check <-- isResident fromReg ;;
      if isJust check
      then
        (* jww (2015-08-29): It's OK for the residency to not match, if it is
           never restored afterwards. *)
        (* (if useVerifier is VerifyEnabledStrict *)
        (*  then checkResidency fromReg toSpillSlot *)
        (*  else pure tt) ;; *)
        allocStack toSpillSlot ;;
        addMove (weakenResolvingMove mv) ;;
        pure $ rcons acc mv
      else pure acc

    | Restore fromSpillSlot toReg fromSplit =>
      (* jww (2015-08-27): Should I be using aggregate resolving moves here
         like this, or should I use a list in [ResolvingMove], which would
         allow the topological sort to reorder them? *)
      reserveReg toReg fromSpillSlot fromSplit ;;
      addMove (weakenResolvingMove mv) ;;
      freeStack fromSpillSlot ;;
      assignReg toReg fromSpillSlot ;;
      pure $ rcons acc mv

    | AllocReg toVar toReg fromSplit =>
      reserveReg toReg toVar fromSplit ;;
      pure acc

    | FreeReg fromReg fromVar fromSplit =>
      releaseReg fromReg fromVar fromSplit ;;
      pure acc

    | Looped x =>
      errorT $ LoopInResolvingMoves (weakenResolvingMove x) ;;
      addMove (weakenResolvingMove mv) ;;
      pure $ rcons acc mv

    | AllocStack toVar =>
      allocStack toVar ;;
      pure acc

    | FreeStack fromVar =>
      freeStack fromVar ;;
      pure acc
    end.

Definition verifyTransitions (moves : seq (@ResolvingMove maxReg))
  (from : nat) (to : nat) : Verified unit :=
  if useVerifier is VerifyDisabled
  then pure tt else
  forM_ moves $ fun mv =>
    st <-- use _verDesc ;;
    match mv with
    | Move fromReg fromVar toReg =>
      checkAllocation (Some (Some fromReg)) fromVar from 4 ;;
      checkAllocation (Some (Some toReg)) fromVar to 5

    | Transfer fromReg fromVar toReg =>
      checkAllocation (Some (Some fromReg)) fromVar from 6 ;;
      checkAllocation (Some (Some toReg)) fromVar to 7

    | Spill fromReg toSpillSlot fromSplit =>
      checkAllocation (Some (Some fromReg)) toSpillSlot from 8 ;;
      unless fromSplit $ checkAllocation (Some None) toSpillSlot to 9

    | Restore fromSpillSlot toReg fromSplit =>
      unless fromSplit $ checkAllocation (Some None) fromSpillSlot from 10 ;;
      checkAllocation (Some (Some toReg)) fromSpillSlot to 11

    | AllocReg toVar toReg fromSplit =>
      (* It's OK for a stack variable to be present here, since as an
         optimized we do not restore if the next instructions immediately
         overwrites it. *)
      unless fromSplit
        (let alloc := allocationFor toVar from in
         (if alloc is Some (Some otherReg)
          then errorT $ AllocationDoesNotMatch toVar None
                (option_map (option_map (@nat_of_ord maxReg)) alloc)
                from 12
          else pure tt)) ;;
      checkAllocation (Some (Some toReg)) toVar to 13

    | FreeReg fromReg fromVar fromSplit =>
      checkAllocation (Some (Some fromReg)) fromVar from 14 ;;
      unless fromSplit $ checkAllocation None fromVar to 15

    | Looped x => pure tt

    | AllocStack toVar =>
      checkAllocation None toVar from 16 ;;
      checkAllocation (Some None) toVar to 17

    | FreeStack fromVar =>
      checkAllocation (Some None) fromVar from 18 ;;
      checkAllocation None fromVar to 19
    end.

End Verify.

Module VerifyLensLaws.

Include LensLaws.

Variable a b : Type.
Variable P : a -> Prop.

(* Program Instance Lens__verDesc : GetterLaws (@_verDesc maxReg a). *)
Program Instance Lens__verState : LensLaws (@_verState maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verInit : LensLaws (@_verInit maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verFinal : LensLaws (@_verFinal maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verMoves : LensLaws (@_verMoves maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verErrors : LensLaws (@_verErrors maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verExt : LensLaws (@_verExt maxReg a).
Obligation 2. by case: x. Qed.

End VerifyLensLaws.
