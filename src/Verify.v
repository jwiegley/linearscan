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

Definition allocationsAt (pos : nat) : seq (Allocation maxReg) :=
  [seq i | i <- intervals
         & let int := intVal i in
           ibeg int <= pos < iend int].

Definition allocationFor (var : VarId) (pos : nat) : option (option PhysReg) :=
  match [seq i <- allocationsAt pos | ivar (intVal i) == var] with
  | [::]   => None                (* not allocated here *)
  | [:: a] => Some (intReg a)     (* allocated in reg or on stack *)
  | _      => None                (* over-allocated! but see the Theorem
                                     [no_allocations_intersect] in Spec.v *)
  end.

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

Definition reserveReg (reg : PhysReg) (var : VarId) :
  Verified unit :=
  addMove $ RSAllocReg var reg ;;
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
  else err.

Definition releaseReg (reg : PhysReg) (var : VarId) :
  Verified unit :=
  addMove $ RSFreeReg reg var ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ reservation == Some var) is Some H
  then _verState .= packRegState (ReleaseRegS H)
  else errorT $ VarNotReservedForReg var reg
                  (vnth (rsAllocs st) reg ^_ reservation) 2.

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

Definition assignReg (reg : PhysReg) (var : VarId) : Verified unit :=
  addMove $ RSAssignReg var reg ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ reservation == Some var) is Some H
  then (* When a variable is assigned to a register, all of its older
          values in other registers are invalidated. *)
       vfoldr_with_index (fun reg x act =>
                            if fst x == Some var
                            then clearReg reg var >> act
                            else act) (pure tt) (rsAllocs st) ;;
       _verState .= packRegState (AssignRegS H)
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
  allocs <-- use _verState ;;
  _verInit %= IntMap_insert bid allocs.

Definition verifyBlockEnd (bid : nat) (liveOuts : IntSet) : Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
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

      when (varKind ref != Input)
        (st <-- use _verDesc ;;
         if vnth (rsAllocs st) reg ^_ reservation is Some v
         then errorT $ PhysRegAlreadyReservedForVar reg v
         else
           if [seq i <- allocationsAt pc.-1 | intReg i == Some reg ] is x :: _
           then errorT $ AllocationDoesNotMatch (ivar (intVal x)) None
                           (Some (option_map (@nat_of_ord maxReg) (intReg x)))
                           pc.-1 0
           else pure tt)

    | inr var =>
        if maybeLookup allocs (var, varKind ref) isn't Some reg
        then errorT $ VarNotAllocated var
        else
          (* We decrement pc by 1 to offset what [Assign.setAllocations]
             added. *)
          match varKind ref with
          | Input       => checkResidency reg var
          | InputOutput => checkResidency reg var ;;
                           checkAllocation (Some (Some reg)) var pc.-1 1 ;;
                           assignReg reg var
          | Temp        => checkAllocation (Some (Some reg)) var pc.-1 2 ;;
                           checkReservation reg var
          | Output      => checkAllocation (Some (Some reg)) var pc.-1 3 ;;
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
      checkResidency fromReg fromVar ;;
      checkReservation toReg fromVar ;;
      addMove (weakenResolvingMove mv) ;;
      pure $ rcons acc mv

    | Spill fromReg toSpillSlot fromSplit =>
      checkStack toSpillSlot ;;
      check <-- isResident fromReg ;;
      (* Spills are not necessary if the variable is not resident. *)
      if check == Some toSpillSlot
      then addMove (weakenResolvingMove mv) ;;
           pure $ rcons acc mv
      else let mv' := FreeStack maxReg toSpillSlot in
           addMove (weakenResolvingMove mv') ;;
           pure $ rcons acc mv'

    | Restore fromSpillSlot toReg fromSplit =>
      checkStack fromSpillSlot ;;
      checkReservation toReg fromSpillSlot ;;
      addMove (weakenResolvingMove mv) ;;
      pure $ rcons acc mv

    | AllocReg toVar toReg    => reserveReg toReg toVar ;; pure acc
    | FreeReg fromReg fromVar => releaseReg fromReg fromVar ;; pure acc

    | AssignReg fromVar toReg => assignReg toReg fromVar ;; pure acc
    | ClearReg fromReg toVar  => clearReg fromReg toVar  ;; pure acc

    | AllocStack toVar  => allocStack toVar  ;; pure acc
    | FreeStack fromVar => freeStack fromVar ;; pure acc

    | Looped x =>
      errorT $ LoopInResolvingMoves (weakenResolvingMove x) ;;
      addMove (weakenResolvingMove mv) ;;
      pure $ rcons acc mv
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

    | Spill fromReg toSpillSlot fromSplit =>
      checkAllocation (Some (Some fromReg)) toSpillSlot from 6 ;;
      unless fromSplit $ checkAllocation (Some None) toSpillSlot to 7
    | Restore fromSpillSlot toReg fromSplit =>
      unless fromSplit $ checkAllocation (Some None) fromSpillSlot from 8 ;;
      checkAllocation (Some (Some toReg)) fromSpillSlot to 9

    | AllocReg toVar toReg =>
      checkAllocation (Some (Some toReg)) toVar to 10
    | FreeReg fromReg fromVar =>
      checkAllocation (Some (Some fromReg)) fromVar from 11

    | AssignReg fromVar toReg =>
      checkAllocation (Some (Some toReg)) fromVar to 12
    | ClearReg fromReg toVar =>
      checkAllocation (Some (Some fromReg)) toVar from 13

    | AllocStack toVar  => checkAllocation (Some None) toVar to 14
    | FreeStack fromVar => checkAllocation (Some None) fromVar from 15

    | Looped x => pure tt
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
