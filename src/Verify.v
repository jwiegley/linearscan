Require Import LinearScan.Lib.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Trans.Either.
Require Import Hask.Control.Monad.Trans.State.
Require Import LinearScan.Context.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.Resolve.
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

Definition errorsT (errs : seq AllocError) : Verified unit :=
  st <-- use _verDesc ;;
  _verErrors %= fun m =>
    flip (IntMap_insert pc) m $
      if IntMap_lookup pc m is Some (d, prevErrs)
      then (d, prevErrs ++ errs)
      else (fromRegStateDesc st, errs).

Definition errorT (err : AllocError) : Verified unit := errorsT [:: err].

Variable useVerifier : UseVerifier.

Definition addMove (mv : ResolvingMoveSet) : Verified unit :=
  _verMoves %= IntMap_alter (fun mxs => @Some _ $ if mxs is Some xs
                                                  then rcons xs mv
                                                  else [:: mv]) pc.

Definition reserveReg (reg : PhysReg) (var : VarId) : Verified unit :=
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
  else if useVerifier is VerifyEnabledStrict
       then err
       else pure tt.

Definition releaseReg (reg : PhysReg) (var : VarId) : Verified unit :=
  addMove $ RSFreeReg reg var ;;
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
          match varKind ref with
          | Input  => checkResidency reg var
          | Temp   => checkReservation reg var
          | Output => assignReg reg var
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
        releaseReg fromReg fromVar ;;
        reserveReg toReg fromVar ;;
        addMove (weakenResolvingMove mv) ;;
        check <-- isResident fromReg ;;
        (if useVerifier is VerifyEnabledStrict
         then when (isJust check) $
                checkResidency fromReg fromVar ;;
                assignReg toReg fromVar
         else assignReg toReg fromVar) ;;
        pure $ rcons acc mv

    | Transfer fromReg fromVar toReg =>
      unless (fromReg == toReg) $
        releaseReg fromReg fromVar ;;
        reserveReg toReg fromVar ;;
        pure acc

    | Spill fromReg toSpillSlot =>
      releaseReg fromReg toSpillSlot ;;
      check <-- isResident fromReg ;;
      if isJust check
      then (if useVerifier is VerifyEnabledStrict
            then checkResidency fromReg toSpillSlot
            else pure tt) ;;
           allocStack toSpillSlot ;;
           addMove (weakenResolvingMove mv) ;;
           pure $ rcons acc mv
      else pure acc

    | Restore fromSpillSlot toReg =>
      reserveReg toReg fromSpillSlot ;;
      addMove (weakenResolvingMove mv) ;;
      freeStack fromSpillSlot ;;
      assignReg toReg fromSpillSlot ;;
      pure $ rcons acc mv

    | AllocReg toVar toReg =>
      reserveReg toReg toVar ;;
      pure acc

    | FreeReg fromReg fromVar =>
      releaseReg fromReg fromVar ;;
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
