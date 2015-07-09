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

Inductive UseVerifier := VerifyDisabled | VerifyEnabled.

Definition RegAllocations := Vec (option VarId * option VarId) maxReg.

Record RegStateDesc := {
  rsAllocs : RegAllocations;
  rsStack  : IntSet
}.

Definition residency :
  Lens' (option VarId * option VarId) (option VarId) := _1.
Definition reservation :
  Lens' (option VarId * option VarId) (option VarId) := _2.

Definition newRegStateDesc : RegStateDesc :=
  {| rsAllocs := vconst (None, None)
   ; rsStack  := emptyIntSet
   |}.

(* The pattern is: actual, actual, expected *)
Inductive AllocError :=
  | VarNotAllocated of VarId
  | VarNotResident of VarId
  | VarNotResidentForReg of VarId & nat & option VarId
  | VarNotReservedForReg of VarId & nat & option VarId
  | PhysRegAlreadyResidentForVar of nat & VarId
  | PhysRegAlreadyReservedForVar of nat & VarId
  | RegAlreadyReservedToVar of nat & VarId & VarId
  | BlockWithoutPredecessors of BlockId
  | UnknownPredecessorBlock of BlockId & BlockId
  | ErrorAtBlockEnd of BlockId.

Inductive RegState : RegStateDesc -> Prop :=
  | StartState : RegState newRegStateDesc

  | ReserveRegS st r v :
    vnth (rsAllocs st) r ^_ reservation == None ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (reservation .~ Some v)
       ; rsStack  := rsStack st
       |}

  | ReleaseRegS st r v :
    vnth (rsAllocs st) r ^_ reservation == Some v ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (reservation .~ None)
       ; rsStack  := rsStack st
       |}

  | AssignRegS st r v :
    vnth (rsAllocs st) r ^_ reservation == Some v ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (residency .~ Some v)
       ; rsStack  := rsStack st
       |}

  | ClearRegS st r v :
    vnth (rsAllocs st) r ^_ residency == Some v ->
    RegState
      {| rsAllocs := vmodify (rsAllocs st) r (residency .~ None)
       ; rsStack  := rsStack st
       |}

  | AllocStackS st v :
    ~~ IntSet_member v (rsStack st) ->
    RegState
      {| rsAllocs := rsAllocs st
       ; rsStack  := IntSet_insert v (rsStack st)
       |}

  | FreeStackS st v :
    IntSet_member v (rsStack st) ->
    RegState
      {| rsAllocs := rsAllocs st
       ; rsStack  := IntSet_delete v (rsStack st)
       |}.

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
  verBlocks : IntMap RegStateSig;
  verMoves  : IntMap (seq ResolvingMoveSet);
  verErrors : IntMap (seq AllocError);
  verExt    : A
}.

Definition newVerifiedSig (i : A) :=
  {| verDesc   := newRegStateDesc
   ; verState  := StartState
   ; verBlocks := emptyIntMap
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
     ; verBlocks := verBlocks s
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verDesc s; verState s)).

Definition _verBlocks : Lens' VerifiedSig (IntMap RegStateSig) :=
  fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verBlocks := x
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verBlocks s)).

Definition _verMoves :
  Lens' VerifiedSig (IntMap (seq ResolvingMoveSet)) := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verBlocks := verBlocks s
     ; verMoves  := x
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verMoves s)).

Definition _verErrors :
  Lens' VerifiedSig (IntMap (seq AllocError)) := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verBlocks := verBlocks s
     ; verMoves  := verMoves s
     ; verErrors := x
     ; verExt    := verExt s
     |}) (f (verErrors s)).

Definition _verExt : Lens' VerifiedSig A := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verBlocks := verBlocks s
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := x
     |}) (f (verExt s)).

Definition Verified := StateT VerifiedSig mType.

Variable pc : OpId.

Definition errorsT (errs : seq AllocError) : Verified unit :=
  _verErrors %= IntMap_insert pc errs.

Definition errorT (err : AllocError) : Verified unit :=
  errorsT [:: err].

Variable useVerifier : UseVerifier.

Definition addMove (mv : ResolvingMoveSet) : Verified unit :=
  _verMoves %= IntMap_alter
    (fun mxs => @Some _ $ if mxs is Some xs
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

Definition isReserved (reg : PhysReg) (var : VarId) : Verified bool :=
  st <-- use _verDesc ;;
  pure (vnth (rsAllocs st) reg ^_ reservation == Some var).

Definition checkReservation (reg : PhysReg) (var : VarId) : Verified unit :=
  b  <-- isReserved reg var ;;
  unless b
    (st <-- use _verDesc ;;
     errorT $ VarNotReservedForReg var reg
       (vnth (rsAllocs st) reg ^_ reservation)).

Definition releaseReg (reg : PhysReg) (var : VarId) : Verified unit :=
  addMove $ RSFreeReg reg var ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ reservation == Some var) is Some H
  then _verState .= packRegState (ReleaseRegS H)
  else errorT $ VarNotReservedForReg var reg
         (vnth (rsAllocs st) reg ^_ reservation).

Definition assignReg (reg : PhysReg) (var : VarId) : Verified unit :=
  addMove $ RSAssignReg var reg ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ reservation == Some var) is Some H
  then _verState .= packRegState (AssignRegS H)
  else errorT $ VarNotReservedForReg reg var
    (vnth (rsAllocs st) reg ^_ reservation).

Definition isResident (reg : PhysReg) (var : VarId) : Verified bool :=
  st <-- use _verDesc ;;
  pure (vnth (rsAllocs st) reg ^_ residency == Some var).

Definition checkResidency (reg : PhysReg) (var : VarId) : Verified unit :=
  b  <-- isResident reg var ;;
  unless b
    (st <-- use _verDesc ;;
     errorT $ VarNotResidentForReg var reg
       (vnth (rsAllocs st) reg ^_ residency)).

Definition clearReg (reg : PhysReg) (var : VarId) : Verified unit :=
  addMove $ RSClearReg var reg ;;
  st <-- use _verDesc ;;
  if prop (vnth (rsAllocs st) reg ^_ residency == Some var) is Some H
  then _verState .= packRegState (ClearRegS H)
  else errorT $ VarNotResidentForReg var reg
    (vnth (rsAllocs st) reg ^_ residency).

(* Definition allocStack (v : 'I_maxVar) : Verified unit := pure tt. *)

(* Definition freeStack (v : 'I_maxVar) : Verified unit := pure tt. *)

Definition checkLiveness (vars : IntSet) : Verified unit :=
  st <-- use _verDesc ;;
  forM_ (IntSet_toList vars) $ fun var =>
    unless (vfoldl_with_index (fun reg b p =>
      b || if p ^_ residency is Some var then true else false)
                              false (rsAllocs st)) $
      errorT $ VarNotResident var.

Definition verifyBlockBegin (bid : nat) (liveIns : IntSet) (loops : LoopState) :
  Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
  (if IntMap_lookup bid (forwardBranches loops) is Some fwds
   then
     forM_ (IntSet_toList fwds) (fun pred =>
       exits <-- use _verBlocks ;;
       if IntMap_lookup pred exits isn't Some allocs
       then errorT $ UnknownPredecessorBlock bid pred
       else _verState .= allocs)
   else
     when (IntSet_size liveIns > 0) $
       errorT $ BlockWithoutPredecessors bid) ;;
  checkLiveness liveIns.

Definition verifyBlockEnd (bid : nat) (liveOuts : IntSet) : Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
  (* Check to ensure that all "live out" variables are resident in registers
     at the end of the block. *)
  checkLiveness liveOuts ;;

  (* Clear out all known allocations, saving them for this block. *)
  allocs <-- use _verState ;;
  _verState .= packRegState StartState ;;

  _verBlocks %= IntMap_insert bid allocs.

Definition verifyApplyAllocs (op : opType1) (allocs : seq (VarId * PhysReg)) :
  Verified (seq opType2) :=
  (if useVerifier isn't VerifyDisabled
   then
     forM_ (sortBy (fun x y => VarKind_leq (varKind x) (varKind y))
                   (opRefs oinfo op)) (fun ref =>
       (* Determine which register this variable has been associated with by the
          allocation for this operation. *)
       match varId ref with
       | inl reg =>
         (* Direct register references are mostly left alone; we just check to
            make sure that it's not overwriting a variable in a register. *)
         st <-- use _verDesc ;;
         if varKind ref is Input
         then
           if vnth (rsAllocs st) reg is (Some v, _)
           then errorT $ PhysRegAlreadyResidentForVar reg v
           else pure tt
         else
           if vnth (rsAllocs st) reg is (_, Some v)
           then errorT $ PhysRegAlreadyReservedForVar reg v
           else pure tt

       | inr var =>
         if maybeLookup allocs var isn't Some reg
         then errorT $ VarNotAllocated var
         else
           match varKind ref with
           | Input  => checkResidency reg var
           | Temp   => checkReservation reg var
           | Output => checkReservation reg var ;;
                       assignReg reg var
           end
       end)
   else pure tt) ;;

  lift $ applyAllocs oinfo op allocs.

Definition verifyResolutions (moves : seq (@ResGraphEdge maxReg)) :
  Verified (seq (ResolvingMove maxReg)) :=
  if useVerifier is VerifyDisabled
  then pure $ map (@resMove maxReg) moves else
  fmap rev $ forFoldM [::] moves $ fun acc mv =>
    st <-- use _verDesc ;;
    match resMove mv with
    | Move fromReg fromVar toReg =>
      checkResidency fromReg fromVar ;;
      unless (fromReg == toReg) $
        releaseReg fromReg fromVar ;;
        reserveReg toReg fromVar ;;
        addMove (weakenResolvingMove (resMove mv)) ;;
        assignReg toReg fromVar ;;
        when (resGhost mv) (releaseReg toReg fromVar) ;;
        pure $ resMove mv :: acc

    | Swap fromReg fromVar toReg toVar =>
      checkResidency fromReg fromVar ;;
      checkResidency toReg toVar ;;
      releaseReg fromReg fromVar ;;
      releaseReg toReg toVar ;;
      addMove (weakenResolvingMove (resMove mv)) ;;
      reserveReg fromReg toVar ;;
      reserveReg toReg fromVar ;;
      assignReg fromReg toVar ;;
      assignReg toReg fromVar ;;
      pure $ resMove mv :: acc

    | Spill fromReg toSpillSlot =>
      releaseReg fromReg toSpillSlot ;;
      check <-- isResident fromReg toSpillSlot ;;
      if check
      then addMove (weakenResolvingMove (resMove mv)) ;;
           pure $ resMove mv :: acc
      else pure acc

    | Restore fromSpillSlot toReg =>
      reserveReg toReg fromSpillSlot ;;
      addMove (weakenResolvingMove (resMove mv)) ;;
      assignReg toReg fromSpillSlot ;;
      when (resGhost mv)
        (releaseReg toReg fromSpillSlot) ;;
      pure $ resMove mv :: acc

    | AllocReg toVar toReg =>
      reserveReg toReg toVar ;;
      when (resGhost mv)
        (releaseReg toReg toVar) ;;
      pure acc

    | FreeReg fromReg fromVar =>
      releaseReg fromReg fromVar ;;
      pure acc

    (* | AllocStack toVar => pure acc *)
    (* | FreeStack fromVar => pure acc *)
    end.

End Verify.

Module VerifyLensLaws.

Include LensLaws.

Variable a b : Type.
Variable P : a -> Prop.

(* Program Instance Lens__verDesc : GetterLaws (@_verDesc maxReg a). *)
Program Instance Lens__verState : LensLaws (@_verState maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verBlocks : LensLaws (@_verBlocks maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verMoves : LensLaws (@_verMoves maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verErrors : LensLaws (@_verErrors maxReg a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verExt : LensLaws (@_verExt maxReg a).
Obligation 2. by case: x. Qed.

End VerifyLensLaws.
