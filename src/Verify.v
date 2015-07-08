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

Variable maxVar : nat.          (* max number of variables *)
Hypothesis variables_exist : 0 < maxVar.

Variables opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable oinfo : OpInfo maxReg opType1 opType2.

Inductive UseVerifier :=
  | VerifyDisabled
  | VerifyEnabledUnitializedOK
  | VerifyEnabled.

Record RegStateDesc := {
  rsRegs        : Vec (option 'I_maxVar) maxReg;
  rsAllocs      : Vec (option 'I_maxReg) maxVar;
  rsGhostRegs   : Vec (option 'I_maxVar) maxReg;
  rsGhostAllocs : Vec (option 'I_maxReg) maxVar;
  rsStack       : Vec bool maxVar
}.

Definition newRegStateDesc : RegStateDesc :=
  {| rsRegs        := vconst None
   ; rsAllocs      := vconst None
   ; rsGhostRegs   := vconst None
   ; rsGhostAllocs := vconst None
   ; rsStack       := vconst false
   |}.

Definition IntSet_to_seq_fin {n : nat} (s : IntSet) :
  all (ltn ^~ n) (IntSet_toList s) -> seq 'I_n.
Proof.
  elim: (IntSet_toList s) => [_|? ? IHxs /andP [H ?]] /=.
    exact: [::].
  exact: cons (Ordinal H) (IHxs _).
Defined.

Definition keepOnly {A : Type} `(xs : seq 'I_n) :
  Vec (option A) n -> Vec (option A) n :=
  vmap_with_index (fun i x => if i \in xs then x else None).

(* The pattern is: actual, actual, expected *)
Inductive AllocError :=
  | VarId_OutOfBounds of VarId & nat
  | VarNotAllocated of VarId
  | FreeUnallocatedVar of VarId
  | FreeVarAllocatedToDifferentReg of VarId & nat & nat
  | FreeRegNotAllocatedToVar of nat & VarId
  | VarWithoutAllocation of VarId
  | AllocVarAllocatedToDifferentReg of VarId & nat & nat
  | CheckVarAllocatedToDifferentReg of VarId & nat & nat
  | MoveRegNotAllocated of nat & nat
  | SwapRegNotAllocated of nat & nat
  | SpillRegNotAllocated of nat & nat
  | RegNotAllocatedToVar of nat & VarId
  | CheckRegAllocatedToDifferentVar of nat & VarId & VarId
  | AllocRegAllocatedToDifferentVar of nat & VarId & VarId
  | RegAlreadyAllocatedTo of nat & VarId
  | SpillToWrongSlot of nat & VarId & VarId
  | BlockWithoutPredecessors of BlockId
  | UnknownPredecessorBlock of BlockId & BlockId
  | ErrorAtBlockEnd of BlockId.

Definition checkAlloc' st (var : 'I_maxVar) (mreg : option 'I_maxReg)
  (strict : bool) (checkGhosts : bool) :
  option AllocError :=
  let check regs reg :=
    let res :=
      if vnth regs reg isn't Some var'
      then Some (RegNotAllocatedToVar reg var)
      else
        if var == var'
        then None
        else Some (CheckRegAllocatedToDifferentVar reg var' var) in
    if mreg is Some reg'
    then if reg == reg'
         then res
         else Some (CheckVarAllocatedToDifferentReg var reg reg')
    else res in
  let go :=
    if vnth (rsAllocs st) var is Some reg
    then check (rsRegs st) reg
    else
      if strict
      then Some (VarNotAllocated var)
      else None in
  if checkGhosts
  then if vnth (rsGhostAllocs st) var is Some reg
       then check (rsGhostRegs st) reg
       else go
  else go.

Definition checkLiveness st : seq 'I_maxVar -> seq AllocError :=
  flip (forFold [::]) $ fun acc var =>
    if checkAlloc' st var None false false is Some err
    then err :: acc
    else acc.

Definition liveRegisters st : seq 'I_maxVar -> seq 'I_maxReg :=
  flip (forFold [::]) $ fun acc var =>
    if vnth (rsAllocs st) var is Some reg
    then reg :: acc
    else acc.

Definition clearGhost (reg : 'I_maxReg) (var : 'I_maxVar)
  (ghostRegs   : Vec (option 'I_maxVar) maxReg)
  (ghostAllocs : Vec (option 'I_maxReg) maxVar) :
  (Vec (option 'I_maxVar) maxReg * Vec (option 'I_maxReg) maxVar) :=
  (if vnth ghostAllocs var is Some r
   then vreplace ghostRegs r None
   else ghostRegs,
   if vnth ghostRegs reg is Some v
   then vreplace ghostAllocs v None
   else ghostAllocs).

Inductive RegState : RegStateDesc -> Prop :=
  | StartState : RegState newRegStateDesc

  | AllocRegS st r v :
    vnth (rsRegs   st) r == None ->
    vnth (rsAllocs st) v == None ->
    RegState
      {| rsRegs        := vreplace (rsRegs   st) r (Some v)
       ; rsAllocs      := vreplace (rsAllocs st) v (Some r)
       ; rsGhostRegs   := rsGhostRegs   st
       ; rsGhostAllocs := vreplace (rsGhostAllocs st) v None
       ; rsStack       := rsStack st
       |}

  | FreeRegS st r v :
    vnth (rsRegs   st) r == Some v ->
    vnth (rsAllocs st) v == Some r ->
    let: (gregs, gallocs) :=
       clearGhost r v (rsGhostRegs st) (rsGhostAllocs st) in
    RegState
      {| rsRegs        := vreplace (rsRegs   st) r None
       ; rsAllocs      := vreplace (rsAllocs st) v None
       ; rsGhostRegs   := vreplace gregs r (Some v)
       ; rsGhostAllocs := vreplace gallocs v (Some r)
       ; rsStack       := rsStack st
       |}

  | ClearGhostsS st :
    RegState
      {| rsRegs        := rsRegs st
       ; rsAllocs      := rsAllocs st
       ; rsGhostRegs   := vconst None
       ; rsGhostAllocs := vconst None
       ; rsStack       := rsStack st
       |}

  | AllocStackS st v :
    vnth (rsAllocs st) v == None ->
    vnth (rsStack  st) v == false ->
    RegState
      {| rsRegs        := rsRegs st
       ; rsAllocs      := rsAllocs st
       ; rsGhostRegs   := rsGhostRegs st
       ; rsGhostAllocs := rsGhostAllocs st
       ; rsStack       := vreplace (rsStack st) v true
       |}

  | FreeStackS st v :
    vnth (rsAllocs st) v == None ->
    vnth (rsStack  st) v == true ->
    RegState
      {| rsRegs        := rsRegs st
       ; rsAllocs      := rsAllocs st
       ; rsGhostRegs   := rsGhostRegs st
       ; rsGhostAllocs := rsGhostAllocs st
       ; rsStack       := vreplace (rsStack st) v false
       |}.

Definition getRegStateDesc `(st : RegState rd) := rd.
Arguments getRegStateDesc [rd] st /.

Definition packRegState `(st : RegState rd) := exist RegState rd st.
Arguments packRegState [rd] st /.

Variable A : Type.

Definition BlockExitAllocations :=
  IntMap (seq (('I_maxVar + 'I_maxVar) * 'I_maxReg)).

Record VerifiedSig := {
  verDesc   : RegStateDesc;
  verState  : RegState verDesc;
  (* [verBlocks] gives the final allocation state for any blocks; it only
     contains mappings for variables listed in a block's "live out" set. *)
  verBlocks : BlockExitAllocations;
  verMoves  : IntMap (seq (@ResolvingMove maxReg));
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

Definition _verBlocks : Lens' VerifiedSig BlockExitAllocations := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc   := verDesc s
     ; verState  := verState s
     ; verBlocks := x
     ; verMoves  := verMoves s
     ; verErrors := verErrors s
     ; verExt    := verExt s
     |}) (f (verBlocks s)).

Definition _verMoves :
  Lens' VerifiedSig (IntMap (seq (@ResolvingMove maxReg))) := fun _ _ f s =>
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

Definition checkAlloc (var : 'I_maxVar) (reg : 'I_maxReg) (checkGhosts : bool) :
  Verified unit :=
  st <-- use _verDesc ;;
  if checkAlloc' st var (Some reg)
                 (if useVerifier is VerifyEnabled
                  then true else false) checkGhosts is Some err
  then errorT err
  else pure tt.

Definition addMove (mv : @ResolvingMove maxReg) : Verified unit :=
  _verMoves %= IntMap_alter
    (fun mxs => @Some _ $ if mxs is Some xs
                          then rcons xs mv
                          else [:: mv]) pc.

Definition allocReg (reg : 'I_maxReg) (var : 'I_maxVar) : Verified unit :=
  addMove $ AllocReg var reg ;;
  st <-- use _verDesc ;;
  decide (vnth (rsRegs st) reg == None)
    (fun H1 =>
       decide (vnth (rsAllocs st) var == None)
         (fun H2 => _verState .= packRegState (AllocRegS H1 H2))
         (fun _  =>
            if vnth (rsAllocs st) var is Some r
            then errorT $ AllocVarAllocatedToDifferentReg var r reg
            else pure tt))
    (fun _  =>
       if vnth (rsRegs st) reg is Some v
       then
         when (v != var) $
           errorT $ AllocRegAllocatedToDifferentVar reg v var
       else pure tt).

Definition freeReg (reg : 'I_maxReg) (var : 'I_maxVar) : Verified unit :=
  addMove $ FreeReg reg var ;;
  st <-- use _verDesc ;;
  decide (vnth (rsRegs st) reg == Some var)
    (fun H1 =>
       decide (vnth (rsAllocs st) var == Some reg)
         (fun H2 => _verState .= packRegState (FreeRegS H1 H2))
         (fun _  =>
            if vnth (rsAllocs st) var is Some r
            then errorT $ FreeVarAllocatedToDifferentReg var r reg
            else errorT $ FreeUnallocatedVar var))
    (fun _  => errorT $ FreeRegNotAllocatedToVar reg var).

(* Definition allocStack (v : 'I_maxVar) : Verified unit := pure tt. *)

(* Definition freeStack (v : 'I_maxVar) : Verified unit := pure tt. *)

Lemma size_is0 : forall a (l : seq a), l = nil -> size l == 0.
Proof. move=> a. by case. Qed.

Definition checkVar (vid : VarId) : Verified 'I_maxVar :=
  if prop (vid < maxVar) is Some H
  then pure $ Ordinal H
  else
    errorT $ VarId_OutOfBounds vid maxVar ;;
    pure $ Ordinal variables_exist.

Definition verifyBlockBegin (bid : nat) (liveIns : IntSet) (loops : LoopState) :
  Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
  if IntMap_lookup bid (forwardBranches loops) is Some fwds
  then
    forFoldM true (IntSet_toList fwds) (fun isFirst pred =>
      exits <-- use _verBlocks ;;
      (if IntMap_lookup pred exits isn't Some allocs
       then errorT $ UnknownPredecessorBlock bid pred
       (* else forM_ (IntSet_toList liveIns) $ fun vid => *)
       (*   var <-- checkVar vid ;; *)
       (*   if maybeLookup allocs (inr var) is Some reg *)
       (*   then allocReg reg var *)
       (*   else *)
       (*     if maybeLookup allocs (inl var) is Some reg *)
       (*     then allocReg reg var ;; *)
       (*          freeReg reg var *)
       (*     else errorT $ VarWithoutAllocation vid *)
       else
         forM_ (IntSet_toList liveIns) (fun vid =>
           var <-- checkVar vid ;;
           if maybeLookup allocs (inr var) is Some reg
           then pure tt
           else
             if maybeLookup allocs (inl var) is Some reg
             then pure tt
             else errorT $ VarWithoutAllocation vid) ;;
         when isFirst $
           forM_ allocs $ fun z =>
             match z with
             | (inl var, reg) => allocReg reg var ;;
                                 freeReg reg var
             | (inr var, reg) => allocReg reg var
             end) ;;
      pure false) ;;
    pure tt
  else
    if IntSet_size liveIns == 0
    then pure tt
    else
      if useVerifier is VerifyEnabledUnitializedOK
      then pure tt
      else errorT $ BlockWithoutPredecessors bid.

Definition verifyBlockEnd (bid : nat) (liveOuts : IntSet) : Verified unit :=
  if useVerifier is VerifyDisabled then pure tt else
  st <-- use _verDesc ;;

  let allocs := vfoldl_with_index
    (fun var acc mreg =>
       if mreg is Some reg
       then (inr var, reg) :: acc
       else acc) [::] (rsAllocs st) in

  let allocs' := vfoldl_with_index
    (fun var acc mreg =>
       if mreg is Some reg
       then if maybeLookup acc (inr var) is None
            then if maybeValueLookup acc reg is None
                 then (inl var, reg) :: acc
                 else acc
            else acc
       else acc) allocs (rsGhostAllocs st) in

  _verBlocks %= IntMap_insert bid allocs' ;;

  decide (all (ltn ^~ maxVar) (IntSet_toList liveOuts))
    (fun L =>
       let vars := IntSet_to_seq_fin L in
       st <-- use _verDesc ;;
       if checkLiveness st vars is e :: es
       then errorsT $ ErrorAtBlockEnd bid :: e :: es
       else pure tt)
    (fun _ =>
       forM_ (IntSet_toList liveOuts) $ fun var =>
         when (maxVar <= var) $
           errorT $ VarId_OutOfBounds var maxVar) ;;

  (* Clear out all known allocations *)
  _verState .= packRegState StartState.

(*
Definition replaceReg (reg : 'I_maxReg) (var : 'I_maxVar) : Verified unit :=
  st <-- use _verDesc ;;
  (if vnth (rsRegs st) reg is Some v
   then freeReg reg v
   else pure tt) ;;
  allocReg reg var.
*)

Definition verifyApplyAllocs (op : opType1) (allocs : seq (VarId * PhysReg)) :
  Verified (seq opType2) :=
  (if useVerifier isn't VerifyDisabled
   then
     forM_ (opRefs oinfo op) (fun ref =>
       (* Determine which register this variable has been associated with by the
          allocation for this operation. *)
       match varId ref with
       | inl reg =>
         (* Direct register references are mostly left alone; we just check to
            make sure that it's not overwriting a variable in a register. *)
         st <-- use _verDesc ;;
         if vnth (rsRegs st) reg is Some v
         then errorT $ RegAlreadyAllocatedTo reg v
         else pure tt

       | inr vid =>
         if maybeLookup allocs vid isn't Some reg
         then errorT $ VarWithoutAllocation vid
         else
           var <-- checkVar vid ;;
           match varKind ref with
           | Input  => checkAlloc var reg true
           | Temp   => pure tt         (* jww (2015-07-04): What to do here? *)
           | Output => checkAlloc var reg false
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
      if vnth (rsRegs st) fromReg isn't Some fromVar
      then
        errorT $ MoveRegNotAllocated fromReg toReg ;;
        addMove (resMove mv) ;;
        pure acc
      else
        if fromReg == toReg
        then pure acc
        else
          freeReg fromReg fromVar ;;
          allocReg toReg fromVar ;;
          addMove (resMove mv) ;;
          when (resGhost mv) (freeReg toReg fromVar) ;;
          pure $ resMove mv :: acc

    | Swap fromReg fromVar toReg toVar =>
      if vnth (rsRegs st) fromReg isn't Some fromVar
      then
        errorT $ SwapRegNotAllocated fromReg toReg ;;
        addMove (resMove mv) ;;
        pure acc
      else
        if vnth (rsRegs st) toReg isn't Some toVar
        then
          errorT $ SwapRegNotAllocated toReg fromReg ;;
          addMove (resMove mv) ;;
          pure acc
        else
          if fromVar != toVar
          then checkAlloc toVar toReg false ;;
               checkAlloc fromVar fromReg false ;;
               addMove (resMove mv) ;;
               pure $ resMove mv :: acc
          else pure acc

    | Spill fromReg toSpillSlot =>
      if vnth (rsRegs st) fromReg isn't Some fromVar
      then
        errorT $ SpillRegNotAllocated fromReg toSpillSlot ;;
        addMove (resMove mv) ;;
        pure acc
      else
        stackVar <-- checkVar toSpillSlot ;;
        if fromVar != stackVar
        then
          errorT $ SpillToWrongSlot fromReg fromVar toSpillSlot ;;
          addMove (resMove mv) ;;
          pure acc
        else
          addMove (resMove mv) ;;
          freeReg fromReg fromVar ;;
          pure $ resMove mv :: acc

    | Restore fromSpillSlot toReg =>
      stackVar <-- checkVar fromSpillSlot ;;
      allocReg toReg stackVar ;;
      addMove (resMove mv) ;;
      when (resGhost mv) (freeReg toReg stackVar) ;;
      pure $ resMove mv :: acc

    | AllocReg toVar toReg =>
      var <-- checkVar toVar ;;
      allocReg toReg var ;;
      when (resGhost mv) (freeReg toReg var) ;;
      pure acc

    | FreeReg fromReg fromVar =>
      checkVar fromVar >>= freeReg fromReg ;;
      pure acc

    (* | AllocStack toVar => pure acc *)
    (* | FreeStack fromVar => pure acc *)
    end.

End Verify.

Module VerifyLensLaws.

Include LensLaws.

Variable a b : Type.
Variable P : a -> Prop.

(* Program Instance Lens__verDesc : GetterLaws (@_verDesc maxReg maxVar a). *)
Program Instance Lens__verState : LensLaws (@_verState maxReg maxVar a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verBlocks : LensLaws (@_verBlocks maxReg maxVar a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verMoves : LensLaws (@_verMoves maxReg maxVar a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verErrors : LensLaws (@_verErrors maxReg maxVar a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verExt : LensLaws (@_verExt maxReg maxVar a).
Obligation 2. by case: x. Qed.

End VerifyLensLaws.
