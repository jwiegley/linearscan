Require Import LinearScan.Lib.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Trans.Either.
Require Import Hask.Control.Monad.Trans.State.
Require Import LinearScan.Context.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.Resolve.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Verify.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Variable maxVar : nat.          (* max number of variables *)
Variables opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable oinfo : OpInfo maxReg opType1 opType2.

Record RegStateDesc := {
  rsRegs   : Vec (option 'I_maxVar) maxReg;
  rsAllocs : Vec (option 'I_maxReg) maxVar;
  rsStack  : Vec bool maxVar
}.

Definition newRegStateDesc : RegStateDesc :=
  {| rsRegs   := vconst None
   ; rsAllocs := vconst None
   ; rsStack  := vconst false
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

Inductive AllocError :=
  | VarId_OutOfBounds of VarId & nat
  | VarNotAllocated of VarId
  | FreeUnallocatedVar of VarId
  | FreeVarAllocatedToDifferentReg of VarId & nat & nat
  | FreeRegNotAllocatedToVar of nat & VarId
  | VarWithoutAllocation of VarId
  | VarAllocatedToDifferentReg of VarId & nat & nat
  | RegNotAllocated of nat
  | RegNotAllocatedToVar of nat & VarId
  | RegAllocatedToDifferentVar of nat & VarId & VarId
  | RegAlreadyAllocatedTo of nat & VarId
  | SpillingToWrongSlot of nat & VarId & VarId.

Definition checkAlloc' st (var : 'I_maxVar) : option AllocError :=
  if vnth (rsAllocs st) var isn't Some reg
  then Some (VarNotAllocated var)
  else if vnth (rsRegs st) reg isn't Some var'
       then Some (RegNotAllocatedToVar reg var)
       else if var == var'
            then None
            else Some (RegAllocatedToDifferentVar reg var var').

Definition checkLiveness st : seq 'I_maxVar -> seq AllocError :=
  flip (forFold [::]) $ fun acc var =>
    if checkAlloc' st var is Some err
    then err :: acc
    else acc.

Definition liveRegisters st : seq 'I_maxVar -> seq 'I_maxReg :=
  flip (forFold [::]) $ fun acc var =>
    if vnth (rsAllocs st) var is Some reg
    then reg :: acc
    else acc.

Inductive RegState : RegStateDesc -> Prop :=
  | StartState : RegState newRegStateDesc

  | AllocReg st r v :
    vnth (rsRegs   st) r == None ->
    vnth (rsAllocs st) v == None ->
    RegState
      {| rsRegs   := vreplace (rsRegs   st) r (Some v)
       ; rsAllocs := vreplace (rsAllocs st) v (Some r)
       ; rsStack  := rsStack st
       |}

  | FreeReg st r v :
    vnth (rsRegs   st) r == Some v ->
    vnth (rsAllocs st) v == Some r ->
    RegState
      {| rsRegs   := vreplace (rsRegs   st) r None
       ; rsAllocs := vreplace (rsAllocs st) v None
       ; rsStack  := rsStack st
       |}

  | AllocStack st v :
    vnth (rsAllocs st) v == None ->
    vnth (rsStack  st) v == false ->
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := vreplace (rsStack st) v true
       |}

  | FreeStack st v :
    vnth (rsAllocs st) v == None ->
    vnth (rsStack  st) v == true ->
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := vreplace (rsStack st) v false
       |}.

Definition getRegStateDesc `(st : RegState rd) := rd.
Arguments getRegStateDesc [rd] st /.

Variable A : Type.

Record VerifiedSig := {
  verDesc  : RegStateDesc;
  verState : RegState verDesc;
  verExt   : A
}.

Definition _verDesc : Getter VerifiedSig RegStateDesc := fun _ _ _ f s =>
  fmap (const s) (f (verDesc s)).

Definition _verState :
  Lens' VerifiedSig { rd : RegStateDesc | RegState rd } := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc  := x.1
     ; verState := x.2
     ; verExt   := verExt s
     |}) (f (verDesc s; verState s)).

Definition _verExt : Lens' VerifiedSig A := fun _ _ f s =>
  fmap (fun x =>
    {| verDesc  := verDesc s
     ; verState := verState s
     ; verExt   := x
     |}) (f (verExt s)).

Definition packVerified `(st : RegState rd) (s : A) : VerifiedSig :=
  {| verDesc  := rd
   ; verState := st
   ; verExt   := s |}.
Arguments packVerified [rd] st s /.

(* The [Verified] transformer stack uses [EitherT] to allow sudden exit due to
   error, otherwise it maintains the current [RegState] plus whatever
   additional state the user desires. *)
Definition Verified :=
  StateT VerifiedSig (EitherT (OpId * seq AllocError) mType).

Definition _aside {a b : Type} {P : a -> Prop} :
  Lens' { x : a * b | P (fst x) } b :=
  fun _ _ f s =>
    let: exist (x, y) H := s in
    fmap (fun z => exist _ (x, z) H) (f y).

Definition resetAllocState : Verified unit :=
  a <-- use _verExt ;;
  putT $ packVerified StartState a.

Definition runVerified `(m : Verified b) (i : A) :
  mType ((OpId * seq AllocError) + b) :=
  fst <$> m {| verDesc  := newRegStateDesc
             ; verState := StartState
             ; verExt   := i |}.

Definition decide {T : Type} (H : bool)
  (kt : (H = true)  -> T)
  (kf : (H = false) -> T) : T :=
  (fun (if_true  : (fun b : bool => protect_term (H = b) -> T) true)
       (if_false : (fun b : bool => protect_term (H = b) -> T) false) =>
    if H as b return ((fun b0 : bool => protect_term (H = b0) -> T) b)
    then if_true
    else if_false)
  (fun (E : H = true)  => kt E)
  (fun (E : H = false) => kf E)
  (erefl H).

Arguments decide {T} H kt kf.

Variable pc : OpId.

Definition errorsT {a} (errs : seq AllocError) : Verified a :=
  fun _ => pure $ inl (pc, errs).

Definition errorT {a} (err : AllocError) : Verified a :=
  errorsT [:: err].

Definition checkAlloc (var : 'I_maxVar) : Verified unit :=
  st <-- use _verDesc ;;
  if checkAlloc' st var is Some err
  then errorT err
  else pure tt.

Definition allocReg (reg : 'I_maxReg) (var : 'I_maxVar) : Verified unit :=
  st <-- use _verDesc ;;
  a  <-- use _verExt ;;
  decide (vnth (rsRegs st) reg == None)
    (fun H1 =>
       decide (vnth (rsAllocs st) var == None)
         (fun H2 => putT $ packVerified (AllocReg H1 H2) a)
         (fun _  =>
            if vnth (rsAllocs st) var is Some r
            then errorT $ VarAllocatedToDifferentReg var reg r
            else pure tt))
    (fun _  =>
       if vnth (rsRegs st) reg is Some v
       then
         when (v != var) $
           errorT $ RegAllocatedToDifferentVar reg var v
       else pure tt).

Definition freeReg (reg : 'I_maxReg) (var : 'I_maxVar) : Verified unit :=
  st <-- use _verDesc ;;
  a  <-- use _verExt ;;
  decide (vnth (rsRegs st) reg == Some var)
    (fun H1 =>
       decide (vnth (rsAllocs st) var == Some reg)
         (fun H2 => putT $ packVerified (FreeReg H1 H2) a)
         (fun _  =>
            if vnth (rsAllocs st) var is Some r
            then errorT $ FreeVarAllocatedToDifferentReg var reg r
            else errorT $ FreeUnallocatedVar var))
    (fun _  => errorT $ FreeRegNotAllocatedToVar reg var).

(* Definition allocStack (v : 'I_maxVar) : Verified unit := pure tt. *)

(* Definition freeStack (v : 'I_maxVar) : Verified unit := pure tt. *)

Lemma size_is0 : forall a (l : seq a), l = nil -> size l == 0.
Proof. move=> a. by case. Qed.

Definition checkVar (vid : VarId) : Verified 'I_maxVar :=
  decide (vid < maxVar)
    (fun H => pure $ Ordinal H)
    (fun _ => errorT $ VarId_OutOfBounds vid maxVar).

Definition verifyBlockBegin (liveIns : IntSet)
  (allocs : seq (VarId * PhysReg)) : Verified unit :=
  resetAllocState ;;
  forM_ (IntSet_toList liveIns) $ fun vid =>
    if maybeLookup allocs vid isn't Some reg
    then errorT $ VarWithoutAllocation vid
    else checkVar vid >>= allocReg reg.

Definition verifyBlockEnd (liveOuts : IntSet) : Verified unit :=
  decide (all (ltn ^~ maxVar) (IntSet_toList liveOuts))
    (fun L =>
       st <-- use _verDesc ;;
       if checkLiveness st (IntSet_to_seq_fin L) is e :: es
       then errorsT (e :: es)
       else pure tt)
    (fun _ =>
       forM_ (IntSet_toList liveOuts) $ fun var =>
         when (maxVar <= var) $
           errorT $ VarId_OutOfBounds var maxVar).

Definition verifyApplyAllocs (op : opType1) (allocs : seq (VarId * PhysReg)) :
  Verified (seq opType2) :=
  forM_ (opRefs oinfo op) (fun ref =>
    (* Get the current allocation state of all registers. *)
    st <-- use _verDesc ;;

    (* Determine which register this variable has been associated with by the
       allocation for this operation. *)
    match varId ref with
    | inl reg =>
      (* Direct register references are mostly left alone; we just check to
         make sure that it's not overwriting a variable in a register. *)
      if vnth (rsRegs st) reg is Some v
      then errorT $ RegAlreadyAllocatedTo reg v
      else pure tt

    | inr vid =>
      if maybeLookup allocs vid isn't Some reg
      then errorT $ VarWithoutAllocation vid
      else
        var <-- checkVar vid ;;
        match varKind ref with
        | Input  => checkAlloc var
        | Temp   => pure tt         (* jww (2015-07-04): What to do here? *)
        | Output =>
            (* Writing to a register undoes any previous allocation. *)
            (if vnth (rsRegs st) reg is Some v
             then freeReg reg v
             else pure tt) ;;
            allocReg reg var
        end
    end) ;;

  lift $ lift $ applyAllocs oinfo op allocs.

Definition verifyResolutions (moves : seq (ResolvingMove maxReg)) :
  Verified unit :=
  forM_ moves $ fun mv =>
    st <-- use _verDesc ;;
    match mv with
    | Move fromReg toReg =>
      if vnth (rsRegs st) fromReg isn't Some fromVar
      then errorT $ RegNotAllocated fromReg
      else
        if vnth (rsRegs st) toReg is Some toVar
        then errorT $ RegAlreadyAllocatedTo toReg toVar
        else
          freeReg fromReg fromVar ;;
          allocReg toReg fromVar

    | Swap fromReg toReg =>
      if vnth (rsRegs st) fromReg isn't Some fromVar
      then errorT $ RegNotAllocated fromReg
      else
        if vnth (rsRegs st) toReg isn't Some toVar
        then errorT $ RegNotAllocated toReg
        else
          when (fromVar != toVar) $
            freeReg toReg toVar ;;
            freeReg fromReg fromVar ;;
            allocReg toReg fromVar ;;
            allocReg fromReg toVar

    | Spill fromReg toSpillSlot =>
      if vnth (rsRegs st) fromReg isn't Some fromVar
      then errorT $ RegNotAllocated fromReg
      else
        stackVar <-- checkVar toSpillSlot ;;
        if fromVar != stackVar
        then errorT $ SpillingToWrongSlot fromReg toSpillSlot fromVar
        else
          freeReg fromReg fromVar ;;
          (* checkStackFree *)
          (* AllocStack *)
          pure tt

    | Restore fromSpillSlot toReg =>
      stackVar <-- checkVar fromSpillSlot ;;
      if vnth (rsRegs st) toReg is Some toVar
      then
        when (toVar != stackVar) $
          freeReg toReg toVar ;;
          allocReg toReg stackVar
      else
        (* checkStackAlloc ;; *)
        allocReg toReg stackVar

    | Nop => pure tt
    end.

End Verify.

Module VerifyLensLaws.

Include LensLaws.

Variable a b : Type.
Variable P : a -> Prop.

Program Instance Lens__aside : LensLaws (@_aside a b P).

(* Program Instance Lens__verDesc : GetterLaws (@_verDesc maxReg maxVar a). *)
Program Instance Lens__verState : LensLaws (@_verState maxReg maxVar a).
Obligation 2. by case: x. Qed.
Program Instance Lens__verExt : LensLaws (@_verExt maxReg maxVar a).
Obligation 2. by case: x. Qed.

End VerifyLensLaws.
