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
  | VarNotAllocated of VarId
  | RegNotAllocatedToVar of nat & VarId
  | RegAllocatedToDifferentVar of nat & VarId & VarId
  | VarId_OutOfBounds.

Definition checkLiveness st : seq 'I_maxVar -> seq AllocError :=
  flip (forFold [::]) $ fun acc var =>
    if vnth (rsAllocs st) var isn't Some reg
    then VarNotAllocated var :: acc
    else if vnth (rsRegs st) reg isn't Some var'
         then RegNotAllocatedToVar reg var :: acc
         else if nat_of_ord var == var'
              then acc
              else RegAllocatedToDifferentVar reg var var' :: acc.

Definition liveRegisters st : seq 'I_maxVar -> seq 'I_maxReg :=
  flip (forFold [::]) $ fun acc var =>
    if vnth (rsAllocs st) var is Some reg
    then reg :: acc
    else acc.

Inductive RegState : RegStateDesc -> Prop :=
  | StartState : RegState newRegStateDesc

  (* Based on the code flow analysis, [ins] is the set of incoming registers.
     Anything other than these should not be presently active, all them should
     be active, and they should apply to the correct variables. *)
  | BlockCheck st (lives : seq 'I_maxVar) :
    size (checkLiveness st lives) == 0 ->
    RegState
      {| rsRegs   := keepOnly (liveRegisters st lives) $ rsRegs st
       ; rsAllocs := keepOnly lives $ rsAllocs st
       ; rsStack  := rsStack st
       |}

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

Definition VerifiedSig := { d : RegStateDesc * A | RegState (fst d) }.

Definition packVerified `(st : RegState rd) (s : A) :=
  exist (RegState \o fst) (rd, s) st.
Arguments packVerified [rd] st s /.

(* The [Verified] transformer stack uses [EitherT] to allow sudden exit due to
   error, otherwise it maintains the current [RegState] plus whatever
   additional state the user desires. *)
Definition Verified := EitherT (seq AllocError) (StateT VerifiedSig mType).

Definition _rs {a b : Type} {P : a -> Prop} :
  Getter { x : a * b | P (fst x) } a :=
  fun _ _ _ f s => fmap (const s) (f (fst (proj1_sig s))).

Definition _aside {a b : Type} {P : a -> Prop} :
  Lens' { x : a * b | P (fst x) } b :=
  fun _ _ f s =>
    let: exist (x, y) H := s in
    fmap (fun z => exist _ (x, z) H) (f y).

Definition runVerified `(m : Verified b) (i : A) : mType (seq AllocError + b) :=
  fmap fst <$> m (exist _ (newRegStateDesc, i) StartState).

Definition allocReg (r : 'I_maxReg) (v : 'I_maxVar) : Verified unit := pure tt.

Definition freeReg (r : 'I_maxReg) (v : 'I_maxVar) : Verified unit := pure tt.

Definition allocStack (v : 'I_maxVar) : Verified unit := pure tt.

Definition freeStack (v : 'I_maxVar) : Verified unit := pure tt.

Definition verifyCheckBlock' (st : RegStateDesc) (s : A) (lives : IntSet) :
  seq AllocError + VerifiedSig.
Proof.
  case L: (all (ltn ^~ maxVar) (IntSet_toList lives)).
    have l := IntSet_to_seq_fin L.
    move=> {L lives}.
    case B: (checkLiveness st l) => [|e es].
      have H : size (checkLiveness st l) == 0.
        by rewrite B.
      exact (inr (packVerified (BlockCheck H) s)).
    exact: inl (e :: es).
  exact: inl [:: VarId_OutOfBounds].
Defined.

Definition verifyCheckBlock (lives : IntSet) : Verified unit :=
  pure tt.
  (* z <-- lift $ use _ex1 ;; *)
  (* let: (st, a) := z in *)
  (* match verifyCheckBlock' st a lives *)
  (* return Verified unit with *)
  (* | inl es => pure (inl es) *)
  (* | inr x  => lift $ putT x *)
  (* end. *)

Definition verifyApplyAllocs (op : opType1) (allocs : seq (VarId * PhysReg)) :
  Verified (seq opType2) :=
  lift $ lift $ applyAllocs oinfo op allocs.

Definition verifyResolutions (moves : seq (ResolvingMove maxReg)) :
  Verified unit :=
  forM_ moves $ fun mv =>
    match mv with
    | Move    x y =>
        pure tt
    | Swap    x y =>
        pure tt
    | Spill   x s =>
        pure tt
    | Restore s x =>
        pure tt
    | Nop         =>
        pure tt
    end.

End Verify.

Module VerifyLensLaws.

Include LensLaws.

Variable a b : Type.
Variable P : a -> Prop.

(* Program Instance Lens__rs : LensLaws (@_rs a b P). *)
Program Instance Lens__aside : LensLaws (@_aside a b P).

End VerifyLensLaws.
