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
  elim: (IntSet_toList s) => [|x xs IHxs] /= H.
    exact: [::].
  move/andP: H => [H1 H2].
  exact: cons (Ordinal H1) (IHxs _).
Defined.

Definition RV := ('I_maxReg + 'I_maxVar)%type.

Definition keepOnly {A : Type} `(xs : seq 'I_n) :
  Vec (option A) n -> Vec (option A) n :=
  vmap_with_index (fun i x => if i \in xs then x else None).

Definition verifyLiveness (st : RegStateDesc) : seq 'I_maxVar -> bool :=
  all (fun var =>
    if vnth (rsAllocs st) var isn't Some reg  then false else
    if vnth (rsRegs st)   reg isn't Some var' then false else
    var == var').

Definition liveRegisters (st : RegStateDesc) : seq 'I_maxVar -> seq 'I_maxReg :=
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
    verifyLiveness st lives ->
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

(*
  | MoveReg st r1 r2 v :
    vnth (rsRegs st) r1 == Some v ->
    vnth (rsRegs st) r2 == None ->
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}

  | SwapReg st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}

  | SpillReg st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}

  | LoadReg st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}
*)

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
       |}

  | UseReg st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}

  | SetReg st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}.

Variable A : Type.

Definition AllocError := nat.

(* The [Verified] transformer stack uses [EitherT] to allow sudden exit due to
   error, otherwise it maintains the current [RegState] plus whatever
   additional state the user desires. *)
Definition Verified :=
  EitherT AllocError (StateT { d : RegStateDesc * A | RegState (fst d) } mType).

Definition verifyCheckBlock (liveIn : IntSet) : Verified unit := pure tt.

Definition verifyApplyAllocs (op : opType1) (allocs : seq (VarId * PhysReg)) :
  Verified (seq opType2) :=
  lift $ lift $ applyAllocs oinfo op allocs.

Definition verifyResolutions (moves : seq (ResolvingMove maxReg)) :
  Verified unit := pure tt.

End Verify.
