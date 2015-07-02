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

Inductive RegState : RegStateDesc -> Prop :=
  | StartState : RegState newRegStateDesc

  (* Based on the code flow analysis, [ins] is the set of incoming registers.
     Anything other than these should not be presently active, all them should
     be active, and they should apply to the correct variables. *)
  | BeginBlock st (liveIns : seq 'I_maxVar) :
    all (fun var =>
           if vnth (rsAllocs st) var isn't Some reg  then false else
           if vnth (rsRegs st)   reg isn't Some var' then false else
           var == var') liveIns ->
    let liveRegs := forFold [::] liveIns $ fun acc var =>
      if vnth (rsAllocs st) var is Some reg
      then reg :: acc
      else acc in
    RegState
      {| rsRegs   := keepOnly liveRegs $ rsRegs st
       ; rsAllocs := keepOnly liveIns $ rsAllocs st
       ; rsStack  := rsStack st
       |}

  | EndBlock st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}

  | AllocReg st r v :
    RegState
      {| rsRegs   := vreplace (rsRegs st) r (Some v)
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}

  | MoveReg st :
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

  | RestoreReg st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
       |}

  | FreeReg st :
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
       ; rsStack  := rsStack st
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

Definition Verified :=
  EitherT AllocError (StateT { d : RegStateDesc * A | RegState (fst d) } mType).

Definition verifyBlockBegin (liveIn : IntSet) : Verified unit := pure tt.

Definition verifyApplyAllocs (op : opType1) (allocs : seq (VarId * PhysReg)) :
  Verified (seq opType2) :=
  lift $ lift $ applyAllocs oinfo op allocs.

Definition verifyResolutions (moves : seq (ResolvingMove maxReg)) :
  Verified unit := pure tt.

Definition verifyBlockEnd (liveOut : IntSet) : Verified unit := pure tt.

End Verify.
