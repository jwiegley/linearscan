Require Import LinearScan.Lib.
Require Import Hask.Control.Monad.Trans.State.
Require Import LinearScan.Context.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.ScanState.
Require Import LinearScan.Morph.
Require Import LinearScan.Cursor.
Require Import LinearScan.Spec.
Require Import LinearScan.Spill.
Require Import LinearScan.Split.

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

Inductive RegState : RegStateDesc -> Prop :=
  | StartState : RegState newRegStateDesc

  (* Based on the code flow analysis, [ins] is the set of incoming registers.
     Anything other than these should not be presently active, all them should
     be active, and they should apply to the correct variables. *)
  | BeginBlock st ins :
    forall H : all (ltn ^~ maxVar) (IntSet_toList ins),
    all (fun var =>
           if vnth (rsAllocs st) var isn't Some reg  then false else
           if vnth (rsRegs st)   reg isn't Some var' then false else
           var == var') (IntSet_to_seq_fin H) ->
    RegState
      {| rsRegs   := rsRegs st
       ; rsAllocs := rsAllocs st
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

Definition Verified := StateT { d : RegStateDesc * A | RegState (fst d) } mType.

Definition verifyApplyAllocs (op : opType1) (allocs : seq (VarId * PhysReg)) :
  Verified (seq opType2) :=
  lift $ iso_to $ applyAllocs oinfo op allocs.

End Verify.
