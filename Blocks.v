Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Blocks.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Inductive VarKind : Set := Input | Temp | Output.

Section EqVarKind.

Implicit Type s : VarKind.

Fixpoint eqVarKind s1 s2 {struct s2} :=
  match s1, s2 with
  | Input, Input   => true
  | Temp, Temp     => true
  | Output, Output => true
  | _, _           => false
  end.

Lemma eqVarKindP : Equality.axiom eqVarKind.
Proof.
  move.
  move=> b1 b2 /=.
  case: b1; case: b2=> /=;
  constructor=> //=;
  by case.
Qed.

Canonical VarKind_eqMixin := EqMixin eqVarKindP.
Canonical VarKind_eqType :=
  Eval hnf in EqType VarKind VarKind_eqMixin.

End EqVarKind.

Definition VarId := nat.

(* [VarInfo] abstracts information about the caller's notion of variables
   associated with an operation. *)
Record VarInfo := {
  varId       : PhysReg + VarId;   (* from 0 to highest var index *)
  varKind     : VarKind;
  regRequired : bool
}.

Definition nat_of_varId v := match varId v with
  | inl n => nat_of_ord n
  | inr v => v + maxReg
  end.

Inductive OpKind : Set :=
  IsNormal | IsCall | IsBranch | IsLoopBegin | IsLoopEnd.

Definition OpId := nat.

(* The [OpInfo] structure is a collection of functions that allow us to
   determine information about each operation coming from the caller's
   side. *)
Record OpInfo (accType opType1 opType2 : Set) := {
  opKind      : opType1 -> OpKind;
  opRefs      : opType1 -> seq VarInfo;
  moveOp      : PhysReg -> PhysReg -> accType -> seq opType2 * accType;
  swapOp      : PhysReg -> PhysReg -> accType -> seq opType2 * accType;
  saveOp      : PhysReg -> option VarId -> accType -> seq opType2 * accType;
  restoreOp   : option VarId -> PhysReg -> accType -> seq opType2 * accType;
  applyAllocs : opType1 -> seq (VarId * PhysReg) -> seq opType2;
  showOp1     : OpId -> seq (nat * (PhysReg + VarId))
                     -> seq (nat * (PhysReg + VarId)) -> opType1 -> string
}.

Definition BlockId := nat.

Record BlockInfo (blockType1 blockType2 opType1 opType2 : Set) := {
  blockId         : blockType1 -> BlockId;
  blockSuccessors : blockType1 -> seq BlockId;
  blockOps        : blockType1 -> (seq opType1 * seq opType1 * seq opType1);
  setBlockOps     : blockType1 -> seq opType2 -> seq opType2 -> seq opType2
                      -> blockType2;
  showBlock1      : BlockId
                 -> OpId
                 -> IntSet     (* liveIn *)
                 -> IntSet     (* liveOut *)
                 -> (OpId -> seq opType1 -> string)
                 -> blockType1
                 -> string;
  traceBlocks     : string -> seq blockType1 -> seq blockType1
}.

Close Scope string_scope.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo accType opType1 opType2.

Definition allBlockOps (block : blockType1) : seq opType1 :=
  let: (a, b, c) := blockOps binfo block in a ++ b ++ c.

Definition blockSize (block : blockType1) := size (allBlockOps block).

(* jww (2015-01-12): Some of the things described by Wimmer in the section on
   dealing with computing of intervals have yet to be done:

   - Loop handling (reordering blocks to optimize allocation)
   - Extending of ranges for input/output variables
*)

Definition foldOps {a} (f : a -> opType1 -> a) (z : a) : seq blockType1 -> a :=
  foldl (fun bacc blk => foldl f bacc (allBlockOps blk)) z.

Definition countOps : seq blockType1 -> nat :=
  foldOps (fun acc _ => acc.+1) 0.

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations (blocks : seq blockType1) : seq blockType1 :=
  blocks.

End Blocks.

Tactic Notation "VarKind_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "VarKind_Input"
  | Case_aux c "VarKind_Temp"
  | Case_aux c "VarKind_Output"
  ].
