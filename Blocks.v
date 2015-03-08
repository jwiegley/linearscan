Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Blocks.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

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

Inductive OpKind : Set := IsNormal | IsCall | IsBranch.

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
  showOp      : opType1 -> string
}.

Definition BlockId := nat.

Record BlockInfo (blockType1 blockType2 opType1 opType2 : Set) := {
  blockId         : blockType1 -> BlockId;
  blockSuccessors : blockType1 -> seq BlockId;
  blockOps        : blockType1 -> (seq opType1 * seq opType1 * seq opType1);
  setBlockOps     : blockType1 -> seq opType2 -> seq opType2 -> seq opType2
                      -> blockType2
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
    - Loop handling (reordering blocks to optimize allocation) *)

Definition foldOps {a} (f : a -> opType1 -> a) (z : a) : seq blockType1 -> a :=
  foldl (fun bacc blk => foldl f bacc (allBlockOps blk)) z.

Definition countOps : seq blockType1 -> nat :=
  foldOps (fun acc _ => acc.+1) 0.

End Blocks.
