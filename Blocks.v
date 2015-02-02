Require Import LinearScan.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Blocks.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Inductive VarKind : Set := Input | Temp | Output.

Definition VarId := nat.

(* [VarInfo] abstracts information about the caller's notion of variables
   associated with an operation. *)
Record VarInfo (varType : Set) := {
  varId       : varType -> VarId;     (* from 0 to highest var index *)
  varKind     : varType -> VarKind;
  regRequired : varType -> bool
}.

Inductive OpKind : Set :=
  IsNormal | IsCall | IsBranch | IsLoopBegin | IsLoopEnd.

(* The [OpInfo] structure is a collection of functions that allow us to
   determine information about each operation coming from the caller's
   side. *)
Record OpInfo (accType opType1 opType2 varType : Set) := {
  opKind      : opType1 -> OpKind;
  opRefs      : opType1 -> seq varType * seq PhysReg;
  moveOp      : PhysReg -> PhysReg -> accType -> seq opType2 * accType;
  swapOp      : PhysReg -> PhysReg -> accType -> seq opType2 * accType;
  saveOp      : PhysReg -> option VarId -> accType -> seq opType2 * accType;
  restoreOp   : option VarId -> PhysReg -> accType -> seq opType2 * accType;
  applyAllocs : opType1 -> seq (VarId * PhysReg) -> seq opType2
}.

Definition BlockId := nat.

Record BlockInfo (blockType1 blockType2 opType1 opType2 : Set) := {
  blockId         : blockType1 -> BlockId;
  blockSuccessors : blockType1 -> seq BlockId;
  blockOps        : blockType1 -> seq opType1;
  setBlockOps     : blockType1 -> seq opType2 -> blockType2
}.

Variables blockType1 blockType2 opType1 opType2 varType accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo accType opType1 opType2 varType.
Variable vinfo : VarInfo varType.

Definition blockSize (block : blockType1) := size (blockOps binfo block).

(* jww (2015-01-12): Some of the things described by Wimmer in the section on
   dealing with computing of intervals have yet to be done:

   - Loop handling (reordering blocks to optimize allocation)
   - Extending of ranges for input/output variables
*)

Definition OpId := nat.

Definition foldOps {a} (f : a -> opType1 -> a) (z : a) : seq blockType1 -> a :=
  foldl (fun bacc blk => foldl f bacc (blockOps binfo blk)) z.

Definition countOps : seq blockType1 -> nat :=
  foldOps (fun acc _ => acc.+1) 0.

Definition foldOpsRev {a} (f : a -> opType1 -> a) (z : a)
  (blocks : seq blockType1) : a :=
  foldl (fun bacc blk => foldl f bacc (rev (blockOps binfo blk)))
        z (rev blocks).

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
