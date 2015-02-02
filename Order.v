Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.Blocks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MOrder (Mach : Machine).

Include MBlocks Mach.

Section Order.

Variables blockType1 blockType2 opType1 opType2 varType accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo accType opType1 opType2 varType.
Variable vinfo : VarInfo varType.

(* jww (2014-11-19): Note that we are currently not computing the block order
   in any intelligent way. This is covered in quite some depth in Christian
   Wimmer's thesis.  At the moment we're simply accepting whatever block order
   is passed to us by the caller.  However, implementing this function
   properly is a strong means of improving the accuracy and efficiency of this
   algorithm. *)
Definition computeBlockOrder (blocks : seq blockType1) :
  seq blockType1 := blocks.

End Order.

End MOrder.
