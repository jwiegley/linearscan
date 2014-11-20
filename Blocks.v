Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.NonEmpty.
Require Import LinearScan.Range.
Require Import LinearScan.Vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MBlocks (Mach : Machine).

(* Import Mach. *)

Section Blocks.

Variable blockType : Set.

Definition computeBlockOrder (blocks : seq blockType) : seq blockType :=
  (* jww (2014-11-19): Implementing this function provides an opportunity to
     optimize for better allocation. *)
  blocks.

End Blocks.

End MBlocks.