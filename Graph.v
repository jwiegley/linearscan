Require Import Allocate.
Require Import Lib.
Require Import Machine.

Generalizable All Variables.

Module MLinearScan (M : Machine).
Include MAllocate M.

(** * Program graphs *)

Definition VirtReg := nat.

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {
    postOrderTraversal : a
}.

Definition determineIntervals (g : Graph VirtReg)
  : { sd : ScanStateDesc | ScanState sd }.
  (* jww (2014-09-26): NYI *)
Admitted.

Definition allocateRegisters (g : Graph VirtReg) : ScanStateDesc :=
  proj1_sig (uncurry_sig linearScan (determineIntervals g)).

End MLinearScan.