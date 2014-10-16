Require Import Allocate.
Require Import Lib.
Require Import NonEmpty.
Require Import Range.
Require Import Machine.

Generalizable All Variables.

Module MLinearScan (M : Machine).
Include MAllocate M.

(** * Program graphs *)

Definition VirtReg := nat.

Class Block := {
    loopStart  : bool;
    loopEnd    : bool;
    references : list (VirtReg + PhysReg)
}.

Fixpoint processBlocks (maxVirtReg : nat)
  (blocks : NonEmpty Block) (offset : nat)
  (start stop : option nat ) : nat * Vec (NonEmpty UsePos) maxVirtReg * nat.
Admitted.

Definition determineIntervals (blocks : NonEmpty Block)
  : { sd : ScanStateDesc | ScanState sd }.
Admitted.

Definition allocateRegisters (blocks : NonEmpty Block) : ScanStateDesc :=
  proj1_sig (uncurry_sig linearScan (determineIntervals blocks)).

End MLinearScan.