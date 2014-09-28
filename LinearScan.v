(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import Machine.
Require Import Allocate.

Module MyMachine <: Machine.

Definition maxReg := 32.

Lemma registers_exist : maxReg > 0.
Proof. unfold maxReg. omega. Qed.

End MyMachine.

Module Import Allocator := MAllocate MyMachine.

(* Set Extraction KeepSingleton. *)
(* Unset Extraction AutoInline. *)

Extraction Language Haskell.

Separate Extraction allocateRegisters.
