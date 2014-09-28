Require Import Machine.
Require Import LinearScan.

Module MyMachine <: Machine.

Definition maxReg := 32.

Lemma registers_exist : maxReg > 0.
Proof. unfold maxReg. omega. Qed.

End MyMachine.

Module Import LS := MLinearScan MyMachine.

Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extraction Language Haskell.

Separate Extraction allocateRegisters.
