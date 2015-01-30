Require Import LinearScan.Lib.

Module Type Machine.

Variable maxReg : nat.          (* max number of registers *)
Variable regSize : nat.         (* size of registers *)

Hypothesis registers_exist : maxReg > 0.

Definition PhysReg : predArgType := 'I_maxReg.

End Machine.
