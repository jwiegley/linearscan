Require Import LinearScan.Lib.

Module Type Machine.

Variable maxReg : nat.          (* max number of registers *)

Hypothesis registers_exist : maxReg > 0.

Definition PhysReg := 'I_maxReg.

End Machine.
