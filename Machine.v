Require Import Lib.

Module Type Machine.

Variable maxReg : nat.          (* max number of registers *)

Hypothesis registers_exist : maxReg > 0.

End Machine.
