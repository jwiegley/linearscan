(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Machine.
Require Import Graph.

Module MyMachine <: Machine.

Definition maxReg := 32.

Lemma registers_exist : maxReg > 0.
Proof. unfold maxReg. omega. Qed.

End MyMachine.

Module Import LinearScan := MLinearScan MyMachine.

(* Set Extraction KeepSingleton. *)
(* Unset Extraction AutoInline. *)

Extraction Language Haskell.

(** Danger!  Using Int is efficient, but requires we know we won't exceed its
    bounds. *)
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive unit    => "()" [ "()" ].
Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
(* Extract Inductive sumbool => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ]. *)
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive prod    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant negb => "(Prelude.not)".
Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant eqb  => "(Prelude.==)".
Extract Inlined Constant plus => "(Prelude.+)".
Extract Inlined Constant mult => "(Prelude.*)".
Extract Inlined Constant app  => "(Prelude.++)".

Extract Inlined Constant map        => "(Prelude.map)".
Extract Inlined Constant fold_left  => "(\f -> Prelude.flip (Data.List.foldl' f))".
Extract Inlined Constant fold_right => "Prelude.foldr".
Extract Inlined Constant existsb    => "(Prelude.any)".
Extract Inlined Constant filter     => "(Prelude.filter)".
Extract Inlined Constant proj1_sig  => "".

Extraction Blacklist String List Vector NonEmpty.

Separate Extraction LinearScan.allocateRegisters.
