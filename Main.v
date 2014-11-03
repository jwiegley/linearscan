(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import Lib.
Require Import Blocks.
Require Import Machine.

Module MyMachine <: Machine.

Definition maxReg := 32.

Lemma registers_exist : (maxReg > 0).
Proof. unfold maxReg. ssomega. Qed.

End MyMachine.

Module Import LinearScan := MLinearScan MyMachine.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(** Danger!  Using Int is efficient, but requires we know we won't exceed its
    bounds. *)
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive unit    => "()" [ "()" ].
Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sum     => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive prod    => "(,)" ["(,)"].
Extract Inductive sigT    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant andb       => "(Prelude.&&)".
Extract Inlined Constant app        => "(Prelude.++)".
Extract Inlined Constant apply      => "(Prelude.$)".
Extract Inlined Constant beq_nat    => "(Prelude.==)".
Extract Inlined Constant compose    => "(Prelude..)".
Extract Inlined Constant eqb        => "(Prelude.==)".
(* Extract Inlined Constant existsb    => "(Prelude.any)". *)
Extract Inlined Constant filter     => "(Prelude.filter)".
(* Extract Inlined Constant fold_left  => "(\f -> Prelude.flip (Data.List.foldl' f))". *)
Extract Inlined Constant foldl      => "Data.List.foldl'".
(* Extract Inlined Constant fold_right => "Prelude.foldr". *)
Extract Inlined Constant foldr      => "Prelude.foldr".
Extract Inlined Constant fst        => "(Prelude.fst)".
(* Extract Inlined Constant id         => "(Prelude.id)". *)
Extract Inlined Constant length     => "(Data.List.length)".
Extract Inlined Constant size       => "(Data.List.length)".
Extract Inlined Constant map        => "(Prelude.map)".
Extract Inlined Constant predn      => "(Prelude.pred)".
Extract Inlined Constant minus      => "(Prelude.-)".
Extract Inlined Constant mult       => "(Prelude.*)".
Extract Inlined Constant negb       => "(Prelude.not)".
Extract Inlined Constant orb        => "(Prelude.||)".
Extract Inlined Constant plus       => "(Prelude.+)".
Extract Inlined Constant proj1_sig  => "".
Extract Inlined Constant safe_hd    => "(Prelude.head)".
Extract Inlined Constant snd        => "(Prelude.snd)".
Extract Inlined Constant tail_plus  => "(Prelude.+)".

(* Constants specific to the ssreflect library. *)
Extract Inlined Constant addn => "(Prelude.+)".
Extract Inlined Constant cat  => "(Prelude.++)".
Extract Inlined Constant eqn  => "(Prelude.==)".
Extract Inlined Constant maxn => "(Prelude.max)".
Extract Inlined Constant minn => "(Prelude.min)".
Extract Inlined Constant subn => "(Prelude.-)".
Extract Inlined Constant leq  => "(Prelude.<=)".

(* Avoid extracting this function, which has no computational value, but Coq
   insists on ignoring its opacity. *)
(* Extract Inlined Constant boundedTransport *)
(*   => "LinearScan.Utils.boundedTransport'". *)

Extraction Blacklist String List Vector NonEmpty.

Separate Extraction LinearScan.allocateRegisters Interval.splitInterval Range.splitRange.

(* Show which axioms we depend on for this development. *)
Print Assumptions LinearScan.allocateRegisters.
