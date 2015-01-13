(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import LinearScan.Allocate.
Require Import LinearScan.Blocks.
Require Import LinearScan.Lib.
Require Import LinearScan.Machine.

Module MyMachine <: Machine.

Definition maxReg := 32.
Extract Constant maxReg => "32".

Lemma registers_exist : (maxReg > 0).
Proof. unfold maxReg. exact: ltn0Sn. Qed.

Definition PhysReg := 'I_maxReg.

End MyMachine.

Module Import Allocate := MAllocate MyMachine.

Section Main.

Definition mainAlgorithm :
  IState SSError BlockList BlockList unit :=
  (* order blocks and operations (including loop detection) *)
  computeBlockOrder ;;;
  numberOperations ;;;

  (* create intervals with live ranges *)
  computeLocalLiveSets ;;;
  computeGlobalLiveSets ;;;
  ssig <<- buildIntervals ;;

  (* allocate registers *)
  match walkIntervals ssig.2 with
  | inl err => error_ err
  | inr ssig' =>
      resolveDataFlow ;;;

      (* replace virtual registers with physical registers *)
      assignRegNum ssig'.2
  end.

Definition linearScan (blocks : BlockList) : SSError + BlockList :=
  match IState.runIState SSError mainAlgorithm blocks with
  | inl err      => inl err
  | inr (_, res) => inr res
  end.

End Main.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(** Danger!  Using Int is efficient, but requires we know we won't exceed its
    bounds. *)
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant apply   => "(Prelude.$)".
Extract Inlined Constant safe_hd => "Prelude.head".
Extract Inlined Constant sumlist => "Data.List.sum".
Extract Inlined Constant lebf    => "Data.Ord.comparing".
Extract Inlined Constant insert  => "Data.List.insertBy".

Extract Inlined Constant Arith.Plus.tail_plus => "(Prelude.+)".

Extraction Implicit widen_id [ n ].
Extraction Implicit widen_fst [ n ].

Extract Inlined Constant widen_id           => "".
Extract Inlined Constant widen_fst          => "Prelude.id".
Extract Inlined Constant List.destruct_list => "LinearScan.Utils.uncons".
Extract Inlined Constant list_membership    => "Prelude.const".

(* Avoid extracting this function, which has no computational value, but Coq
   insists on ignoring its opacity. *)
(* Extract Inlined Constant boundedTransport => *)
(*   "LinearScan.Utils.boundedTransport'". *)

Extraction Blacklist String List Vector NonEmpty.

Separate Extraction linearScan.

(* Show which axioms we depend on for this development. *)
Print Assumptions linearScan.

(* Print Libraries. *)