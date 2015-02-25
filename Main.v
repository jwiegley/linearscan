(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import LinearScan.Allocate.
Require Import LinearScan.Assign.
Require Import LinearScan.Blocks.
Require Import LinearScan.Build.
Require Import LinearScan.Lib.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Order.
Require Import LinearScan.Resolve.
Require Import LinearScan.ScanState.
Require Import LinearScan.Trace.
Require Import LinearScan.Morph.
Require Import String.

Definition linearScan
  {blockType1 blockType2 opType1 opType2 accType : Set}
  (maxReg : nat) (registers_exist : maxReg > 0)
  (binfo : BlockInfo blockType1 blockType2 opType1 opType2)
  (oinfo : OpInfo maxReg accType opType1 opType2)
  (blocks : seq blockType1) (accum : accType) :
  SSError + (seq blockType2 * accType) :=
  (* order blocks and operations (including loop detection) *)
  let blocks1 := computeBlockOrder blocks in
  (* numberOperations blocks' ;;; *)

  (* create intervals with live ranges *)
  let liveSets  := computeLocalLiveSets binfo oinfo blocks1 in
  let liveSets' := computeGlobalLiveSetsRecursively binfo blocks1 liveSets in

  match buildIntervals binfo oinfo blocks1 liveSets'
  return SSError + (seq blockType2 * accType) with
  | inl err => inl err
  | inr ssig =>

    (* allocate registers *)
    let blocks2 := traceBlocksHere binfo oinfo ssig.1 liveSets' blocks1 in
    match walkIntervals registers_exist ssig.2 (countOps binfo blocks2).+1
    return SSError + (seq blockType2 * accType) with
    | inl err => inl err
    | inr ssig' =>
        let blocks3 := traceBlocksHere binfo oinfo ssig'.1 liveSets' blocks2 in
        let mappings := resolveDataFlow binfo ssig'.2 blocks3 liveSets' in

        (* replace virtual registers with physical registers *)
        inr $ assignRegNum binfo oinfo ssig'.2 liveSets' mappings blocks3 accum
    end
  end.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(** Danger!  Using Int is efficient, but requires we know we won't exceed its
    bounds. *)
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive String.string => "Prelude.String" ["[]" "(:)"].

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant safe_hd => "Prelude.head".
Extract Inlined Constant sumlist => "Data.List.sum".
(* Extract Inlined Constant lebf    => "Data.Ord.comparing". *)
(* Extract Inlined Constant insert  => "Data.List.insertBy". *)

Extract Inlined Constant Arith.Plus.tail_plus => "(Prelude.+)".

Extraction Implicit widen_id [ n ].
Extraction Implicit widen_fst [ n ].

Extract Inlined Constant widen_id           => "".
Extract Inlined Constant widen_fst          => "Prelude.id".
Extract Inlined Constant List.destruct_list => "LinearScan.Utils.uncons".
Extract Inlined Constant list_membership    => "Prelude.const".

Extract Inductive NonEmpty => "[]" ["(:[])" "(:)"].

Extraction Blacklist String List Vector NonEmpty.

Separate Extraction linearScan.

(* Show which axioms we depend on for this development. *)
Print Assumptions linearScan.

(* Print Libraries. *)