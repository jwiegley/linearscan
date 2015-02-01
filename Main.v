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

Definition regSize := 8.
Extract Constant regSize => "8".

Lemma registers_exist : (maxReg > 0).
Proof. unfold maxReg. exact: ltn0Sn. Qed.

Definition PhysReg := 'I_maxReg.

End MyMachine.

Module Import Allocate := MAllocate MyMachine.

Section Main.

Definition linearScan {accType : Set}
  {blockType1 blockType2 opType1 opType2 varType : Set}
  (binfo : BlockInfo blockType1 blockType2 opType1 opType2)
  (oinfo : OpInfo accType opType1 opType2 varType)
  (vinfo : VarInfo varType) (blocks : seq blockType1)
  (accum : accType) : SSError + (seq blockType2 * accType) :=

  (* order blocks and operations (including loop detection) *)
  let blocks' := computeBlockOrder blocks in
  (* numberOperations blocks' ;;; *)

  (* create intervals with live ranges *)
  let liveSets  := computeLocalLiveSets vinfo oinfo binfo blocks' in
  let liveSets' := computeGlobalLiveSets binfo blocks' liveSets in
  let ssig      := buildIntervals vinfo oinfo binfo blocks liveSets' in

  (* allocate registers *)
  match walkIntervals ssig.2 (countOps binfo blocks).+1
  return SSError + (seq blockType2 * accType) with
  | inl err => inl err
  | inr ssig' =>
      let mappings := resolveDataFlow binfo ssig'.2 blocks liveSets' in

      (* replace virtual registers with physical registers *)
      inr $ assignRegNum vinfo oinfo binfo ssig'.2 mappings blocks accum
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
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

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

Extract Inductive IntMap => "Data.IntMap.IntMap"
  ["Data.IntMap.empty" "Data.IntMap.fromList"] "(\fO fS _ -> fO ())".

Extract Inlined Constant IntMap_lookup => "Data.IntMap.lookup".
Extract Inlined Constant IntMap_insert => "Data.IntMap.insert".
Extract Inlined Constant IntMap_alter  => "Data.IntMap.alter".
Extract Inlined Constant IntMap_toList => "Data.IntMap.toList".

Extract Inductive IntSet => "Data.IntSet.IntSet"
  ["Data.IntSet.empty" "Data.IntSet.fromList"] "(\fO fS _ -> fO ())".

Extract Inlined Constant IntSet_member     => "Data.IntSet.member".
Extract Inlined Constant IntSet_insert     => "Data.IntSet.insert".
Extract Inlined Constant IntSet_union      => "Data.IntSet.union".
Extract Inlined Constant IntSet_difference => "Data.IntSet.difference".
Extract Inlined Constant IntSet_foldl      => "Data.IntSet.foldl'".

Extract Inductive NonEmpty => "[]" ["(:[])" "(:)"].

Extraction Blacklist String List Vector NonEmpty.

Separate Extraction linearScan.

(* Show which axioms we depend on for this development. *)
Print Assumptions linearScan.

(* Print Libraries. *)