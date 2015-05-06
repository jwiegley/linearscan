(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.Allocate.
Require Import LinearScan.Assign.
Require Import LinearScan.Blocks.
Require Import LinearScan.Build.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Loops.
Require Import LinearScan.Resolve.
Require Import LinearScan.ScanState.
Require Import LinearScan.Morph.
Require Import String.

Generalizable All Variables.

Inductive FinalStage :=
  | BuildingIntervalsFailed
  | AllocatingRegistersFailed.

Record Details `{dict : Monad} {blockType1 blockType2 opType1 opType2 : Set}
  (maxReg : nat) := {
  reason          : option (SSError * FinalStage);
  liveSets        : IntMap BlockLiveSets;
  inputBlocks     : seq blockType1;
  allocatedBlocks : seq blockType2;
  scanStatePre    : option (ScanStateDesc maxReg);
  scanStatePost   : option (ScanStateDesc maxReg);
  blockInfo       : BlockInfo blockType1 blockType2 opType1 opType2;
  opInfo          : @OpInfo maxReg m dict opType1 opType2;
  loopState       : LoopState
}.

Definition linearScan
  `{dict : Monad m} {blockType1 blockType2 opType1 opType2 : Set}
  (maxReg : nat) (registers_exist : maxReg > 0)
  (binfo : BlockInfo blockType1 blockType2 opType1 opType2)
  (oinfo : @OpInfo maxReg m dict opType1 opType2)
  (blocks : seq blockType1) : m (Details maxReg) :=
  (* order blocks and operations (including loop detection) *)
  z <-- computeBlockOrder binfo blocks ;;
  let: (loops, blocks1) := z in

  (* create intervals with live ranges *)
  let liveSets  := computeLocalLiveSets binfo oinfo blocks1 in
  let liveSets' := computeGlobalLiveSetsRecursively binfo blocks1 liveSets in

  match buildIntervals binfo oinfo blocks1 loops liveSets'
  return m (@Details m dict blockType1 blockType2
                         opType1 opType2 maxReg) with
  | inl err =>
    pure $ Build_Details _ _ _ _ _ _ maxReg
      (Some (err, BuildingIntervalsFailed)) liveSets' blocks1 [::]
      None None binfo oinfo loops
  | inr ssig =>
    (* allocate registers *)
    let opCount := (countOps binfo blocks1).+1 in
    match walkIntervals registers_exist ssig.2 opCount
    return m (Details maxReg) with
    | inl (err, ssig') =>
      pure $ Build_Details _ _ _ _ _ _ maxReg
        (Some (err, AllocatingRegistersFailed)) liveSets' blocks1 [::]
        (Some ssig.1) (Some ssig'.1) binfo oinfo loops
    | inr ssig' =>
        let sd       := finalizeScanState ssig'.2 opCount.*2 in
        let allocs   := determineAllocations sd in
        let mappings := resolveDataFlow binfo allocs blocks1 liveSets' in

        (* replace virtual registers with physical registers *)
        blocks2 <-- assignRegNum binfo oinfo allocs liveSets' mappings blocks1 ;;
        pure $ Build_Details _ _ _ _ _ _ maxReg None liveSets' blocks1 blocks2
          (Some ssig.1) (Some sd) binfo oinfo loops
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