Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.Ops.
Require Import LinearScan.Range.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MBlocks (Mach : Machine).

Include MOps Mach.
Module Import M := MScanState Mach.

Section Blocks.

Open Scope program_scope.

Variable opType : Set.
Variable blockType : Set.

Record BlockInfo := {
  blockToOpList : blockType -> seq opType
}.

Record BlockData := {
  baseBlock : blockType;
  blockInfo : BlockInfo;
  blockOps  : OpList opType
}.

(* jww (2014-11-19): Note that we are currently not computing the block order
   in any intelligent way. This is covered in quite some depth in Christian
   Wimmer's thesis.  At the moment we're simply accepting whatever block order
   is passed to us by the caller.  However, implementing this function
   properly is a strong means of improving the accuracy and efficiency of this
   algorithm. *)
Definition computeBlockOrder :
  IState SSError (seq blockType) (seq blockType) unit := return_ tt.

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations (blockInfo : BlockInfo) (opInfo : OpInfo opType) :
  IState SSError (seq blockType) (seq BlockData) unit :=
  let f block x :=
      let: (i, blocks') := x in
      let k op := {| baseOp  := op
                   ; opInfo  := opInfo
                   ; opId    := i
                   ; opAlloc := fun _ => Unallocated |} in
      let blk  := {| baseBlock := block
                   ; blockInfo := blockInfo
                   ; blockOps  := map k (blockToOpList blockInfo block) |} in
      (i.+2, blk :: blocks') in
  imodify SSError $ @snd _ _ \o foldr f (1, nil).

Definition BlockState := IState SSError (seq BlockData) (seq BlockData).

(* jww (2014-12-01): The following two functions are used for computing
   accurate live ranges. they constitute a dataflow analysis which determines
   the true live range for variables referenced from loops.  At the moment
   these are being left unimplemented, but this is very likely something that
   will need to be done for the sake of the correctness of the algorithm. *)
Definition computeLocalLiveSets : BlockState unit := return_ tt.
Definition computeGlobalLiveSets : BlockState unit := return_ tt.

Definition buildIntervals : BlockState ScanStateSig :=
  let mkint (ss : ScanStateSig)
            (mx : option RangeSig)
            (f : forall sd, ScanState sd -> forall d, Interval d
                   -> ScanStateSig) :=
      let: (exist sd st) := ss in match mx with
           | Some (exist _ r) => f _ st _ (I_Sing r)
           | None => ss
           end in

  let handleVar ss mx := mkint ss mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i) in

  bxs <<- iget SSError ;;
  let: (blocks, blockInfo) := bxs in
  let ops := flatten (map blockOps blocks) in
  let: (ops', varRanges, regRanges) := processOperations ops in
  let regs := vmap (fun mr =>
                      if mr is Some r
                      then Some (packInterval (I_Sing r.2))
                      else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  return_ $ foldl handleVar s2 varRanges.

Definition resolveDataFlow : BlockState unit := return_ tt.

Definition assignRegNum : BlockState unit := return_ tt.

End Blocks.

Arguments computeBlockOrder {opType blockType}.
Arguments numberOperations {opType blockType}.
Arguments computeLocalLiveSets {opType blockType}.
Arguments computeGlobalLiveSets {opType blockType}.
Arguments buildIntervals {opType _ blockType}.
Arguments resolveDataFlow {opType blockType}.
Arguments assignRegNum {opType blockType}.

End MBlocks.