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
Include MScanState Mach.

Section Blocks.

Open Scope program_scope.

Variable opType : Set.
Variable opInfo : OpInfo opType.
Variable blockType : Set -> Set.

Record BlockInfo (A : Set) (P : A -> opType) := {
  blockElems : blockType A -> seq A;
  blockToOpList : blockType A -> seq opType
}.

Definition BlockList := seq (blockType opType).
Definition BlockState := IState SSError BlockList BlockList.

Definition computeBlockOrder : BlockState unit :=
  (* jww (2014-11-19): Implementing this function provides an opportunity to
     optimize for better allocation. *)
  return_ tt.

Definition numberOperations : BlockState unit := return_ tt.
Definition computeLocalLiveSets : BlockState unit := return_ tt.
Definition computeGlobalLiveSets : BlockState unit := return_ tt.
Definition buildIntervals : BlockState unit := return_ tt.
Definition walkIntervals : BlockState unit := return_ tt.
Definition resolveDataFlow : BlockState unit := return_ tt.
Definition assignRegNum : BlockState unit := return_ tt.

Definition determineIntervals (ops : seq opType) :
  OpList opType * ScanStateSig :=
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

  let: (ops', varRanges, regRanges) :=
       processOperations opInfo ops in
  let regs := vmap (fun mr =>
                      if mr is Some r
                      then Some (packInterval (I_Sing r.2))
                      else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  (ops', foldl handleVar s2 varRanges).

End Blocks.

Arguments computeBlockOrder {opType blockType}.
Arguments numberOperations {opType blockType}.
Arguments computeLocalLiveSets {opType blockType}.
Arguments computeGlobalLiveSets {opType blockType}.
Arguments buildIntervals {opType blockType}.
Arguments walkIntervals {opType blockType}.
Arguments resolveDataFlow {opType blockType}.
Arguments assignRegNum {opType blockType}.

End MBlocks.