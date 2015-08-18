Require Import LinearScan.Lib.
Require Import LinearScan.Context.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Trace.

(* These T-suffixed types and constructors are for data that is meant to be
   exported from Coq, and so must dwell in [Set]. *)

Definition IntervalIdT : Set := nat.
Definition PhysRegT : Set := nat.

Inductive SpillConditionT : Set :=
  | NewToHandledT       of IntervalIdT
  | UnhandledToHandledT of IntervalIdT
  | ActiveToHandledT    of IntervalIdT & PhysRegT
  | InactiveToHandledT  of IntervalIdT & PhysRegT.

Inductive SplitPositionT : Set :=
  | BeforePosT of nat
  | EndOfLifetimeHoleT of nat.

Definition TrueIfActiveT : Set := bool.

Inductive SSTrace : Set :=
  | EOverlapsWithFixedInterval of nat & PhysRegT
  | ESplitAssignedIntervalForReg of PhysRegT
  | ESplitActiveOrInactiveInterval of TrueIfActiveT
  | EIntervalHasUsePosReqReg of IntervalIdT
  | EIntervalBeginsAtSplitPosition
  | EMoveUnhandledToActive of PhysRegT
  | ESplitActiveIntervalForReg of PhysRegT
  | ESplitAnyInactiveIntervalForReg of PhysRegT
  | ESpillInterval of SpillConditionT
  | ESpillCurrentInterval
  | ESplitUnhandledInterval
  | ESplitCurrentInterval of SplitPositionT
  | ETryAllocateFreeReg of PhysRegT & option nat & IntervalIdT
  | EAllocateBlockedReg of PhysRegT & option nat & IntervalIdT
  | ERemoveUnhandledInterval of IntervalIdT
  | ECannotInsertUnhandled
  | EIntervalBeginsBeforeUnhandled of IntervalIdT
  | ENoValidSplitPosition of IntervalIdT
  | ECannotSplitSingleton of IntervalIdT
  | ERegisterAlreadyAssigned of PhysRegT
  | ERegisterAssignmentsOverlap of PhysRegT & IntervalIdT & nat
  | ECannotModifyHandledInterval of IntervalIdT
  | EUnexpectedNoMoreUnhandled
  | ECannotSpillIfRegisterRequired of PhysRegT
  | EFuelExhausted
  | EUnhandledIntervalsRemain
  | EActiveIntervalsRemain
  | EInactiveIntervalsRemain
  | ENotYetImplemented of nat.

End Trace.
