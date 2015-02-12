Require Import LinearScan.Lib.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.
Require Import LinearScan.Morph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Cursor.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

(** ** ScanStateCursor *)

(** A [ScannStateCursor] gives us a view of the first unhandled element within
    a [ScanState].  The cursor is only valid if such an unhandled element
    exists, so it combines that assertion with a view onto that element. *)

Record ScanStateCursor (sd : ScanStateDesc maxReg) : Prop := {
    curState  : ScanState InUse sd;
    curExists : size (unhandled sd) > 0;

    curId := safe_hd _ curExists;
    curIntDetails := vnth (intervals sd) (fst curId)
}.

Arguments curState {sd} _.
Arguments curExists {sd} _.
Arguments curId {sd} _.
Arguments curIntDetails {sd} _.

Definition curInterval `(cur : ScanStateCursor sd) := (curIntDetails cur).2.
Arguments curInterval [sd] cur /.

Definition curPosition `(cur : ScanStateCursor sd) : nat :=
  intervalStart (curInterval cur).
Arguments curPosition [sd] cur /.

Lemma curPosition_odd `(cur : ScanStateCursor sd) :
  odd (curPosition cur).
Proof.
  rewrite /curPosition.
  case: (curInterval cur) => [? ? ? r|? ? ? ? [? r] ?] /=;
  exact: (Range_beg_odd r).
Qed.

Definition withCursor {Q a pre}
  (f : forall sd : ScanStateDesc maxReg, ScanStateCursor sd
         -> SState pre (@SSMorphHasLen maxReg) Q a) :
  SState pre (@SSMorphHasLen maxReg) Q a.
Proof.
  destruct 1.
  destruct thisHolds.
  destruct haslen_is_SSMorphLen.
  pose {| curState  := thisState
        ; curExists := first_nonempty |} as p.
  specialize (f thisDesc p).
  apply f.
  exact: Build_SSInfo.
Defined.

End Cursor.