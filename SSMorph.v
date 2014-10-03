Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import Fin.
Require Import Interval.
Require Import Lib.
Require Import ScanState.
Require Import Hask.IEndo.
Require Import Hask.IApplicative.
Require Import Hask.IMonad.
Require Import Hask.IState.

Generalizable All Variables.

Open Scope nat_scope.
Open Scope program_scope.

(* Inductive tlist {a : Type} : list a -> Type := *)
(*   | tnil : tlist nil *)
(*   | tcons x xs : tlist xs -> tlist (x :: xs). *)

(* Definition Has {a} (x : a) {xs : list a} (T : tlist xs) := *)

(* Notation " '[ ] " := (tlist nil) (at level 100) : type_scope. *)
(* Notation "x ':: y" := (tlist (x :: y)) (at level 100) : type_scope. *)
(* Notation " '[ x ] " := (tlist (x :: nil)) : type_scope. *)
(* Notation " '[ x ; .. ; y ] " := (tlist (cons x .. (cons y nil) ..)) : type_scope. *)

(* Goal '[true ; false ; true]. *)

Module MSSMorph (M : Machine).
Include MScanState M.

(** ** SSMorph *)

(** A [SSMorph] is a relation describe a lawful transition between two
    states.  It is a [PreOrder] relation. *)

Record SSMorph (sd1 sd2 : ScanStateDesc) : Prop := {
    next_interval_increases : nextInterval sd1     <= nextInterval sd2;
    total_extent_decreases  : unhandledExtent sd2  <= unhandledExtent sd1;
    handled_count_increases : length (handled sd1) <= length (handled sd2)
}.

Arguments next_interval_increases [sd1 sd2] _.
Arguments total_extent_decreases  [sd1 sd2] _.
Arguments handled_count_increases [sd1 sd2] _.

Definition newSSMorph (s : ScanStateDesc) : SSMorph s s.
Proof. constructor; auto. Defined.

Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity (nextInterval y); auto.
  transitivity (unhandledExtent y); auto.
  transitivity (length (handled y)); auto.
Qed.

Record > SSMorphSt (sd1 sd2 : ScanStateDesc) : Prop := {
    st_is_SSMorph :> SSMorph sd1 sd2;

    total_extent_measurably_decreases :
      unhandledExtent sd2 < unhandledExtent sd1
}.

Record SSMorphLen (sd1 sd2 : ScanStateDesc) : Prop := {
    len_is_SSMorph :> SSMorph sd1 sd2;

    transportation (x : IntervalId sd1) : IntervalId sd2 :=
      transportId (next_interval_increases len_is_SSMorph) x;

    unhandled_nonempty :
      length (unhandled sd1) > 0 -> length (unhandled sd2) > 0
}.

Program Instance SSMorphLen_PO : PreOrder SSMorphLen.
Obligation 1.
  unfold Reflexive. intros.
  constructor; auto; constructor; auto.
Qed.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity y; assumption. auto.
Qed.

Definition newSSMorphLen (s : ScanStateDesc) : SSMorphLen s s.
Proof. intros. constructor; auto. constructor; auto. Defined.

Record > SSMorphStLen (sd1 sd2 : ScanStateDesc) : Prop := {
    stlen_is_SSMorph    :> SSMorph sd1 sd2;
    stlen_is_SSMorphLen :> SSMorphLen sd1 sd2;
    stlen_is_SSMorphSt  :> SSMorphSt sd1 sd2
}.

Record SSMorphHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    haslen_is_SSMorph    :> SSMorph sd1 sd2;
    haslen_is_SSMorphLen :> SSMorphLen sd1 sd2;

    first_nonempty : length (unhandled sd1) > 0
}.

Definition newSSMorphHasLen (sd : ScanStateDesc)
  (H : length (unhandled sd) > 0) : SSMorphHasLen sd sd.
Proof. repeat (constructor; auto). Defined.

Record SSMorphStHasLen (sd1 sd2 : ScanStateDesc) : Prop := {
    sthaslen_is_SSMorph       :> SSMorph sd1 sd2;
    sthaslen_is_SSMorphLen    :> SSMorphLen sd1 sd2;
    sthaslen_is_SSMorphSt     :> SSMorphSt sd1 sd2;
    sthaslen_is_SSMorphHasLen :> SSMorphHasLen sd1 sd2
}.

Inductive ScanStateRelation : Prop :=
  | SSR_Morph : forall sd1 sd2, SSMorph sd1 sd2 -> ScanStateRelation.

Record SSInfo (startDesc : ScanStateDesc) (P : relation ScanStateDesc) := {
    thisDesc  : ScanStateDesc;
    thisHolds : P startDesc thisDesc;
    thisState : ScanState thisDesc
}.

Arguments thisDesc  {_ P} _.
Arguments thisHolds {_ P} _.
Arguments thisState {_ P} _.

Definition SState (sd : ScanStateDesc) (P Q : relation ScanStateDesc) :=
  IState (SSInfo sd P) (SSInfo sd Q).

Definition withScanState {P Q : relation ScanStateDesc} {a pre}
  (f : forall sd : ScanStateDesc, ScanState sd -> SState pre P Q a)
  : SState pre P Q a :=
  iget >>>= fun i => f (thisDesc i) (thisState i).

Arguments withScanState {P Q a pre} f.

Definition withScanStatePO {P a pre} `{PO : PreOrder _ P}
  (f : forall sd : ScanStateDesc, ScanState sd
         -> SState sd P P a)
  : SState pre P P a.
Proof.
  exists. intros i.
  destruct i.
  specialize (f thisDesc0 thisState0).
  destruct f.
  assert (SSInfo thisDesc0 P).
    eapply {| thisDesc  := _
            ; thisHolds := _
            |}.
  apply p in H.
  destruct H.
  split. apply a0.
  destruct s.
  eexists.
  apply (transitivity thisHolds0 thisHolds1).
  assumption.
  Grab Existential Variables.
  apply thisState0.
  reflexivity.
Defined.

Arguments withScanStatePO {P a pre _} f.

Definition liftLen {pre a}
  : SState pre SSMorphLen SSMorphLen a
      -> SState pre SSMorphHasLen SSMorphHasLen a.
Proof.
  intros.
  destruct X.
  exists. intros.
  destruct H.
  destruct thisHolds0.
  specialize (p
    {| thisDesc  := thisDesc0
     ; thisHolds := haslen_is_SSMorphLen0
     ; thisState := thisState0
     |}).
  destruct p.
  split. apply a0.
  eexists.
  rapply Build_SSMorphHasLen.
  apply haslen_is_SSMorph0.
  apply haslen_is_SSMorphLen0.
  apply first_nonempty0.
  assumption.
Defined.

Definition stbind {P Q R a b}
  (f : (a -> IState Q R b)) (x : IState P Q a) : IState P R b :=
  @ijoin IState _ P Q R b (@imap _ _ P Q _ _ f x).

Notation "m >>>= f" := (stbind f m) (at level 25, left associativity).

Notation "X <<- A ; B" := (A >>>= (fun X => B))
  (right associativity, at level 84, A1 at next level).

Notation "A ;;; B" := (_ <<- A ; B)
  (right associativity, at level 84, A1 at next level).

Definition return_ {I X} := @ipure IState _ I X.

Definition weakenStHasLenToHasLen {pre}
  : SState pre SSMorphStHasLen SSMorphHasLen unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - apply thisHolds0.
  - assumption.
Defined.

Definition weakenStHasLenToSt {pre}
  : SState pre SSMorphStHasLen SSMorphSt unit.
Proof.
  constructor. intros HS.
  split. apply tt.
  destruct HS.
  rapply Build_SSInfo.
  - apply thisHolds0.
  - assumption.
Defined.

Definition withLenCursor {Q a pre}
  (f : forall sd : ScanStateDesc, ScanStateCursor sd
         -> SState pre SSMorphHasLen Q a)
  : SState pre SSMorphHasLen Q a.
Proof.
  constructor. intros i.
  destruct i.
  pose proof thisHolds0.
  destruct thisHolds0.
  destruct haslen_is_SSMorphLen0.
  pose proof first_nonempty0.
  apply unhandled_nonempty0 in H0.
  pose {| curState  := thisState0
        ; curExists := H0 |} as p.
  specialize (f thisDesc0 p).
  destruct f as [res].
  apply res.
  rapply Build_SSInfo.
  apply H.
  assumption.
Defined.

Definition moveUnhandledToActive {pre} (reg : PhysReg)
  : SState pre SSMorphHasLen SSMorphSt unit.
Proof.
  constructor. intros.
  split. apply tt.
  destruct H.
  destruct thisDesc0.
  destruct thisHolds0.
  destruct haslen_is_SSMorphLen0.
  destruct unhandled0; simpl in *. omega.
  pose (ScanState_moveUnhandledToActive nextInterval0 unhandled0
          (* unhsort *)
          active0 inactive0 handled0 intervals0 assignments0
          fixedIntervals0 i reg lists_are_unique0).
  specialize (s thisState0).
  eapply {| thisState := s
          |}.
  Grab Existential Variables.
  pose (NoDup_unhandledExtent_cons nextInterval0 i unhandled0 intervals0
         (V.replace assignments0 i (Some reg)) assignments0 fixedIntervals0
         (i :: active0) active0 inactive0 inactive0 handled0 handled0
         (move_unhandled_to_active _ i unhandled0 active0 inactive0 handled0
            lists_are_unique0) lists_are_unique0)
      as ue_cons.
  rapply Build_SSMorphSt; auto;
  unfold lt in *; intuition;
  [ apply le_Sn_le in ue_cons | ];
  apply le_trans with
    (m := unhandledExtent
            {| nextInterval     := nextInterval0
             ; unhandled        := i :: unhandled0
             ; active           := active0
             ; inactive         := inactive0
             ; handled          := handled0
             ; intervals        := intervals0
             ; assignments      := assignments0
             ; fixedIntervals   := fixedIntervals0
             ; lists_are_unique := lists_are_unique0
             |});
  assumption.
Defined.

Definition moveActiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (active sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveActiveToInactive `(st : ScanState sd) (x : IntervalId sd)
  (H: In x (active sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveInactiveToActive `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToActive sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveInactiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd))
  : { sd' : ScanStateDesc | ScanState sd' & SSMorphLen sd sd' }.
Proof.
  pose (ScanState_moveInactiveToHandled sd x st H).
  eexists. apply s.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
  apply Le.le_n_Sn.
Defined.

End MSSMorph.