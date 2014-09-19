(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf *)

(* Require Import Coq.Arith.Compare_dec. *)
Require Import Coq.Arith.EqNat.
(* Require Import Coq.Init.Datatypes. *)
Require Import Coq.Lists.List.
(* Require Import Coq.Logic.ProofIrrelevance. *)
Require Import Coq.Numbers.Natural.Peano.NPeano.
(* Require Import Coq.omega.Omega. *)
Require Import Coq.Program.Basics.
(* Require Import Coq.Program.Equality. *)
Require Import Coq.Program.Tactics.
(* Require Import Coq.Sorting.Permutation. *)
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
(* Require Import Coq.Vectors.Fin. *)
(* Require Import Recdef. *)
Require Import Recdef.
Require Import Lib.
Require Import RState.

Module Import LN := ListNotations.

Open Scope nat_scope.
Open Scope program_scope.

Generalizable All Variables.

(****************************************************************************)

(** * Core data types *)

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
  uloc   : nat;
  regReq : bool
}.

(** ** Range *)

(** The extent of a [Range] is the set of locations it ranges over.  By
    summing the extent of a list of ranges, we have an idea of how much ground
    is left to cover, and this gives us a notion of well-founded recursion for
    iterating over intervals that may split as we examine them -- i.e., whose
    total extent must decrease after each pass.

    A Range is built up from a set of use positions, and defines the inclusive
    range of those positions.  It can be extended, or split, but never shrunk.
    Also, the non-empty list of use positions is not guaranteed to be in any
    order, and overlapping use positions are accepted but only the most recent
    one "wins". *)

Record RangeDesc := {
    rbeg : nat;
    rend : nat;
    ups  : NonEmpty UsePos;

    range_nonempty : rbeg < rend         (* this comes in handy *)
}.

Inductive Range : RangeDesc -> Set :=
  | R_Sing u :
      Range {| rbeg := uloc u
             ; rend := S (uloc u)
             ; ups  := NE_Sing u
             ; range_nonempty := le_n (S (uloc u))
             |}
  | R_Cons u x : Range x -> forall (H : uloc u < rbeg x),
      Range {| rbeg := uloc u
             ; rend := rend x
             ; ups  := NE_Cons u (ups x)
             ; range_nonempty := Lt.lt_trans _ _ _ H (range_nonempty x)
             |}
  | R_Extend x b' e' : Range x ->
      Range {| rbeg := min b' (rbeg x)
             ; rend := Peano.max e' (rend x)
             ; ups  := ups x
             ; range_nonempty := min_lt_max _ _ _ _ (range_nonempty x)
             |}.

Definition rangeExtent (x : RangeDesc) := rend x - rbeg x.

Definition rangesIntersect `(x : RangeDesc) `(y : RangeDesc) : bool :=
  if rbeg x <? rbeg y
  then rbeg y <? rend x
  else rbeg x <? rend y.

Definition anyRangeIntersects (is js : NonEmpty RangeDesc) : bool :=
  fold_right
    (fun r b => orb b (existsb (rangesIntersect r) (NE_to_list js)))
    false (NE_to_list is).

(** ** Interval *)

(** A lifetime interval defines the lifetime of a variable.  It is defined as
    a list of ranges "covered" by that variable in the low-level intermediate
    representation (LIR).  Gaps in the list of ranges are called "lifetime
    holes".

    A lifetime is not necessarily only the distance that a variable is first
    and last used.  The lifetime of a variable used in a loop extends to the
    whole loop, for example, even if it is only used at the very end.  In this
    sense, coverage takes into account code flow, or what ranges would map to
    if all loops were unrolled, and then rolled back keeping track of
    coverage.

    Use positions are actual instructions where a variable is read from or
    written to, and whether it is required to be in a register at that
    point. *)

(** If for some reason we cannot assign a single register for all ranges, then
    the interval is split into two or more intervals, so each interval can be
    assigned its own register. *)

Record IntervalDesc := {
    ibeg : nat;
    iend : nat;
    rds  : NonEmpty RangeDesc;

    interval_nonempty : ibeg < iend         (* comes in handy *)
}.

Lemma lt_le_shuffle : forall {x y z w}, x < y -> y <= z -> z < w -> x < w.
Proof. intros. omega. Qed.

Inductive Interval : IntervalDesc -> Set :=
  | I_Sing : forall x, Range x ->
      Interval {| ibeg := rbeg x
                ; iend := rend x
                ; rds  := NE_Sing x
                ; interval_nonempty := range_nonempty x
                |}
  | I_Cons1 : forall x y ib ie ne,
      Interval {| ibeg := ib; iend := ie; rds := NE_Sing y;
                  interval_nonempty := ne |}
        -> Range x -> forall (H : rend x <= ib),
      Interval {| ibeg := rbeg x
                ; iend := ie
                ; rds  := NE_Cons x (NE_Sing y)
                ; interval_nonempty := lt_le_shuffle (range_nonempty x) H ne
                |}
  | I_Consn : forall x y xs ib ie ne,
      Interval {| ibeg := ib; iend := ie; rds := NE_Cons y xs;
                  interval_nonempty := ne |}
        -> Range x -> forall (H : rend x <= ib),
      Interval {| ibeg := rbeg x
                ; iend := ie
                ; rds  := NE_Cons x (NE_Cons y xs)
                ; interval_nonempty := lt_le_shuffle (range_nonempty x) H ne
                |}.

Definition intervalStart `(i : Interval d) : nat := ibeg d.
Definition intervalEnd   `(i : Interval d) : nat := iend d.

Lemma Interval_nonempty : forall `(i : Interval rs),
  intervalStart i < intervalEnd i.
Proof.
  intros. unfold intervalStart, intervalEnd.
  induction i; simpl in *;
  induction r; simpl in *; min_max.
Qed.

Definition intervalCoversPos `(i : Interval rs) (pos : nat) : bool :=
  andb (intervalStart i <=? pos) (pos <? intervalEnd i).

Definition intervalExtent `(i : Interval rs) :=
  intervalEnd i - intervalStart i.

Lemma Interval_extent_nonempty : forall `(i : Interval rs),
  intervalExtent i > 0.
Proof.
  intros.
  unfold intervalExtent.
  pose (Interval_nonempty i).
  apply lt_minus in l.
  assumption.
Qed.

(****************************************************************************)

(** * Main algorithm *)

Section Allocator.

Variable maxReg : nat.          (* max number of registers *)

Hypothesis registers_exist : maxReg > 0.

Definition VirtReg := nat.
Definition PhysReg := fin maxReg.

(** ** ScanState *)

(** A [ScanState] is always relative to a current position (pos) as we move
    through the sequentialized instruction stream over which registers are
    allocated.. *)

Record ScanStateDesc := {
    nextInterval : nat;
    IntervalId   := fin nextInterval;

    unhandledExtent : nat;

    unhandled : list IntervalId;   (* starts after pos *)
    active    : list IntervalId;   (* ranges over pos *)
    inactive  : list IntervalId;   (* falls in lifetime hole *)
    handled   : list IntervalId;   (* ends before pos *)

    getInterval  : IntervalId -> { d : IntervalDesc & Interval d };
    assignments  : IntervalId -> option PhysReg;

    unhandled_sorted : LocallySorted cmp_le unhandled;

    all_state_lists  := unhandled ++ active ++ inactive ++ handled;
    lists_are_unique : NoDup all_state_lists
}.

Definition transportId `(H : nextInterval st <= nextInterval st')
  (x : IntervalId st) : IntervalId st'.
Proof.
  destruct st. destruct st'.
  unfold IntervalId0, IntervalId1 in *.
  unfold IntervalId in *. simpl in *.
  apply (fin_transport nextInterval0 nextInterval1 H).
  assumption.
Defined.

Lemma NoDup_wip : forall n x unh act inact hnd,
  NoDup (unh ++ act ++ inact ++ hnd) ->
  NoDup ((x :: map (fin_bump n) unh) ++
         map (fin_bump n) act ++ map (fin_bump n) inact ++ map (fin_bump n) hnd).
Proof.
Admitted.

Lemma LocallySorted_uncons : forall a (f : relation a) (x : a) (xs : list a),
  LocallySorted f (x :: xs) -> LocallySorted f xs.
Proof.
Admitted.

Lemma LocallySorted_fin_bump : forall n (x : fin (S n)) (xs : list (fin n)),
  LocallySorted cmp_le xs ->
    x = ultimate_Sn n ->
    LocallySorted cmp_le (x :: map (fin_bump n) xs).
Proof.
Admitted.

Lemma move_active_to_inactive : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (active sd)
    -> NoDup (unhandled sd ++ remove cmp_eq_dec x (active sd) ++
              (x :: inactive sd) ++ handled sd).
Proof.
  intros.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply NoDup_juggle.
  rewrite app_assoc.
  rewrite app_assoc.
  apply NoDup_swap.
  rewrite <- app_assoc.
  assumption.
  apply H0.
Defined.

Lemma move_active_to_handled : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (active sd)
    -> NoDup (unhandled sd ++ remove cmp_eq_dec x (active sd) ++
              inactive sd ++ x :: handled sd).
Proof.
  intros.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply NoDup_swap2.
  rewrite <- app_assoc.
  apply NoDup_juggle.
  rewrite app_assoc.
  apply NoDup_swap2.
  rewrite app_assoc.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite app_assoc.
  apply NoDup_swap2.
  rewrite <- app_assoc.
  assumption.
  apply H0.
Defined.

Definition move_inactive_to_active : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (inactive sd)
    -> NoDup (unhandled sd ++ x :: active sd ++
              remove cmp_eq_dec x (inactive sd) ++ handled sd).
Proof.
Admitted.

Definition move_inactive_to_handled : forall sd x,
  NoDup (unhandled sd ++ active sd ++ inactive sd ++ handled sd)
    -> In x (inactive sd)
    -> NoDup (unhandled sd ++ active sd ++
              remove cmp_eq_dec x (inactive sd) ++ x :: handled sd).
Proof.
Admitted.

(** The [ScanState] inductive data type describes the allowable state
    transitions that can be applied to a [ScanStateDesc] value.

    In essence there are five mutating operations:

    1. Create a new unhandled interval.  This can occur for two reasons:

       a. Adding a new interval to be considered before the linear scan
          algorithm has started.
       b. Splitting the current interval, which pushes back its "pieces" as
          new unhandled intervals.

    2. Remove the first unhandled interval.  This happens when we remove it in
       order to make it the new current interval.

    3. Add the current interval to the active list.

    4. Move an item from the active list to the inactive or handled lists.

    5. Move an item from the inactive list to the active or handled lists. *)

Inductive ScanState : ScanStateDesc -> Set :=
  | ScanState_nil :
    ScanState
      {| nextInterval     := 0
       ; unhandledExtent  := 0
       ; unhandled        := nil
       ; active           := nil
       ; inactive         := nil
       ; handled          := nil
       ; getInterval      := fin_contra
       ; assignments      := fin_contra
       ; unhandled_sorted := LSorted_nil _
       ; lists_are_unique := NoDup_nil _
       |}

  | ScanState_newUnhandled
      ni ue unh unhsort act inact hnd geti assgn lau :
    forall `(i : Interval d),
    ScanState
      {| nextInterval     := ni
       ; unhandledExtent  := ue
       ; unhandled        := unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; getInterval      := geti
       ; assignments      := assgn
       ; unhandled_sorted := unhsort
       ; lists_are_unique := lau
       |} ->
    forall newi (H : newi = ultimate_Sn ni),
    ScanState
      {| nextInterval     := S ni
       ; unhandledExtent  := ue + intervalExtent i
       ; unhandled        := newi :: map (fin_bump ni) unh
       ; active           := map (fin_bump ni) act
       ; inactive         := map (fin_bump ni) inact
       ; handled          := map (fin_bump ni) hnd
       ; getInterval      :=
         fun n => match cmp_eq_dec n newi with
                  | left _ => existT _ d i
                  | right Hn => geti (fin_safe_reduce n (rew_in_not_eq H Hn))
                  end
       ; assignments      :=
         fun n => match cmp_eq_dec n newi with
                  | left _ => None
                  | right Hn => assgn (fin_safe_reduce n (rew_in_not_eq H Hn))
                  end
       ; unhandled_sorted := LocallySorted_fin_bump _ _ _ unhsort H
       ; lists_are_unique := NoDup_wip ni newi unh _ _ _ lau
       |}

  | ScanState_dropUnhandled
      ni ue x unh unhsort act inact hnd geti assgn lau :
    ScanState
      {| nextInterval     := ni
       ; unhandledExtent  := ue
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; getInterval      := geti
       ; assignments      := assgn
       ; unhandled_sorted := unhsort
       ; lists_are_unique := lau
       |} ->
    forall newe,
    newe = intervalExtent (projT2 (geti x)) ->
    (IF unh = [] then newe = ue else newe < ue) ->
    ScanState
      {| nextInterval     := ni
       ; unhandledExtent  := ue - newe
       ; unhandled        := unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; getInterval      := geti
       ; assignments      := assgn
       ; unhandled_sorted := LocallySorted_uncons _ _ _ _ unhsort
       ; lists_are_unique := NoDup_uncons _ _ _ _ lau
       |}

  | ScanState_moveActiveToInactive sd x :
    ScanState sd -> forall (H : In x (active sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandledExtent  := unhandledExtent sd
       ; unhandled        := unhandled sd
       ; active           := remove cmp_eq_dec x (active sd)
       ; inactive         := x :: inactive sd
       ; handled          := handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique := move_active_to_inactive sd x (lists_are_unique sd) H
       |}

  | ScanState_moveActiveToHandled sd x :
    ScanState sd -> forall (H : In x (active sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandledExtent  := unhandledExtent sd
       ; unhandled        := unhandled sd
       ; active           := remove cmp_eq_dec x (active sd)
       ; inactive         := inactive sd
       ; handled          := x :: handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique := move_active_to_handled sd x (lists_are_unique sd) H
       |}

  | ScanState_moveInactiveToActive sd x :
    ScanState sd -> forall (H : In x (inactive sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandledExtent  := unhandledExtent sd
       ; unhandled        := unhandled sd
       ; active           := x :: active sd
       ; inactive         := remove cmp_eq_dec x (inactive sd)
       ; handled          := handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique := move_inactive_to_active sd x (lists_are_unique sd) H
       |}

  | ScanState_moveInactiveToHandled sd x :
    ScanState sd -> forall (H : In x (inactive sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandledExtent  := unhandledExtent sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := remove cmp_eq_dec x (inactive sd)
       ; handled          := x :: handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique := move_inactive_to_handled sd x (lists_are_unique sd) H
       |}.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require String.
Open Scope string_scope.

Tactic Notation "ScanState_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ScanState_nil"
  | Case_aux c "ScanState_newUnhandled"
  | Case_aux c "ScanState_dropUnhandled"
  | Case_aux c "ScanState_moveActiveToInactive"
  | Case_aux c "ScanState_moveActiveToHandled"
  | Case_aux c "ScanState_moveInactiveToActive"
  | Case_aux c "ScanState_moveInactiveToHandled"
  ].

Theorem ScanState_only_grows `(st : ScanState sd)
  : { sd' : ScanStateDesc & nextInterval sd <= nextInterval sd' }.
Proof.
  inversion st; simpl in *.
  - eexists. apply Le.le_0_n.
  - exists sd.
    rewrite <- H1. simpl.
    reflexivity.
Admitted.

Definition transportIntervalId `(st : ScanState sd) (i : IntervalId sd)
  : { sd' : ScanStateDesc & IntervalId sd' }.
Proof.
  pose (ScanState_only_grows st).
  destruct s.
  exists x.
  apply (transportId l).
  assumption.
Defined.

Lemma ScanState_active_bounded : forall st,
  length (active st) <= nextInterval st.
Proof.
  destruct st. simpl.
  unfold all_state_lists0 in lists_are_unique0.
  compute.
  apply NoDup_unapp in lists_are_unique0.
  inversion lists_are_unique0.
  apply NoDup_swap in H0.
  apply NoDup_unapp in H0.
  inversion H0.
  apply fin_list in H2.
  auto.
Qed.

(** ** SSMorph *)

(** A [SSMorph] is a relation describe a lawful transition between two
    states.  It is a [PreOrder] relation. *)

Record SSMorph (sd1 : ScanStateDesc) (sd2 : ScanStateDesc) := {
    next_interval_increases : nextInterval sd1 <= nextInterval sd2;
    total_extent_decreases :
      unhandledExtent sd2 <= unhandledExtent sd1;
    handled_count_increases : length (handled sd1) <= length (handled sd2)
}.

Arguments next_interval_increases [sd1 sd2] _.
Arguments total_extent_decreases  [sd1 sd2] _.
Arguments handled_count_increases [sd1 sd2] _.

Definition newSSMorph (s : ScanStateDesc) : SSMorph s s.
Proof. constructor; auto. Defined.

Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Defined.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity (nextInterval y); auto.
  transitivity (unhandledExtent y); auto.
  transitivity (length (handled y)); auto.
Defined.

(** ** CurrentInterval *)

Record CurrentInterval `(st : ScanState sd) := {
    currentIntervalId : IntervalId sd;
    currentDesc       : IntervalDesc;
    currentInterval   : Interval currentDesc

    (* not_present : ~ In currentIntervalId (all_state_lists sd) *)
}.

Arguments currentIntervalId [sd st] _.
Arguments currentDesc       [sd st] _.
Arguments currentInterval   [sd st] _.
(* Arguments not_present       [sd st] _ _. *)

(*
Lemma totalExtent_cons : forall st x (xs : list (IntervalId st)),
  totalExtent (x :: xs) = totalExtent [x] + totalExtent xs.
Proof.
  intros.
  assert (x :: xs = [x] ++ xs) by auto.
  rewrite H. clear H.
  unfold totalExtent.
  rewrite fold_left_app.
  rewrite Plus.plus_comm. simpl.
  induction xs. reflexivity.
  apply (fold_left_plus (IntervalId st)
           (fun (x : IntervalId st) =>
              intervalExtent (projT2 (getInterval st x)))).
Qed.

Lemma unhandled_extent_cons : forall (st : ScanState) x xs,
  x :: xs = unhandled st -> totalExtent xs < totalExtent (x :: xs).
Proof.
  intros.
  rewrite totalExtent_cons.
  unfold totalExtent at 2. simpl.
  remember (projT2 (getInterval st x)) as i.
  assert (intervalExtent i > 0).
    unfold intervalExtent.
    apply lt_minus.
    apply Interval_nonempty.
  omega.
Qed.

Definition unhandledExtent st := totalExtent (unhandled st).
*)

Record SSMorphSt (sd1 : ScanStateDesc) (sd2 : ScanStateDesc) : Prop := {
    is_SSMorph :> SSMorph sd1 sd2;

    total_extent_measurably_decreases :
      unhandledExtent sd2 < unhandledExtent sd1
}.

Program Instance SSMorphSt_Trans : Transitive SSMorphSt.
Obligation 1.
  constructor.
    destruct H. destruct H0.
    transitivity y; assumption.
  inversion H. inversion H0.
  destruct total_extent_measurably_decreases1. omega.
  destruct total_extent_measurably_decreases0. omega.
  right. omega.
Qed.

Theorem compose_ssmorph_with_ssmorphst : forall (sd1 sd2 sd3 : ScanStateDesc),
  SSMorphSt sd1 sd2 -> SSMorph sd2 sd3 -> SSMorphSt sd1 sd3.
Proof.
  intros.
  constructor.
  inversion H.
  transitivity sd2; assumption.
  inversion H. inversion H0. omega.
Qed.

Theorem ssmorphst_proj_unhandledExtent : forall (sd1 sd3 : ScanStateDesc),
  SSMorphSt sd1 sd3 -> unhandledExtent sd3 < unhandledExtent sd1.
Proof.
  intros. inversion H. assumption.
Qed.

Lemma ScanState_unhandledExtent_nonzero `(st : ScanState sd) :
  length (unhandled sd) > 0 <-> unhandledExtent sd > 0.
Proof.
  intros.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil".
    split; intros; inversion H.
  - Case "ScanState_newUnhandled".
    pose (Interval_extent_nonempty i); omega.
  - Case "ScanState_dropUnhandled".
    destruct (geti x). simpl.
    pose (Interval_extent_nonempty i0).
    split; intros.
      destruct unh. inversion H.
      inversion i.
        inversion H0. inversion H1.
      omega.
    destruct unh.
      inversion i. inversion H0.
        subst. simpl in *.
        rewrite H2 in H.
        rewrite Minus.minus_diag in H.
        inversion H.
      inversion H0.
      contradiction H1. reflexivity.
    simpl. apply Gt.gt_Sn_O.
  - Case "ScanState_moveActiveToInactive".
    apply IHst.
  - Case "ScanState_moveActiveToHandled".
    apply IHst.
  - Case "ScanState_moveInactiveToActive".
    apply IHst.
  - Case "ScanState_moveInactiveToHandled".
    apply IHst.
Qed.

Definition nextUnhandled `(st : ScanState sd)
  : option { sd' : ScanStateDesc &
             { st' : ScanState sd' &
               CurrentInterval st' & SSMorphSt sd sd' } }.
Proof.
  destruct sd.
  destruct unhandled0.
    apply None.
  apply Some.

  assert (unhandledExtent0 > 0) as Hu.
    apply (@ScanState_unhandledExtent_nonzero
           {| nextInterval := nextInterval0
            ; unhandledExtent := unhandledExtent0
            ; unhandled := i :: unhandled0
            ; active := active0
            ; inactive := inactive0
            ; handled := handled0
            ; getInterval := getInterval0
            ; assignments := assignments0
            ; unhandled_sorted := unhandled_sorted0
            ; lists_are_unique := lists_are_unique0 |}); simpl.
      apply st.
    omega.

  destruct (getInterval0 i) as [? int].

  pose (ScanState_dropUnhandled
        nextInterval0
        unhandledExtent0
        i unhandled0
        unhandled_sorted0
        active0
        inactive0
        handled0
        getInterval0
        assignments0
        lists_are_unique0 st).

  eexists.
  pose (intervalExtent (projT2 (getInterval0 i))).
  eexists (s n eq_refl _).

  rapply Build_CurrentInterval.
    apply i.
    apply int.

  (* Prove that a call to [nextUnhandled] must always reduce the unhandled
     extent. *)
  clear s.
  constructor.
    constructor; auto.
    simpl. unfold intervalExtent.
    unfold intervalStart, intervalEnd.
    remember (getInterval0 i) as v.
    destruct v. simpl.
    destruct unhandledExtent0; simpl. auto.
    right.
    assert (ibeg x0 < iend x0)
      by (apply (interval_nonempty x0)).
    apply lt_minus in H.
    destruct (iend x0 - ibeg x0);
      inversion H; omega.

  (* jww (2014-09-19): How can I remove this duplication? *)
  simpl. unfold intervalExtent.
  unfold intervalStart, intervalEnd.
  remember (getInterval0 i) as v.
  destruct v. simpl.
  assert (ibeg x0 < iend x0)
    by (apply (interval_nonempty x0)).
  apply lt_minus in H. omega.

  Grab Existential Variables.
  destruct unhandled0.
    left. split. reflexivity.
    admit.
  admit.
Defined.

Definition moveActiveToHandled `(st : ScanState sd) `(x : IntervalId sd)
  (H : In x (active sd))
  : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd sd' }.
Proof.
  pose (ScanState_moveActiveToHandled sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorph; auto.
  apply Le.le_n_Sn.
Defined.

(*
Lemma moveActiveToHandled_spec1 : forall st st' (x : IntervalId st) H,
  st' = moveActiveToHandled x H -> nextInterval st' = nextInterval st.
Proof. intros. subst. destruct st. reflexivity. Qed.
*)

Definition moveActiveToInactive `(st : ScanState sd) `(x : IntervalId sd)
  (H : In x (active sd))
  : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd sd' }.
Proof.
  pose (ScanState_moveActiveToInactive sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorph; auto.
Defined.

(*
Lemma moveActiveToInactive_spec1 : forall st st' (x : IntervalId st) H,
  st' = moveActiveToInactive x H -> nextInterval st' = nextInterval st.
Proof. intros. subst. destruct st. reflexivity. Qed.
*)

Definition moveInactiveToActive `(st : ScanState sd) `(x : IntervalId sd)
  (H : In x (inactive sd))
  : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd sd' }.
Proof.
  pose (ScanState_moveInactiveToActive sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorph; auto.
Defined.

Definition moveInactiveToHandled `(st : ScanState sd) `(x : IntervalId sd)
  (H : In x (inactive sd))
  : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd sd' }.
Proof.
  pose (ScanState_moveInactiveToHandled sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorph; auto.
  apply Le.le_n_Sn.
Defined.

(* We need to know that [x] is not already a member of the [ScanState].  We
   know it was removed from the [ScanState] by [nextUnhandled], but it may
   have been split and the other parts added back to the unhandled list, so we
   need to know that it's not going to recur. *)
Definition addToActive `(st : ScanState sd) `(result : CurrentInterval st)
  (reg : PhysReg) : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd sd' }.
Proof.
Admitted.
(*
  destruct st.
  destruct result.
  eexists {| nextInterval := nextInterval0
           ; unhandled    := unhandled0
           ; active       := currentIntervalId0 :: active0
           ; inactive     := inactive0
           ; handled      := handled0
           ; getInterval  := getInterval0
           ; assignments  := fun i =>
               if cmp_eq_dec i currentIntervalId0
               then Some reg
               else assignments0 i
           |}.
  rapply Build_SSMorph; simpl; auto.
  Grab Existential Variables.
  apply NoDup_swap.
  rewrite <- app_comm_cons.
  apply NoDup_swap_cons.
  apply NoDup_cons; assumption.
Defined.
*)

(** ** Main functions *)

Definition getRegisterIndex `(st : ScanState sd) (k : IntervalId sd -> nat)
  (z : PhysReg -> option nat) (is : list (IntervalId sd))
  : PhysReg -> option nat :=
  fold_right
    (fun x f => fun r =>
       match assignments sd x with
       | None => f r
       | Some a => if cmp_eq_dec a r then Some (k x) else f r
       end) z is.

Definition nextIntersectionWith `(st : ScanState sd)
  `(x : Interval xd) (yid : IntervalId sd) : nat.
Proof.
Admitted.

Function findRegister (freeUntilPos : PhysReg -> option nat) (reg : PhysReg)
  {measure fin_to_nat reg} : (PhysReg * option nat)%type :=
  match freeUntilPos reg with
  | None => (reg, None)
  | Some pos =>
      match pred_fin reg with
      | None => (reg, Some pos)
      | Some nreg =>
          match findRegister freeUntilPos nreg with
          | (reg', None) => (reg', None)
          | (reg', Some pos') =>
              if pos <? pos'
              then (reg', Some pos')
              else (reg,  Some pos)
          end
      end
  end.
Proof. intros. apply pred_fin_lt. assumption. Qed.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg `(st : ScanState sd) `(i : CurrentInterval st)
  : option (PhysReg *
            { sd' : ScanStateDesc &
              { st' : ScanState sd' &
                CurrentInterval st' & SSMorph sd sd' } }) :=
  (* The first part of this algorithm has been modified to be more functional:
     instead of mutating an array called [freeUntilPos] and finding the
     register with the highest value, we use a function produced by a fold,
     and iterate over the register set. *)
  let currentId := currentIntervalId i in
  let cd        := currentDesc i in
  let current   := currentInterval i in

  (* set freeUntilPos of all physical registers to maxInt
     for each interval it in active do
       freeUntilPos[it.reg] = 0 *)
  let freeUntilPos' :=
        getRegisterIndex st (const 0) (const None) (active sd) in

  (* for each interval it in inactive intersecting with current do
       freeUntilPos[it.reg] = next intersection of it with current *)
  let intersectingIntervals :=
        filter (fun x =>
                  anyRangeIntersects (rds cd) (rds (projT1 (getInterval sd x))))
               (inactive sd) in
  let freeUntilPos :=
        getRegisterIndex st (nextIntersectionWith st current) freeUntilPos'
                         intersectingIntervals in

  (* reg = register with highest freeUntilPos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := findRegister freeUntilPos lastReg in

  let result := existT _ sd (existT2 _ _ st i (newSSMorph sd)) in
  let useReg := (reg, result) in

  (* [mres] indicates the highest use position of the indicated register,
     which is the furthest available. *)
  match mres with
  | None => Some useReg
  | Some n =>
      (* if freeUntilPos[reg] = 0 then
           // no register available without spilling
           allocation failed
         else if current ends before freeUntilPos[reg] then
           // register available for the whole interval
           current.reg = reg
         else
           // register available for the first part of the interval
           current.reg = reg
           split current before freeUntilPos[reg] *)
      if beq_nat n 0
      then None
      else if ltb (intervalEnd current) n
           then Some useReg
           else None            (* jww (2014-09-12): NYI *)
  end.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  This is why the
    type differs from [tryAllocateFreeReg], since in all cases the final state
    is changed. *)
Definition allocateBlockedReg `(st : ScanState sd) `(i : CurrentInterval st)
  : option PhysReg *
    { sd' : ScanStateDesc &
      { st' : ScanState sd' & CurrentInterval st' & SSMorph sd sd' } } :=
  (* set nextUsePos of all physical registers to maxInt *)

  (* for each interval it in active do
       nextUsePos[it.reg] = next use of it after start of current
     for each interval it in inactive intersecting with current do
       nextUsePos[it.reg] = next use of it after start of current *)

  (* reg = register with highest nextUsePos
     if first usage of current is after nextUsePos[reg] then
       // all other intervals are used before current, so it is best
       // to spill current itself
       assign spill slot to current
       split current before its first use position that requires a register
     else
       // spill intervals that currently block reg
       current.reg = reg
       split active interval for reg at position
       split any inactive interval for reg at the end of its lifetime hole *)

  (* // make sure that current does not intersect with
     // the fixed interval for reg
     if current intersects with the fixed interval for reg then
       split current before this intersection *)

  let result := existT _ sd (existT2 _ _ st i (newSSMorph sd)) in
  (None, result).

(*
Definition transportId `(H : nextInterval st = nextInterval st')
  (x : IntervalId st) : IntervalId st' :=
  transportId_le (Nat.eq_le_incl _ _ H) x.
*)

Definition existT_in_cons : forall {A a} {l : list A},
  {x : A & In x l} -> {x : A & In x (a :: l)}.
Proof.
  destruct l; intros; simpl.
    destruct X. inversion i.
  destruct X. exists x.
  apply in_inv in i.
  destruct i.
    right. left. assumption.
  right. right. assumption.
Defined.

Definition activeIntervals `(st : ScanState sd)
  : list { i : IntervalId sd & In i (active sd) } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          existT _ x (in_eq x xs) :: map existT_in_cons (go xs)
      end in
  go (active sd).

Definition inactiveIntervals `(st : ScanState sd)
  : list { i : IntervalId sd & In i (inactive sd) } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          existT _ x (in_eq x xs) :: map existT_in_cons (go xs)
      end in
  go (inactive sd).

(* Given a starting [ScanState] (at which point, [st = st0]), walk through the
   list of active intervals and mutate [st0] until it reflects the desired end
   state. *)
Fixpoint checkActiveIntervals `(st : ScanState sd) pos
  : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd sd' } :=
  let fix go (sd : ScanStateDesc) (st : ScanState sd) ss is pos :=
    match is with
    | nil => ss
    | x :: xs =>
        (* // check for intervals in active that are handled or inactive
           for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it does not cover position then
               move it from active to inactive *)
        let i := projT2 (getInterval sd (projT1 x)) in
        let st1 := if intervalEnd i <? pos
                   then moveActiveToHandled st (projT1 x) (projT2 x)
                   else if negb (intervalCoversPos i pos)
                        then moveActiveToInactive st (projT1 x) (projT2 x)
                        else ss in
        go sd st st1 xs pos
    end in
  go sd st (existT2 _ _ sd st (newSSMorph sd)) (activeIntervals st) pos.

(*
Lemma checkActiveIntervals_spec1 `(st : ScanState sd) : forall sp pos,
  sp = checkActiveIntervals st pos
    -> nextInterval (projT1 sp) = nextInterval sd.
Proof.
  intros. subst.
  induction st; simpl.
  - reflexivity.
  - admit.
  - 
  induction active0. reflexivity.
  unfold all_state_lists0 in *.
  pose proof lists_are_unique0.
  apply NoDup_swap in H.
  rewrite <- app_comm_cons in H.
  inversion H.
  subst. apply NoDup_swap in H3.
  specialize (IHactive0 H3).
Admitted.
*)

(* Given a starting [ScanState] (at which point, [st = st0]), walk through the
   list of active intervals and mutate [st0] until it arrives at the desired
   end state. *)

(*
Fixpoint checkActiveIntervals st pos
  : { st' : ScanState & nextInterval st' = nextInterval st } :=
  let fix go st st0 H is pos :=
    match is with
    | nil => existT _ st0 eq_refl
    | x :: xs =>
        (* // check for intervals in active that are handled or inactive
           for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it does not cover position then
               move it from active to inactive *)
        let i := projT2 (getInterval st (projT1 x)) in
        let p :=
            if intervalEnd i <? pos
            then let st1 := moveActiveToHandled (projT1 x) (projT2 x) in
                 let H'  := moveActiveToHandled_spec1 st st1 _ _ eq_refl
                 existT _ st1 H'
            else if negb (intervalCoversPos i pos)
                 then let st1 := moveActiveToInactive (projT1 x) (projT2 x) in
                      let H'  := moveActiveToInactive_spec1 st st1 _ _
                                                            eq_refl in
                      existT _ st1 H'
                 else existT _ st0 eq_refl in
        go st (projT1 p) (projT2 p) xs pos
    end in
  go st st eq_refl (activeIntervals st) pos.
*)

(*
Lemma checkActiveIntervals_spec1 : forall st st' pos,
  st' = checkActiveIntervals st pos -> nextInterval st = nextInterval st'.
Proof.
  intros.
  assert (nextInterval (checkActiveIntervals st pos) = nextInterval st).
    clear. destruct st. simpl.
    pose moveActiveToHandled_spec1.
    pose moveActiveToInactive_spec1.
    induction active0. reflexivity.
    admit.
  congruence.
(*.
  unfold all_state_lists0 in *.
  clear H.
  apply NoDup_swap in lists_are_unique0.
  rewrite <- app_comm_cons in lists_are_unique0.
  inversion lists_are_unique0.
  subst. apply NoDup_swap in H2.
  apply (IHactive0 H2).
*)
Admitted.
*)

(*
Lemma checkActiveIntervals_spec2 `(st : ScanState sd) : forall ss i pos
  (H : ss = checkActiveIntervals st pos),
  ~ In i (all_state_lists sd)
    -> ~ In (transportId (next_interval_increases (projT2 ss)) i)
            (all_state_lists (projT1 ss)).
Proof.
  intros.
  destruct ss. simpl.
  destruct s. simpl.
  unfold all_state_lists in *.
  simpl in H0.
  destruct x. simpl.
  destruct H.
  unfold not in *. intros.
  apply H0.
Admitted.
*)

(*
Fixpoint checkInactiveIntervals st pos : ScanState :=
  let fix go st st0 (is : list (IntervalId st)) (pos : nat) :=
    match is with
    | nil => st0
    | x :: xs =>
        (* // check for intervals in inactive that are handled or active
           for each interval it in inactive do
             if it ends before position then
               move it from inactive to handled
             else if it covers position then
               move it from inactive to active *)
        let i := projT2 (getInterval st x) in
        let x0 := transportId eq_refl x in
        let st1 := if intervalEnd i <? pos
                   then moveInactiveToHandled x0
                   else if intervalCoversPos i pos
                        then moveInactiveToActive x0
                        else st0 in
        go st st1 xs pos
    end in
  go st st (inactive st) pos.

Lemma checkInactiveIntervals_spec1 : forall st st0 pos,
  st0 = checkInactiveIntervals st pos -> nextInterval st = nextInterval st0.
Proof.
Admitted.

Lemma checkInactiveIntervals_spec2 : forall st st' i pos
  (H : st' = checkInactiveIntervals st pos),
  ~ In i (all_state_lists st)
    -> ~ In (transportId (checkInactiveIntervals_spec1 st st' pos H) i)
            (all_state_lists st').
Proof.
Admitted.
*)

Fixpoint checkInactiveIntervals `(st : ScanState sd) pos
  : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd sd' } :=
  let fix go (sd : ScanStateDesc) (st : ScanState sd) ss is pos :=
    match is with
    | nil => ss
    | x :: xs =>
        (* // check for intervals in inactive that are handled or active
           for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it covers position then
               move it from active to inactive *)
        let i := projT2 (getInterval sd (projT1 x)) in
        let st1 := if intervalEnd i <? pos
                   then moveInactiveToHandled st (projT1 x) (projT2 x)
                   else if intervalCoversPos i pos
                        then moveInactiveToActive st (projT1 x) (projT2 x)
                        else ss in
        go sd st st1 xs pos
    end in
  go sd st (existT2 _ _ sd st (newSSMorph sd)) (inactiveIntervals st) pos.

(*
Lemma checkInactiveIntervals_spec2 `(st : ScanState sd) : forall ss i pos
  (H : ss = checkInactiveIntervals st pos),
  ~ In i (all_state_lists sd)
    -> ~ In (transportId (next_interval_increases (projT2 ss)) i)
            (all_state_lists (projT1 ss)).
Proof.
Admitted.
*)

Definition projTT1 {A} {P Q : A -> Type} (e : {x : A & P x & Q x}) : A :=
  let (x,_,_) := e in x.

Definition projTT2 {A} {P Q : A -> Type} (e : {x : A & P x & Q x})
  : P (projTT1 e) := let (x,p,_) as x return (P (projTT1 x)) := e in p.

Definition projTT3 {A} {P Q : A -> Type} (e : {x : A & P x & Q x})
  : Q (projTT1 e) := let (x,_,q) as x return (Q (projTT1 x)) := e in q.

Definition handleInterval `(st0 : ScanState sd0) `(i : CurrentInterval st0)
  : { sd' : ScanStateDesc & ScanState sd' & SSMorph sd0 sd' } :=
  (* position = start position of current *)
  let currentId := currentIntervalId i in
  let cd        := currentDesc i in
  let current   := currentInterval i in
  let position  := intervalStart current in

  (* // check for intervals in active that are handled or inactive
     for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let sp1  := checkActiveIntervals st0 position in
  (* let Hnp1 := checkActiveIntervals_spec2 st0 sp1 currentId position *)
  (*                                        eq_refl (not_present i) in *)
  let cid1 := transportId (next_interval_increases (projTT3 sp1)) currentId in

  (* // check for intervals in inactive that are handled or active
     for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let sp2 := checkInactiveIntervals (projTT2 sp1) position in
  (* let Hnp2 := checkInactiveIntervals_spec2 (projT1 sp1) sp2 cid1 position *)
  (*                                          eq_refl Hnp1 in *)
  let cid2 := transportId (next_interval_increases (projTT3 sp2)) cid1 in

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg *)
  let current' :=
      Build_CurrentInterval (projTT1 sp2) (projTT2 sp2)
                            cid2 (currentDesc i) (currentInterval i) in
      (* {| currentIntervalId := cid2 *)
      (*  ; currentDesc       := currentDesc i *)
      (*  ; currentInterval   := currentInterval i *)
      (*  (* ; not_present       := Hnp2 *) *)
      (*  |} in *)
  let (mreg, result) :=
      match tryAllocateFreeReg st0 i with (* jww (2014-09-19): wrong? *)
      | Some (reg, result) => (Some reg, result)
      | None => allocateBlockedReg st0 i
      end in

  (* if current has a register assigned then
       add current to active *)
  match result with
  | existT sd3 (existT2 st3 current' ss3) =>
      match mreg with
      | Some reg =>
          let (sd4,st4,ss4) := addToActive st3 current' reg in
          existT2 _ _ sd4 st4 (transitivity ss3 ss4)
      | None => existT2 _ _ sd3 st3 ss3
      end
  end.

Function linearScan (sd : ScanStateDesc) (st : ScanState sd)
  {measure unhandledExtent sd} : { sd' : ScanStateDesc & ScanState sd' } :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match nextUnhandled st with
  | None => existT _ sd st
  | Some (existT sd1 (existT2 st1 i smorph1)) =>
    match handleInterval st1 i with
    | existT2 sd2 st2 smorph2 => linearScan sd2 st2
    end
  end.
Proof.
  (* We must prove that after every call to handleInterval, the total extent
     of the remaining unhandled intervals is less than it was before. *)
  intros.
  apply ssmorphst_proj_unhandledExtent.
  apply compose_ssmorph_with_ssmorphst with (sd2 := sd1); assumption.
Defined.

(****************************************************************************)

(** * Program graphs *)

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {}.

Definition determineIntervals (g : Graph VirtReg)
  : { sd : ScanStateDesc & ScanState sd }.
Admitted.

Definition allocateRegisters (g : Graph VirtReg)
  : { sd : ScanStateDesc & ScanState sd } :=
  let (sd,st) := determineIntervals g in linearScan sd st.

End Allocator.
