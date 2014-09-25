(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf *)

Require Import Alternative.
Require Import Coq.Arith.EqNat.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.ProofIrrelevance.
(* Require Import Coq.Sorting.Mergesort. *)
(* Require Import Coq.Sorting.Sorting. *)
Require Import Coq.Structures.Orders.
Require Import Recdef.
Require Import Lib.
Require String.

Module Import LN := ListNotations.
(* Module Import MergeSort := Sort FinOrder. *)

Open Scope string_scope.
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

Definition rangesIntersect (x y : RangeDesc) : bool :=
  if rbeg x <? rbeg y
  then rbeg y <? rend x
  else rbeg x <? rend y.

Definition rangesIntersectionPoint (x y : RangeDesc) : option nat :=
  if rangesIntersect x y
  then Some (min (rbeg x) (rbeg y))
  else None.

Definition anyRangeIntersects (is js : NonEmpty RangeDesc) : bool :=
  fold_right
    (fun r b => orb b (existsb (rangesIntersect r) (NE_to_list js)))
    false (NE_to_list is).

Fixpoint NE_fold_left {a b : Set} (f : a -> b -> a) (ne : NonEmpty b) (z : a) : a :=
  match ne with
    | NE_Sing x => f z x
    | NE_Cons x xs => NE_fold_left f xs (f z x)
  end.

Definition firstIntersectionPoint (rd1 rd2 : NonEmpty RangeDesc)
  : option nat :=
  NE_fold_left
    (fun acc rd =>
       match acc with
       | Some x => Some x
       | None =>
         NE_fold_left
           (fun acc' rd' =>
              match acc' with
              | Some x => Some x
              | None => rangesIntersectionPoint rd rd'
              end) rd2 None
       end) rd1 None.

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

    (** Caching this property comes in handy, as it can be tricky to determine
        it by reduction in some cases. *)
    interval_nonempty : ibeg < iend
}.

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

Definition intervalCoversPos `(i : Interval rs) (pos : nat) : bool :=
  andb (intervalStart i <=? pos) (pos <? intervalEnd i).

Definition intervalExtent `(i : Interval rs) :=
  intervalEnd i - intervalStart i.

Lemma Interval_nonempty : forall `(i : Interval rs),
  intervalStart i < intervalEnd i.
Proof.
  intros. unfold intervalStart, intervalEnd.
  induction i; simpl in *;
  induction r; simpl in *; min_max.
Qed.

Lemma Interval_extent_nonzero : forall `(i : Interval rs),
  intervalExtent i > 0.
Proof.
  intros.
  unfold intervalExtent.
  pose (Interval_nonempty i).
  apply lt_minus in l. assumption.
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

    unhandled : list IntervalId;   (* starts after pos *)
    active    : list IntervalId;   (* ranges over pos *)
    inactive  : list IntervalId;   (* falls in lifetime hole *)
    handled   : list IntervalId;   (* ends before pos *)

    getInterval  : IntervalId -> { d : IntervalDesc & Interval d };
    assignments  : IntervalId -> option PhysReg

    (* jww (2014-09-25): I haven't demonstrated yet that these extra
       restrictions are worth the effort.  It would be nicely to add them back
       in once everything is functioning. *)

    (* unhandled_sorted : StronglySorted cmp_le unhandled; *)

    (* all_state_lists  := unhandled ++ active ++ inactive ++ handled; *)
    (* lists_are_unique : NoDup all_state_lists *)
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

(*
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
*)

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
       ; unhandled        := nil
       ; active           := nil
       ; inactive         := nil
       ; handled          := nil
       ; getInterval      := fin_contra
       ; assignments      := fin_contra
       (* ; unhandled_sorted := LSorted_nil _ *)
       (* ; lists_are_unique := NoDup_nil _ *)
       |}

  | ScanState_newUnhandled
      ni unh (* unhsort *) act inact hnd geti assgn (* lau *) :
    forall `(i : Interval d),
    ScanState
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; getInterval      := geti
       ; assignments      := assgn
       (* ; unhandled_sorted := unhsort *)
       (* ; lists_are_unique := lau *)
       |} ->
    forall newi (H : newi = ultimate_Sn ni),
    (* jww (2014-09-25): I really do need to ensure that what is added here
       does not break ordering or non-duplication. *)
    ScanState
      {| nextInterval     := S ni
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
       (* ; unhandled_sorted := unhsort *)
       (* ; lists_are_unique := lau *)
       |}

  | ScanState_moveUnhandledToActive
      ni unh (* unhsort *) act inact hnd geti assgn (* lau *) x reg :
    ScanState
      {| nextInterval     := ni
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; getInterval      := geti
       ; assignments      := assgn
       (* ; unhandled_sorted := unhandled_sorted sd *)
       (* ; lists_are_unique := move_inactive_to_handled sd x (lists_are_unique sd) H *)
       |} ->
    ScanState
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := x :: act
       ; inactive         := inact
       ; handled          := hnd
       ; getInterval      := geti
       ; assignments      := fun i => if cmp_eq_dec i x
                                      then Some reg
                                      else assgn i
       (* ; unhandled_sorted := unhandled_sorted sd *)
       (* ; lists_are_unique := move_inactive_to_handled sd x (lists_are_unique sd) H *)
       |}

  | ScanState_moveActiveToInactive sd x :
    ScanState sd -> forall (H : In x (active sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := remove cmp_eq_dec x (active sd)
       ; inactive         := x :: inactive sd
       ; handled          := handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       (* ; lists_are_unique := move_active_to_inactive sd x (lists_are_unique sd) H *)
       |}

  | ScanState_moveActiveToHandled sd x :
    ScanState sd -> forall (H : In x (active sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := remove cmp_eq_dec x (active sd)
       ; inactive         := inactive sd
       ; handled          := x :: handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       (* ; lists_are_unique := move_active_to_handled sd x (lists_are_unique sd) H *)
       |}

  | ScanState_moveInactiveToActive sd x :
    ScanState sd -> forall (H : In x (inactive sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := x :: active sd
       ; inactive         := remove cmp_eq_dec x (inactive sd)
       ; handled          := handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       (* ; lists_are_unique := move_inactive_to_active sd x (lists_are_unique sd) H *)
       |}

  | ScanState_moveInactiveToHandled sd x :
    ScanState sd -> forall (H : In x (inactive sd)),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := remove cmp_eq_dec x (inactive sd)
       ; handled          := x :: handled sd
       ; getInterval      := getInterval sd
       ; assignments      := assignments sd
       (* ; unhandled_sorted := unhandled_sorted sd *)
       (* ; lists_are_unique := move_inactive_to_handled sd x (lists_are_unique sd) H *)
       |}.

Tactic Notation "ScanState_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ScanState_nil"
  | Case_aux c "ScanState_newUnhandled"
  | Case_aux c "ScanState_moveUnhandledToActive"
  | Case_aux c "ScanState_moveActiveToInactive"
  | Case_aux c "ScanState_moveActiveToHandled"
  | Case_aux c "ScanState_moveInactiveToActive"
  | Case_aux c "ScanState_moveInactiveToHandled"
  ].

(*
Theorem ScanState_active_bounded : forall st,
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
*)

Ltac cmp_reflexive :=
  match goal with
    [ |- context [match cmp_eq_dec ?X ?X with _ => _ end] ] =>
      assert (cmp_eq_dec X X = left eq_refl) as Hrcmp
        by (intros; destruct (cmp_eq_dec X X);
              [ f_equal; apply proof_irrelevance
              | intuition ]);
      rewrite Hrcmp in *; clear Hrcmp; simpl in *
  end.

Definition unhandledExtent `(sd : ScanStateDesc) : nat :=
  match unhandled sd with
  | nil => 0
  | [i] => intervalExtent (projT2 (getInterval sd i))
  | xs  =>
    let f n x := n + intervalExtent (projT2 (getInterval sd x)) in
    fold_left f xs 0
  end.

Theorem ScanState_unhandledExtent `(st : ScanState sd) :
  let unh := unhandled sd in
  let ue  := unhandledExtent sd in
  match unh with
  | nil    => ue = 0
  | [i]    => ue = intervalExtent (projT2 (getInterval sd i))
  | i :: _ => ue > intervalExtent (projT2 (getInterval sd i))
  end.
Proof.
  destruct sd.
  destruct unhandled0 eqn:Heqe;
  unfold unhandledExtent; simpl.
    reflexivity.
  destruct l eqn:Heqe2; simpl.
    reflexivity.
  apply fold_gt.
  pose (Interval_extent_nonzero (projT2 (getInterval0 i0))).
  omega.
Defined.

Lemma unhandledExtent_cons
  : forall ni i (unh : list (fin ni)) geti assgn assgn'
           (act act' inact inact' hnd hnd' : list (fin ni)),
  unhandledExtent
    {|
    nextInterval := ni;
    unhandled := unh;
    active := act;
    inactive := inact;
    handled := hnd;
    getInterval := geti;
    assignments := assgn |} <
  unhandledExtent
    {|
    nextInterval := ni;
    unhandled := i :: unh;
    active := act';
    inactive := inact';
    handled := hnd';
    getInterval := geti;
    assignments := assgn' |}.
Proof.
  intros.
  induction unh; unfold unhandledExtent; simpl;
  pose (Interval_extent_nonzero (projT2 (geti i))). omega.
  destruct unh; simpl. omega.
  apply fold_fold_lt. omega.
Qed.

Record NextScanState (P : ScanStateDesc -> Prop) : Type := {
    nextDesc   : ScanStateDesc;
    nextState  : ScanState nextDesc;
    morphProof : P nextDesc
}.

Arguments nextDesc  [P] _.
Arguments nextState [P] _.
Arguments morphProof [P] _.

Definition NextScanState_transitivity
  {P : ScanStateDesc -> ScanStateDesc -> Prop} `{Transitive _ P}
  `(n : NextScanState (P sd0)) `(o : NextScanState (P (nextDesc n)))
  : NextScanState (P sd0).
  destruct n. destruct o.
  simpl in *.
  rapply Build_NextScanState.
    apply nextState1.
  transitivity nextDesc0; assumption.
Defined.

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
Obligation 1. constructor; auto. Defined.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity (nextInterval y); auto.
  transitivity (unhandledExtent y); auto.
  transitivity (length (handled y)); auto.
Defined.

Record SSMorphLen (sd1 sd2 : ScanStateDesc) : Prop := {
    len_is_SSMorph :> SSMorph sd1 sd2;

    unhandled_nonempty :
      length (unhandled sd1) > 0 -> length (unhandled sd2) > 0
}.

Definition newSSMorphLen (s : ScanStateDesc) : SSMorphLen s s.
Proof. intros. constructor; auto. constructor; auto. Defined.

(** ** CurrentInterval *)

Record CurrentInterval `(st : ScanState sd) := {
    currentIntervalId : IntervalId sd;
    currentDesc       : IntervalDesc;
    currentInterval   : Interval currentDesc

    (* jww (2014-09-20): Not sure if I need this *)
    (* not_present : ~ In currentIntervalId (all_state_lists sd) *)
}.

Arguments currentIntervalId [sd st] _.
Arguments currentDesc       [sd st] _.
Arguments currentInterval   [sd st] _.

Record SSMorphSt (sd1 sd2 : ScanStateDesc) : Prop := {
    st_is_SSMorph :> SSMorph sd1 sd2;

    total_extent_measurably_decreases :
      unhandledExtent sd2 < unhandledExtent sd1
}.

(* jww (2014-09-25): This is just a stub and will be deleted. *)
Definition newSSMorphSt (s : ScanStateDesc) : SSMorphSt s s.
  constructor.
  constructor; auto.
Admitted.

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

Lemma ScanState_unhandledExtent_nonzero `(st : ScanState sd) :
  length (unhandled sd) > 0 <-> unhandledExtent sd > 0.
Proof.
  intros.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil".
    split; intros; inversion H.
  - Case "ScanState_newUnhandled".
    pose (Interval_extent_nonzero i).
    destruct unh eqn:Heqe;
    unfold unhandledExtent; simpl.
      split; intros; try cmp_reflexive; auto.
    destruct l eqn:Heqe2; simpl.
      split; intros; try cmp_reflexive; auto. omega.
    split; intros.
      apply fold_gt.
      cmp_reflexive. omega.
    apply Gt.gt_Sn_O.
  - Case "ScanState_moveUnhandledToActive".
    apply ScanState_unhandledExtent in st.
    rename st into i. simpl in *.
    destruct unh eqn:Heqe.
      split; intros. inversion H. auto.
    unfold unhandledExtent; simpl.
    destruct l eqn:Heqe2; simpl.
      split; intros.
      apply Interval_extent_nonzero.
      auto.
    split; intros.
      apply fold_gt.
      pose (Interval_extent_nonzero (projT2 (geti f))).
      omega.
    omega.
  - Case "ScanState_moveActiveToInactive".  apply IHst.
  - Case "ScanState_moveActiveToHandled".   apply IHst.
  - Case "ScanState_moveInactiveToActive".  apply IHst.
  - Case "ScanState_moveInactiveToHandled". apply IHst.
Qed.

(*
Lemma ScanState_no_unhandledExtent `(st : ScanState sd)
  (H : length (unhandled sd) = 0) : unhandledExtent sd = 0.
Proof.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". apply H.
  - Case "ScanState_newUnhandled". inversion H.
  - Case "ScanState_moveUnhandledToActive".
    apply ScanState_unhandledExtent in st.
    rename st into Hi. simpl in *.
    destruct unh eqn:Heqe;
    unfold unhandledExtent; simpl.
      reflexivity.
    simpl in H. inversion H.
  - Case "ScanState_moveActiveToInactive".  apply IHst. assumption.
  - Case "ScanState_moveActiveToHandled".   apply IHst. assumption.
  - Case "ScanState_moveInactiveToActive".  apply IHst. assumption.
  - Case "ScanState_moveInactiveToHandled". apply IHst. assumption.
Defined.

Lemma ScanState_sole_unhandledExtent `(st : ScanState sd)
  (H : length (unhandled sd) = 1) :
  intervalExtent (projT2 (getInterval sd
                  (safe_hd (unhandled sd) (one_gt_zero _ H)))) =
  unhandledExtent sd.
Proof.
  pose proof st as Hi.
  apply ScanState_unhandledExtent in Hi.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". inversion H.
  - Case "ScanState_newUnhandled".
    clear IHst.
    cmp_reflexive.
    inversion H.
    rewrite map_length in H2.
    pose (ScanState_no_unhandledExtent st). simpl in e.
    destruct unh eqn:Heqe;
    unfold unhandledExtent in *; simpl in *.
      auto.
    destruct l eqn:Heqe2; inversion H2.
  - Case "ScanState_moveUnhandledToActive".
    clear IHst.
    destruct unh eqn:Heqe. inversion H.
    assert (l = []). apply nil_list_0. auto.
    simpl in *. subst.
    unfold unhandledExtent in *; simpl in *.
    assumption.
  - Case "ScanState_moveActiveToInactive".  apply IHst. assumption.
  - Case "ScanState_moveActiveToHandled".   apply IHst. assumption.
  - Case "ScanState_moveInactiveToActive".  apply IHst. assumption.
  - Case "ScanState_moveInactiveToHandled". apply IHst. assumption.
Defined.

Lemma ScanState_more_unhandledExtent `(st : ScanState sd)
  (H : length (unhandled sd) > 1) :
  intervalExtent (projT2 (getInterval sd
                  (safe_hd (unhandled sd) (gt_one_gt_zero _ H)))) <
  unhandledExtent sd.
Proof.
  pose proof st as Hi0.
  apply ScanState_unhandledExtent in Hi0.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". inversion H.
  - Case "ScanState_newUnhandled".
    clear IHst.
    apply ScanState_unhandledExtent in st.
    rename st into Hi.
    cmp_reflexive.
    destruct unh eqn:Heqe.
      inversion H. inversion H2.
    unfold unhandledExtent in *; simpl in *.
    omega.
  - Case "ScanState_moveUnhandledToActive".
    clear IHst.
    apply ScanState_unhandledExtent in st.
    rename st into Hi.
    destruct unh eqn:Heqe. inversion H.
    subst. simpl in *.
    destruct l. inversion H. inversion H1.
    unfold unhandledExtent in *; simpl in *.
    omega.
  - Case "ScanState_moveActiveToInactive".  apply IHst. assumption.
  - Case "ScanState_moveActiveToHandled".   apply IHst. assumption.
  - Case "ScanState_moveInactiveToActive".  apply IHst. assumption.
  - Case "ScanState_moveInactiveToHandled". apply IHst. assumption.
Defined.

Definition nextUnhandled `(st : ScanState sd)
  : option { sd' : ScanStateDesc &
             { st' : ScanState sd' &
               CurrentInterval st' & SSMorphSt sd sd' } }.
Proof.
  pose (ScanState_sole_unhandledExtent st).
  pose (ScanState_more_unhandledExtent st).

  destruct sd.
  destruct unhandled0.
    apply None.
  apply Some.

  pose (ScanState_dropUnhandled
        nextInterval0
        i unhandled0
        (* unhandled_sorted0 *)
        active0
        inactive0
        handled0
        getInterval0
        assignments0
        (* lists_are_unique0 *) st).

  eexists.
  pose (intervalExtent (projT2 (getInterval0 i))).
  exists s.

  rapply Build_CurrentInterval.
    apply i.
    apply (projT2 (getInterval0 i)).

  (* Prove that a call to [nextUnhandled] must always reduce the unhandled
     extent. *)
  clear s.
  constructor.
    constructor; auto.
    destruct unhandled0 eqn:Heqe;
    unfold unhandledExtent; simpl.
      apply Le.le_0_n.
    destruct l0 eqn:Heqe2; simpl. omega.
    apply fold_fold_le. omega.

  pose (Interval_extent_nonzero (projT2 (getInterval0 i))).
  destruct unhandled0 eqn:Heqe;
  unfold unhandledExtent; simpl.
    omega.
  destruct l0 eqn:Heqe2; simpl. omega.
  apply fold_fold_lt. omega.
Defined.
*)

Definition moveActiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (active sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveActiveToHandled sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
  apply Le.le_n_Sn.
Defined.

Definition moveActiveToInactive `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (active sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveActiveToInactive sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveInactiveToActive `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveInactiveToActive sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
Defined.

Definition moveInactiveToHandled `(st : ScanState sd) (x : IntervalId sd)
  (H : In x (inactive sd)) : NextScanState (SSMorphLen sd).
Proof.
  pose (ScanState_moveInactiveToHandled sd x st H). eexists. apply s.
  destruct sd. simpl.
  rapply Build_SSMorphLen; auto.
  rapply Build_SSMorph; auto.
  apply Le.le_n_Sn.
Defined.

Definition moveUnhandledToActive `(st : ScanState sd) (reg : PhysReg)
  (H : length (unhandled sd) > 0) : NextScanState (SSMorphSt sd).
Proof.
  destruct sd.
  destruct unhandled0; simpl in *. omega.
  pose (ScanState_moveUnhandledToActive
          nextInterval0 unhandled0
          (* unhsort *)
          active0 inactive0 handled0
          getInterval0 assignments0
          (* lau *)
          i reg).
  eexists. apply s. apply st.
  pose (unhandledExtent_cons nextInterval0 i unhandled0 getInterval0
         (fun i0 : fin nextInterval0 =>
            if cmp_eq_dec i0 i
            then Some reg
            else assignments0 i0) assignments0
         (i :: active0) active0 inactive0 inactive0 handled0 handled0)
    as ue_cons.
  rapply Build_SSMorphSt; auto.
  rapply Build_SSMorph; auto.
  apply (Lt.lt_le_weak _ _ ue_cons).
Defined.

(** ** Main functions *)

Definition nextIntersectionWith
  `(Interval xd) `(it : IntervalId sd) : option nat :=
  let itval := getInterval sd it in
  firstIntersectionPoint (rds (projT1 itval)) (rds xd).

Definition getRegisterIndex `(st : ScanState sd) (k : IntervalId sd -> option nat)
  (z : PhysReg -> option nat) (is : list (IntervalId sd))
  : PhysReg -> option nat :=
  fold_right
    (fun x f => fun r =>
       match assignments sd x with
       | None => f r
       | Some a => if cmp_eq_dec a r then k x else f r
       end) z is.

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
Proof. intros; apply pred_fin_lt; assumption. Qed.

(** If [tryAllocateFreeReg] fails to allocate a register, the [ScanState] is
    left unchanged.  If it succeeds, or is forced to split [current], then a
    register will have been assigned. *)
Definition tryAllocateFreeReg `(st : ScanState sd) `(current : Interval cd)
  (H : length (unhandled sd) > 0)
  : option (NextScanState (SSMorphSt sd)) :=
  (* The first part of this algorithm has been modified to be more functional:
     instead of mutating an array called [freeUntilPos] and finding the
     register with the highest value, we use a function produced by a fold,
     and iterate over the register set. *)

  (* set freeUntilPos of all physical registers to maxInt
     for each interval it in active do
       freeUntilPos[it.reg] = 0 *)
  let freeUntilPos' :=
        getRegisterIndex st (const None) (const None) (active sd) in

  (* for each interval it in inactive intersecting with current do
       freeUntilPos[it.reg] = next intersection of it with current *)
  let intersectingIntervals :=
        filter (fun x => anyRangeIntersects
                           (rds cd) (rds (projT1 (getInterval sd x))))
               (inactive sd) in
  let freeUntilPos :=
        getRegisterIndex st (nextIntersectionWith current) freeUntilPos'
                         intersectingIntervals in

  (* reg = register with highest freeUntilPos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := findRegister freeUntilPos lastReg in
  let result      := moveUnhandledToActive st reg H in

  (* [mres] indicates the highest use position of the indicated register,
     which is the furthest available. *)
  match mres with
  | None => Some result
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
           then Some result
           else None            (* jww (2014-09-12): NYI *)
  end.

(** If [allocateBlockedReg] fails, it's possible no register was assigned and
    that the only outcome was to split one or more intervals.  This is why the
    type differs from [tryAllocateFreeReg], since in all cases the final state
    is changed. *)
Definition allocateBlockedReg `(st : ScanState sd) `(current : Interval cd)
  (H : length (unhandled sd) > 0)
  : NextScanState (SSMorphSt sd) :=
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

  Build_NextScanState _ sd st (newSSMorphSt sd).

Definition activeIntervals `(st : ScanState sd)
  : list { i : IntervalId sd & In i (active sd) } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          existT _ x (in_eq x xs) :: map existT_in_cons (go xs)
      end in
  go (active sd).

Fixpoint checkActiveIntervals `(st : ScanState sd) pos
  : NextScanState (SSMorphLen sd) :=
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
  go sd st (Build_NextScanState _ sd st (newSSMorphLen sd))
     (activeIntervals st) pos.

Definition inactiveIntervals `(st : ScanState sd)
  : list { i : IntervalId sd & In i (inactive sd) } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          existT _ x (in_eq x xs) :: map existT_in_cons (go xs)
      end in
  go (inactive sd).

Fixpoint checkInactiveIntervals `(st : ScanState sd) pos
  : NextScanState (SSMorphLen sd) :=
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
  go sd st (Build_NextScanState _ sd st (newSSMorphLen sd))
     (inactiveIntervals st) pos.

Lemma SSMorphLenLenSt_transitivity
  `( i : SSMorphLen sd0 sd1)
  `( j : SSMorphLen sd1 sd2)
  `( k : SSMorphSt  sd2 sd3) : SSMorphSt sd0 sd3.
Proof.
  constructor;
  destruct i;
  destruct j;
  destruct k.
    transitivity sd1; auto.
    transitivity sd2; auto.
  intuition.
Qed.

Definition handleInterval `(st0 : ScanState sd0)
  (H : length (unhandled sd0) > 0) : NextScanState (SSMorphSt sd0) :=
  (* position = start position of current *)
  let currentId := safe_hd (unhandled sd0) H in
  let current   := projT2 (getInterval sd0 currentId) in
  let position  := intervalStart current in

  (* // check for intervals in active that are handled or inactive
     for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let sp1  := checkActiveIntervals st0 position in
  let Hlt1 := unhandled_nonempty sd0 (nextDesc sp1) (morphProof sp1) H in
  let H1   := next_interval_increases (morphProof sp1) in
  let cid1 := transportId H1 currentId in

  (* // check for intervals in inactive that are handled or active
     for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let sp2  := checkInactiveIntervals (nextState sp1) position in
  let Hlt2 := unhandled_nonempty (nextDesc sp1) (nextDesc sp2)
                                 (morphProof sp2) Hlt1 in
  let H2   := next_interval_increases (morphProof sp2) in
  let cid2 := transportId H2 cid1 in

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg
     if current has a register assigned then
       add current to active (done by the helper functions) *)
  let result :=
      fromMaybe (allocateBlockedReg (nextState sp2) current Hlt2)
                (tryAllocateFreeReg (nextState sp2) current Hlt2) in
  {| nextDesc   := nextDesc result
   ; nextState  := nextState result
   ; morphProof :=
       SSMorphLenLenSt_transitivity (morphProof sp1) (morphProof sp2)
                                    (morphProof result)
   |}.

Lemma list_cons_nonzero : forall {a x} {xs l : list a},
  l = x :: xs -> length l > 0.
Proof. intros. rewrite H. simpl. omega. Qed.

(* while unhandled /= { } do
     current = pick and remove first interval from unhandled
     HANDLE_INTERVAL (current) *)

Function linearScan (sd : ScanStateDesc) (st : ScanState sd)
  {measure unhandledExtent sd} : { sd' : ScanStateDesc & ScanState sd' } :=
  match destruct_list (unhandled sd) with
  | inleft (existT x (exist xs H)) =>
    match handleInterval st (list_cons_nonzero H) with
    | Build_NextScanState sd2 st2 smorph2 => linearScan sd2 st2
    end
  | inright _ => existT _ sd st
  end.
(* We must prove that after every call to handleInterval, the total extent
   of the remaining unhandled intervals is less than it was before. *)
Proof. intros; inversion smorph2; assumption. Defined.

(****************************************************************************)

(** * Program graphs *)

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {
    postOrderTraversal : a
}.

Definition determineIntervals (g : Graph VirtReg)
  : { sd : ScanStateDesc & ScanState sd }.
Admitted.

Definition allocateRegisters (g : Graph VirtReg)
  : { sd : ScanStateDesc & ScanState sd } :=
  let (sd,st) := determineIntervals g in linearScan sd st.

End Allocator.
