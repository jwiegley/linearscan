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
(* Require Import Coq.Sorting.Sorting. *)
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
    ups  : NonEmpty UsePos
}.

Inductive Range : RangeDesc -> Set :=
  | R_Sing u :
      Range {| rbeg := uloc u
             ; rend := uloc u
             ; ups  := NE_Sing u
             |}
  | R_Cons u x : Range x -> uloc u < rbeg x
      -> Range {| rbeg := rbeg x
                ; rend := rend x
                ; ups  := NE_Cons u (ups x)
                |}
  | R_Extend x b' e' : Range x
      -> Range {| rbeg := min b' (rbeg x)
                ; rend := Peano.max e' (rend x)
                ; ups  := ups x
                |}.

Definition rangesIntersect `(x : RangeDesc) `(y : RangeDesc) : bool :=
  if rbeg x <? rbeg y then rbeg y <? rend x else rbeg x <? rend y.

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

Inductive Interval : NonEmpty RangeDesc -> Set :=
  | I_Sing : forall x, Range x -> Interval (NE_Sing x)
  | I_Cons1 : forall x y,
      Range x -> Interval (NE_Sing y) -> rend y <= rbeg y
        -> Interval (NE_Cons x (NE_Sing y))
  | I_Consn : forall x y xs,
      Range x -> Interval (NE_Cons y xs) -> rend y <= rbeg y
        -> Interval (NE_Cons x (NE_Cons y xs)).

Definition intervalStart `(i : Interval rs) : nat := rbeg (NE_hd rs).
Definition intervalEnd   `(i : Interval rs) : nat := rend (NE_tl rs).

Definition intervalCoversPos `(i : Interval rs) (pos : nat) : bool :=
  andb (intervalStart i <=? pos) (pos <? intervalEnd i).

Definition intervalExtent `(i : Interval rs) :=
  intervalEnd i - intervalStart i.

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

Record ScanState := {
    nextInterval : nat;
    IntervalId   := fin nextInterval;

    unhandled : list IntervalId;   (* starts after pos *)
    active    : list IntervalId;   (* ranges over pos *)
    inactive  : list IntervalId;   (* falls in lifetime hole *)
    handled   : list IntervalId;   (* ends before pos *)

    getInterval  : IntervalId -> { rs : NonEmpty RangeDesc & Interval rs };
    assignments  : IntervalId -> option PhysReg;

    all_state_lists  := unhandled ++ active ++ inactive ++ handled;
    lists_are_unique : NoDup all_state_lists;

    current   : option { rs : NonEmpty RangeDesc & Interval rs };
    currentId : option { i : IntervalId & ~ In i all_state_lists }
}.

Definition totalExtent `(xs : list (IntervalId st)) : nat :=
  fold_left (fun n x => n + intervalExtent (projT2 (getInterval st x))) xs 0.

Program Definition newScanState
  : ScanState := {| nextInterval := 0
                  ; unhandled    := nil
                  ; active       := nil
                  ; inactive     := nil
                  ; handled      := nil
                  ; assignments  := const None
                  |}.
Obligation 1. inversion H. Defined.
Obligation 2. constructor. Defined.
Obligation 3. apply None. Defined.
Obligation 4. apply None. Defined.

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

Record SSMorph (s : ScanState) (s' : ScanState) := {
    next_interval_only_increases : nextInterval s     <= nextInterval s';
    total_extent_only_decreases  :
      totalExtent (unhandled s') <= totalExtent (unhandled s);
    handled_count_only_increases : length (handled s) <= length (handled s')
}.

Program Instance SSMorph_PO : PreOrder SSMorph.
Obligation 1. constructor; auto. Defined.
Obligation 2.
  constructor; destruct H; destruct H0.
  transitivity (nextInterval y); auto.
  transitivity (totalExtent (unhandled y)); auto.
  transitivity (length (handled y)); auto.
Defined.

(** ** CurrentInterval *)

Record CurrentInterval (st : ScanState) := {
    currentIntervalId : IntervalId st;
    currentRanges     : NonEmpty RangeDesc;
    currentInterval   : Interval currentRanges;

    not_present : ~ In currentIntervalId (all_state_lists st)
}.

Definition SST (a : Type) := RState ScanState SSMorph a.

Definition return_ {a : Type} :=
  @pure SST (RState_Applicative ScanState SSMorph SSMorph_PO) a.

Lemma fold_left_0_r : forall a (f : a -> nat) xs (y : a),
   fold_left (fun (n : nat) (x : a) => n + f x) xs (f y) =
   fold_left (fun (n : nat) (x : a) => n + f x) xs 0 + (f y).
Proof.
Admitted.

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
  apply (fold_left_0_r (IntervalId st)
           (fun (x : IntervalId st) =>
              intervalExtent (projT2 (getInterval st x)))).
Qed.

Lemma unhandled_extent_cons : forall (st : ScanState) x xs,
  x :: xs = unhandled st -> totalExtent xs <= totalExtent (x :: xs).
Proof.
  intros.
  rewrite totalExtent_cons.
  apply Plus.le_plus_r.
Qed.

Definition nextUnhandled (st : ScanState)
  : option { st' : ScanState & CurrentInterval st' & SSMorph st st' }.
Proof.
  pose (unhandled_extent_cons st).
  destruct st.
  destruct unhandled0.
    apply None.
  apply Some.
  destruct (getInterval0 i) as [rs int].
  eexists {| unhandled   := unhandled0
           ; active      := active0
           ; inactive    := inactive0
           ; handled     := handled0
           ; getInterval := getInterval0
           ; assignments := assignments0
           |}.
  rapply Build_CurrentInterval.
  (**) apply int.
  (**) unfold all_state_lists. simpl.
       unfold all_state_lists0 in lists_are_unique0.
       inversion lists_are_unique0. apply H1.
  rapply Build_SSMorph.
  (**) reflexivity.
  (**) simpl. apply l. reflexivity.
  (**) reflexivity.
  Grab Existential Variables.
  apply Some. exists i.
  inversion lists_are_unique0. assumption.
  apply Some. exists rs. assumption.
  inversion lists_are_unique0; assumption.
Defined.

Definition moveActiveToHandled `(x : IntervalId st)
  (H : In x (active st)) : ScanState.
Proof.
  constructor. intros.
  destruct H0.
  destruct st.
  destruct st0.
  eapply {| after :=
            {| unhandled   := unhandled0
             ; active      := remove cmp_eq_dec x active0
             ; inactive    := inactive0
             ; handled     := x :: handled0
             ; getInterval := getInterval0
             ; assignments := assignments0
             |}
          |}.
  Grab Existential Variables.
  (* 1 *)
    constructor; simpl in *.
    - admit.
    - 
  inversion H0.
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
  apply H.
Defined.

Lemma moveActiveToHandled_spec1 : forall st st' (x : IntervalId st) H,
  st' = moveActiveToHandled x H -> nextInterval st' = nextInterval st.
Proof. intros. subst. destruct st. reflexivity. Qed.

Definition moveActiveToInactive `(x : IntervalId st)
  (H : In x (active st)) : ScanState.
Proof.
  destruct st.
  eapply {| unhandled   := unhandled0
          ; active      := remove cmp_eq_dec x active0
          ; inactive    := x :: inactive0
          ; handled     := handled0
          ; getInterval := getInterval0
          ; assignments := assignments0
          |}.
    Grab Existential Variables.
  apply NoDup_swap.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply NoDup_juggle.
  rewrite app_assoc.
  rewrite app_assoc.
  apply NoDup_swap.
  rewrite <- app_assoc.
  assumption.
  apply H.
Defined.

Lemma moveActiveToInactive_spec1 : forall st st' (x : IntervalId st) H,
  st' = moveActiveToInactive x H -> nextInterval st' = nextInterval st.
Proof. intros. subst. destruct st. reflexivity. Qed.

Definition moveInactiveToHandled `(x : IntervalId st) : ScanState.
Proof.
  destruct st.
  eapply {| unhandled   := unhandled0
          ; active      := active0
          ; inactive    := remove cmp_eq_dec x inactive0
          ; handled     := x :: handled0
          ; getInterval := getInterval0
          ; assignments := assignments0
          |}.
    Grab Existential Variables.
Admitted.

Definition moveInactiveToActive `(x : IntervalId st) : ScanState.
Proof.
  destruct st.
  eapply {| unhandled   := unhandled0
          ; active      := x :: active0
          ; inactive    := remove cmp_eq_dec x inactive0
          ; handled     := handled0
          ; getInterval := getInterval0
          ; assignments := assignments0
          |}.
    Grab Existential Variables.
Admitted.

(* We need to know that [x] is not already a member of the [ScanState].  We
   know it was removed from the [ScanState] by [nextUnhandled], but it may
   have been split and the other parts added back to the unhandled list, so we
   need to know that it's not going to recur. *)
Definition addToActive (result : CurrentInterval) (reg : PhysReg) : SST unit.
Proof.
  constructor. intros.
  destruct result.
  destruct resultState0.
  eexists
    (tt, {| nextInterval := nextInterval0
          ; unhandled    := unhandled0
          ; active       := currentIntervalId0 :: active0
          ; inactive     := inactive0
          ; handled      := handled0
          ; getInterval  := getInterval0
          ; assignments  := fun i =>
              if cmp_eq_dec i currentIntervalId0
              then Some reg
              else assignments0 i
          |}).
  constructor.
  destruct x. simpl.
  Grab Existential Variables.
  unfold all_state_lists in *.
  unfold all_state_lists0 in *.
  unfold IntervalId, IntervalId0 in *. simpl in *.
  apply NoDup_swap.
  rewrite <- app_comm_cons.
  apply NoDup_swap_cons.
  apply NoDup_cons; assumption.
Defined.

(** ** Main functions *)

Definition getRegisterIndex (st : ScanState) (k : IntervalId st -> nat)
  (z : PhysReg -> option nat) (is : list (IntervalId st))
  : PhysReg -> option nat :=
  fold_right
    (fun x f => fun r =>
       match assignments st x with
       | None => f r
       | Some a => if cmp_eq_dec a r then Some (k x) else f r
       end) z is.

Definition nextIntersectionWith (st : ScanState)
  `(x : Interval xd) (yid : IntervalId st) : nat.
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
Definition tryAllocateFreeReg (i : CurrentInterval)
  : option (PhysReg * CurrentInterval) :=
  (* The first part of this algorithm has been modified to be more functional:
     instead of mutating an array called [freeUntilPos] and finding the
     register with the highest value, we use a function produced by a fold,
     and iterate over the register set. *)
  let st        := resultState i in
  let currentId := currentIntervalId i in
  let rs        := currentRanges i in
  let current   := currentInterval i in

  (* set freeUntilPos of all physical registers to maxInt
     for each interval it in active do
       freeUntilPos[it.reg] = 0 *)
  let freeUntilPos' :=
        getRegisterIndex st (const 0) (const None) (active st) in

  (* for each interval it in inactive intersecting with current do
       freeUntilPos[it.reg] = next intersection of it with current *)
  let intersectingIntervals :=
        filter (fun x =>
                  anyRangeIntersects rs (projT1 (getInterval st x)))
               (inactive st) in
  let freeUntilPos :=
        getRegisterIndex st (nextIntersectionWith st current) freeUntilPos'
                         intersectingIntervals in

  (* reg = register with highest freeUntilPos *)
  let lastReg     := ultimate_from_nat maxReg registers_exist in
  let (reg, mres) := findRegister freeUntilPos lastReg in
  let useReg      := (reg, {| resultState       := st
                            ; currentRanges     := rs
                            ; currentIntervalId := currentId
                            ; currentInterval   := current
                            ; not_present       := not_present i
                           |}) in

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
Definition allocateBlockedReg (i : CurrentInterval)
  : option PhysReg * CurrentInterval :=
  let st        := resultState i in
  let currentId := currentIntervalId i in
  let rs        := currentRanges i in
  let current   := currentInterval i in

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
       splse current before this intersection *)
  (None, i).

Definition transportId_le `(H : nextInterval st <= nextInterval st')
  (x : IntervalId st) : IntervalId st'.
Proof.
  destruct st. destruct st'.
  unfold IntervalId0, IntervalId1 in *.
  unfold IntervalId in *. simpl in *.
  apply (fin_transport nextInterval0 nextInterval1 H).
  assumption.
Defined.

Definition transportId `(H : nextInterval st = nextInterval st')
  (x : IntervalId st) : IntervalId st' :=
  transportId_le (Nat.eq_le_incl _ _ H) x.

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

Definition activeIntervals (st : ScanState)
  : list { i : IntervalId st & In i (active st) } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          existT _ x (in_eq x xs) :: map existT_in_cons (go xs)
      end in
  go (active st).

(* Given a starting [ScanState] (at which point, [st = st0]), walk through the
   list of active intervals and mutate [st0] until it reflects the desired end
   state. *)
Fixpoint checkActiveIntervals st pos : ScanState :=
  let fix go st st0 is pos :=
    match is with
    | nil => st0
    | x :: xs =>
        (* // check for intervals in active that are handled or inactive
           for each interval it in active do
             if it ends before position then
               move it from active to handled
             else if it does not cover position then
               move it from active to inactive *)
        let i := projT2 (getInterval st (projT1 x)) in
        let st1 := if intervalEnd i <? pos
                   then moveActiveToHandled (projT1 x) (projT2 x)
                   else if negb (intervalCoversPos i pos)
                        then moveActiveToInactive (projT1 x) (projT2 x).
                        else st0 in
        go st st1 xs pos
    end in
  go st st (activeIntervals st) pos.

(*
Lemma checkActiveIntervals_spec1 : forall st st' pos,
  st' = checkActiveIntervals st pos -> nextInterval st' = nextInterval st.
Proof.
  intros. subst. destruct st. simpl.
  induction active0. reflexivity.
  unfold all_state_lists0 in *.
  pose proof lists_are_unique0.
  apply NoDup_swap in H.
  rewrite <- app_comm_cons in H.
  inversion H.
  subst. apply NoDup_swap in H3.
  specialize (IHactive0 H3).
Admitted.

(* Given a starting [ScanState] (at which point, [st = st0]), walk through the
   list of active intervals and mutate [st0] until it arrives at the desired
   end state. *)

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

Lemma checkActiveIntervals_spec2 : forall st st' i pos
  (H : st' = checkActiveIntervals st pos),
  ~ In i (all_state_lists st)
    -> ~ In (transportId (checkActiveIntervals_spec1 st st' pos H) i)
            (all_state_lists st').
Proof.
Admitted.

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

Definition handleInterval (i : CurrentInterval) : ScanState :=
  (* position = start position of current *)
  let st0       := resultState i in
  let currentId := currentIntervalId i in
  let rs        := currentRanges i in
  let current   := currentInterval i in
  let position  := intervalStart current in

  (* // check for intervals in active that are handled or inactive
     for each interval it in active do
       if it ends before position then
         move it from active to handled
       else if it does not cover position then
         move it from active to inactive *)
  let st1 := checkActiveIntervals st0 position in
  let Heq1 := checkActiveIntervals_spec1 st0 st1 position eq_refl in
  let cid1 := transportId (eq_trans Heq1 eq_refl) currentId in
  let Hnp1 := checkActiveIntervals_spec2 st0 st1 currentId position
                                         eq_refl (not_present i) in

  (* // check for intervals in inactive that are handled or active
     for each interval it in inactive do
       if it ends before position then
         move it from inactive to handled
       else if it covers position then
         move it from inactive to active *)
  let st2  := checkInactiveIntervals st1 position in
  let Heq2 := checkInactiveIntervals_spec1 st1 st2 position eq_refl in
  let cid2 := transportId (eq_trans Heq2 eq_refl) cid1 in
  let Hnp2 := checkInactiveIntervals_spec2 st1 st2 cid1 position
                                           eq_refl Hnp1 in

  (* // find a register for current
     tryAllocateFreeReg
     if allocation failed then
       allocateBlockedReg *)
  let newDesc := {| resultState       := st2
                  ; currentRanges     := currentRanges i
                  ; currentIntervalId := cid2
                  ; currentInterval   := currentInterval i
                  ; not_present       := Hnp2
                  |} in
  let (mreg, result) :=
      match tryAllocateFreeReg i with
      | Some (reg, result) => (Some reg, result)
      | None => allocateBlockedReg i
      end in

  (* if current has a register assigned then
       add current to active *)
  match mreg with
  | Some reg => addToActive result reg
  | None => resultState result
  end.

Function linearScan (st : ScanState) {measure unhandledExtent st}
  : ScanState :=
  (* while unhandled /= { } do
       current = pick and remove first interval from unhandled
       HANDLE_INTERVAL (current) *)
  match nextUnhandled st with
  | None => st
  | Some i => linearScan (handleInterval i)
  end.
Proof.
  (* We must prove that after every call to handleInterval, the total extent
     of the remaining unhandled intervals is less than it was before. *)
  intros.
  unfold unhandledExtent.
  unfold intervalExtent.
  unfold intervalStart, intervalEnd.
  induction st.
Admitted.

(****************************************************************************)

(** * Program graphs *)

(** Given a node graph of our low-level intermediate representation, where
    instructions are associated with virtual registers, compute the linear
    mapping to intervals. *)

Class Graph (a : Set) := {}.

Definition determineIntervals (g : Graph VirtReg) : ScanState.
Admitted.

Definition allocateRegisters : Graph VirtReg -> ScanState :=
  linearScan ∘ determineIntervals.

End Allocator.

