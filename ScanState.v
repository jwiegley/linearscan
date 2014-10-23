Require Import Lib.

Require Export Machine.
Require Export Interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MScanState (Mach : Machine).
Import Mach.

Definition maxReg := maxReg.
Definition PhysReg := fin maxReg.
Definition registers_exist := registers_exist.

(** ** ScanStateDesc *)

(** A [ScanStateDesc] is always relative to a current position as we move
    through the sequentialized instruction stream over which registers are
    allocated. *)

Record ScanStateDesc := {
    nextInterval : nat;
    IntervalId   := fin nextInterval;

    unhandled : list (IntervalId * nat);   (* starts after pos *)
    active    : list IntervalId;           (* ranges over pos *)
    inactive  : list IntervalId;           (* falls in lifetime hole *)

    unhandledIds    := map (@fst _ _) unhandled;
    unhandledStarts := map (@snd _ _) unhandled;

    (* jww (2014-10-01): Prove: The length of the active intervals list <
       maxReg. *)
    (* active_registers : length active < min maxReg nextInterval; *)

    (* jww (2014-10-01): The handled list is unnecessary and can be deleted
       when everything is working. *)
    handled   : list IntervalId;   (* ends before pos *)

    intervals   : Vec { d : IntervalDesc | Interval d } nextInterval;
    assignments : Vec (option PhysReg) nextInterval;

    (** Fixed Intervals

        Some machine instructions require their operands in fixed
        registers. Such constraints are already considered during the
        construction of the LIR by emitting physical register operands instead
        of virtual register operands. Although the register allocator must
        leave these operands unchanged, they must be considered during
        register allocation because they limit the number of available
        registers. Information about physical registers is collected in fixed
        intervals.

        For each physical register, one fixed interval stores where the
        register is not available for allocation. Use positions are not needed
        for fixed intervals because they are never split and spilled. Register
        constraints at method calls are also modeled using fixed intervals:
        Because all registers are destroyed when the call is executed, ranges
        of length 1 are added to all fixed intervals at the call
        site. Therefore, the allocation pass cannot assign a register to any
        interval there, and all intervals are spilled before the call. *)

    fixedIntervals :
      Vec (option { d : IntervalDesc | FixedInterval d }) maxReg;

    unhandled_sorted : StronglySorted leq unhandledStarts;

    all_state_lists  := unhandledIds ++ active ++ inactive ++ handled;
    lists_are_unique : uniq all_state_lists
}.

Definition widen_id (sd : ScanStateDesc) :=
  widen_ord (leqnSn (nextInterval sd)).

Definition getInterval `(i : IntervalId sd) :=
 (V.nth (intervals sd) (to_vfin i)).2.

Definition getAssignment `(i : IntervalId sd) :=
  V.nth (assignments sd) (to_vfin i).

Definition unhandledExtent `(sd : ScanStateDesc) : nat :=
  match unhandledIds sd with
  | nil => 0
  | [:: i] => intervalExtent (V.nth (intervals sd) (to_vfin i)).2
  | xs  =>
    let f n x := n + intervalExtent (V.nth (intervals sd) (to_vfin x)).2 in
    foldl f 0 xs
  end.

Lemma uniq_unhandledExtent_cons
  : forall ni i (unh : list (fin ni * nat)) ints assgn assgn' fixints
      (act act' inact inact' hnd hnd' : list (fin ni))
      (lau : uniq (map (@fst _ _) unh ++ act ++ inact ++ hnd))
      (lau' : uniq ((fst i :: map (@fst _ _) unh) ++ act' ++ inact' ++ hnd'))
      unhs unhs',
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := unh
     ; active           := act
     ; inactive         := inact
     ; handled          := hnd
     ; intervals        := ints
     ; assignments      := assgn
     ; fixedIntervals   := fixints
     ; unhandled_sorted := unhs
     ; lists_are_unique := lau
     |} <
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := i :: unh
     ; active           := act'
     ; inactive         := inact'
     ; handled          := hnd'
     ; intervals        := ints
     ; assignments      := assgn'
     ; fixedIntervals   := fixints
     ; unhandled_sorted := unhs'
     ; lists_are_unique := lau'
     |}.
Proof.
  intros.
  induction unh;
  unfold unhandledExtent;
  simpl; destruct i as [i beg];
  pose (Interval_extent_nonzero (V.nth ints (to_vfin i)).2).
    auto.
  destruct unh;
  simpl; destruct a as [a ?];
  first by (rewrite add0n; apply ltn_plus).
  apply fold_fold_lt; rewrite 2!add0n -addnA.
  exact: ltn_plus.
Qed.

Lemma move_unhandled_to_active : forall n (x : fin n) unh act inact hnd,
  uniq ((x :: unh) ++ act ++ inact ++ hnd)
    -> uniq (unh ++ (x :: act) ++ inact ++ hnd).
Proof. by intros; rewrite cat_cons -cat1s uniq_catCA cat1s -cat_cons. Qed.

Lemma sort_uniq_cons : forall d sd,
  uniq [seq (fst i) | i <- isort snd
    ((ord_max, ibeg d) :: [seq (widen_id (fst p), snd p)
                          | p <- unhandled sd])] =
  uniq [seq (fst i) | i <-
    ((ord_max, ibeg d) :: [seq (widen_id (fst p), snd p)
                          | p <- unhandled sd])].
Proof.
Admitted.

Lemma sort_has_mem_cons : forall d sd,
  has
    (mem
       [seq (fst i)
          | i <- isort snd
                   ((ord_max, ibeg d)
                    :: [seq (widen_id (fst p), snd p)
                       | p <- unhandled sd])]) =
  has
    (mem
       [seq (fst i)
          | i <- ((ord_max, ibeg d)
                    :: [seq (widen_id (fst p), snd p)
                       | p <- unhandled sd])]).
Proof.
Admitted.

Lemma uniq_unhandled_cons : forall d sd,
 uniq (ord_max :: [seq widen_id i | i <- all_state_lists sd])
   -> uniq
        ([seq fst i | i <- isort snd
            ((ord_max, ibeg d)
               :: [seq (widen_id (fst p), snd p) | p <- unhandled sd])] ++
         [seq widen_id i | i <- active sd] ++
         [seq widen_id i | i <- inactive sd] ++
         [seq widen_id i | i <- handled sd]).
Proof.
  rewrite /all_state_lists /unhandledIds.
  move=> d sd /= /andP [H1 H2].
  have H: [seq fst i | i <- [seq (widen_id (fst p), snd p) | p <- unhandled sd]]
      = [seq widen_id i | i <- [seq fst i | i <- unhandled sd]].
    by elim: (unhandled sd) => // a l IHl /=; f_equal.
  rewrite cat_uniq sort_uniq_cons sort_has_mem_cons
         -cat_uniq /= H -!map_cat.
  by apply/andP.
Qed.

Lemma unhandled_sorted_uncons : forall ni (x : (ordinal ni * nat)) unh,
 StronglySorted (fun m n : nat => m <= n) [seq snd i | i <- x :: unh]
   -> StronglySorted (fun m n : nat => m <= n) [seq snd i | i <- unh].
Proof. by move=> ni x unh; invert. Qed.

Lemma move_active_to_inactive : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ rem x (active sd) ++
              (x :: inactive sd) ++ handled sd).
Proof.
  intros.
  rewrite uniq_catC.
  rewrite <- catA.
  rewrite <- catA.
  apply uniq_juggle.
  rewrite catA.
  rewrite catA.
  rewrite uniq_catC.
  rewrite <- catA.
  assumption.
  apply H0.
Qed.

Lemma move_active_to_handled : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ rem x (active sd) ++
              inactive sd ++ x :: handled sd).
Proof.
  intros.
  rewrite uniq_catC.
  rewrite <- catA.
  rewrite <- catA.
  rewrite uniq_catCA2.
  rewrite <- catA.
  apply uniq_juggle.
  rewrite catA.
  rewrite uniq_catCA2.
  rewrite catA.
  rewrite uniq_catC.
  rewrite <- catA.
  rewrite catA.
  rewrite uniq_catCA2.
  rewrite <- catA.
  assumption.
  apply H0.
Qed.

Lemma move_inactive_to_active : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ x :: active sd ++
              rem x (inactive sd) ++ handled sd).
Proof.
  intros.
  rewrite -cat_cons.
  rewrite uniq_catC.
  rewrite <- catA.
  rewrite uniq_catC.
  rewrite -!catA.
  rewrite (catA (handled sd)).
  rewrite uniq_catCA2.
  apply uniq_juggle.
  rewrite !catA.
  rewrite uniq_catC.
  rewrite <- catA.
  rewrite uniq_catCA2.
  rewrite <- catA.
  rewrite catA.
  rewrite uniq_catCA2.
  rewrite <- catA.
  assumption.
  apply H0.
Qed.

Lemma move_inactive_to_handled : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ active sd ++
              rem x (inactive sd) ++ x :: handled sd).
Proof.
  intros.
  rewrite (catA (unhandledIds sd)).
  rewrite uniq_catC.
  rewrite -!catA.
  apply uniq_juggle.
  rewrite (catA (inactive sd)).
  rewrite uniq_catC.
  rewrite -!catA.
  assumption.
  apply H0.
Qed.

(** Given a vector of optional positions associated with register, return the
    first register (counting downwards) which is either [None], or the highest
    of [Some] value.

    The worst case scenario is that every register has [Some n] with the same
    n, in which case register 0 is selected. *)

Definition registerWithHighestPos
  : Vec (option nat) maxReg -> fin maxReg * option nat :=
  fold_left_with_index
    (fun reg (res : fin maxReg * option nat) x =>
       match (res, x) with
       | ((r, None), _) => (r, None)
       | (_, None) => (reg, None)
       | ((r, Some n), Some m) =>
         if n < m then (reg, Some m) else (r, Some n)
       end) (Ordinal registers_exist, Some 0).

(** Given a vector from registers to values, find the slot corresponding to
    the register assigned to [i] and replace it with [x]. *)

Definition atIntervalReg {sd : ScanStateDesc} (i : IntervalId sd)
  {a} (v : Vec a maxReg) (x : a) :=
  match V.nth (assignments sd) (to_vfin i) with
  | None => v
  | Some r => V.replace v (to_vfin r) x
  end.

(** ** ScanState *)

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

Inductive ScanState : ScanStateDesc -> Prop :=
  | ScanState_nil :
    ScanState
      {| nextInterval     := 0
       ; unhandled        := nil
       ; active           := nil
       ; inactive         := nil
       ; handled          := nil
       ; intervals        := V.nil _
       ; assignments      := V.nil _
       ; fixedIntervals   := V.const None _
       ; unhandled_sorted := SSorted_nil _
       ; lists_are_unique := uniq_nil _
       |}

  | ScanState_newUnhandled d sd :
    forall `(i : Interval d),
    ScanState sd ->
    ScanState
      {| nextInterval     := S (nextInterval sd)
       ; unhandled        :=
           isort snd ((ord_max, ibeg d)
             :: map (fun p => (widen_id (fst p), snd p)) (unhandled sd))
       ; active           := map (@widen_id sd) (active sd)
       ; inactive         := map (@widen_id sd) (inactive sd)
       ; handled          := map (@widen_id sd) (handled sd)
       ; intervals        := V.shiftin (d; i) (intervals sd)
       ; assignments      := V.shiftin None (assignments sd)
       ; fixedIntervals   := fixedIntervals sd
       ; unhandled_sorted := StronglySorted_isort_f _ _
       ; lists_are_unique := uniq_unhandled_cons d
                               (uniq_fin_cons (lists_are_unique sd))
       |}

  | ScanState_moveUnhandledToActive
      ni unh (* unhsort *) act inact hnd ints assgn fixints x reg unhs :
    forall lau : uniq ((fst x :: map (@fst _ _) unh) ++ act ++ inact ++ hnd),
    ScanState
      {| nextInterval     := ni
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; assignments      := assgn
       ; fixedIntervals   := fixints
       ; unhandled_sorted := unhs
       ; lists_are_unique := lau
       |} ->
    ScanState
      {| nextInterval     := ni
       ; unhandled        := unh
       ; active           := fst x :: act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       (* jww (2014-10-01): Prove: It was None before this call *)
       ; assignments      := V.replace assgn (to_vfin (fst x)) (Some reg)
       ; fixedIntervals   := fixints
       ; unhandled_sorted := unhandled_sorted_uncons unhs
       ; lists_are_unique := move_unhandled_to_active lau
       |}

  | ScanState_moveActiveToInactive sd x :
    ScanState sd -> forall (H : x \in active sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := x :: inactive sd
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique := move_active_to_inactive (lists_are_unique sd) H
       |}

  | ScanState_moveActiveToHandled sd x :
    ScanState sd -> forall (H : x \in active sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := inactive sd
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique := move_active_to_handled (lists_are_unique sd) H
       |}

  | ScanState_moveInactiveToActive sd x :
    ScanState sd -> forall (H : x \in inactive sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := x :: active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique := move_inactive_to_active (lists_are_unique sd) H
       |}

  | ScanState_moveInactiveToHandled sd x :
    ScanState sd -> forall (H : x \in inactive sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       ; unhandled_sorted := unhandled_sorted sd
       ; lists_are_unique :=
         move_inactive_to_handled (lists_are_unique sd) H
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

Definition ScanStateSig := { sd : ScanStateDesc | ScanState sd}.

Definition getScanStateDesc `(st : ScanState sd) := sd.

(** [ScanState_unhandledExtent] relates the [unhandledExtent] of a [ScanState]
    with the [intervalExtent] of the first member of its [unhandled] list. *)
Theorem ScanState_unhandledExtent `(st : ScanState sd) :
  let ue := unhandledExtent sd in
  match unhandled sd with
  | nil    => ue = 0
  | [:: i] => ue = intervalExtent (V.nth (intervals sd) (to_vfin (fst i))).2
  | i :: _ => ue > intervalExtent (V.nth (intervals sd) (to_vfin (fst i))).2
  end.
Proof.
  destruct sd.
  destruct unhandled0 eqn:Heqe;
  unfold unhandledExtent; simpl. reflexivity.
  destruct l eqn:Heqe2; simpl. reflexivity.
  apply fold_gt.
  destruct p0.
  pose (Interval_extent_nonzero (V.nth intervals0 (to_vfin i)).2).
  by rewrite add0n addnC ltn_plus.
Qed.

(** ** ScanStateCursor *)

(** A [ScannStateCursor] gives us a view of the first unhandled element within
    a [ScanState].  The cursor is only valid if such an unhandled element
    exists, so it combines that assertion with a view onto that element. *)

Record ScanStateCursor (sd : ScanStateDesc) : Prop := {
    curState  : ScanState sd;
    curExists : length (unhandled sd) > 0;

    curId         := safe_hd curExists;
    curIntDetails := V.nth (intervals sd) (to_vfin (fst curId))
}.

Arguments curState {sd} _.
Arguments curExists {sd} _.
Arguments curId {sd} _.
Arguments curIntDetails {sd} _.

Definition curStateDesc `(cur : ScanStateCursor sd) := sd.
Definition curIntDesc   `(cur : ScanStateCursor sd) := (curIntDetails cur).1.
Definition curInterval  `(cur : ScanStateCursor sd) := (curIntDetails cur).2.

Definition curPosition `(cur : ScanStateCursor sd) :=
  intervalStart (curInterval cur).

(** ** NextScanState *)

(** A [NextScanState] is a [ScanState] produced by mutating a prior
    [ScanState], while respecting the given predicate on the newly generated
    version.  This allows us to define well-founded recursion easily on the
    composition a series of [ScanState] mutations. *)

Record NextScanState (P : ScanStateDesc -> Prop) : Type := {
    nextDesc   : ScanStateDesc;
    nextState  : ScanState nextDesc;
    morphProof : P nextDesc
}.

Arguments Build_NextScanState [P] _ _ _.

Arguments nextDesc   [P] _.
Arguments nextState  [P] _.
Arguments morphProof [P] _.

Definition NextState `(cur : ScanStateCursor sd) P := NextScanState (P sd).

Definition NextStateDep  `(cur : ScanStateCursor sd) P Q :=
  { x : NextScanState (P sd) | Q x }.

Definition NextStateWith `(cur : ScanStateCursor sd) P A :=
  (A * NextScanState (P sd))%type.

Definition NSS_transport
  (P Q : ScanStateDesc -> ScanStateDesc -> Prop)
  {sd : ScanStateDesc} `(n : NextScanState (P sd'))
  (f : P sd' (nextDesc n) -> Q sd (nextDesc n)) : NextScanState (Q sd) :=
  {| nextDesc   := nextDesc n
   ; nextState  := nextState n
   ; morphProof := f (morphProof n)
   |}.

End MScanState.