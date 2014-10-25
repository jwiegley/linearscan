Require Import Lib.

Require Export Machine.
Require Export Interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MScanState (Mach : Machine).
Import Mach.

Import EqNotations.

Definition maxReg := maxReg.
Definition PhysReg := fin maxReg.
Definition registers_exist := registers_exist.

(** ** ScanStateDesc *)

(** A [ScanStateDesc] is always relative to a current position as we move
    through the sequentialized instruction stream over which registers are
    allocated. *)

Record ScanStateDesc : Type := {
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

    all_state_lists := unhandledIds ++ active ++ inactive ++ handled
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
       |}

  | ScanState_newUnhandled sd :
    ScanState sd -> forall `(i : Interval d),
    let n   := (ord_max, ibeg d) in
    let unh := map (fun p => (widen_id (fst p), snd p)) (unhandled sd) in
    ScanState
      {| nextInterval     := S (nextInterval sd)
       ; unhandled        := insert (fun m => lebf snd m n) n unh
       ; active           := map (@widen_id sd) (active sd)
       ; inactive         := map (@widen_id sd) (inactive sd)
       ; handled          := map (@widen_id sd) (handled sd)
       ; intervals        := V.shiftin (d; i) (intervals sd)
       ; assignments      := V.shiftin None (assignments sd)
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveUnhandledToActive
      ni unh act inact hnd ints assgn fixints x reg :
    ScanState
      {| nextInterval     := ni
       ; unhandled        := x :: unh
       ; active           := act
       ; inactive         := inact
       ; handled          := hnd
       ; intervals        := ints
       ; assignments      := assgn
       ; fixedIntervals   := fixints
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
       |}

  | ScanState_moveActiveToInactive sd :
    ScanState sd -> forall `(H : x \in active sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := x :: inactive sd
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveActiveToHandled sd :
    ScanState sd -> forall `(H : x \in active sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := rem x (active sd)
       ; inactive         := inactive sd
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveInactiveToActive sd :
    ScanState sd -> forall `(H : x \in inactive sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := x :: active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
       |}

  | ScanState_moveInactiveToHandled sd :
    ScanState sd -> forall `(H : x \in inactive sd),
    ScanState
      {| nextInterval     := nextInterval sd
       ; unhandled        := unhandled sd
       ; active           := active sd
       ; inactive         := rem x (inactive sd)
       ; handled          := x :: handled sd
       ; intervals        := intervals sd
       ; assignments      := assignments sd
       ; fixedIntervals   := fixedIntervals sd
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

Definition ScanStateSig := { sd : ScanStateDesc | ScanState sd }.

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

Lemma Forall_widen : forall sd x (xs : list (IntervalId sd * nat)),
  List.Forall (lebf snd x) xs
    -> List.Forall (lebf snd (widen_id (fst x), snd x))
                   [seq (widen_id (fst p), snd p) | p <- xs].
Proof.
  move=> ? x xs.
  elim: xs x => //= [? ? IHys] ? H /=.
  constructor; first by inv H.
  by apply IHys; inv H.
Qed.

Lemma StronglySorted_widen : forall sd (xs : list (IntervalId sd * nat)),
  StronglySorted (lebf snd) xs
    -> StronglySorted (lebf snd) [seq (widen_id (fst p), snd p) | p <- xs].
Proof.
  move=> ?.
  elim=> /= [|? ? ?] H; first by constructor.
  constructor; first by inv H.
  by apply Forall_widen; inv H.
Qed.

Theorem unhandled_sorted `(st : ScanState sd) :
  StronglySorted (lebf snd) (unhandled sd).
Proof.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". constructor.
  - Case "ScanState_newUnhandled".
    rewrite /unh.
    by apply/StronglySorted_insert_spec/StronglySorted_widen/IHst.
  - Case "ScanState_moveUnhandledToActive". inv IHst.
  - Case "ScanState_moveActiveToInactive". apply IHst.
  - Case "ScanState_moveActiveToHandled". apply IHst.
  - Case "ScanState_moveInactiveToActive". apply IHst.
  - Case "ScanState_moveInactiveToHandled".  apply IHst.
Qed.

Lemma move_unhandled_to_active : forall n (x : fin n) unh act inact hnd,
  uniq ((x :: unh) ++ act ++ inact ++ hnd)
    -> uniq (unh ++ (x :: act) ++ inact ++ hnd).
Proof. by intros; rewrite cat_cons -cat1s uniq_catCA cat1s -cat_cons. Qed.

Lemma move_active_to_inactive : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ rem x (active sd) ++
              (x :: inactive sd) ++ handled sd).
Proof.
  intros.
  rewrite uniq_catC -catA -catA.
  apply uniq_juggle.
    by rewrite catA catA uniq_catC -catA.
  by apply H0.
Qed.

Lemma move_active_to_handled : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ rem x (active sd) ++
              inactive sd ++ x :: handled sd).
Proof.
  intros.
  rewrite uniq_catC -catA -catA uniq_catCA2 -catA.
  apply uniq_juggle.
    by rewrite catA uniq_catCA2 catA uniq_catC -catA catA uniq_catCA2 -catA.
  by apply H0.
Qed.

Lemma move_inactive_to_active : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ x :: active sd ++
              rem x (inactive sd) ++ handled sd).
Proof.
  intros.
  rewrite -cat_cons uniq_catC -catA uniq_catC -!catA
          (catA (handled sd)) uniq_catCA2.
  apply uniq_juggle.
    by rewrite !catA uniq_catC -catA uniq_catCA2 -catA catA uniq_catCA2 -catA.
  by apply H0.
Qed.

Lemma move_inactive_to_handled : forall sd x,
  uniq (unhandledIds sd ++ active sd ++ inactive sd ++ handled sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ active sd ++
              rem x (inactive sd) ++ x :: handled sd).
Proof.
  intros.
  rewrite (catA (unhandledIds sd)) uniq_catC -!catA.
  apply uniq_juggle.
    by rewrite (catA (inactive sd)) uniq_catC -!catA.
  by apply H0.
Qed.

Lemma notin_fst
  : forall n P x y (xs : seq (fin n * nat)),
  fst x != fst y
    -> @fst _ nat y \notin [seq fst i | i <- xs]
    -> fst y \notin [seq fst i | i <- insert (P^~ x) x xs].
Proof.
  move=> n P x y.
  elim=> /= [|z zs IHzs] Heqe H.
    by rewrite mem_seq1 eq_sym.
  move: H.
  rewrite in_cons negb_orb => /andP [H1 H2].
  case E: (P z x).
    rewrite map_cons in_cons negb_orb.
    apply/andP; split. by [].
    by apply IHzs.
  rewrite map_cons in_cons negb_orb.
  apply/andP; split.
    by rewrite eq_sym.
  rewrite map_cons in_cons negb_orb.
  by apply/andP.
Qed.

Lemma uniq_insert_cons
  : forall n P (f : fin n -> fin (S n)) x (xs : seq (fin n * nat)),
  uniq [seq fst i | i <- x :: xs]
    -> uniq [seq fst i | i <- insert (P ^~ x) x xs].
Proof.
  move=> n P f x.
  elim=> //= y ys IHys /and3P [H1 ? ?].
  move: H1.
  rewrite in_cons negb_orb => /andP [? ?].
  case E: (P y x).
    rewrite map_cons cons_uniq.
    apply/andP; split.
      by apply notin_fst.
    by apply/IHys/andP.
  rewrite !map_cons !cons_uniq.
  rewrite in_cons negb_orb.
  apply/and3P; split; auto.
  by apply/andP.
Qed.

Lemma map_f_notin :
  forall (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) (x : T1),
  injective f -> x \notin s -> f x \notin [seq f i | i <- s].
Proof.
  move=> T1 T2 f.
  elim=> // x xs IHxs x0 Hinj.
  rewrite in_cons negb_orb => /andP [H1 H2].
  rewrite map_cons in_cons negb_orb.
  apply/andP; split.
    by rewrite inj_eq.
  by apply IHxs.
Qed.

Lemma uniq_trans_fst
  : forall n (f : fin n -> fin (S n)) (xs : seq (fin n * nat)),
  injective f
    -> uniq [seq fst i | i <- xs]
    -> uniq [seq fst i | i <- [seq (fun p => (f (fst p), snd p)) p | p <- xs]].
Proof.
  move=> n f.
  elim=> // x xs IHxs Hinj.
  rewrite map_cons cons_uniq => /andP [H1 H2].
  rewrite -map_comp map_cons map_comp /=.
  apply/andP; split.
    rewrite -map_comp.
    replace ([eta fst] \o (fun p : fin n * nat => (f (fst p), snd p)))
       with (f \o @fst _ nat); last by [].
    rewrite map_comp.
    by apply map_f_notin.
  by apply IHxs.
Qed.

Lemma no_ord_max : forall n (xs : seq (fin n * nat)),
   ord_max
     \notin [ seq fst i
            | i <- [seq (widen_ord (leqnSn n) (fst p), snd p) | p <- xs] ].
Proof.
  move=> n.
  elim=> // x xs IHxs.
  rewrite -map_comp map_cons in_cons negb_orb /=.
  apply/andP; split.
    apply lift_bounded.
  rewrite map_comp.
  apply IHxs.
Qed.

Lemma in_map_inj : forall n x xs,
  let f := widen_ord (leqnSn n) in
  x \in [seq f i | i <- xs] -> { y | x = f y & y \in xs }.
Proof.
  move=> n x xs.
  elim E: xs => //= [y ys IHys] Hin.
  case X: (x == widen_ord (leqnSn n) y).
    exists y. by apply/eqP/X.
    rewrite in_cons.
    by apply/orP; left.
  move: map_cons in_cons X Hin => -> -> ->.
  rewrite orb_false_l => Hin.
  specialize (IHys Hin).
  case: IHys => z Heqe2 Hin2.
  exists z. by [].
  case Y: (y == z).
    rewrite in_cons eq_sym.
    by apply/orP; left.
  rewrite in_cons.
  by apply/orP; right.
Qed.

Lemma not_in_widen : forall n (xs : seq (fin n * nat)) z,
  let f := widen_ord (leqnSn n) in
  z \notin [seq fst i | i <- xs]
    -> f z
         \notin [seq fst i | i <- [seq (f (fst p), snd p) | p <- xs]].
Proof.
  move=> n.
  elim=> //= x xs IHxs z Hni.
  move: Hni.
  rewrite in_cons negb_orb => /andP [H1 H2].
  rewrite in_cons negb_orb.
  apply/andP; split. by [].
  by apply IHxs.
Qed.

Lemma not_mem_insert_cons
  : forall n (x : fin n.+1 * nat) (xs : seq (fin n * nat)) z,
  let f := widen_ord (leqnSn n) in
  let xs' : seq (fin n.+1 * nat) := [seq (f (fst p), snd p) | p <- xs] in
  fst x != f z
    -> ~~ (mem [seq fst i | i <- xs]) z
    -> ~~ (mem [seq fst i | i <- insert ((lebf snd)^~ x) x
                  [seq (f (fst p), snd p) | p <- xs]]) (f z).
Proof.
  move=> n x.
  elim=> //= [|y ys IHys] z Hne Hmem.
    by rewrite mem_seq1 eq_sym.
  move: Hmem. rewrite in_cons negb_orb => /andP [? ?].
  case E: (lebf snd (widen_ord (leqnSn n) (fst y), snd y) x).
    rewrite map_cons in_cons negb_orb.
    apply/andP; split. by [].
    by apply IHys.
  rewrite map_cons in_cons negb_orb.
  apply/andP; split.
    by rewrite eq_sym.
  rewrite map_cons in_cons negb_orb.
  apply/andP; split. by [].
  by apply not_in_widen.
Qed.

Lemma unhandled_insert_uniq : forall sd d,
  let n   := (ord_max, ibeg d) in
  let unh := map (fun p => (widen_id (fst p), snd p)) (unhandled sd) in
  let xs  := insert (fun m => lebf snd m n) n unh in
  uniq (all_state_lists sd)
    -> uniq ([seq (fst i) | i <- xs] ++
             [seq widen_id i | i <- active sd] ++
             [seq widen_id i | i <- inactive sd] ++
             [seq widen_id i | i <- handled sd]).
Proof.
  move=> sd d n unh xs IHst.
  rewrite /all_state_lists /unhandledIds /IntervalId.
  rewrite -!map_cat cat_uniq => /=.
  move: IHst.
  rewrite cat_uniq => /and3P [H2 H3 H4].
  apply/and3P; split.
  + apply uniq_insert_cons.
      by apply widen_ord.
    rewrite map_cons /=.
    apply/andP; split.
      by apply no_ord_max.
    apply uniq_trans_fst.
      by apply widen_ord_inj.
    by assumption.
  + move: H3 => /hasPn H3.
    apply/hasPn. move=> x Hin.
    apply in_map_inj in Hin.
    set f := widen_ord (leqnSn (nextInterval sd)).
    case: Hin => y -> Hin.
    have Hne: fst n != f y.
      rewrite /n /f /=.
      apply lift_bounded.
    by apply/not_mem_insert_cons/(H3 y Hin).
  + rewrite map_inj_uniq. by [].
    by apply widen_ord_inj.
Qed.

Theorem lists_are_unique `(st : ScanState sd) : uniq (all_state_lists sd).
Proof.
  rewrite /all_state_lists /unhandledIds /IntervalId.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". by [].
  - Case "ScanState_newUnhandled".
    by apply unhandled_insert_uniq.
  - Case "ScanState_moveUnhandledToActive".
    by apply move_unhandled_to_active.
  - Case "ScanState_moveActiveToInactive".
    by apply (@move_active_to_inactive _ x IHst H).
  - Case "ScanState_moveActiveToHandled".
    by apply (@move_active_to_handled _ x IHst H).
  - Case "ScanState_moveInactiveToActive".
    by apply (@move_inactive_to_active _ x IHst H).
  - Case "ScanState_moveInactiveToHandled".
    by apply (@move_inactive_to_handled _ x IHst H).
Qed.

Lemma size_insert : forall (a : eqType) P (x : a) xs,
  size (insert (P ^~ x) x xs) = (size xs).+1.
Proof.
  move=> a P x.
  elim=> //= [y ys IHys].
  case E: (P y x) => /=. by rewrite IHys.
  by [].
Qed.

Theorem all_intervals_represented `(st : ScanState sd) :
  size (all_state_lists sd) == nextInterval sd.
Proof.
  rewrite /all_state_lists /unhandledIds /IntervalId /nextInterval.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". by [].

  - Case "ScanState_newUnhandled".
    rewrite !size_cat !size_map size_insert /=.
    by move: IHst; rewrite !size_cat !size_map /=.

  - Case "ScanState_moveUnhandledToActive".
    rewrite !size_cat size_map /=.
    by move: IHst; rewrite !size_cat size_map /= addnS.

  - Case "ScanState_moveActiveToInactive".
    rewrite !size_cat size_map size_rem /=; last by [].
    move: IHst; rewrite !size_cat size_map /=.
    case E: (active sd). by rewrite E in H; inv H.
    by rewrite [_.-1 + _]addnC addSn -[_ + _.-1]addnC -addSn /=.

  - Case "ScanState_moveActiveToHandled".
    rewrite !size_cat size_map size_rem /=; last by [].
    move: IHst; rewrite !size_cat size_map.
    case E: (active sd). by rewrite E in H; inv H.
    by rewrite 2!addnS -addSn /=.

  - Case "ScanState_moveInactiveToActive".
    rewrite -cat_cons !size_cat size_map size_rem /=; last by [].
    move: IHst; rewrite !size_cat size_map /=.
    case E: (inactive sd). rewrite E in H. inv H.
    by rewrite 2!addnS -addSn /=.

  - Case "ScanState_moveInactiveToHandled".
    rewrite !size_cat size_map size_rem /=; last by [].
    move: IHst; rewrite !size_cat size_map /=.
    case E: (inactive sd). rewrite E in H. inv H.
    by rewrite 2!addnS -addSn /=.
Qed.

(* jww (2014-10-25): Proving this will require that the constructor accepts a
   proof that there is romo in the active pool, and then in tryAllocateFreeReg
   is when we split based on whether that list is full or not (for this is
   what causes allocation there to fail).  With the knowledge of that split,
   we would then know that there is either room, or no room (but after
   spilling there should then be room again).

   But rather than taking the size of the active list to determine this, we
   would have another lemma stating that if the algorithm that determines
   freeUntilPos fails to find a free register, this implies that size (active
   sd) == maxReg. *)
(*
Theorem actives_within_range `(st : ScanState sd) :
  size (active sd) <= maxReg.
Proof.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". by [].
  - Case "ScanState_newUnhandled".
    by rewrite size_map.
  - Case "ScanState_moveUnhandledToActive". (* TODO *)
  - Case "ScanState_moveActiveToInactive".
    rewrite size_rem; last by [].
    case E: (active sd) => //=.
    by rewrite E /= in IHst; apply ltnW.
  - Case "ScanState_moveActiveToHandled".
    rewrite size_rem; last by [].
    case E: (active sd) => //=.
    by rewrite E /= in IHst; apply ltnW.
  - Case "ScanState_moveInactiveToActive". (* TODO *)
  - Case "ScanState_moveInactiveToHandled".
    by [].
Qed.
*)

Theorem uniq_unhandledExtent_cons
  : forall ni i (unh : list (fin ni * nat)) ints assgn assgn' fixints
      (act act' inact inact' hnd hnd' : list (fin ni)),
  unhandledExtent
    {| nextInterval     := ni
     ; unhandled        := unh
     ; active           := act
     ; inactive         := inact
     ; handled          := hnd
     ; intervals        := ints
     ; assignments      := assgn
     ; fixedIntervals   := fixints
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

End MScanState.