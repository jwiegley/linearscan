Require Import Lib.

Require Export Machine.
Require Export Interval.
Require Export ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MLinearSpec (Mach : Machine).
Import Mach.
Module Import MS := MScanState Mach.

Import EqNotations.

Definition maxReg := maxReg.
Definition PhysReg := fin maxReg.
Definition registers_exist := registers_exist.

(** * Linear scan specification *)

(** This module contains Theorems which prove properties concerning the
    specification the linear register allocation algorithm, but which are not
    directly used in implementing the algorithm. *)

Lemma Forall_widen : forall n x (xs : list (fin n * nat)),
  List.Forall (lebf snd x) xs
    -> List.Forall (lebf snd (widen_id (fst x), snd x))
                   [seq (widen_id (fst p), snd p) | p <- xs].
Proof.
  move=> ? x xs.
  elim: xs x => //= [? ? IHys] ? H /=.
  constructor; first by inv H.
  by apply IHys; inv H.
Qed.

Lemma StronglySorted_widen : forall n (xs : list (fin n * nat)),
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
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". constructor.

  - Case "ScanState_newUnhandled".
    rewrite /unh.
    by apply/StronglySorted_insert_spec/StronglySorted_widen/IHst.

  - Case "ScanState_moveUnhandledToActive". inv IHst.
  - Case "ScanState_moveActiveToInactive". apply IHst.
  - Case "ScanState_moveActiveToHandled". apply IHst.
  - Case "ScanState_moveInactiveToActive". apply IHst.
  - Case "ScanState_moveInactiveToHandled".  apply IHst.

  - Case "ScanState_splitCurrentInterval".
    rewrite /unhandled /unh' in IHst *.
    apply StronglySorted_insert_spec.
    apply StronglySorted_inv in IHst.
    move: IHst => [H1 H2].
    apply: StronglySorted_widen.
    by constructor.
Qed.

Lemma uniq_rem : forall n x (xs : seq (fin n * PhysReg)),
  uniq [seq snd i | i <- xs] -> uniq [seq snd i | i <- rem x xs].
Proof.
  move=> n x.
  elim=> [|y ys IHys] Huniq //=.
  move: cons_uniq Huniq => -> /andP [H1 H2].
  case: (y == x); first by [].
  rewrite cons_uniq.
  apply/andP; split.
    admit.
  by apply IHys.
Qed.

Lemma in_snd_trans : forall (a b : eqType) (x : a * b) (xs ys : seq (a * b)),
  x \in xs -> ~~ has (mem [seq snd i | i <- xs]) [seq snd i | i <- ys]
    -> snd x \notin [seq snd i | i <- ys].
Admitted.

Theorem active_regs_are_unique `(st : ScanState sd) :
  uniq ([ seq snd i | i <- active sd ] ++ [ seq snd i | i <- inactive sd ]).
Proof.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". constructor.
  - Case "ScanState_newUnhandled".
    by rewrite /widen_fst -!map_comp /funcomp //.
  - Case "ScanState_moveUnhandledToActive".
    move: map_cat => /= <- in IHst *; apply/andP.
    admit.

  - Case "ScanState_moveActiveToInactive".
    move: IHst.
    rewrite /= !cat_uniq.
    move/and3P=> [H1 H2 H3].
    apply/and3P; split.
    + by apply/uniq_rem.
    + admit.
    + rewrite cons_uniq.
      apply/andP; split; last by [].
      by apply in_snd_trans with (xs := active sd).

  - Case "ScanState_moveActiveToHandled".
    move: IHst.
    rewrite /= !cat_uniq.
    move/and3P=> [H1 H2 H3].
    apply/and3P; split; last by [].
      by apply/uniq_rem.
    admit.

  - Case "ScanState_moveInactiveToActive".
    simpl in *.
    apply/andP; split.
      admit.
    admit.

  - Case "ScanState_moveInactiveToHandled".
    move: IHst.
    rewrite /= !cat_uniq.
    move/and3P=> [H1 H2 H3].
    apply/and3P; split; first by [].
      admit.
    by apply/uniq_rem.

  - Case "ScanState_splitCurrentInterval".
    by rewrite /widen_fst -!map_comp /funcomp //.
Qed.

(** The number of active or inactive registers cannot exceed the number of
    registers available (or, if there are more register than intervals to be
    allocated, the number of intervals). *)
Theorem limit_active_registers `(st : ScanState sd) :
  size (active sd ++ inactive sd) <= minn maxReg (nextInterval sd).
Admitted.

Lemma move_unhandled_to_active : forall n (x : fin n) unh act inact hnd,
  uniq ((x :: unh) ++ act ++ inact ++ hnd)
    -> uniq (unh ++ (x :: act) ++ inact ++ hnd).
Proof. by intros; rewrite cat_cons -cat1s uniq_catCA cat1s -cat_cons. Qed.

Lemma uniq_juggle : forall n (a : eqType) (xs ys : list (fin n * a)) zs,
  uniq ([seq fst i | i <- xs] ++ [seq fst i | i <- ys] ++ zs)
    -> forall x, x \in xs
    -> uniq ([seq fst i | i <- rem x xs] ++ [seq fst i | i <- x :: ys] ++ zs).
Proof.
  move=> n a.
  elim=> [|x xs IHxs] ys zs H x0 Hin //=.
  case E: (x == x0) => /=.
    move: E => /eqP <-.
    by rewrite -cat1s uniq_catCA cat1s -cat_cons.
  apply/andP.
  split.
    rewrite !mem_cat.
    move: cat_uniq H => -> /and3P => [[H1 H2 H3]].
    move: cons_uniq H1 => -> /andP => [[H4 H5]].
    rewrite negb_orb.
    apply/andP.
    apply negbT in E.
    split. admit. (* exact: not_in_rem. *)
    rewrite has_sym in H2.
    inversion H2 as [H2'].
    move: negb_orb H2' => -> /andP [H6 H7].
    rewrite in_cons negb_orb.
    apply/andP. split. admit. admit.
  apply IHxs.
    inversion H as [H'].
    by move: H' => /andP [_ ?].
  move: in_cons Hin => -> /orP [He|_] //.
  move: eq_sym E He => -> /eqP E /eqP He.
  contradiction.
Qed.

Lemma move_active_to_inactive : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- rem x (active sd)] ++
              [seq fst i | i <- x :: inactive sd] ++ handledIds sd).
Proof.
  intros.
  rewrite uniq_catC -catA -catA.
  apply uniq_juggle.
    by rewrite catA catA uniq_catC -catA.
  exact: H0.
Qed.

Lemma move_active_to_handled : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- rem x (active sd)] ++
              inactiveIds sd ++ [seq fst i | i <- x :: handled sd]).
Proof.
  intros.
  rewrite uniq_catC -catA -catA uniq_catCA2 -catA.
  apply uniq_juggle.
    by rewrite catA uniq_catCA2 catA uniq_catC -catA catA uniq_catCA2 -catA.
  exact: H0.
Qed.

Lemma move_inactive_to_active : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- x :: active sd] ++
              [seq fst i | i <- rem x (inactive sd)] ++ handledIds sd).
Proof.
  intros.
Admitted.
(*   rewrite -cat_cons uniq_catC -catA uniq_catC -!catA *)
(*           (catA (handled sd)) uniq_catCA2. *)
(*   apply uniq_juggle. *)
(*     by rewrite !catA uniq_catC -catA uniq_catCA2 -catA catA uniq_catCA2 -catA. *)
(*   exact: H0. *)
(* Qed. *)

Lemma move_inactive_to_handled : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ activeIds sd
               ++ [seq fst i | i <- rem x (inactive sd)]
               ++ [seq fst i | i <- x :: handled sd]).
Proof.
  intros.
  rewrite (catA (unhandledIds sd)) uniq_catC -!catA.
  apply uniq_juggle.
    admit.
    (* by rewrite (catA (inactive sd)) uniq_catC -!catA. *)
  exact: H0.
Qed.

Lemma notin_fst : forall n P x y (xs : seq (fin n * nat)),
  fst x != fst y
    -> @fst _ nat y \notin [seq fst i | i <- xs]
    -> fst y \notin [seq fst i | i <- insert (P ^~ x) x xs].
Proof.
  move=> n P x y.
  elim=> /= [|z zs IHzs] Heqe H.
    by rewrite mem_seq1 eq_sym.
  move: H.
  rewrite in_cons negb_orb => /andP [H1 H2].
  rewrite /insert.
  case E: (P z x).
    rewrite map_cons in_cons negb_orb.
    apply/andP; split. by [].
    exact: IHzs.
  rewrite map_cons in_cons negb_orb.
  apply/andP; split.
    by rewrite eq_sym.
  rewrite map_cons in_cons negb_orb.
  by apply/andP.
Qed.

Lemma uniq_insert_cons :
  forall n P (f : fin n -> fin (S n)) x (xs : seq (fin n * nat)),
  uniq [seq fst i | i <- x :: xs]
    -> uniq [seq fst i | i <- insert (P ^~ x) x xs].
Proof.
  move=> n P f x.
  elim=> //= y ys IHys /and3P [H1 ? ?].
  move: H1.
  rewrite in_cons negb_orb => /andP [? ?].
  rewrite /insert.
  case E: (P y x).
    rewrite map_cons cons_uniq.
    apply/andP; split.
      exact: notin_fst.
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
  exact: IHxs.
Qed.

Lemma uniq_trans_fst :
  forall n (f : fin n -> fin (S n)) (xs : seq (fin n * nat)),
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
    exact: map_f_notin.
  exact: IHxs.
Qed.

Lemma no_ord_max : forall n (xs : seq (fin n * nat)),
   ord_max \notin [ seq fst i | i <- [seq widen_fst p | p <- xs] ].
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
Defined.

Lemma not_in_widen : forall n (xs : seq (fin n * nat)) z,
  let f := widen_ord (leqnSn n) in
  z \notin [seq fst i | i <- xs]
    -> f z \notin [seq fst i | i <- [seq (f (fst p), snd p) | p <- xs]].
Proof.
  move=> n.
  elim=> //= x xs IHxs z Hni.
  move: Hni.
  rewrite in_cons negb_orb => /andP [H1 H2].
  rewrite in_cons negb_orb.
  apply/andP; split. by [].
  exact: IHxs.
Qed.

Lemma not_mem_insert_cons :
  forall n (x : fin n.+1 * nat) (xs : seq (fin n * nat)) z,
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
  rewrite /insert.
  case E: (lebf snd (widen_ord (leqnSn n) (fst y), snd y) x).
    rewrite map_cons in_cons negb_orb.
    apply/andP; split. by [].
    exact: IHys.
  rewrite map_cons in_cons negb_orb.
  apply/andP; split.
    by rewrite eq_sym.
  rewrite map_cons in_cons negb_orb.
  apply/andP; split. by [].
  exact: not_in_widen.
Qed.

Lemma uniq_1st_of_four (T : eqType) (xs1 xs2 : seq T) : forall (ys : seq T),
  uniq xs1 == uniq xs2 -> uniq (xs1 ++ ys) == uniq (xs2 ++ ys).
Admitted.

Lemma unhandled_insert_uniq : forall n beg xs ys,
  let wf := @widen_fst n _ in
  let x  := (ord_max, beg) in
  uniq ([seq fst i | i <- xs] ++ ys)
    -> uniq ([seq fst i | i <- insert (lebf snd ^~ x) x (map wf xs)] ++
             map widen_id ys).
Proof.
  move=> n beg xs ys wf x IHst.
Admitted.
(*   rewrite -!map_cat cat_uniq => /=. *)
(*   move: IHst. *)
(*   rewrite cat_uniq => /and3P [H2 H3 H4]. *)
(*   apply/and3P; split. *)
(*   + apply uniq_insert_cons. *)
(*       exact: widen_ord. *)
(*     rewrite map_cons /=. *)
(*     apply/andP; split. *)
(*       exact: no_ord_max. *)
(*     apply uniq_trans_fst. *)
(*       exact: widen_ord_inj. *)
(*     by []. *)
(*   + move: H3 => /hasPn H3. *)
(*     apply/hasPn. move=> ? Hin. *)
(*     apply in_map_inj in Hin. *)
(*     set f := widen_ord (leqnSn n). *)
(*     case: Hin => y -> Hin. *)
(*     have Hne: fst x != f y. *)
(*       by apply lift_bounded. *)
(*     by apply/not_mem_insert_cons/(H3 y Hin). *)
(*   + rewrite map_inj_uniq. by []. *)
(*     exact: widen_ord_inj. *)
(* Qed. *)

Theorem lists_are_unique `(st : ScanState sd) : uniq (all_state_lists sd).
Proof.
  rewrite /all_state_lists /unhandledIds /IntervalId.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". by [].
  - Case "ScanState_newUnhandled".
    rewrite /unhandledIds /activeIds /inactiveIds /handledIds. simpl.
    move: cat_uniq IHst => -> /and3P [H1 H2 H3].
    rewrite cat_uniq.
    apply/and3P; split.
    + admit.
    + admit.
    + admit.
  - Case "ScanState_moveUnhandledToActive".
    exact: move_unhandled_to_active.
  - Case "ScanState_moveActiveToInactive".
    exact: (@move_active_to_inactive _ x IHst H).
  - Case "ScanState_moveActiveToHandled".
    exact: (@move_active_to_handled _ x IHst H).
  - Case "ScanState_moveInactiveToActive".
    exact: (@move_inactive_to_active _ x IHst H).
  - Case "ScanState_moveInactiveToHandled".
    exact: (@move_inactive_to_handled _ x IHst H).
  - Case "ScanState_splitCurrentInterval".
    (* exact: unhandled_insert_uniq. *)
    admit.
Qed.

Theorem all_intervals_represented `(st : ScanState sd) :
  size (all_state_lists sd) == nextInterval sd.
Proof.
  rewrite /all_state_lists /unhandledIds /IntervalId /nextInterval.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". by [].

  - Case "ScanState_newUnhandled".
    rewrite !size_cat !size_map ?size_insert /=.
    by move: IHst; rewrite !size_cat !size_map /=.

  - Case "ScanState_moveUnhandledToActive".
    rewrite !size_cat size_map /=.
    by move: IHst; rewrite !size_cat size_map /= addnS.

  - Case "ScanState_moveActiveToInactive".
    admit.
    (* rewrite !size_cat size_map size_rem /=; last by []. *)
    (* move: IHst; rewrite !size_cat size_map /=. *)
    (* case E: (active sd). by rewrite E in H; inv H. *)
    (* by rewrite [_.-1 + _]addnC addSn -[_ + _.-1]addnC -addSn /=. *)

  - Case "ScanState_moveActiveToHandled".
    admit.
    (* rewrite !size_cat size_map size_rem /=; last by []. *)
    (* move: IHst; rewrite !size_cat size_map. *)
    (* case E: (active sd). by rewrite E in H; inv H. *)
    (* by rewrite 2!addnS -addSn /=. *)

  - Case "ScanState_moveInactiveToActive".
    admit.
    (* rewrite -cat_cons !size_cat size_map size_rem /=; last by []. *)
    (* move: IHst; rewrite !size_cat size_map /=. *)
    (* case E: (inactive sd). rewrite E in H. inv H. *)
    (* by rewrite 2!addnS -addSn /=. *)

  - Case "ScanState_moveInactiveToHandled".
    admit.
    (* rewrite !size_cat size_map size_rem /=; last by []. *)
    (* move: IHst; rewrite !size_cat size_map /=. *)
    (* case E: (inactive sd). rewrite E in H. inv H. *)
    (* by rewrite 2!addnS -addSn /=. *)

  - Case "ScanState_splitCurrentInterval".
    rewrite /unhandled /active /inactive /handled in IHst *.
    rewrite !size_cat !size_map size_insert /=.
    by move: IHst; rewrite !size_cat !size_map /=.
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

End MLinearSpec.