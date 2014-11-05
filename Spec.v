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
    apply: StronglySorted_insert_spec.
    apply StronglySorted_inv in IHst.
    move: IHst => [H1 H2].
    apply: StronglySorted_widen.
    by constructor.
Qed.

Theorem allocated_regs_are_unique `(st : ScanState sd) :
  uniq ([ seq snd i | i <- active sd ++ inactive sd ]).
Proof.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". constructor.
  - Case "ScanState_newUnhandled".
    by rewrite /widen_fst -!map_cat -!map_comp /funcomp //.

  - Case "ScanState_moveUnhandledToActive".
    move=> /= in IHst *; apply/andP; split=> //.

    (* jww (2014-10-31): Need the following evidence here:
         reg \notin [seq snd i | i <- act ++ inact]

       This will need to come from the [ScanState_moveUnhandledToActive]
       constructor, but doing so will require obtaining it from the algorithm,
       which will be a more substantial change. *)
    admit.

  - Case "ScanState_moveActiveToInactive".
    move: IHst; set s2 := (X in uniq X) => IHst.
    rewrite (@perm_eq_uniq _ _ s2) => //.
    apply/perm_map.
    rewrite perm_rem_cons; last by [].
    exact: perm_eq_refl.

  - Case "ScanState_moveActiveToHandled".
    move: IHst; set s2 := (X in uniq X) => IHst.
    apply/(@subseq_uniq _ _ s2); last exact: IHst.
    apply/map_subseq/cat_subseq;
      first exact: rem_subseq.
    exact: subseq_refl.

  - Case "ScanState_moveInactiveToActive".
    rewrite /= -cons_uniq -map_cons.
    move: IHst; set s2 := (X in uniq X) => IHst.
    rewrite (@perm_eq_uniq _ _ s2); first exact: IHst.
    apply/perm_map.
    rewrite -cat_cons perm_catC perm_rem_cons // perm_catC.
    exact: perm_eq_refl.

  - Case "ScanState_moveInactiveToHandled".
    move: IHst; set s2 := (X in uniq X) => IHst.
    apply/(@subseq_uniq _ _ s2); last exact: IHst.
    apply/map_subseq/cat_subseq;
      first exact: subseq_refl.
    exact: rem_subseq.

  - Case "ScanState_splitCurrentInterval".
    by rewrite /widen_fst -!map_cat -!map_comp /funcomp //.
Qed.

(** The number of active or inactive registers cannot exceed the number of
    registers available (or, if there are more register than intervals to be
    allocated, the number of intervals). *)
Theorem limit_active_registers `(st : ScanState sd) :
  size (active sd ++ inactive sd) <= minn maxReg (nextInterval sd).
(* jww (2014-10-31): Implementing this will need supporting evidence from the
   algorithm; I don't think the constructors give us enough detail to
   determine here by induction. *)
Admitted.

Tactic Notation "uniq_reorg" ident(s2) ident(sd) ident(Huniq) tactic(H) :=
  set s2 := unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd;
  rewrite (@perm_eq_uniq _ _ s2); first exact: Huniq; H;
  by apply/perm_map; rewrite perm_rem_cons;
    first do [ exact: perm_eq_refl
             | by rewrite perm_catC; exact: perm_eq_refl ].

Lemma move_active_to_inactive : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- rem x (active sd)] ++
              [seq fst i | i <- x :: inactive sd] ++ handledIds sd).
Proof.
  move=> sd x Huniq Hin.
  uniq_reorg s2 sd Huniq (rewrite perm_cat2l !catA perm_cat2r -!map_cat).
Qed.

Lemma move_active_to_handled : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- rem x (active sd)] ++
              inactiveIds sd ++ [seq fst i | i <- x :: handled sd]).
Proof.
  move=> sd x Huniq Hin.
  uniq_reorg s2 sd Huniq
    (rewrite perm_cat2l perm_catCA perm_eq_sym perm_catCA
             perm_cat2l -!map_cat perm_eq_sym).
Qed.

Lemma move_inactive_to_active : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- x :: active sd] ++
              [seq fst i | i <- rem x (inactive sd)] ++ handledIds sd).
Proof.
  move=> sd x Huniq Hin.
  uniq_reorg s2 sd Huniq
    (rewrite perm_cat2l !catA perm_cat2r perm_catC -!map_cat).
Qed.

Lemma move_inactive_to_handled : forall sd x,
  uniq (unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ activeIds sd
               ++ [seq fst i | i <- rem x (inactive sd)]
               ++ [seq fst i | i <- x :: handled sd]).
Proof.
  move=> sd x Huniq Hin.
  uniq_reorg s2 sd Huniq (rewrite 2!perm_cat2l -!map_cat).
Qed.

Lemma no_ord_max : forall n (xs : seq (fin n)),
  ord_max \notin [ seq widen_id i | i <- xs ].
Proof.
  move=> n; elim=> // [x xs IHxs] /=.
  rewrite in_cons /=.
  apply/norP; split; last assumption.
  exact: lift_bounded.
Qed.

Lemma map_widen_fst : forall (a : eqType) n (xs : seq (fin n * a)),
  [seq fst i | i <- [seq (@widen_fst n a) i | i <- xs]] =
  [seq (@widen_id n) i | i <- [seq fst i | i <- xs]].
Proof. move=> a n xs. by rewrite -!map_comp. Qed.

Theorem lists_are_unique `(st : ScanState sd) : uniq (all_state_lists sd).
Proof.
  rewrite /all_state_lists
          /unhandledIds /activeIds /inactiveIds /handledIds /=.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". by [].

  - Case "ScanState_newUnhandled".
    move: IHst; rewrite -!map_cat => IHst /=.
    set s2 := [seq fst i | i <- n :: unh] ++
              [seq fst i
              | i <- [seq widen_fst i
                     | i <- active sd ++ inactive sd ++ handled sd]].
    rewrite (@perm_eq_uniq _ _ s2) /s2 /unh /n.
      rewrite map_cons !map_widen_fst /=.
      apply/andP; split.
        rewrite mem_cat.
        apply/norP; split; exact: no_ord_max.
      rewrite -map_cat map_inj_uniq; first exact: IHst.
      exact: widen_ord_inj.
    rewrite perm_cat2r.
    apply/perm_map.
    by rewrite insert_perm.

  - Case "ScanState_moveUnhandledToActive".
    move: IHst; rewrite /= -cons_uniq -!map_cat => IHst.
    set s2 := fst x :: [seq fst i | i <- unh] ++
              [seq fst i | i <- act ++ inact ++ hnd].
    rewrite (@perm_eq_uniq _ _ s2); first exact: IHst.
    by rewrite -perm_cat_cons.

  - Case "ScanState_moveActiveToInactive".
    exact: (@move_active_to_inactive _ x IHst H).
  - Case "ScanState_moveActiveToHandled".
    exact: (@move_active_to_handled _ x IHst H).
  - Case "ScanState_moveInactiveToActive".
    exact: (@move_inactive_to_active _ x IHst H).
  - Case "ScanState_moveInactiveToHandled".
    exact: (@move_inactive_to_handled _ x IHst H).

  - Case "ScanState_splitCurrentInterval".
    move: IHst; rewrite/= -cons_uniq -!map_cat => /= /andP [Hin IHst].
    set s2 := [seq fst i | i <- x2 :: unh'] ++
              [seq fst i | i <- [seq widen_fst i
                                | i <- act ++ inact ++ hnd]].
    rewrite (@perm_eq_uniq _ _ s2) /s2 /unh' /x /x2.
      rewrite map_cons !map_widen_fst /=.
      apply/andP; split.
        rewrite in_cons.
        apply/norP; split.
          exact: lift_bounded.
        rewrite mem_cat.
        apply/norP; split; exact: no_ord_max.
      apply/andP; split.
        rewrite mem_cat.
        apply/norP; split.
          apply map_f_notin; first exact: widen_ord_inj.
          by move/not_in_app in Hin.
        apply map_f_notin; first exact: widen_ord_inj.
        move: Hin.
        rewrite mem_cat.
        by move/norP => [_ Hin].
      rewrite -map_cat map_inj_uniq; first exact: IHst.
      exact: widen_ord_inj.
    rewrite perm_cat2r.
    apply/perm_map.
    by rewrite insert_perm.
Qed.

Lemma has_size : forall (a : eqType) x (xs : seq a), x \in xs -> 0 < size xs.
Proof. move=> a x; elim=> //. Qed.

Theorem all_intervals_represented `(st : ScanState sd) :
  size (all_state_lists sd) == nextInterval sd.
Proof.
  rewrite /all_state_lists
          /unhandledIds /activeIds /inactiveIds /handledIds /=
          !size_cat !size_map.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". by [].

  - Case "ScanState_newUnhandled".
    by rewrite /unh size_insert !size_map addSn.

  - Case "ScanState_moveUnhandledToActive".
    by rewrite addnA addnS -addSn -addnA.

  - Case "ScanState_moveActiveToInactive".
    rewrite size_rem; last assumption.
    rewrite addSn addnS -addSn prednK //.
    exact: has_size.

  - Case "ScanState_moveActiveToHandled".
    rewrite size_rem; last assumption.
    rewrite 2!addnS -addSn prednK //.
    exact: has_size.

  - Case "ScanState_moveInactiveToActive".
    rewrite size_rem; last assumption.
    rewrite addSn -addnS -addSn prednK //.
    exact: has_size.

  - Case "ScanState_moveInactiveToHandled".
    rewrite size_rem; last assumption.
    rewrite addnS -addSn prednK //.
    exact: has_size.

  - Case "ScanState_splitCurrentInterval".
    by rewrite size_insert /= !size_map.
Qed.

End MLinearSpec.