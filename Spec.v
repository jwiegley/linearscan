Require Import Lib.

Require Export ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MLinearSpec (Mach : Machine).
Import Mach.
Module Import MS := MScanState Mach.

(** * Linear scan specification *)

(** This module contains Theorems which prove properties concerning the
    specification the linear register allocation algorithm, but which are not
    directly used in implementing the algorithm. *)

Module SortednessProof.

(* SSReflect doesn't provide a scheme for determining sortedness, so we
   confine the import of the Sorted library to this section. *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Ssreflect.seq.

Lemma Forall_widen : forall n x (xs : list (fin n * nat)),
  Forall (lebf snd x) xs
    -> Forall (lebf snd (widen_id (fst x), snd x))
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

Lemma Forall_insert_spec : forall a x (xs : seq (a * nat)) z,
  Forall (lebf snd x) xs -> lebf snd x z
    -> Forall (lebf snd x) (insert (lebf snd ^~ z) z xs).
Proof.
  move=> a x.
  elim=> /= [|y ys IHys] z H Hlt.
    by constructor.
  rewrite /insert.
  case L: (lebf snd y z).
    constructor. by inv H.
    by apply: IHys; inv H.
  by constructor.
Qed.

Lemma StronglySorted_insert_spec a (l : list (a * nat)) : forall z,
  StronglySorted (lebf snd) l
    -> StronglySorted (lebf snd) (insert (lebf snd ^~ z) z l).
Proof.
  move=> z.
  elim: l => /= [|x xs IHxs] Hsort.
    by constructor.
  inv Hsort. clear Hsort.
  specialize (IHxs H1).
  rewrite /insert.
  case L: (lebf snd x z).
    constructor. exact: IHxs.
    exact: Forall_insert_spec.
  constructor.
    by constructor.
  constructor.
    unfold lebf in *.
    apply ltnW. rewrite ltnNge.
    apply/negP/eqP. by rewrite L.
  apply Forall_impl with (P := (fun m : a * nat => lebf snd x m)).
    rewrite /lebf.
    move=> a0 Hlt.
    move: L => /negP.
    rewrite /lebf.
    move=> /negP.
    rewrite -ltnNge.
    move=> /ltnW L.
    exact: (leq_trans L).
  by [].
Qed.

Theorem unhandled_sorted `(st : ScanState sd) :
  StronglySorted (lebf snd) (unhandled sd).
Proof.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". by constructor.

  - Case "ScanState_newUnhandled".
    exact/StronglySorted_insert_spec/StronglySorted_widen/IHst.

  - Case "ScanState_setInterval". exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.
  - Case "ScanState_moveUnhandledToActive". inv IHst.
  - Case "ScanState_moveActiveToInactive". exact: IHst.
  - Case "ScanState_moveActiveToHandled". exact: IHst.
  - Case "ScanState_moveInactiveToActive". exact: IHst.
  - Case "ScanState_moveInactiveToHandled".  exact: IHst.
Qed.

End SortednessProof.

Theorem allocated_regs_are_unique `(st : ScanState sd) :
  uniq ([ seq snd i | i <- active sd ++ inactive sd ]).
Proof.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". constructor.
  - Case "ScanState_newUnhandled".
    by rewrite /widen_fst -!map_cat -!map_comp /funcomp //.

  - Case "ScanState_setInterval". exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.
  - Case "ScanState_moveUnhandledToActive".
    move=> /= in IHst *; apply/andP; split=> //.

    (* jww (2014-10-31): Need the following evidence here:
         reg \notin [seq snd i | i <- act ++ inact]

       This will need to come from the [ScanState_moveUnhandledToActive]
       constructor, but doing so will require obtaining it from the algorithm,
       which may be a substantial change. *)
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
Qed.

(** The number of active or inactive registers cannot exceed the number of
    registers available (or, if there are more register than intervals to be
    allocated, the number of intervals). *)
Theorem limit_active_registers `(st : ScanState sd) :
  size (active sd) <= minn maxReg (nextInterval sd).
(* jww (2014-10-31): Implementing this will need supporting evidence from the
   algorithm; I don't think the constructors give us enough detail to
   determine it here by induction. *)
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

  - Case "ScanState_setInterval". exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.
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
Qed.

Theorem all_intervals_represented `(st : ScanState sd) :
  size (all_state_lists sd) == nextInterval sd.
Proof.
  rewrite /all_state_lists
          /unhandledIds /activeIds /inactiveIds /handledIds /=
          !size_cat !size_map.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". by [].

  - Case "ScanState_newUnhandled".
    by rewrite /unh insert_size !size_map addSn.

  - Case "ScanState_setInterval". exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.

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
Qed.

Theorem ScanState_newUnhandled_spec `(st : ScanState sd) : forall d i,
  unhandledExtent (getScanStateDesc (@ScanState_newUnhandled _ st d i)) ==
  unhandledExtent sd + intervalExtent i.
Proof.
  move=> d i /=.
  rewrite /unhandledExtent /=.
  case: sd st => ni IntervalId0 ? ? unh /= ? ? ? _ /=.
  rewrite -!map_comp insert_f_sumlist map_cons -map_comp /funcomp
          sumlist_cons vnth_last /= addnC.
  apply/eqP; congr (_ + _).
  elim: unh => [//|u us IHus] /=.
  rewrite !sumlist_cons IHus.
  congr (_ + _).
  by rewrite vnth_vshiftin.
Qed.

Theorem ScanState_hasInterval_spec `(st : ScanState sd) : forall xid,
  let int := vnth (intervals sd) xid in
  xid \in unhandledIds sd -> intervalExtent int.2 <= unhandledExtent sd.
Proof.
  move=> xid /= Hin.
  rewrite /unhandledExtent /=.
  set g := (X in sumlist (map X _)).
  have ->: intervalExtent (vnth (intervals sd) xid).2 = g xid by [].
  exact: in_sumlist.
Qed.

Theorem ScanState_setInterval_spec `(st : ScanState sd) : forall xid d i H1 H2,
  let st'  := @ScanState_setInterval _ st xid d i H1 H2 in
  let sd'  := getScanStateDesc st' in
  let diff := intervalExtent (vnth (intervals sd) xid).2 - intervalExtent i in
  xid \in unhandledIds sd -> unhandledExtent sd' == unhandledExtent sd - diff.
Proof.
  move=> xid d i Hlt Heqe /= Hin.
  move: (lists_are_unique st) => {st}.
  rewrite /all_state_lists cat_uniq => /and3P [Hlau _ _].
  case: sd => ni IntervalId0 ints fixints unh /= act inact hnd /=
    in xid Hlt Heqe Hin Hlau *.
  rewrite /unhandledExtent /=.
  rewrite -!map_comp /funcomp => {act inact hnd}.
  rewrite {}/IntervalId0 in unh Hin Hlau *.
  set f := (X in sumlist (map X _)).
  set g := (X in sumlist (map X _) - _).
  elim: unh => [//|u us IHus] /= in Hin Hlau *.
  rewrite !sumlist_cons {1}/f {1}/g /=.
  have Huniq: uniq (fst u :: [seq fst i | i <- us]) by exact: Hlau.
  move: in_cons Hin => -> /orP [/eqP Heq {IHus}|Hin].
    rewrite Heq in f Hlt Heqe *.
    have ->: sumlist (map f us) = sumlist (map g us).
      rewrite /f /g.
      elim: us => //= [y ys IHys] in Hlau Huniq *.
      rewrite !sumlist_cons IHys;
      move: Hlau => /and3P [H1 _ ?];
      move: in_cons H1 => -> /norP [? ?];
        first rewrite vnth_vreplace_neq //=;
      exact/andP.
    rewrite vnth_vreplace addsubsubeq; first by [].
    exact: ltnW.
  move: cons_uniq Huniq => -> /andP [Huniq1 Huniq2].
  move: Hlau => /andP [_ Hlau].
  move: IHus => /(_ Hin Hlau) /= /eqP ->.
  rewrite vnth_vreplace_neq.
    rewrite -addnBA; first by [].
    apply: subn_leq.
    pose h y := intervalExtent (vnth ints y).2.
    have ->: [seq g i | i <- us] = [ seq (h \o fst) x | x <- us ]
      by exact: eq_map.
    have ->: intervalExtent (vnth ints xid).2 = h xid by [].
    rewrite (map_comp _ fst).
    exact: in_sumlist.
  exact: (in_notin Hin).
Qed.

End MLinearSpec.