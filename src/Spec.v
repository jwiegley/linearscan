Require Import LinearScan.Lib.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** * Linear scan specification *)

(** This module contains Theorems which prove properties concerning the
    specification the linear register allocation algorithm, but which are not
    directly used in implementing the algorithm. *)

Module UnhandledSorted.

Lemma Forall_widen : forall n x (xs : list ('I_n * nat)),
  List.Forall (lebf (@snd _ _) x) xs
    -> List.Forall (lebf (@snd _ _) (widen_id (fst x), snd x))
                   [seq (widen_id (fst p), snd p) | p <- xs].
Proof.
  move=> ? x xs.
  elim: xs x => //= [? ? IHys] ? H /=.
  constructor; first by inv H.
  by apply IHys; inv H.
Qed.

Lemma StronglySorted_widen : forall n (xs : list ('I_n * nat)),
  StronglySorted (lebf (@snd _ _)) xs
    -> StronglySorted (lebf (@snd _ _)) [seq widen_fst p | p <- xs].
Proof.
  move=> ?.
  elim=> /= [|? ? ?] H; first by constructor.
  constructor; first by inv H; auto.
  by apply Forall_widen; inv H.
Qed.

Lemma Forall_insert_spec : forall a x (xs : seq (a * nat)) z,
  List.Forall (lebf (@snd _ _) x) xs -> lebf (@snd _ _) x z
    -> List.Forall (lebf (@snd _ _) x) (insert (lebf (@snd _ _)) z xs).
Proof.
  move=> a x.
  elim=> /= [|y ys IHys] z H Hlt.
    by constructor.
  rewrite /insert.
  case L: (lebf (@snd _ _) y z).
    constructor. by inv H.
    by apply: IHys; inv H.
  by constructor.
Qed.

Lemma StronglySorted_insert_spec a (l : list (a * nat)) : forall z,
  StronglySorted (lebf (@snd _ _)) l
    -> StronglySorted (lebf (@snd _ _)) (insert (lebf (@snd _ _)) z l).
Proof.
  move=> z.
  elim: l => /= [|x xs IHxs] Hsort.
    by constructor.
  inv Hsort.
  specialize (IHxs H1).
  rewrite /insert.
  case L: (lebf (@snd _ _) x z).
    constructor. exact: IHxs.
    exact: Forall_insert_spec.
  constructor.
    by constructor.
  constructor.
    unfold lebf in *.
    apply ltnW. rewrite ltnNge.
    apply/negP/eqP. by rewrite L.
  apply List.Forall_impl with (P := (fun m : a * nat => lebf (@snd _ _) x m)).
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

Theorem unhandled_sorted `(st : @ScanState maxReg b sd) :
  StronglySorted (lebf (@snd _ _)) (unhandled sd).
Proof.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". by constructor.
  - Case "ScanState_newUnhandled".
    exact/StronglySorted_insert_spec/StronglySorted_widen/IHst.
  - Case "ScanState_finalize". exact: IHst.
  - Case "ScanState_newHandled".
    rewrite /=.
    exact: StronglySorted_widen.
  - Case "ScanState_setInterval". exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.
  - Case "ScanState_moveUnhandledToActive". by inv IHst.
  - Case "ScanState_moveUnhandledToHandled". by inv IHst.
  - Case "ScanState_moveActiveToInactive". exact: IHst.
  - Case "ScanState_moveActiveToHandled". exact: IHst.
  - Case "ScanState_moveInactiveToActive". exact: IHst.
  - Case "ScanState_moveInactiveToHandled".  exact: IHst.
Qed.

End UnhandledSorted.

Theorem allocated_regs_are_unique `(st : @ScanState maxReg b sd) :
  uniq ([ seq snd i | i <- active sd ]).
Proof.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil".                   by [].
  - Case "ScanState_newUnhandled".          by rewrite -map_comp.
  - Case "ScanState_finalize".              exact: IHst.
  - Case "ScanState_newHandled".            by rewrite -map_comp.
  - Case "ScanState_setInterval".           exact: IHst.
  - Case "ScanState_setFixedIntervals".     exact: IHst.
  - Case "ScanState_moveUnhandledToActive". by apply/andP.
  - Case "ScanState_moveUnhandledToHandled". exact: IHst.
  - Case "ScanState_moveActiveToInactive".  exact: proj_rem_uniq.
  - Case "ScanState_moveActiveToHandled".   exact: proj_rem_uniq.
  - Case "ScanState_moveInactiveToActive".  by apply/andP.
  - Case "ScanState_moveInactiveToHandled". by [].
Qed.

Tactic Notation "uniq_reorg" ident(s2) ident(sd) ident(Huniq) tactic(H) :=
  set s2 := unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd;
  rewrite (@perm_eq_uniq _ _ s2); first exact: Huniq; H;
  by apply/perm_map; rewrite perm_rem_cons;
    first do [ exact: perm_eq_refl
             | by rewrite perm_catC; exact: perm_eq_refl ].

Lemma move_active_to_inactive : forall maxReg sd x,
  uniq (@unhandledIds maxReg sd ++
        activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- rem x (active sd)] ++
              [seq fst i | i <- x :: inactive sd] ++ handledIds sd).
Proof.
  move=> ? sd x Huniq Hin.
  uniq_reorg s2 sd Huniq (rewrite perm_cat2l !catA perm_cat2r -!map_cat).
Qed.

Lemma move_active_to_handled : forall maxReg sd x,
  uniq (@unhandledIds maxReg sd ++
        activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in active sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- rem x (active sd)] ++
              inactiveIds sd ++
              [seq fst i | i <- (fst x, Some (snd x)) :: handled sd]).
Proof.
  move=> ? sd x Huniq Hin.
  set s2 := unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd.
  rewrite (@perm_eq_uniq _ _ s2); first exact: Huniq.
  rewrite perm_cat2l perm_catCA perm_eq_sym perm_catCA
          perm_cat2l perm_eq_sym
          map_cons /= -cat_rcons perm_cat2r perm_rcons
          -map_cons perm_map => //.
  rewrite perm_eq_sym.
  exact: perm_to_rem.
Qed.

Lemma move_inactive_to_active : forall maxReg sd x,
  uniq (@unhandledIds maxReg sd ++
        activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ [seq fst i | i <- x :: active sd] ++
              [seq fst i | i <- rem x (inactive sd)] ++ handledIds sd).
Proof.
  move=> ? sd x Huniq Hin.
  uniq_reorg s2 sd Huniq
    (rewrite perm_cat2l !catA perm_cat2r perm_catC -!map_cat).
Qed.

Lemma perm_flip :
  forall (T : eqType) (s1 s2 s3 : seq T),
  perm_eq s1 (s3 ++ s2) = perm_eq s1 (s2 ++ s3).
Proof.
  move=> T s1 s2 s3.
  by rewrite perm_eq_sym -perm_catC perm_eq_sym.
Qed.

Lemma move_inactive_to_handled : forall maxReg sd x,
  uniq (@unhandledIds maxReg sd ++
        activeIds sd ++ inactiveIds sd ++ handledIds sd)
    -> x \in inactive sd
    -> uniq (unhandledIds sd ++ activeIds sd
               ++ [seq fst i | i <- rem x (inactive sd)]
               ++ [seq fst i | i <- (fst x, Some (snd x)) :: handled sd]).
Proof.
  move=> ? sd x Huniq Hin.
  set s2 := unhandledIds sd ++ activeIds sd ++ inactiveIds sd ++ handledIds sd.
  rewrite (@perm_eq_uniq _ _ s2); first exact: Huniq.
  rewrite perm_cat2l perm_catCA perm_eq_sym perm_catCA
          map_cons /= -cat_rcons !catA perm_cat2r
          perm_flip cat_rcons perm_flip perm_cat2r
          -map_cons perm_map => //.
  exact: perm_to_rem.
Qed.

Theorem lists_are_unique `(st : @ScanState maxReg b sd) :
  uniq (all_state_lists sd).
Proof.
  rewrite /all_state_lists
          /unhandledIds /activeIds /inactiveIds /handledIds /=.
  ScanState_cases (induction st) Case.
  - Case "ScanState_nil". by [].

  - Case "ScanState_newUnhandled".
    rewrite /=.
    set s2 :=
      [seq fst i | i <- n :: unh] ++
      [seq fst i | i <- [seq widen_fst i | i <- active sd]] ++
      [seq fst i | i <- [seq widen_fst i | i <- inactive sd]] ++
      [seq fst i | i <- [seq widen_fst i | i <- handled sd]].
    rewrite (@perm_eq_uniq _ _ s2) /s2 /unh /n.
      rewrite map_cons !map_widen_fst.
      apply/andP; split.
        rewrite !mem_cat.
        apply/norP; split. exact: no_ord_max.
        apply/norP; split. exact: no_ord_max.
        apply/norP; split; exact: no_ord_max.
      rewrite -!map_cat map_inj_uniq.
        exact: IHst.
      exact: widen_ord_inj.
    rewrite perm_cat2r.
    apply/perm_map.
    by rewrite insert_perm.

  - Case "ScanState_finalize". exact: IHst.
  - Case "ScanState_newHandled".
    rewrite /= !map_widen_fst.
    set s2 :=
      ord_max :: [seq widen_id i | i <- [seq fst i | i <- unhandled sd]] ++
      [seq widen_id i | i <- [seq fst i | i <- active sd]] ++
      [seq widen_id i | i <- [seq fst i | i <- inactive sd]] ++
      [seq widen_id i | i <- [seq fst i | i <- handled sd]].
    rewrite (@perm_eq_uniq _ _ s2).
      rewrite /s2 cons_uniq -!map_cat.
      apply/andP; split.
        exact: no_ord_max.
      rewrite map_inj_uniq => //.
        exact: widen_ord_inj.
    rewrite /s2 !catA.
    by rewrite -perm_cat_cons.

  - Case "ScanState_setInterval". exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.
  - Case "ScanState_moveUnhandledToActive".
    move: IHst; rewrite /= -cons_uniq => IHst.
    set s2 :=
      fst x :: [seq fst i | i <- unh] ++
      [seq fst i | i <- act] ++
      [seq fst i | i <- inact] ++
      [seq fst i | i <- hnd].
    rewrite (@perm_eq_uniq _ _ s2); first exact: IHst.
    by rewrite -perm_cat_cons.

  - Case "ScanState_moveUnhandledToHandled".
    move: IHst; rewrite /= -cons_uniq => IHst.
    set s2 :=
      fst x :: [seq fst i | i <- unh] ++
      [seq fst i | i <- act] ++
      [seq fst i | i <- inact] ++
      [seq fst i | i <- hnd].
    rewrite (@perm_eq_uniq _ _ s2); first exact: IHst.
    rewrite /s2 !catA.
    by rewrite -perm_cat_cons.

  - Case "ScanState_moveActiveToInactive".
    exact: (@move_active_to_inactive _ _ x IHst H).
  - Case "ScanState_moveActiveToHandled".
    exact: (@move_active_to_handled _ _ x IHst H).
  - Case "ScanState_moveInactiveToActive".
    exact: (@move_inactive_to_active _ _ x IHst H).
  - Case "ScanState_moveInactiveToHandled".
    exact: (@move_inactive_to_handled _ _ x IHst H).
Qed.

Theorem actives_are_unique `(st : @ScanState maxReg b sd) :
  uniq (active sd).
Proof.
  pose H1 := allocated_regs_are_unique st.
  pose H2 := lists_are_unique st.
  move: H2.
  rewrite /all_state_lists cat_uniq.
  move/and3P=> [_ _ H3].
  move: H3.
  rewrite cat_uniq.
  rewrite /activeIds.
  move/and3P=> [H3 _ _].
  exact: uniq_proj.
Qed.

Theorem all_intervals_represented `(st : @ScanState maxReg b sd) :
  size (all_state_lists sd) == nextInterval sd.
Proof.
  rewrite /all_state_lists
          /unhandledIds /activeIds /inactiveIds /handledIds
          /= !size_cat !size_map.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". by [].

  - Case "ScanState_newUnhandled".
    by rewrite /unh insert_size !size_map addSn.

  - Case "ScanState_finalize". exact: IHst.
  - Case "ScanState_newHandled". by rewrite 3!addnS !size_map.
  - Case "ScanState_setInterval". exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.

  - Case "ScanState_moveUnhandledToActive".
    by rewrite addnA addnS -addSn -addnA.

  - Case "ScanState_moveUnhandledToHandled".
    by rewrite 3!addnS -addSn.

  - Case "ScanState_moveActiveToInactive".
    rewrite size_rem; last assumption.
    rewrite addSn addnS -addSn prednK //.
    apply: has_size.
    exact H.

  - Case "ScanState_moveActiveToHandled".
    rewrite size_rem; last assumption.
    rewrite 2!addnS -addSn prednK //.
    apply: has_size.
    exact H.

  - Case "ScanState_moveInactiveToActive".
    rewrite size_rem; last assumption.
    rewrite addSn -addnS -addSn prednK //.
    apply: has_size.
    exact H.

  - Case "ScanState_moveInactiveToHandled".
    rewrite size_rem; last assumption.
    rewrite addnS -addSn prednK //.
    apply: has_size.
    exact H.
Qed.

Lemma insert_in_widen_helper : forall n x y z ws,
  (widen_id x, y) \in [seq widen_fst i | i <- ws]
    -> (widen_id x, y) \in insert (lebf (snd (B:=nat))) (@ord_max n, z)
                                  [seq widen_fst i | i <- ws].
Proof.
  move=> n x y z.
  elim=> //= [u us IHus].
  rewrite /insert /= -/insert.
  case: (lebf (snd (B:=nat)) (widen_fst u) (ord_max, z)).
    rewrite !in_cons.
    move/orP=> [H|H].
      by apply/orP; left.
    apply/orP; right.
    exact: IHus.
  rewrite !in_cons.
  move/orP=> [H|H].
    apply/orP; right.
    by apply/orP; left.
  apply/orP; right.
  by apply/orP; right.
Qed.

Lemma insert_in_widen : forall n x (y z : nat) xs,
  (@widen_id n x, y) \in insert (lebf (snd (B:=nat))) (ord_max, z)
                                [seq widen_fst i | i <- xs]
    -> (x, y) \in xs.
Proof.
  move=> n x y z.
  elim=> [|w ws IHws] /=.
    rewrite /insert /in_mem /=.
    move/orP=> [H|H] //.
    move: xpair_eqE H => -> /andP [H _].
    move: (lift_bounded x) => Hneg.
    move/eqP in H.
    rewrite -H in Hneg.
    by move/eqP in Hneg.
  rewrite /insert /in_mem /= -/insert.
  case: (lebf (snd (B:=nat)) (widen_fst w) (ord_max, z)) => /=.
    destruct w; simpl.
    move/orP=> [H|H].
      move: xpair_eqE H => -> /andP [/eqP H1 /eqP H2].
      rewrite /widen_id in H1.
      inv H1.
      apply/orP; left.
      apply/eqP.
      f_equal.
      destruct x; destruct o.
      rewrite /nat_of_ord in H0.
      subst.
      f_equal.
      exact: eq_irrelevance.
    apply/orP; right.
    exact: IHws.
  move/orP=> [H|H].
    move: xpair_eqE H => -> /andP [/eqP H1 _].
    move: (lift_bounded x) => H2.
    rewrite -H1 in H2.
    by move/negP in H2.
  move/orP: H => [H|H].
    move: xpair_eqE H => -> /andP [/eqP H1 /eqP H2].
    rewrite /widen_id in H1.
    inv H1.
    destruct w; simpl in *.
    destruct x; destruct o.
    apply/orP; left.
    rewrite /nat_of_ord in H0.
    subst.
    replace (Ordinal i) with (Ordinal i0); last first.
      f_equal.
      exact: eq_irrelevance.
    apply/eqP.
    f_equal.
  apply/orP; right.
  exact/IHws/insert_in_widen_helper.
Qed.

Lemma leqNEltnEq : forall n m, n < m.+1 -> (n < m) = false -> n = m.
Proof.
  move=> n m H1 H2.
  move/negbT in H2.
  rewrite -leqNgt in H2.
  by ordered.
Qed.

Lemma in_contra : forall (a : eqType) (x : a) (xs : seq a),
  x \in xs -> x \notin xs -> False.
Proof.
  move=> a x.
  elim=> //= [y ys IHys] Hin Hnotin.
  rewrite in_cons in Hin Hnotin.
  move/orP: Hin => [Hin|Hin].
    rewrite negb_or in Hnotin.
    move/andP: Hnotin => [H1 H2].
    move/eqP in Hin.
    rewrite Hin in H1.
    by move/negP in H1.
  rewrite negb_or in Hnotin.
  move/andP: Hnotin => [H1 H2].
  exact: IHys.
Qed.

Lemma in_projr : forall (a b : eqType) (x : a) (y : b) (xs : seq (a * b)),
  (x, y) \in xs -> x \in [seq fst i | i <- xs] /\ y \in [seq snd i | i <- xs].
Proof.
  move=> a b x y.
  elim=> //= [z zs IHzs] H.
  split.
    rewrite in_cons.
    move: in_cons H => -> /orP [H|H].
      apply/orP; left.
      destruct z.
      move: xpair_eqE H => -> /andP [/eqP ? /eqP ?] /=.
      by apply/eqP.
    apply/orP; right.
    by move: (IHzs H) => [? ?].
  rewrite in_cons.
  move: in_cons H => -> /orP [H|H].
    apply/orP; left.
    destruct z.
    move: xpair_eqE H => -> /andP [/eqP ? /eqP ?] /=.
    by apply/eqP.
  apply/orP; right.
  by move: (IHzs H) => [? ?].
Qed.

Lemma insert_in_ord_max : forall n (y z : nat) (xs : seq ('I_n * nat)),
  (@ord_max n, y) \in insert (lebf (snd (B:=nat))) (ord_max, z)
                             [seq widen_fst i | i <- xs]
    -> y == z.
Proof.
  move=> n y z.
  elim=> /= [|x xs IHxs] H.
    rewrite /insert /in_mem /= in H.
    move/orP: H => [H|H] //.
    by move/eqP: H; invert.
    rewrite /insert /= -/insert in H.
  case: (lebf (snd (B:=nat)) (widen_fst x) (ord_max, z)) in H *.
    move: in_cons H => -> /orP [H|H].
      move: H.
      case: x => [x1 x2].
      rewrite /widen_fst /= xpair_eqE.
      move/andP => [/eqP H1 _].
      move: (lift_bounded x1) => H2.
      rewrite H1 in H2.
      by move/negP in H2.
    exact: IHxs.
  move: in_cons H => -> /orP [H|H].
    move/eqP in H.
    by inv H.
  move: in_cons H => -> /orP [H|H].
    move: H.
    case: x => [x1 x2].
    rewrite /widen_fst /= xpair_eqE.
    move/andP => [/eqP H1 _].
    move: (lift_bounded x1) => H2.
    rewrite H1 in H2.
    by move/negP in H2.
  rewrite /widen_fst /= in H.
  move/in_projr: H => [/= H1 _].
  rewrite -map_comp /funcomp /= in H1.
  move: (no_ord_max [seq fst x | x <- xs]) => H2.
  rewrite -map_comp /funcomp /= in H2.
  exfalso.
  exact: (in_contra H1 H2).
Qed.

Theorem beginnings `(st : @ScanState maxReg b sd) : forall uid beg,
  (uid, beg) \in unhandled sd -> ibeg (getInterval uid) == beg.
Proof.
  move=> uid beg Hin.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil". by [].
  - Case "ScanState_newUnhandled".
    case: uid => [m Hm] in Hin *.
    case E: (m < (nextInterval sd)).
      move: Hin.
      replace (Ordinal Hm) with (widen_id (Ordinal E)).
        rewrite vnth_vshiftin.
        move=> Hin.
        apply: IHst.
        rewrite /n in Hin.
        exact: (@insert_in_widen _ _ _ (ibeg d)).
      rewrite /widen_id /widen_ord /=.
      f_equal.
      exact: eq_irrelevance.
    move: Hin.
    replace (Ordinal Hm) with (@ord_max (nextInterval sd)).
      rewrite vnth_last /= /n /unh.
      move=> Hin.
      rewrite eq_sym.
      exact: (@insert_in_ord_max (nextInterval sd) _ _ (unhandled sd)).
    clear -E.
    move/(leqNEltnEq Hm) in E.
    subst.
    rewrite /ord_max /widen_id /widen_ord /=.
    f_equal.
    exact: eq_irrelevance.
  - Case "ScanState_finalize". exact: IHst.
  - Case "ScanState_newHandled".
    move/mapP: Hin => [[? ?] H0 Hin].
    rewrite /widen_fst /= in Hin.
    inversion Hin => /=.
    rewrite ?vnth_vshiftin -H3 in H0 *.
    exact: IHst.
  - Case "ScanState_setInterval".
    case E: (xid == uid).
      move/eqP in E.
      subst.
      rewrite vnth_vreplace /=.
      move/eqP: H => ->.
      exact: IHst.
    move/negbT in E.
    rewrite vnth_vreplace_neq => //.
    exact: IHst.
  - Case "ScanState_setFixedIntervals". exact: IHst.
  - Case "ScanState_moveUnhandledToActive".
    apply: IHst.
    rewrite in_cons.
    apply/orP.
    by right.
  - Case "ScanState_moveUnhandledToHandled".
    apply: IHst.
    rewrite in_cons.
    apply/orP.
    by right.
  - Case "ScanState_moveActiveToInactive". exact: IHst.
  - Case "ScanState_moveActiveToHandled". exact: IHst.
  - Case "ScanState_moveInactiveToActive". exact: IHst.
  - Case "ScanState_moveInactiveToHandled". exact: IHst.
Qed.

Lemma map_filter_fst_widen :
  forall (b : eqType) c n (f : ('I_n.+1 * b) -> c)
         (xs : seq ('I_n * b)) (x : b),
    [seq f i | i <- [seq widen_fst p | p <- xs] & snd i == x] =
    [seq f (widen_fst i) | i <- xs & snd i == x].
Proof.
  move=> b c n f.
  elim=> //= [y ys IHys] x.
  case E: (snd y == x) => /=.
    by rewrite IHys.
  exact: IHys.
Qed.

Lemma map_filter_vshiftin :
  forall (b : eqType) n (xs : seq ('I_n * b)) (x : b)
         (v : Vec IntervalSig n) (y : IntervalSig),
  [seq (vnth (vshiftin v y) (fst i)).1
     | i <- [seq widen_fst j | j <- xs] & snd i == x] =
  [seq (vnth v (fst i)).1 | i <- xs & snd i == x].
Proof.
  move=> b n.
  elim=> //= [z zs IHzs] x v y.
  case E: (snd z == x) => /=.
    by rewrite IHzs vnth_vshiftin.
  exact: IHzs.
Qed.

Definition intervalsForReg `(sd : ScanStateDesc maxReg)
  (reg : PhysReg maxReg) : seq IntervalDesc :=
  let descOf {a} (x : IntervalId sd * a) :=
      getIntervalDesc (getInterval (fst x)) in
  (if vnth (fixedIntervals sd) reg is Some int then [:: int.1] else [::])
  ++ [seq descOf x | x <-  handled sd & snd x == Some reg]
  ++ [seq descOf x | x <-   active sd & snd x ==      reg]
  ++ [seq descOf x | x <- inactive sd & snd x ==      reg].

Definition regAvailForInterval `(sd : ScanStateDesc maxReg)
  (d : IntervalDesc) (reg : PhysReg maxReg) : bool :=
  ~~ has (intervalsIntersect d) (intervalsForReg sd reg).

Fixpoint between_all `(R : rel a) (xs : seq a) : bool :=
  if xs is y :: ys
  then all (R y) ys && between_all R ys
  else true.

Lemma all_xpredT_true : forall a (xs : seq a), all xpredT xs.
Proof. by move=> a; elim. Qed.

Lemma all_catC {a} (P : pred a) (xs ys : seq a) :
  all P (xs ++ ys) = all P (ys ++ xs).
Proof.
  case: xs => /= [|x xs] in ys *.
    by rewrite cats0.
  case: ys => // [|y ys].
    by rewrite cats0.
  by rewrite !all_cat /= andbA andbC.
Qed.

Lemma all_all_cons : forall a (xs ys : seq a) (x : a) (R : rel a)
  (Hsym : symmetric R),
  all (fun y : a => all (R y) (x :: xs)) ys =
  all (R x) ys && all (fun y : a => all (R y) xs) ys.
Proof.
  move=> a xs ys x R Hsym.
  elim: ys => // [y ys IHys].
  rewrite [all]lock -{1}lock /= -lock IHys /= -!andbA.
  congr (_ && _).
    by rewrite Hsym.
  by rewrite and_swap.
Qed.

Lemma between_all_cat : forall a (xs ys : seq a) (R : rel a)
  (Hsym : symmetric R),
  between_all R (xs ++ ys) =
  [&& between_all R xs
  ,   between_all R ys
  ,   all (fun x => all (R x) ys) xs
  &   all (fun y => all (R y) xs) ys
  ].
Proof.
  move=> a xs ys R Hsym.
  elim: xs => [|x xs IHxs] in ys Hsym *.
    by rewrite /= all_xpredT_true Bool.andb_true_r.
  rewrite cat_cons all_all_cons;
    last by exact: Hsym.
  rewrite /= all_cat {}IHxs /=;
    last by exact: Hsym.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite Bool.andb_diag.
  by rewrite -!andbA and_swap.
Qed.

Lemma between_all_catC {a} (xs ys : seq a) (R : rel a) (Hsym : symmetric R) :
  between_all R (xs ++ ys) = between_all R (ys ++ xs).
Proof.
  case: xs => /= [|x xs] in ys *.
    by rewrite cats0.
  case: ys => // [|y ys].
    by rewrite cats0.
  rewrite !between_all_cat; try exact: Hsym.
  rewrite !all_cat /= andbA andbC -!andbA.
  congr (_ && _).
  congr (_ && _).
  rewrite ![LHS]andbA and_swap !andbA andbC -!andbA.
  congr (_ && _).
  rewrite [R y x]Hsym.
  rewrite [LHS]andbC -!andbA.
  rewrite and_swap.
  rewrite andbA.
  rewrite and_swap -!andbA.
  congr (_ && _).
Admitted.

Lemma all_rem_filter_f :
  forall (a : eqType) (xs : seq a) (y : a)
         b (Q : pred b) (f : a -> b) (P : pred a),
   all Q [seq f i | i <- xs & P i] ->
   all Q [seq f i | i <- rem y xs & P i].
Proof.
  move=> a xs y b Q f P.
  elim: xs => //= [x xs IHxs].
  case E: (x == y) => /=.
    move/eqP in E.
    rewrite {}E.
    case: (P y) => //=.
    by move/andP=> [*].
  case: (P x) => //=.
  move/andP=> [*].
  apply/andP; split => //.
  exact: IHxs.
Qed.

Lemma between_all_rem :
  forall (a : eqType) (xs : seq a) (y : a)
         b (R : rel b) (f : a -> b) (P : pred a),
  between_all R [seq f i | i <- xs & P i]
    -> between_all R [seq f i | i <- rem y xs & P i].
Proof.
  move=> a xs y b R f P.
  elim: xs => //= [x xs IHxs].
  case E: (x == y) => /=.
    case: (P x) => //=.
    by move/andP=> [H1 H2].
  case: (P x) => //=.
  move/andP=> [H1 H2].
  apply/andP; split.
    exact: all_rem_filter_f.
  exact: IHxs.
Qed.

Arguments between_all_rem : default implicits.

Lemma all_impl3of4 :
  forall a (x y z w v : seq a) (P : pred a) (H : all P z -> all P v),
    all P (x ++ y ++ z ++ w) ->
    all P (x ++ y ++ v ++ w).
Proof.
Admitted.

Lemma all_impl4of4 :
  forall a (x y z w v : seq a) (P : pred a) (H : all P w -> all P v),
    all P (x ++ y ++ z ++ w) ->
    all P (x ++ y ++ z ++ v).
Proof.
Admitted.

Lemma between_all_impl3of4 :
  forall a (x y z w v : seq a) (R : rel a)
         (H : between_all R z -> between_all R v),
    between_all R (x ++ y ++ z ++ w) ->
    between_all R (x ++ y ++ v ++ w).
Proof.
Admitted.

Lemma between_all_impl4of4 :
  forall a (x y z w v : seq a) (R : rel a)
         (H : between_all R w -> between_all R v),
    between_all R (x ++ y ++ z ++ w) ->
    between_all R (x ++ y ++ z ++ v).
Proof.
Admitted.

Lemma between_all_impl3of3 :
  forall a (x y z v : seq a) (R : rel a)
         (H : between_all R z -> between_all R v),
    between_all R (x ++ y ++ z) ->
    between_all R (x ++ y ++ v).
Proof.
Admitted.

Lemma between_all_inv3of4 :
  forall (a : eqType) b (x y w : seq b) (z : seq a) (s : a) (P : pred a)
         (f : a -> b) (R : rel b),
    between_all R (x ++ y ++ [seq f i | i <- z & P i] ++ w)
      -> s \in z
      -> all (R (f s)) (x ++ y ++ [seq f i | i <- z & P i] ++ w).
Proof.
Admitted.

Lemma between_all_inv4of4 :
  forall (a : eqType) b (x y z : seq b) (w : seq a) (s : a) (P : pred a)
         (f : a -> b) (R : rel b),
    between_all R (x ++ y ++ z ++ [seq f i | i <- w & P i])
      -> s \in w
      -> all (R (f s)) (x ++ y ++ z ++ [seq f i | i <- w & P i]).
Proof.
Admitted.

Notation "f .: g" := (fun x y => f (g x y)) (at level 100).

Ltac nao_setup IHst :=
  rewrite !between_all_cat in IHst *;
  move/andP: IHst => [H1 /andP [H2 /andP [H3 H4]]];
  do !(apply/andP; split=> //).

Ltac nao_resolve :=
  rewrite map_cons /=;
  apply/andP; split=> //;
  apply/orP; left;
  apply/nandP; left;
  by rewrite negb_eq.

Lemma sym_neg : forall a (R : rel a), symmetric R -> symmetric (negb .: R).
Proof.
  move=> a R H x y.
  by rewrite H.
Qed.

Lemma between_all_map_rem_cons_f :
  forall b (R : rel b) (a : eqType) (f : a -> b)
         (xs ys : seq a) (x : a) (P : pred a),
  between_all R [seq f i | i <- [seq j <- rem x xs | P j] ++
                                x :: [seq j <- ys | P j]] =
  between_all R [seq f i | i <- [seq j <- xs | P j] ++
                                [seq j <- ys | P j]].
Proof.
Admitted.

Lemma between_all_map_catC :
  forall b (R : rel b) (a : eqType) (f : a -> b) (xs ys : seq a),
  between_all R [seq f i | i <- xs ++ ys] =
  between_all R [seq f i | i <- ys ++ xs].
Proof.
Admitted.

Lemma all_transport : forall a (xs : seq a) (P Q : pred a),
  (forall x : a, P x = Q x) -> all P xs = all Q xs.
Admitted.

Lemma contractions_disjoint :
  forall a d b c : IntervalDesc,
    ~~ intervalsIntersect a d ->
    ibeg b >= ibeg a ->
    iend b <= iend a ->
    ibeg c >= ibeg d ->
    iend c <= iend d ->
    ~~ intervalsIntersect b c.
Admitted.

Lemma all_all_contract
  (a : Type) (P : a -> bool)
  (b : Type) (Q : b -> bool)
  (maxReg : nat)
  (sd : ScanStateDesc maxReg)
  (xid : 'I_(nextInterval sd))
  (i : IntervalSig)
  (xs : seq (IntervalId sd * a))
  (ys : seq (IntervalId sd * b)) :
  all (fun y : IntervalDesc =>
         all (fun y0 : IntervalDesc => ~~ intervalsIntersect y y0)
             [seq (vnth (intervals sd) (fst x)).1
             | x <- xs
             & P (snd x)])
      [seq (vnth (intervals sd) (fst x)).1
      | x <- ys
      & Q (snd x)]
  -> all (fun x : IntervalDesc =>
            all (fun y0 : IntervalDesc => ~~ intervalsIntersect x y0)
                [seq (vnth (vreplace (intervals sd) xid i) (fst x0)).1
                | x0 <- ys
                & Q (snd x0)])
         [seq (vnth (vreplace (intervals sd) xid i) (fst x)).1
         | x <- xs
         & P (snd x)].
Proof.
Admitted.

Lemma between_all_contract
  (a : Type)
  (P : a -> bool)
  (maxReg : nat)
  (sd : ScanStateDesc maxReg)
  (xid : 'I_(nextInterval sd))
  (i : IntervalSig)
  (xs : seq (IntervalId sd * a)) :
  between_all (negb .: intervalsIntersect)
    ([seq (vnth (intervals sd) (fst x)).1 | x <- xs & P (snd x)])
  -> between_all (negb .: intervalsIntersect)
       ([seq (vnth (vreplace (intervals sd) xid i) (fst x)).1
        | x <- xs & P (snd x)]).
Proof.
  move=> H.
  elim: xs => //= [x xs IHxs] in H *.
  case E: (P (snd x)) in IHxs H *.
    move/andP: H => [H0 H1].
    apply/andP; split.
      rewrite {IHxs H1}.
      elim: xs => //= [y ys IHys] in H0 *.
      case F: (P (snd y)) in IHys H0 *.
        move/andP: H0 => [H1 H2].
        apply/andP; split.
          rewrite {IHys H2}.
          apply (@contractions_disjoint
            (vnth (intervals sd) (fst x)).1
            (vnth (intervals sd) (fst y)).1
            (vnth (vreplace (intervals sd) xid i) (fst x)).1
            (vnth (vreplace (intervals sd) xid i) (fst y)).1) => //.
          - admit.
          - admit.
          - admit.
          - admit.
        exact: (IHys H2).
      exact: (IHys H0).
    exact: IHxs H1.
  exact: IHxs H.
Admitted.

Tactic Notation "breakdown" tactic(T) :=
    repeat match goal with
    | [ H : is_true (@between_all _ _ (@cat _ _ _)) |- _ ] =>
      move: H;
      try rewrite -!map_cat;
      try rewrite -!flatten_cat;
      try rewrite -!filter_cat;
      rewrite between_all_cat; last assumption;
      try rewrite -!map_cat;
      try rewrite -!flatten_cat;
      try rewrite -!filter_cat;
      try rewrite !all_cat;
      move=> H;
      repeat match goal with
      | [ H: is_true (_ && _) |- _ ] => move/andP: H => [? ?]
      | [ H: is_true [&& _, _, _, _ & _ ] |- _ ] => move: H => [*]
      | [ H: is_true [&& _, _, _ & _ ] |- _ ] => move: H => [*]
      | [ H: is_true [&& _, _ & _ ] |- _ ] => move: H => [*]
      | [ H: is_true [&& _ & _ ] |- _ ] => move: H => [*]
      end
    | [ |- is_true (@between_all _ _ (@cat _ _ _)) ] =>
      try rewrite -!map_cat;
      try rewrite -!flatten_cat;
      try rewrite -!filter_cat;
      rewrite between_all_cat; last assumption;
      try rewrite -!map_cat;
      try rewrite -!flatten_cat;
      try rewrite -!filter_cat;
      try rewrite !all_cat;
      repeat match goal with
      | [ |- is_true (_ && _) ] => apply/andP; split
      | [ |- is_true [&& _, _, _, _ & _ ] ] => split
      | [ |- is_true [&& _, _, _ & _ ] ] => split
      | [ |- is_true [&& _, _ & _ ] ] => split
      | [ |- is_true [&& _ & _ ] ] => split
      end
    end; move=> //; try T.

Theorem no_allocations_overlap `(st : @ScanState maxReg InUse sd)
  (registers_exist : maxReg > 0) :
  forall reg : PhysReg maxReg,
  between_all (negb .: intervalsIntersect) (intervalsForReg sd reg).
Proof.
  move=> reg.
  rewrite /intervalsForReg.
  ScanState_cases (induction st) Case; simpl in *.
  - Case "ScanState_nil".
    by rewrite vnth_vconst.
  - Case "ScanState_newUnhandled".
    rewrite !map_filter_vshiftin.
    exact: IHst.
  - Case "ScanState_finalize".
    exact: IHst.
  - Case "ScanState_newHandled".
    rewrite !map_filter_vshiftin.
    exact: IHst.
  - Case "ScanState_setInterval".
    (* jww (2015-07-05): We should be able to prove this based on the fact
       that intervals may only contract. *)
    have Hsym := sym_neg intervalsIntersect_sym.
    pose f x := x == Just reg.
    pose g x := x == reg.
    rewrite between_all_cat; last exact: Hsym.
    rewrite between_all_cat in IHst; last exact: Hsym.
    move/andP: IHst => [IHst0 /andP [IHst1 /andP [IHst2 IHst3]]].
    apply/andP; split => //.
    apply/andP; split => //.
      rewrite between_all_cat; last exact: Hsym.
      rewrite between_all_cat in IHst1; last exact: Hsym.
      move/andP: IHst1 => [IHst10 /andP [IHst11 /andP [IHst12 IHst13]]].
      apply/andP; split => //.
        exact: (@between_all_contract _ f maxReg sd).
      apply/andP; split => //.
        rewrite between_all_cat; last exact: Hsym.
        rewrite between_all_cat in IHst11; last exact: Hsym.
        move/andP: IHst11 => [IHst110 /andP [IHst111 /andP [IHst112 IHst113]]].
        do 2 (apply/andP; split => //;
          first exact: (@between_all_contract _ g maxReg sd)).
        apply/andP; split => //;
        exact: (@all_all_contract _ g _ g maxReg sd).
      rewrite -map_cat -filter_cat in IHst12.
      rewrite -map_cat -filter_cat in IHst13.
      rewrite -map_cat -filter_cat.
      apply/andP; split => //.
        exact: (@all_all_contract _ f _ g maxReg sd).
      exact: (@all_all_contract _ g _ f maxReg sd).
    apply/andP; split => //.
      rewrite {IHst0 IHst1 IHst3}.
      case: (vnth (fixedIntervals sd) reg) => //= [int] in IHst2 *.
      move: IHst2.
      rewrite -!map_cat -!filter_cat Bool.andb_true_r all_cat.
      move/andP=> [IHst21 IHst22].
      apply/andP; split.
        admit.
      admit.
    rewrite {IHst0 IHst1 IHst2}.
    move: IHst3.
    rewrite -!map_cat -!filter_cat !all_cat.
    move/andP=> [IHst31 IHst32].
    apply/andP; split.
      admit.
    admit.
  - Case "ScanState_setFixedIntervals".
    have Hneeded :
      forall reg,
        if vnth regs reg is Some int
        then all (negb \o intervalsIntersect int.1)
                 (intervalsForReg sd reg)
        else true
          by admit.
    specialize (Hneeded reg).
    rewrite /intervalsForReg in Hneeded.
    have Hsym := sym_neg intervalsIntersect_sym.
    rewrite between_all_cat; last exact: Hsym.
    rewrite between_all_cat in IHst; last exact: Hsym.
    case: (vnth regs reg) => [int|] in Hneeded *.
      move: Hneeded.
      rewrite all_cat.
      move/andP => [H1 H2].
      do !(move/andP: IHst => [? IHst]).
      rewrite !andbA.
      do !(apply/andP; split => //=).
      clear -H2.
      rewrite /funcomp /getInterval in H2.
      have H0 :
        (fun y : IntervalDesc => ~~ intervalsIntersect y int.1 && true) =1
        (fun x : IntervalDesc => ~~ intervalsIntersect int.1 x).
        move=> x.
        by rewrite Bool.andb_true_r intervalsIntersect_sym.
      rewrite (all_transport _ H0).
      exact: H2.
    rewrite /=.
    rewrite all_xpredT_true Bool.andb_true_r.
    move: IHst.
    by move/andP=> [_ /andP [? _]].
  - Case "ScanState_moveUnhandledToActive".
    have Hsym := sym_neg intervalsIntersect_sym.
    case E: (reg0 == reg) => //.
    rewrite catA between_all_catC; last exact: Hsym.
    rewrite cat_cons /=.
    rewrite all_catC between_all_catC; last exact: Hsym.
    rewrite -!catA.
    apply/andP; split => //.
    move: st.
    set sd := (X in ScanState _ X).
    move=> st.
    have Hneeded :
      all (negb \o intervalsIntersect (vnth ints (fst x)).1)
          (intervalsForReg sd reg)
        by admit.
    exact: Hneeded.
  - Case "ScanState_moveUnhandledToHandled". exact: IHst.
  - Case "ScanState_moveActiveToInactive".
    case E: (snd x == reg).
      rewrite -!map_cat.
      apply: between_all_impl3of3.
        move=> H0.
        rewrite between_all_map_rem_cons_f.
        exact: H0.
      rewrite !map_cat.
      by [].
    apply: between_all_impl3of4.
      exact: between_all_rem.
    by [].
  - Case "ScanState_moveActiveToHandled".
    case S: spilled in H0 *.
      case R: (Nothing == Just reg) => //.
      apply: between_all_impl3of4.
        exact: between_all_rem.
      by [].
    have Hsym := sym_neg intervalsIntersect_sym.
    case E: (Just (snd x) == Just reg).
      rewrite /= between_all_catC /=; last exact: Hsym.
      apply/andP; split => //.
        rewrite all_catC.
        apply: all_impl3of4.
          exact: all_rem_filter_f.
        exact: between_all_inv3of4 _ _ _ _ _ (active sd) x _ _ _ IHst H.
      rewrite between_all_catC; last exact: Hsym.
      apply: between_all_impl3of4.
        exact: between_all_rem.
      by [].
    apply: between_all_impl3of4.
      exact: between_all_rem.
    by [].
  - Case "ScanState_moveInactiveToActive".
    case E: (snd x == reg).
      rewrite -!map_cat.
      apply: between_all_impl3of3.
        move=> H1.
        rewrite -between_all_map_catC.
        rewrite between_all_map_rem_cons_f.
        rewrite between_all_map_catC.
        exact: H1.
      rewrite !map_cat.
      by [].
    apply: between_all_impl4of4.
      exact: between_all_rem.
    by [].
  - Case "ScanState_moveInactiveToHandled".
    case S: spilled.
      case R: (Nothing == Just reg) => //.
      apply: between_all_impl4of4.
        exact: between_all_rem.
      by [].
    have Hsym := sym_neg intervalsIntersect_sym.
    case E: (Just (snd x) == Just reg).
      rewrite /= between_all_catC /=; last exact: Hsym.
      apply/andP; split => //.
        rewrite all_catC.
        apply: all_impl4of4.
          exact: all_rem_filter_f.
        exact: between_all_inv4of4 _ _ _ _ _ (inactive sd) x _ _ _ IHst H.
      rewrite between_all_catC; last exact: Hsym.
      apply: between_all_impl4of4.
        exact: between_all_rem.
      by [].
    apply: between_all_impl4of4.
      exact: between_all_rem.
    by [].
Admitted.
