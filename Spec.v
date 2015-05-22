Require Import LinearScan.Lib.
Require Import LinearScan.Vector.
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

(* SSReflect doesn't provide a scheme for determining sortedness, so we
   confine the import of the Sorted library to this section. *)

(* Require Import Coq.Lists.List. *)
(* Require Import Ssreflect.seq. *)

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

(* Theorem no_regreq_use_positions_on_stack `(st : @ScanState maxReg b sd) : *)
(*   forall x, x \in handled sd -> *)
(*     (snd x != None) || (firstUseReqReg (getInterval (fst x)) == None). *)
(* Proof. *)
(*   move=> [i [r|]] //= Hin. *)
(*   case Heqe: (findIntervalUsePos (getInterval i) UsePos.regReq) *)
(*     => [[[rd r] [u H1 H2]]|] //=. *)

(* Lemma in_rem : forall (a : eqType) (y x : a) xs, *)
(*   y \in rem x xs -> x != y -> y \in xs. *)
(* Proof. *)
(*   move=> a y x. *)
(*   elim=> // [z zs IHzs] Hrem Hneq. *)
(*   rewrite in_cons. *)
(*   apply/orP. *)
(*   case Heq: (y == z). *)
(*     by left. *)
(*   right. *)
(*   apply: IHzs; last by []. *)
(*   have: y != z. *)
(*     apply/eqP. *)
(*     by move/eqP in Heq. *)
(*   by []. *)
(* Qed. *)

(* Lemma no_overlapping_intervals `(st : ScanState sd) : forall x y, *)
(*   x \in active sd -> y \in inactive sd -> *)
(*     ~~ (intervalsIntersect (getInterval (fst x)) *)
(*                            (getInterval (fst y))). *)
(* Proof. *)
(*   move=> x y Hinx Hiny. *)
(*   ScanState_cases (induction st) Case; simpl in *. *)
(*   - Case "ScanState_nil". by []. *)
(*   - Case "ScanState_newUnhandled". *)
(*     have Hinx' := Hinx. *)
(*     move: Hinx' => /mapP. case=> x0 _ Heqx. *)
(*     have Hiny' := Hiny. *)
(*     move: Hiny' => /mapP. case=> y0 _ Heqy. *)
(*     subst. *)
(*     rewrite !vnth_vshiftin. *)
(*     move: Hinx Hiny. *)
(*     rewrite !mem_map. *)
(*     - exact: IHst. *)
(*     - exact: widen_fst_inj. *)
(*     - exact: widen_fst_inj. *)
(*   - Case "ScanState_newHandled". by []. *)
(*   - Case "ScanState_setInterval". by []. *)
(*   - Case "ScanState_setFixedIntervals". exact: IHst. *)
(*   - Case "ScanState_moveUnhandledToActive". by []. *)
(*   - Case "ScanState_moveActiveToInactive". *)
(*     apply: IHst. *)
(*     + case Heqe: (x == x0). *)
(*         by move/eqP: Heqe => ->. *)
(*       apply: (in_rem (y:=x) (x:=x0)). *)
(*         by []. *)
(*       apply: neq_sym. *)
(*       move/eqP in Heqe. *)
(*       by apply/eqP. *)
(*     + by []. *)
(*   - Case "ScanState_moveActiveToHandled". by []. *)
(*   - Case "ScanState_moveInactiveToActive". by []. *)
(*   - Case "ScanState_moveInactiveToHandled". by []. *)
(* Qed. *)

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
