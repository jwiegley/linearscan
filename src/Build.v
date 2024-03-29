Set Warnings "-notation-overridden".

Require Import LinearScan.Lib.
Require Import LinearScan.UsePos.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Morph.
Require Import LinearScan.ScanState.
Require Import LinearScan.Loops.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Build.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg opType1 opType2.

Definition BuildState (b : nat) := IntMap (SortedRanges b.*2.+1).

Definition newBuildState {n} : BuildState n := emptyIntMap.

Definition PendingRanges b e := NonEmpty (BoundedRange b.*2.+1 e.*2.+1).

Definition emptyPendingRanges (b e : nat) (H : b < e) (liveOuts : IntSet) :
  IntMap (PendingRanges b e).
Proof.
  have Hsz : b.*2.+1 < e.*2.+1 by undoubled.
  have empty  := emptyBoundedRange Hsz.
  have f xs vid := IntMap_insert (vid + maxReg) [::: empty] xs.
  exact (IntSet_foldl f emptyIntMap liveOuts).
Defined.

(* We sort ascending in order of range end, with smaller ranges occurring
   after larger ones. *)
Definition BoundedRange_leq {b e} (x y : BoundedRange b.*2.+1 e.*2.+1) : bool.
Proof.
  move: x => [[x _] _].
  move: y => [[y _] _].
  case: (rend x == rend y).
    exact: (rbeg x <= rbeg y).
  exact: (rend x <= rend y).
Defined.

Program Instance BoundedRange_leq_trans {b e} :
  Transitive (@BoundedRange_leq b e).
Obligation 1.
  rewrite /BoundedRange_leq /= in H H0 *.
  destruct x; destruct y; destruct z.
  destruct x; destruct x1; destruct i.
  destruct x0; destruct i0.
  case E1: (rend x == rend x0) in H H0 *;
  case E2: (rend x0 == rend x1) in H H0 *;
  case E3: (rend x1 == rend x) in H H0 *;
  case E4: (rend x == rend x1) in H H0 *;
  move/eqP in E1;
  move/eqP in E2;
  move/eqP in E3;
  move/eqP in E4;
  by ordered.
Qed.

Lemma BoundedRange_leq_antisym {b e} : forall x y,
  ~~ (@BoundedRange_leq b e) y x -> (@BoundedRange_leq b e) x y.
Proof.
  move=> x y Hneg.
  rewrite /BoundedRange_leq /= in Hneg *.
  destruct x; destruct y.
  destruct x; destruct x0.
  case E1: (rend x == rend x0) in Hneg *;
  case E2: (rend x0 == rend x) in Hneg *;
  move/eqP in E1;
  move/eqP in E2;
  by ordered.
Qed.

Definition compilePendingRanges {b e} (Hlt : b < e)
  (ranges : seq (BoundedRange b.*2.+1 e.*2.+1))
  (H : StronglySorted BoundedRange_leq ranges) :
  { rs : SortedRanges b.*2.+1
  | last b.*2.+1 [seq rend r.1 | r <- rs.1] <= e.*2.+1
  & if ranges is _ :: _
    then if rs.1 is r' :: _
         then { H : 0 < size ranges
              | rend (safe_hd ranges H).1.1 <= rend r'.1 }
         else False
    else True}.
Proof.
  elim: ranges => [|r1 rs IHrs] in H *.
    apply: exist2 _ _ (exist2 _ _ [::] _ _) _ _.
    - by constructor.
    - by [].
    - by undoubled.
    - intros; exact: I.

  destruct rs as [|r2 rs2] eqn:R2.
    apply: exist2 _ _ (exist2 _ _ [:: r1.1] _ _) _ _.
    - by constructor; constructor.
    - clear -r1.
      case: r1 => [H1 H2] /=.
      by ordered.
    - clear -r1.
      case: r1 => [H1 H2] /=.
      by ordered.
    - by exists (ltn0Sn _).

  have Hconn : rend r1.1.1 <= rend r2.1.1.
    inv H; inv H2; inv H3.
    rewrite /BoundedRange_leq /= in H2.
    destruct r1; destruct x;
    destruct r2; destruct x0; simpl.
    case E: (rend x == rend x0) => // in H2 *.
    by move/eqP in E; rewrite {}E.

  apply StronglySorted_inv in H.
  move: H => [Hs Hf].
  specialize (IHrs Hs).
  case: IHrs => [[[|r2' rs2'] H2a H2b] /= H3 H4] in Hs *;
    first by [].

  (* Owing to the way the list is sorted, this is the only check we need for
     intersection and adjacency. *)
  case E: (range_ltn r1.1 r2').
    rewrite /=.
    apply: exist2 _ _ (exist2 _ _ [:: r1.1, r2' & rs2'] _ _) _ _.
    - constructor.
        exact: H2a.
      constructor.
        exact: E.
      inv H2a.
      exact/(Forall_ordered E).
    - clear -r1.
      case: r1 => [H1 H2] /=.
      by ordered.
    - by [].
    - by exists (ltn0Sn _).

  move: r1 => [[rd1 r1] Hr1] /= in Hs Hf Hconn E *.
  move: r2' => [rd2' r2'] /= in Hs Hf E R2 H2a H2b H3 H4 *.

  (* Otherwise, if the ranges are directly adjacent, or intersect, coalesce
     them into a single range. *)
  apply: exist2 _ _
    (exist2 _ _ [:: packRange (Range_merge r1 r2') & rs2'] _ _) _ _.

  (* Prove that sorting over range_ltn has been established. *)
  rewrite /range_ltn /= in E *.
  constructor.
    by inv H2a.
  induction rs2' as [|r3 rs3 IHrs3].
    by constructor.
  rewrite /=.
  have Hmax: maxn (rend rd1) (rend rd2') < rbeg r3.1.
    inv Hf.
    clear -Hs H2a H4 Hconn.
    inv H2a; inv H4; inv H1; inv H2.
    rewrite gtn_max.
    rewrite /range_ltn /= in H3.
    by ordered.
  constructor=> //.
  apply IHrs3.
  constructor=> //.
    by inv H2a; inv H1.
  by inv H2a; inv H2.

  rewrite /= in H3 *.
  apply: (last_leq H3).
  rewrite gtn_max in Hmax.
  apply/ltnW.
  move: (Range_bounded r3.2).
  by ordered.

  (* Return a witness to an ordering property [rend rd1 <= maxn (rend rd1)
     (rend rd2')], which makes induction much easier. *)
  rewrite /=.
  rewrite leq_min.
  by ordered.

  rewrite /=.
  intros.
  apply: (last_leq H3).
  rewrite geq_max.
  inv H4.
  by ordered.

  rewrite /=.
  exists (ltn0Sn _).
  rewrite leq_max.
  by apply/orP; left.
Defined.

Program Fixpoint rangesToBoundedRanges {b e} (y : RangeSig) (ys : seq RangeSig)
  (H1 : StronglySorted range_ltn (y :: ys)) (H2 : b.*2.+1 <= rbeg y.1)
  (Hbound : last (rend y.1) [seq rend r.1 | r <- ys] <= e.*2.+1) :
  NonEmpty (BoundedRange b.*2.+1 e.*2.+1) :=
  match ys with
  | nil => NE_Sing y
  | cons z zs =>
      NE_Cons y (@rangesToBoundedRanges b e z zs _ _ _)
  end.
Next Obligation.
  rewrite /= in Hbound.
  by ordered.
Qed.
Next Obligation.
  apply/andP; split=> //.
  apply StronglySorted_impl_cons in H1;
    last exact: range_ltn_trans.
  move: H1 Hbound.
  rewrite [(z; H)]lock.
  rewrite /range_ltn map_comp (last_map rend) /= last_map -lock /=.
  move: (Range_bounded (last (z; H) zs).2).
  case: zs => //= [|w ws].
  by ordered.
  move=> H3 H4 H5.
  apply/(leq_trans _ H5).
  apply/(leq_trans _ H3).
  apply/ltnW.
  by ordered.
Qed.
Next Obligation.
  by inv H1.
Qed.
Next Obligation.
  inv H1; inv H6.
  rewrite /range_ltn /= in H4.
  move: (Range_bounded H0).
  by ordered.
Qed.

Definition compressPendingRanges `(ranges : PendingRanges b e) (H : b < e) :
  PendingRanges b e.
Proof.
  case: ranges => [r|r rs].
    exact: [::: r].
  pose Hsort := sortBy_sorted [::: r & rs] BoundedRange_leq_antisym.
  specialize (Hsort BoundedRange_leq_trans).
  rewrite NE_to_list_from_list /= in Hsort.
  move: (compilePendingRanges H Hsort) => [[srs1 H1 H2] Hbound /= H3].
  clear -srs1 H1 H2 H3 Hbound.
  case E: (insert BoundedRange_leq r (sortBy BoundedRange_leq rs))
    => [|x xs] in H3 *.
    move: E.
    set xs := insert _ _ _.
    move=> E.
    have E1 : size xs = size [::] by rewrite E.
    by rewrite insert_size /= in E1.
  destruct srs1 as [|y ys]; simpl in *.
    contradiction H3.
  exact: (rangesToBoundedRanges H1 H2 Hbound).
Defined.

Definition mergeIntoSortedRanges `(H : b < e)
  (pmap : IntMap (PendingRanges b e)) (rmap : IntMap (SortedRanges e.*2.+1)) :
  IntMap (SortedRanges b.*2.+1).
Proof.
  apply: (IntMap_mergeWithKey _ _ _ pmap rmap).
  - (* The combining function, when entries are present in both maps. *)
    move=> _ brs srs2.
    pose Hsort := sortBy_sorted brs BoundedRange_leq_antisym.
    specialize (Hsort BoundedRange_leq_trans).
    move: (compilePendingRanges H Hsort) => [[srs1 ? ?] Hbound _].
    exact: Some (SortedRanges_cat srs2 Hbound).

  - (* When no rmap entry are present. *)
    apply: IntMap_map _.
    move=> brs.
    pose Hsort := sortBy_sorted brs BoundedRange_leq_antisym.
    specialize (Hsort BoundedRange_leq_trans).
    move: (compilePendingRanges H Hsort) => [srs1 _ _].
    exact: srs1.

  - (* When no pmap entry is present. *)
    move=> sr.
    have H': b.*2.+1 <= e.*2.+1 by undoubled.
    exact: IntMap_map (transportSortedRanges H') sr.
Defined.

Definition upos_before_rend `(r : Range rd) (upos : UsePos) :=
  if ups rd is u :: _
  then upos <= u
  else upos <  rend rd.
Arguments upos_before_rend [rd] r upos /.

Lemma validUsePosition `(r : Range rd) (upos : UsePos)
  (Hbeg : rbeg rd <= upos) (Hend : upos_before_rend r upos) :
  [/\ validRangeBounds (rbeg rd) (rend rd) (upos :: ups rd)
  &   StronglySorted upos_le (upos :: ups rd)].
Proof.
  rewrite /= in Hend.
  split.
    move: (Range_proper r).
    move/andP=> [H1 H2] /=.
    do 3 (apply/andP; split => //).
    case: (ups rd) => //= [u us] in Hend H2 *.
    case: (uvar upos) => // in Hend *;
    case: (uvar u) => //= in Hend H2 *;
    case E: (uloc u == rend rd) => // in Hend *;
    try move/leq_eqF in E;
    by ordered.
  move: (Range_sorted r) => Hsorted.
  constructor=> // {Hbeg}.
  case: (ups rd) => /= [|u us] in Hend Hsorted *.
    by constructor.
  case: (uvar upos) => // in Hend *;
  try case: (uvar u) => //= in Hend *;
  constructor=> //;
  inv Hsorted;
  case: (uloc u == rend rd) => // in Hend;
  try exact/ltnW;
  try exact: Forall_ordered;
  try move/ltnW in Hend;
  apply: Forall_ordered; rewrite /upos_le;
  try exact Hend; auto.
Defined.

Definition makeNewRange {b pos e} (H : b <= pos < e) (upos : UsePos)
  (Heqe : uloc upos == if uvar upos is Input
                       then pos.*2.+1
                       else pos.*2.+2) :
  BoundedRange b.*2.+1 e.*2.+1.
Proof.
  (* If the variable is only [Input], assume it starts from the beginning; and
     if [Output], that it persists until the end.  Only [Temp] variables are
     handled using a single-instruction range. *)
  pose rd :=
    {| rbeg := if (uvar upos == Input) || (uvar upos == InputOutput)
               then b.*2.+1
               else pos.*2.+2
     ; rend := match uvar upos with
               | Input       => pos.*2.+2
               | Temp        => pos.*2.+3
               | InputOutput => e.*2.+1
               | Output      => e.*2.+1
               end
     ; ups  := [:: upos ] |}.

  apply: ((rd; _); _).
    constructor=> /=.
    + case E: (uvar upos) in Heqe rd *;
      move/eqP in Heqe; rewrite {}Heqe;
      try undoubled;
      breakup; try undoubled;
      simpl in *;
      try apply/ltn_addn1;
      rewrite -?doubleS ?ltn_Sdouble;
      try undoubled.
      rewrite doubleS.
      apply ltnW.
      apply ltn_addn1.
      by undoubled.
    + by constructor; constructor.

  rewrite /= => r.
  case: (uvar upos).
  + case U: (pos.*2.+1 == pos.*2.+2).
      move/eqP in U.
      by ordered.
    by undoubled.
  (* jww (2015-08-29): Remove this repetition. *)
  + clear r rd Heqe.
    apply/andP; split;
    rewrite -?doubleS ?ltn_Sdouble;
    by undoubled.
  + clear r rd Heqe.
    apply/andP; split;
    rewrite -?doubleS ?ltn_Sdouble;
    simpl in *;
    try undoubled.
    rewrite doubleS.
    apply ltnW.
    apply ltn_addn1.
    by undoubled.
  + clear r rd Heqe.
    simpl in *.
    apply/andP; split;
    rewrite -?doubleS ?ltn_Sdouble;
    try undoubled.
    rewrite doubleS.
    apply ltnW.
    apply ltn_addn1.
    by undoubled.
Defined.

Definition makeUsePos (pos : nat) (var : VarInfo maxReg) :
  { u : UsePos | uloc u == if uvar u is Input
                           then pos.*2.+1
                           else pos.*2.+2 }.
Proof.
  set upos := {| uloc   := if varKind var is Input
                           then pos.*2.+1
                           else pos.*2.+2
               ; regReq := regRequired var
               ; uvar   := varKind var |}.
  exists upos;
  rewrite /upos;
  case: (varKind var) => //=;
  by rewrite /= odd_double.
Defined.

(* This is the most complex of the variable handling functions, because under
   certain circumstances we need to insert the variable into an existing range
   rather than just create a new range each time, as we do for inputs and
   temporaries. *)
Definition handleOutputVar {b pos e} (H : b <= pos < e)
  (range : option (PendingRanges b e)) (var : VarInfo maxReg) :
  option (PendingRanges b e).
Proof.
  move: (makeUsePos pos var) => [upos Heqe].

  (* If no range exists yet, make a new one that extends from [pos] to [e]. *)
  case: range => [range|]; last first.
    exact (Some [::: makeNewRange H Heqe]).

  (* If [pos] fits within the current range, use it; otherwise, shift the
     beginning of the current range down to [pos] so that our use position may
     fit within it. The boolean value is true if we are to replace the
     beginning of the range list with the new range, and false if we are to
     prepend it only. *)
  have res : (bool * { r1 : RangeSig | (b.*2.+1 <= rbeg r1.1 <= upos) &&
                                       (rend r1.1 <= e.*2.+1) })%type.
    move: (NE_head range) => [r /andP [Hbeg Hend]].
    case E: (upos < head_or_end r.1).
      case: (ups r.1) => /= [|[loc req kind] us].
        split. exact true.
        pose r1 := Range_shift r.2 E.
        have Hr1: r1 = Range_shift r.2 E by [].
        exists r1.
        move: (Range_shift_spec Hr1) => [-> -> _].
        move/eqP: Heqe => ->.
        case: (uvar upos);
        rewrite -?doubleS;
        try undoubled.
          move/andP in H.
          destruct H.
          apply/andP; split.
            apply/andP; split.
              rewrite doubleS.
              apply ltnW.
              apply ltn_addn1.
              by undoubled.
            by undoubled.
          by undoubled.
          apply/andP; split.
            apply/andP; split.
              rewrite doubleS.
              apply ltnW.
              apply ltn_addn1.
              by undoubled.
            by undoubled.
          by undoubled.
          apply/andP; split.
            apply/andP; split.
              rewrite doubleS.
              apply ltnW.
              apply ltn_addn1.
              by undoubled.
            by undoubled.
          by undoubled.
      (* Is the use position at the beginning of the range output only? If so,
         then we can allow a lifetime hole between the current position and
         the beginning of that range. *)
      case: (kind == Output).
        split. exact false.
        have H0 : b <= pos < pos.+1 by ordered.
        pose NR := makeNewRange H0 Heqe.
        exists NR.1.
        rewrite /= {NR}.
        move/eqP: Heqe => ->.
        case: (uvar upos) => /=;
        rewrite -?doubleS;
        try undoubled.
          move/andP in H0.
          destruct H0.
          apply/andP; split.
            apply/andP; split.
              by undoubled.
            rewrite doubleS.
            apply ltnW.
            apply ltn_addn1.
            by undoubled.
          by undoubled.
          apply/andP; split.
            apply/andP; split.
              rewrite doubleS.
              apply ltnW.
              apply ltn_addn1.
              by undoubled.
            by undoubled.
          by undoubled.
          apply/andP; split.
            apply/andP; split.
              rewrite doubleS.
              apply ltnW.
              apply ltn_addn1.
              by undoubled.
            by undoubled.
          by undoubled.
      split. exact true.
      pose r1 := Range_shift r.2 E.
      have Hr1: r1 = Range_shift r.2 E by [].
      exists r1.
      move: (Range_shift_spec Hr1) => [-> -> _].
      move/eqP: Heqe => ->.
      case: (uvar upos);
      rewrite -?doubleS;
      try undoubled.
        move/andP in H.
        destruct H.
        apply/andP; split.
          apply/andP; split.
            rewrite doubleS.
            apply ltnW.
            apply ltn_addn1.
            by undoubled.
          by undoubled.
        by undoubled.
        apply/andP; split.
          apply/andP; split.
            rewrite doubleS.
            apply ltnW.
            apply ltn_addn1.
            by undoubled.
          by undoubled.
        by undoubled.
        apply/andP; split.
          apply/andP; split.
            rewrite doubleS.
            apply ltnW.
            apply ltn_addn1.
            by undoubled.
          by undoubled.
        by undoubled.
    split. exact true.
    move/negbT in E; rewrite -ltnNge /= in E.
    exists r.
    move: (Range_proper r.2) => /=.
    by case: (ups r.1) => [|? ?] /= in E *; ordered.
  move: res => [replaceFirst [r1 /andP [/andP [? Hbeg2] ?]]].

  (* Check whether our use position actually fits within the end of the
     current range, after shifting.  If not, ignore the current range and just
     create a new one.  At the step where we combine the pending ranges, any
     intersecting ranges will be coalesced. *)
  case Hupos : (upos_before_rend r1.2 upos); last first.
    exact: Some [::: makeNewRange H Heqe & range].

  (* We have a valid range to put the use position in; derive this fact from
     what we know so far, and then cons our use position onto the front of the
     existing range. *)
  move: (validUsePosition Hbeg2 Hupos) => [Hloc Hsorted].

  case: replaceFirst.
    have br : BoundedRange b.*2.+1 e.*2.+1.
      exists (Range_cons r1.2 Hloc Hsorted).
      by rewrite /=; ordered.
    case: range => [_|_ rs].
      exact: Some [::: br].
    exact: Some [::: br & rs].
  have br : BoundedRange b.*2.+1 e.*2.+1.
    exists r1.
    by ordered.
  exact: Some [::: br & range].
Defined.

Definition handleVar {b pos e} (H : b <= pos < e)
  (range : option (PendingRanges b e)) (var : VarInfo maxReg) :
  option (PendingRanges b e).
Proof.
  move: (makeUsePos pos var) => [? Heqe].
  case: range => [range|].
    exact: Some [::: makeNewRange H Heqe & range].
  exact: Some [::: makeNewRange H Heqe].
Defined.

Definition handleVars_combine {b pos e} (H : b <= pos < e) (vid : nat)
  (vars : seq (VarInfo maxReg)) (c1 : PendingRanges b e) :
  option (PendingRanges b e).
Proof.
  have Hlt : b < e by ordered.
  have c2 := compressPendingRanges c1 Hlt.
  have c3 := foldl (handleOutputVar H) (Some c2)
                   (filter (fun k => varKind k == Output) vars).
  have c4 := foldl (handleVar H) c3
                   (filter (fun k => varKind k != Output) vars).
  exact: c4.
Defined.

(* If there is no variable reference at this position, do nothing. *)
Definition handleVars_onlyRanges {b pos e} (H : b <= pos < e) :
  IntMap (PendingRanges b e) -> IntMap (PendingRanges b e).
Proof. exact. Defined.

(* If a variable referenced for which no reservation was made (for example, an
   input variable that is not used as an output later in the block), we simply
   add it. *)
Definition handleVars_onlyVars {b pos e} (H : b <= pos < e) :
  IntMap (seq (VarInfo maxReg)) -> IntMap (PendingRanges b e).
Proof.
  apply: IntMap_foldlWithKey _ emptyIntMap => m vid vars.
  have c2 := foldl (handleOutputVar H) None
                   (filter (fun k => varKind k == Output) vars).
  have c3 := foldl (handleVar H) c2
                   (filter (fun k => varKind k != Output) vars).
  case: c3 => [c3|].
    exact: IntMap_insert vid c3 m.
  exact: m.
Defined.

Definition handleVars
  (varRefs : seq (VarInfo maxReg)) `(Hlt : b <= pos < e)
  `(ranges : IntMap (PendingRanges b e)) : IntMap (PendingRanges b e) :=
  let vars := IntMap_map NE_to_list $
              IntMap_groupOn (@nat_of_varId maxReg) varRefs in
  IntMap_mergeWithKey (handleVars_combine Hlt) (handleVars_onlyVars Hlt)
                      (handleVars_onlyRanges Hlt) vars ranges.

Definition reduceOp {b pos e} (block : blockType1) (op : opType1)
  (ranges : IntMap (PendingRanges b e)) (Hlt : b <= pos < e) :
  IntMap (PendingRanges b e) :=
  (* If the operation is a function call, force a flush of every register.

     jww (2015-01-30): This needs to be improved to consider the calling
     convention of the operation. *)
  let refs  := opRefs oinfo op in
  let refs' :=
    if opKind oinfo op is IsCall
    then
      (* Although every register should be dropped, some architectures
         actually pass the address they wish to call to in a variable.  Since
         this is only an input variable, it's OK to allocate it up to the
         call, since we needn't assume it will contain a value after the
         call.  *)
      let regsNeeded :=
          count (fun r => match varId r with
                          | inl _ => false
                          | inr _ => true
                          end) refs in
      drop regsNeeded
           (filter (fun x => varId x \notin map (@varId maxReg) refs)
                   [seq {| varId       := inl n
                           ; varKind     := Temp
                           ; regRequired := true
                        |} | n in ord_enum maxReg]) ++ refs
    else refs in

  handleVars refs' Hlt ranges.

Lemma leq_plus : forall m n, m <= m + n.
Proof. elim=> [|m IHm] //=. Qed.

Lemma ltn_plus : forall m n, 0 < n -> m < m + n.
Proof. elim=> [|m IHm] //=. Qed.

Definition reduceBlock {pos} (bid : BlockId) (block : blockType1)
  (Hsz : 0 < blockSize binfo block)
  (loops : LoopState) (varUses : IntMap IntSet) :
  let sz := blockSize binfo block in
  let b := pos in
  let e := pos + sz in
  IntMap (PendingRanges b e) -> IntMap (PendingRanges b e).
Proof.
  move=> sz b e.
  rewrite /sz /blockSize.
  set ops := allBlockOps binfo block.

  have Hlt : pos <= (pos + sz).-1 < pos + sz.
    apply/andP; split.
      by rewrite -subn1 -addnBA // leq_plus //.
    rewrite prednK.
      by ordered.
    rewrite addn_gt0.
    by apply/orP; right.

  (* If the current block is a loop end block, insert an [Input] pseudo-use
     position at the very end of the block for every variable which was
     referenced within that loop.  This causes the allocation algorithm to
     split other intervals first before those used by the loop. *)
  move=> ranges.
  have :=
    if ~~ IntSet_member bid (loopEndBlocks loops) then ranges else
    let f acc loopIndex blks :=
      if ~~ IntSet_member bid blks then acc else
      if IntMap_lookup loopIndex varUses isn't Some uses then acc else
      IntSet_union acc uses in
    let uses := IntMap_foldlWithKey f emptyIntSet (loopIndices loops) in
    handleVars [seq {| varId       := inr u
                     ; varKind     := Input
                     ; regRequired := false |}
               | u <- IntSet_toList uses] Hlt ranges.
  clear ranges.

  have H : 0 < size ops -> b < pos + (size ops) <= e.
    rewrite /b /e /sz /blockSize.
    replace (allBlockOps binfo block) with ops; last by [].
    move=> ?.
    apply/andP; split=> //.
    exact: ltn_plus.
  elim/last_ind E: ops => [|os o IHos] /= in H *.
    by [].
  move=> ranges.

  have H1 : b <= pos + (size os) < e.
    rewrite size_rcons in H.
    have: 0 < (size os).+1 by [].
    move/H=> /andP [H2 H3].
    apply/andP; split.
      exact: leq_plus.
    by rewrite addnS in H3.
  move: (reduceOp block o ranges H1).

  have: 0 < size os -> b < pos + size os <= e.
    move=> ?.
    apply/andP; split.
      exact: ltn_plus.
    move/andP: H1 => [_ ?].
    exact/ltnW.
  exact: IHos.
Defined.

Definition reduceBlocks (blocks : seq blockType1) (loops : LoopState)
  (varUses : IntMap IntSet) (liveSets : IntMap BlockLiveSets) {pos} :
  BuildState pos.
Proof.
  elim: blocks => [|b blocks IHbs] in pos *.
    exact: newBuildState.

  pose sz := blockSize binfo b.
  case E: (0 < sz);
    last exact: IHbs pos.

  have Hsz : pos < pos + sz by exact: ltn_plus.

  have bid := blockId binfo b.
  have outs := if IntMap_lookup bid liveSets is Some ls
               then blockLiveOut ls
               else emptyIntSet.
  have ranges := emptyPendingRanges Hsz outs.
  have pending := reduceBlock bid E loops varUses ranges.
  exact: mergeIntoSortedRanges Hsz pending (IHbs (pos + sz)).
Defined.

Definition compileIntervals `(bs : BuildState pos) :
  (* Return the set of fixed intervals, and the set of variable intervals,
     respectively. *)
  FixedIntervalsType maxReg * IntMap IntervalSig.
Proof.
  apply: IntMap_foldlWithKey _ (vconst None, emptyIntMap) bs.
  move=> [regs vars] vid rs.
  case E: rs.1 => [|? ?];
    first by exact: (regs, vars).
  case V: (vid < maxReg).
    simpl in E.
    move: (Interval_fromRanges vid E) => /= i.
    exact: (vreplace regs (Ordinal V) (Some (packInterval i)), vars).
  have vid' := vid - maxReg.
  move: (Interval_fromRanges vid' E) => /= i.
  exact: (regs, IntMap_insert vid' (packInterval i) vars).
Defined.

Definition buildIntervals (blocks : seq blockType1) (loops : LoopState)
  (liveSets : IntMap BlockLiveSets) : ScanStateSig maxReg InUse :=
  let add_unhandled_interval (ss  : ScanStateSig maxReg Pending) i :=
        packScanState (ScanState_newUnhandled ss.2 i.2 I) in
  let s0 := ScanState_nil maxReg in
  if blocks isn't b :: bs
  then packScanState (ScanState_finalize s0)
  else
    let varUses := computeVarReferences binfo oinfo (b :: bs) loops in
    let reduced := reduceBlocks (pos:=0) (b :: bs) loops varUses liveSets in
    let: (regs, vars) := compileIntervals reduced in
    let s1 := ScanState_setFixedIntervals s0 regs in
    let s2 := packScanState s1 in
    let s3 := IntMap_foldl add_unhandled_interval s2 vars in
    let s4 := ScanState_finalize s3.2 in
    packScanState s4.

End Build.
