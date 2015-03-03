Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Morph.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Build.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

Definition BuildState (b : nat) := IntMap (SortedRanges b.*2.+1).

Definition newBuildState {n} : BuildState n := emptyIntMap.

Definition PendingRanges b e := NonEmpty (BoundedRange b.*2.+1 e.*2.+1).

Definition emptyPendingRanges (b e : nat) (H : b < e) (liveOuts : IntSet) :
  IntMap (PendingRanges b e).
Proof.
  have Hsz : b.*2.+1 < e.*2.+1 by undoubled.
  have empty  := emptyBoundedRange Hsz (odd_double_plus _).
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

Definition compilePendingRanges {b e}
  (ranges : seq (BoundedRange b.*2.+1 e.*2.+1))
  (H : StronglySorted BoundedRange_leq ranges) :
  { rs : seq (BoundedRange b.*2.+1 e.*2.+1)
  | StronglySorted range_ltn [seq r.1 | r <- rs]
  & if ranges is _ :: _
    then if rs is r' :: _
         then { H : 0 < size ranges
              | rend (safe_hd ranges H).1.1 <= rend r'.1.1 }
         else False
    else True}.
Proof.
  elim: ranges => [|r1 rs IHrs] in H *.
    exists [::].
      by constructor.
    exact: I.

  destruct rs as [|r2 rs2] eqn:R2.
    exists [:: r1].
      by constructor; constructor.
    by exists (ltn0Sn _).

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
  case: IHrs => [[|r2' rs2'] H2 H3] in Hs *;
    first by [].

  (* Owing to the way the list is sorted, this is the only check we need for
     overlap and adjacency. *)
  case E: (range_ltn r1.1 r2'.1).
    rewrite /=.
    exists [:: r1, r2' & rs2'].
    constructor.
      exact: H2.
    constructor.
      exact: E.
    inv H2.
    exact/(Forall_ordered E).
    by exists (ltn0Sn _).

  move: r1 => [[rd1 r1] Hr1] /= in Hs Hf Hconn E *.
  move: r2' => [[rd2' r2'] Hr2] /= in Hs Hf E R2 H2 H3 *.

  (* Otherwise, if the ranges are directly adjacent, or overlap, coalesce them
     into a single range. *)
  apply: exist2 _ _ [:: _ & rs2'] _ _.
  apply: exist _ _ _.
  apply: packRange (Range_merge r1 r2' _).
    rewrite /range_ltn /= in E.
    by move/negbT in E; rewrite -leqNgt in E.
  rewrite /=.
  clear -Hr1 Hr2.
  rewrite leq_min.
  rewrite geq_max.
  by ordered.

  (* Prove that sorting over range_ltn has been established. *)
  rewrite /range_ltn /= in H2 E *.
  constructor.
    by inv H2.
  induction rs2' as [|r3 rs3 IHrs3].
    by constructor.
  rewrite /=.
  have Hmax: maxn (rend rd1) (rend rd2') < rbeg r3.1.1.
    inv Hf.
    clear -Hs H2 H3 Hconn.
    inv H2; inv H3; inv H1; inv H4.
    rewrite gtn_max.
    by ordered.
  constructor=> //.
  apply IHrs3.
  constructor=> //.
    by inv H2; inv H1.
  by inv H2; inv H4.

  (* Return a witness to an ordering property [rend rd1 <= maxn (rend rd1)
     (rend rd2')], which makes induction much easier. *)
  rewrite /=.
  exists (ltn0Sn _).
  rewrite leq_max.
  by apply/orP; left.
Defined.

Definition mergeIntoSortedRanges `(H : b <= e)
  (pmap : IntMap (PendingRanges b e)) (rmap : IntMap (SortedRanges e.*2.+1)) :
  IntMap (SortedRanges b.*2.+1).
Proof.
  apply: (IntMap_mergeWithKey _ _ _ pmap rmap).
  - (* The combining function, when entries are present in both maps. *)
    move=> _ brs sr.

(*
    have H0: b.*2.+1 <= b.*2.+1 <= rbeg br.1.1.
      move: (Range_proper br.1.2).
      move: br => [r Hr] /=.
      by case: (ups r.1); ordered.
    pose ps' := prependRange ranges H0.
    move: ps' => [ps' spec].
    clear H0.
    apply: (Some (@SortedRanges_cat _ ps' _ sr _)) => /=.
    move: br => [r Hlt] in ps' spec *.
    have H4: rend r.1 <= mid.*2.+1.
      have Hlt' := Hlt.
      by ordered.
    have H5: b.*2.+1 <= rend r.1.
      have Hlt' := Hlt.
      move: (Range_proper r.2) => Hrp.
      rewrite /validRangeBounds in Hrp.
      case: (ups r.1) => [|u us] /= in Hrp *.
        by ordered.
      by case: (uvar u) in Hrp *; ordered.
    have p := last_leq Hend H4.
    rewrite -2!last_map -map_comp in spec.
    rewrite spec /= in p.
    rewrite -2!last_map -map_comp in p.
    exact: (last_leq p H5).
*)
    admit.

  - (* When no rmap entry are present. *)
    apply: IntMap_map _.
(*
    have H0: b.*2.+1 <= b.*2.+1 <= rbeg br.1.1.
      move: (Range_proper br.1.2).
      move: br => [r ?] /=.
      by case: (ups r.1); ordered.
    exact: (prependRange ranges H0).1.
*)
    admit.

  - (* When no pmap entry is present. *)
    move=> sr.
    have H': b.*2.+1 <= e.*2.+1 by undoubled.
    exact: IntMap_map (transportSortedRanges H') sr.
Defined.

Definition upos_before_rend `(r : Range rd) (upos : UsePos) :=
  if ups rd is u :: _
  then if (uvar upos != Input) && (uloc u == rend rd)
       then upos <  u
       else upos <= u
  else if uvar upos is Input
       then upos <= rend rd
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
    case: (ups rd) => [|u us] /= in Hend *;
    case: (uvar upos) => // in Hend *;
    try case: (uvar u) => //= in Hend *;
    try case E: (uloc u == rend rd) => // in Hend *;
    try move/andP => [/andP [? H] ?];
    try move/(leq_eqF E) in H;
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
  move/ltnW in Hend;
  exact: Forall_ordered.
Defined.

Definition makeNewRange {b pos e} (H : b <= pos < e)
  (upos : UsePos) (Hodd : odd upos) (Heqe : uloc upos == pos.*2.+1) :
  BoundedRange b.*2.+1 e.*2.+1.
Proof.
  (* If the variable is only [Input], assume it starts from the beginning; and
     if [Output], that it persists until the end.  Only [Temp] variables are
     handled using a single-instruction range. *)
  pose rd :=
    {| rbeg := if uvar upos is Input
               then b.*2.+1
               else pos.*2.+1
     ; rend := match uvar upos with
               | Input  => pos.*2.+1
               | Temp   => pos.*2.+2
               | Output => e.*2.+1
               end
     ; ups  := [:: upos ] |}.

  apply: exist _ _ _.
  apply: exist _ _ _.
   exact: rd.
   constructor=> /=.
   + move/eqP in Heqe; rewrite {}Heqe.
     case: (uvar upos) in rd *;
     by undoubled.
   + by constructor; constructor.
   + by case: (uvar upos); exact: odd_double_plus.
   + by apply/andP; split.

  rewrite /=.
  case: (uvar upos).
  + case U: (pos.*2.+1 == pos.*2.+2).
      move/eqP in U.
      by ordered.
    by undoubled.
  + by undoubled.
  + by undoubled.
Defined.

Definition makeUsePos (pos : nat) (var : VarInfo maxReg) :
  { u : UsePos | uloc u == pos.*2.+1 & odd u }.
Proof.
  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired var
               ; uvar   := varKind var |}.
  have Hodd : odd upos by rewrite /= odd_double.
  by exists upos.
Defined.

(* This is the most complex of the variable handling functions, because under
   certain circumstances we need to insert the variable into an existing range
   rather than just create a new range each time, as we do for inputs and
   temporaries. *)
Definition handleOutputVar {b pos e} (H : b <= pos < e)
  (range : option (PendingRanges b e)) (var : VarInfo maxReg) :
  option (PendingRanges b e).
Proof.
  move: (makeUsePos pos var) => [upos Heqe Hodd].

  (* If no range exists yet, make a new one that extends from [pos] to [e]. *)
  case: range => [range|]; last first.
    exact: Some [::: makeNewRange H Hodd Heqe].

  (* If [pos] fits within the current range, use it; otherwise, shift the
     beginning of the current range down to [pos] so that our use position may
     fit within it. *)
  have res : { r1 : RangeSig | (b.*2.+1 <= rbeg r1.1 <= upos) &&
                               (rend r1.1 <= e.*2.+1) }.
    move: (NE_head range) => [r /andP [Hbeg Hend]].
    case E: (upos < rbeg r.1).
      pose r1 := Range_shift_down r.2 Hodd E.
      have Hr1: r1 = Range_shift_down r.2 Hodd E by [].
      exists r1.
      move: (Range_shift_down_spec Hr1) => [-> -> _].
      move/eqP: Heqe => ->.
      by undoubled.
    move/negbT in E; rewrite -ltnNge /= in E.
    exists r.
    by ordered.
  move: res => [r1 /andP [/andP [? Hbeg2] ?]].

  (* Check whether our use position actually fits within the end of the
     current range, after shifting.  If not, ignore the current range and just
     create a new one.  At the step where we combine the pending ranges, any
     overlapping ranges will be coalesced. *)
  case Hupos : (upos_before_rend r1.2 upos); last first.
    exact: Some [::: makeNewRange H Hodd Heqe & range].

  (* We have a valid range to put the use position in; derive this fact from
     what we know so far, and then cons our use position onto the front of the
     existing range. *)
  move: (validUsePosition Hbeg2 Hupos) => [Hloc Hsorted].
  have br : BoundedRange b.*2.+1 e.*2.+1.
    exists (Range_cons r1.2 Hloc Hsorted Hodd).
    by rewrite /=; ordered.

  case: range => [_|_ rs].
    exact: Some [::: br].
  exact: Some [::: br & rs].
Defined.

Definition handleVar {b pos e} (H : b <= pos < e)
  (range : option (PendingRanges b e)) (var : VarInfo maxReg) :
  option (PendingRanges b e).
Proof.
  move: (makeUsePos pos var) => [upos Heqe Hodd].
  case: range => [range|]; last first.
    exact: Some [::: makeNewRange H Hodd Heqe].
  exact: Some [::: makeNewRange H Hodd Heqe & range].
Defined.

Definition handleVars_combine {b pos e} (H : b <= pos < e) (vid : nat)
  (vars : seq (VarInfo maxReg)) (c1 : PendingRanges b e) :
  option (PendingRanges b e).
Proof.
  have c2 :=
    foldl (handleOutputVar H) (Some c1) [seq k <- vars | varKind k == Output].
  have c3 := foldl (handleVar H) c2 [seq k <- vars | varKind k != Output].
  exact: c3.
Defined.

(* If there is no variable reference at this position, do nothing. *)
Definition handleVars_onlyRanges {b pos e} (H : b <= pos < e) :
  IntMap (PendingRanges b e) -> IntMap (PendingRanges b e).
Proof. exact. Defined.

(* If a variable referenced for which no reservation was made (for example, an
   input variable that is not used as an output later in the block), we simply
   add it.

   jww (2015-03-01): Note that it should be provably impossible for an output
   variable to be seen here for the first time, unless it is not a member of
   the live out set. *)
Definition handleVars_onlyVars {b pos e} (H : b <= pos < e) (vid : nat) :
  IntMap (seq (VarInfo maxReg)) -> IntMap (PendingRanges b e).
Proof.
  apply: IntMap_foldl _ emptyIntMap => m vars.
  have c2 :=
    foldl (handleOutputVar H) None [seq k <- vars | varKind k == Output].
  have c3 := foldl (handleVar H) c2 [seq k <- vars | varKind k == Input].
  case: c3 => [c3|]; last first.
    exact: m.
  exact: IntMap_insert vid c3 m.
Defined.

Definition extractVarInfo (xs : NonEmpty (VarInfo maxReg)) :
  seq (VarInfo maxReg).
Proof.
  case: xs => [x|x xs].
    exact: [:: x].
  exact: (x :: xs).
Defined.

Program Definition handleVars
  (varRefs : seq (VarInfo maxReg)) `(Hlt : b <= pos < e)
  `(ranges : IntMap (PendingRanges b e)) : IntMap (PendingRanges b e) :=
  let vars := IntMap_map extractVarInfo $
              IntMap_groupOn (@nat_of_varId maxReg) varRefs in
  IntMap_mergeWithKey (handleVars_combine Hlt) (handleVars_onlyVars Hlt _)
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
         call.  jww (2015-02-18): This solution is WRONG. *)
      drop (size refs)
           [seq {| varId       := inl n
                 ; varKind     := Temp
                 ; regRequired := true
                 |} | n in ord_enum maxReg] ++ refs
    else refs in

  handleVars refs' Hlt ranges.

Definition reduceBlock {pos} (block : blockType1) :
  let sz := blockSize binfo block in
  let b := pos in
  let e := pos + sz in
  IntMap (PendingRanges b e) -> IntMap (PendingRanges b e).
Proof.
  move=> sz b e.
  rewrite /sz /blockSize.
  set ops := allBlockOps binfo block.

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

Definition reduceBlocks (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) {pos} : BuildState pos.
Proof.
  elim: blocks => [|b blocks IHbs] in pos *.
    exact: newBuildState.

  have bid  := blockId binfo b.
  have outs := if IntMap_lookup bid liveSets is Some ls
               then blockLiveOut ls
               else emptyIntSet.

  pose sz := blockSize binfo b.
  case E: (0 < sz);
    last exact: IHbs pos.

  (* For every variable in the live out set, create an empty range covering
     the entire span. *)
  have Hsz : pos < pos + sz by exact: ltn_plus.

  have pending := reduceBlock (emptyPendingRanges Hsz outs).
  exact: mergeIntoSortedRanges (ltnW Hsz) pending (IHbs (pos + sz)).
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

Definition buildIntervals (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : SSError + ScanStateSig maxReg InUse :=
  let add_unhandled_interval (ss  : ScanStateSig maxReg Pending) i :=
        packScanState (ScanState_newUnhandled ss.2 i.2 I) in
  let s0 := ScanState_nil maxReg in
  if blocks isn't b :: bs
  then inr $ packScanState (ScanState_finalize s0)
  else
    (fun (bs : BuildState 0) =>
       let: (regs, vars) := compileIntervals bs in
       let s1 := ScanState_setFixedIntervals s0 regs in
       let s2 := packScanState s1 in
       let s3 := IntMap_foldl add_unhandled_interval s2 vars in
       let s4 := ScanState_finalize s3.2 in
       inr $ packScanState s4)
    (reduceBlocks (b :: bs) liveSets).

End Build.