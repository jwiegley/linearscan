Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Morph.
Require Import LinearScan.ScanState.

Require Import Coq.Sorting.Sorted.

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

(* block   range   first    last      range   ranges   ranges   block
   beg     beg     use pos  use pos   end     beg      end      end
   |       |       |              |       |   |             |       |
   |       |       |              |       |   |             |       |

   "block beg" and "block end" are fixed at the beginning of processing each
   block.

   "range beg" and "range end" start out equal to "block beg" and "ranges
   beg", but may contract during processing of variables.  They may only
   contract inward, and only as far as "first use pos" and "last use pos".

   When a [UsePos] is found before "range beg", that range is prepended to
   "ranges" and a new range is created to hold the [UsePos].  It extends to
   "block beg" if it is an [Input] variable, otherwise it is equal to "first
   use pos".

   When complete, the variable's liveness within the block extends from "range
   beg" to "ranges end".

   "ranges" is sorted such no range is either overlapping or contiguous with
   another range.

   However, "range end" may equal "ranges beg", which means that when the
   range is appended to the beginning of ranges, two scenarios may occur: if
   "range end == ranges beg", then the first range in ranges simply extend to
   include the range; otherwise, the new range is prepended normally into the
   sorted list of ranges. *)

Record RangeCursor b pos e := {
  cursorMid     : nat;
  cursorHmid    : pos.*2.+1 <= cursorMid.*2.+1;
  cursorHbeg    : b.*2.+1 <= pos.*2.+1;
  cursorPending : BoundedRange b.*2.+1 cursorMid.*2.+1;
  cursorHpos    : pos.*2.+1 <= head_or_end cursorPending.1.1;
  cursorRanges  : SortedRanges cursorMid.*2.+1;
  cursorHend    :
    last cursorMid.*2.+1 [seq rend i.1 | i <- cursorRanges.1] <= e.*2.+1
}.

Definition emptyRangeCursor (b pos e : nat) (H : b < pos <= e) :
  RangeCursor b pos e.
Proof.
  have Hsz : b.*2.+1 < pos.*2.+1 by undoubled.
  apply: {| cursorMid := pos |} => //=.
  - by ordered.
  - exact: (emptyBoundedRange Hsz (odd_double_plus _)).
  - by [].
  - exact: emptySortedRanges.
  - by undoubled.
Defined.

Definition transportRangeCursor {b prev base e}
  (Hlt : b.*2.+1 <= base.*2.+1 <= prev.*2.+1)
  (c : RangeCursor b prev e) : RangeCursor b base e.
Proof.
  case: c => [mid ? ? r /= Hpos rs ?] in Hlt *.
  apply: {| cursorMid := mid |} => //=;
  by case: (ups r.1.1) => /= [|u us] in Hpos *; ordered.
Defined.

Definition PendingRanges b pos e :=
  { _ : IntMap (RangeCursor b pos e) | b.*2.+1 <= pos.*2.+1 <= e.*2.+1 }.

Definition emptyPendingRanges (b pos e : nat) (H : b < pos <= e)
  (liveOuts : IntSet) : PendingRanges b pos e.
Proof.
  have empty  := emptyRangeCursor H.
  have f xs vid := IntMap_insert (vid + maxReg) empty xs.
  exists (IntSet_foldl f emptyIntMap liveOuts).
  by undoubled.
Defined.

Definition mergeIntoSortedRanges `(H : b <= pos)
  (pmap : PendingRanges b b pos) (rmap : IntMap (SortedRanges pos.*2.+1)) :
  IntMap (SortedRanges b.*2.+1).
Proof.
  apply: (IntMap_mergeWithKey _ _ _ pmap.1 rmap).
  - (* The combining function, when entries are present in both maps. *)
    move=> _ [mid Hmid H1 br /= H2 ps H3] rs.
    have H0: b.*2.+1 <= b.*2.+1 <= rbeg br.1.1.
      move: (Range_beg_bounded br.1.2).
      move: br => [r Hr] /= in H2 *.
      by case: (ups r.1); ordered.
    pose ps' := prependRange ps H0.
    move: ps' => [ps' spec].
    clear H0.
    apply: (Some (@SortedRanges_cat _ ps' _ rs _)) => /=.
    move: br => [r Hlt] in H2 ps' spec *.
    have H4: rend r.1 <= mid.*2.+1.
      have Hlt' := Hlt.
      by ordered.
    have H5: b.*2.+1 <= rend r.1.
      have Hlt' := Hlt.
      move: (Range_bounded r.2) => ?.
      by ordered.
    have p := last_leq H3 H4.
    rewrite spec /= in p.
    exact: (last_leq p H5).

  - (* When no rmap entry are present. *)
    apply: IntMap_map _.
    case=> [? _ /= ? br Hpos rs ?].
    have H0: b.*2.+1 <= b.*2.+1 <= rbeg br.1.1.
      move: (Range_beg_bounded br.1.2).
      move: br => [r ?] /= in Hpos *.
      by case: (ups r.1); ordered.
    exact: (prependRange rs H0).1.

  - (* When no pmap entry is present. *)
    apply: IntMap_map _.
    apply: transportSortedRanges.
    by undoubled.
Defined.

Definition varKindLtn (x y : VarKind) : bool :=
  match x, y with
  | Input, Input => false
  | Temp, Input  => false
  | Temp, Temp   => false
  | Output, _    => false
  | _, _         => true
  end.

Definition handleVars_combine {b pos e} (H : b <= pos) (vid : nat)
  (range : RangeCursor b pos.+1 e) (vars : bool * seq VarKind) :
  option (RangeCursor b pos e).
Proof.
  move: range => [mid Hmid H1 br /= H2 srs H3].
  move: vars => [req kinds].

  set upos := {| uloc   := pos.*2.+1
               ; regReq := req |}.
  have Hodd : odd upos by rewrite /= odd_double.

  have E: (upos < head_or_end br.1.1).
    rewrite /=.
    by case: (ups br.1.1) => /= [|u us] in H2 *; undoubled.

  have Hupos: match ups br.1.1 with
      | [::]   => upos < rend br.1.1
      | u :: _ => upos <= u
      end.
    by case: (ups br.1.1) => /= [|u us] in H2 E *; undoubled.

  case K: ((Output \in kinds) && (Input \notin kinds)).
  - (* If this is an output variable that is not also used as an input
       variable, then rather than creating a new range, we simply insert the
       use position into that range.  We also shift up the beginning of the
       range, since it may begin here.  By doing this iteratively for each
       variable, we determine when the range truly starts. *)
    move: br srs => [r Hr] [rs Hsort Hlt] /= in H2 H3 E Hupos *.
    pose r1 := Range_shiftup (b:=upos) r.2 Hodd Hupos.

    have Hloc: rbeg r1.1 <= upos < head_or_end r1.1.
      have Hsh: r1 = Range_shiftup r.2 Hodd Hupos by [].
      rewrite /head_or_end /head_or.
      move: (Range_shiftup_spec Hsh) => [-> -> ->].
      clear Hsh r1.
      by case: (ups r.2) => /= [|u us] in H3 H E *; undoubled.
    pose r2 := Range_cons Hodd r1.2 Hloc.

    rewrite /= in H1 Hloc r2.
    apply: Some {| cursorMid     := mid
                 ; cursorPending := exist _ r2 _
                 ; cursorRanges  := exist2 _ _ rs _ _
                 |} => //=.
    + by ordered.
    + by undoubled.
    + by undoubled.

  - (* Otherwise, we must create a new [BoundedRange], and merge the previous
       one into the [SortedRanges]. *)
    case Hloc: (rbeg br.1.1 <= upos).
    + have U: rbeg br.1.1 <= upos < head_or_end br.1.1
        by ordered.
      pose r1 := Range_cons Hodd br.1.2 U.
      apply: Some {| cursorMid     := mid
                   ; cursorPending := exist _ r1 _
                   ; cursorRanges  := srs
                   |} => //=.
      * by ordered.
      * by undoubled.
      * clear -br.
        move: br => [? Hr].
        exact: Hr.

    + pose r1 := newRange Hodd.

      move/negbT in Hloc.
      rewrite -ltnNge /= in Hloc.

      have Hspan: b.*2.+1 <= (pos.+1).*2.+1 <= rbeg br.1.1.
        apply/andP; split=> //.
        rewrite doubleS.
        simpl in E.
        move: (Range_beg_odd br.1.2) => Hbegodd.
        apply: ltn_odd => //.
        by apply/andP; split.

      apply: Some {| cursorMid     := pos.+1
                   ; cursorPending := exist _ r1 _
                   |} => //=.
      * by ordered.
      * by undoubled.
      * by undoubled.
      * exact: (prependRange srs Hspan).1.
      * case: (prependRange srs Hspan) => [p /= spec].
        have Hmid': (pos.+1).*2.+1 <= mid.*2.+1.
          by undoubled.
        move: br => [r Hlt] in H2 spec E Hupos Hloc Hspan *.
        have H4: rend r.1 <= mid.*2.+1.
          pose Hlt' := Hlt.
          by ordered.
        have Hleq := last_leq H3 H4.
        rewrite spec /= in Hleq.
        apply: (last_leq Hleq _).
        move: (Range_bounded r.2).
        by ordered.
Defined.

Definition handleVars_onlyRanges {b pos e}
  (Hlt : b.*2.+1 <= pos.*2.+1 <= (pos.+1).*2.+1) :
  IntMap (RangeCursor b pos.+1 e) -> IntMap (RangeCursor b pos e).
Proof.
  apply: IntMap_map _.
  exact: (transportRangeCursor Hlt).
Defined.

Definition handleVars_onlyVars {b pos e} (H1 : b <= pos < e) :
  IntMap (bool * seq VarKind) -> IntMap (RangeCursor b pos e).
Proof.
  apply: IntMap_map _.
  move=> [req kinds].
  (* If the variable is only [Input], assume it starts from the beginning; and
     if [Output], that it persists until the end.  Only [Temp] variables are
     simply handled using a single-instruction [Range]. *)
  pose rd :=
    {| rbeg := if Input \in kinds
               then b.*2.+1
               else pos.*2.+1
     ; rend := if Output \in kinds
               then e.*2.+1
               else pos.*2.+2
     ; ups  := [:: {| uloc   := pos.*2.+1
                    ; regReq := req |} ]
     |}.
  apply: {| cursorMid     := e
          ; cursorPending := exist _ (exist _ rd _) _
          |} => //=;
  try undoubled.
  - constructor=> /=.
    + by case: (Input \in kinds); undoubled.
    + by case: (Output \in kinds); undoubled.
    + by constructor; constructor.
    + by case: (Input \in kinds); exact: odd_double_plus.
    + by rewrite odd_double.
  - move=> r.
    case: (Input \in kinds);
    case: (Output \in kinds);
    by undoubled.
  - exists [::] => //.
    by constructor.
  - by undoubled.
Defined.

Definition extractVarInfo (xs : seq (VarInfo maxReg)) : bool * seq VarKind :=
  (find (@regRequired maxReg) xs != size xs,
   sortBy varKindLtn [seq varKind v | v <- xs]).

Program Definition handleVars (varRefs : seq (VarInfo maxReg)) `(Hlt : b <= pos)
  `(ranges : PendingRanges b pos.+1 e) : PendingRanges b pos e :=
  let vars := IntMap_map extractVarInfo $
              IntMap_groupOn (@nat_of_varId maxReg) varRefs in
  IntMap_mergeWithKey (handleVars_combine Hlt) (handleVars_onlyRanges _)
                      (handleVars_onlyVars _) ranges.1 vars.
Obligation 1. by undoubled. Qed.
Obligation 2.
  case: ranges => [ranges H0].
  move/andP: H0 => [H1 H2].
  apply/andP; split=> //.
  move/ltnW: H2.
  by rewrite doubleS ltnS ltn_double.
Qed.
Obligation 3.
  case: ranges => [ranges H0].
  move/andP: H0 => [H1 H2].
  by undoubled.
Qed.

Definition reduceOp {b pos e} (block : blockType1) (op : opType1)
  (ranges : PendingRanges b pos.+1 e) (Hlt : b <= pos) :
  PendingRanges b pos e :=
  (* If the operation is a function call, assuming it makes use of every
     register.
     jww (2015-01-30): This needs to be improved to consider the calling
     convention of the operation. *)
  let refs := opRefs oinfo op in
  let refs' :=
    if opKind oinfo op is IsCall
    then [seq {| varId       := inl n
               ; varKind     := Temp
               ; regRequired := true
               |} | n in ord_enum maxReg] ++ refs
    else refs in

  handleVars refs' Hlt ranges.

Definition reduceBlock {pos} (block : blockType1) :
  let sz := blockSize binfo block in
  let b := pos in
  let e := pos + sz in
  PendingRanges b (pos + sz) e -> PendingRanges b pos e.
Proof.
  move=> sz b e.
  rewrite /sz /blockSize.
  set ops := allBlockOps binfo block.
  rewrite -size_rev.
  elim: (rev ops) => [|o os IHos] /=.
    by rewrite !addn0.
  rewrite !addnS.
  move=> ranges.
  move: (reduceOp block o ranges (leq_plus _ _)).
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
  pose endpos := pos + sz.
  have Hsz  : pos < endpos by exact: ltn_plus.
  have Hsze : pos < endpos <= endpos by ordered.

  have pending := reduceBlock (emptyPendingRanges Hsze outs).
  exact: mergeIntoSortedRanges (ltnW Hsz) pending (IHbs endpos).
Defined.

Definition compileIntervals `(bs : BuildState pos) :
  (* Return the set of fixed intervals, and the set of variable intervals,
     respectively. *)
  FixedIntervalsType maxReg * IntMap IntervalSig.
Proof.
  apply: IntMap_foldlWithKey _ (vconst None, emptyIntMap) bs.
  move=> [regs vars] vid rs.
  case E: rs.1 => [|? ?]; first by exact: (regs, vars).
  case V: (vid < maxReg).
    move: (Interval_fromRanges vid E) => /= i.
    exact: (vreplace regs (Ordinal V) (Some (packInterval i)), vars).
  have vid' := vid - maxReg.
  move: (Interval_fromRanges vid' E) => /= i.
  exact: (regs, IntMap_insert vid' (packInterval i) vars).
Defined.

Definition buildIntervals (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : SSError + ScanStateSig maxReg InUse :=
  let handleVar (ss  : ScanStateSig maxReg Pending) i :=
        packScanState (ScanState_newUnhandled ss.2 i.2 I) in
  let s0 := ScanState_nil maxReg in
  if blocks isn't b :: bs
  then inr $ packScanState (ScanState_finalize s0)
  else
    (fun (bs : BuildState 0) =>
       let: (regs, vars) := compileIntervals bs in
       let s1 := ScanState_setFixedIntervals s0 regs in
       let s2 := packScanState s1 in
       let s3 := IntMap_foldl handleVar s2 vars in
       let s4 := ScanState_finalize s3.2 in
       inr $ packScanState s4)
    (reduceBlocks (b :: bs) liveSets).

End Build.