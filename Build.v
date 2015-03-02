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
  cursorPending : BoundedRange b.*2.+1 cursorMid.*2.+1;
  cursorHpos    : b.*2.+1 <= pos.*2.+1 <= head_or_end cursorPending.1.1;
  cursorRanges  : SortedRanges cursorMid.*2.+1;
  cursorHend    :
    last cursorMid.*2.+1 [seq rend i.1 | i <- cursorRanges.1] <= e.*2.+1
}.

Definition emptyRangeCursor (b e : nat) (H : b < e) : RangeCursor b e e.
Proof.
  have Hsz : b.*2.+1 < e.*2.+1 by undoubled.
  apply: {| cursorMid := e |} => //=.
  - exact: emptyBoundedRange Hsz (odd_double_plus _).
  - by ordered.
  - exact: emptySortedRanges.
  - by undoubled.
Defined.

Definition transportRangeCursor {b prev base e} (Hlt : b <= base <= prev)
  (cursor : RangeCursor b prev e) :
  { cursor' : RangeCursor b base e
  | [/\ ups  (cursorPending cursor).1.1 = ups  (cursorPending cursor').1.1
    &   rend (cursorPending cursor).1.1 = rend (cursorPending cursor').1.1 ] }.
Proof.
  move: cursor => [mid br /= Hpos ranges Hend].
  apply: exist _ {| cursorMid := mid |} _ => //=;
  case: (ups br.1.1) => [|u us] /= in Hpos *;
  move/andP: Hlt => [H1 H2];
  rewrite -leq_double in H1;
  rewrite -leq_double in H2;
  by ordered.
Defined.

Definition shiftRangeCursor {b pos e} (H : b <= pos)
  (cursor : RangeCursor b pos e) :
  { cursor' : RangeCursor b pos e
  | [/\ ups  (cursorPending cursor).1.1 = ups  (cursorPending cursor').1.1
    &   rend (cursorPending cursor).1.1 = rend (cursorPending cursor').1.1 ] }.
Proof.
  case E: (rbeg (cursorPending cursor).1.1 <= pos.*2.+1).
    by exists cursor.
  case: cursor => [mid [r Hr] Hpos ranges Hend] /= in E *.
  move/negbT in E; rewrite -ltnNge /= in E.
  have Hodd : odd pos.*2.+1 by exact: odd_double_plus.
  pose r1 := Range_shift_down r.2 Hodd E.
  rewrite /head_or_end /head_or /= in Hpos.
  apply: exist _ {| cursorMid     := mid
                  ; cursorPending := exist _ r1 _
                  ; cursorRanges  := ranges |} _ => //=.
  - by undoubled.
Defined.

Definition PendingRanges b pos e := IntMap (RangeCursor b pos e).

Definition emptyPendingRanges (b e : nat) (H : b < e) (liveOuts : IntSet) :
  PendingRanges b e e.
Proof.
  have empty  := emptyRangeCursor H.
  have f xs vid := IntMap_insert (vid + maxReg) empty xs.
  exact: (IntSet_foldl f emptyIntMap liveOuts).
Defined.

Definition mergeIntoSortedRanges `(H : b <= pos)
  (pmap : PendingRanges b b pos) (rmap : IntMap (SortedRanges pos.*2.+1)) :
  IntMap (SortedRanges b.*2.+1).
Proof.
  apply: (IntMap_mergeWithKey _ _ _ pmap rmap).
  - (* The combining function, when entries are present in both maps. *)
    move=> _ [mid br /= _ ranges Hend] sr.
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

  - (* When no rmap entry are present. *)
    apply: IntMap_map _.
    case=> [mid br /= _ ranges Hend].
    have H0: b.*2.+1 <= b.*2.+1 <= rbeg br.1.1.
      move: (Range_proper br.1.2).
      move: br => [r ?] /=.
      by case: (ups r.1); ordered.
    exact: (prependRange ranges H0).1.

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

Definition BoundedCursor b pos e :=
  { c : RangeCursor b pos e
  | pos.*2.+1 < rend (cursorPending c).1.2
  & pos.*2.+1 <= head_or_end (cursorPending c).1.2 }.

Definition insertIntoRange {b pos e}
  (upos : UsePos) (Hodd : odd upos) (cursor : BoundedCursor b pos e)
  (Hbeg : rbeg (cursorPending cursor.1).1.1 <= upos)
  (Heqe : uloc upos == pos.*2.+1) : BoundedCursor b pos e.
Proof.
  case: cursor => [[mid [r Hr] Hpos ranges Hend] /= H1 H2] in Hbeg *.
  have Hupos: upos_before_rend r.2 upos.
    rewrite /= in Hpos *.
    case: (ups r.1) => [|u us] /= in Hpos *;
    case: (uvar upos) => //=;
    try case E: (uloc u == rend r.1) => //=;
    try move/eqP in E; rewrite ?E;
    by ordered.
  move: (validUsePosition Hbeg Hupos) => [Hloc Hsorted].
  pose r' := Range_cons r.2 Hloc Hsorted Hodd.
  apply: exist2 _ _ _ _ _.
  - apply: {| cursorMid     := mid
            ; cursorPending := exist _ r' _
            ; cursorRanges  := ranges |} => //=.
    clear -Heqe Hr Hloc.
    rewrite /= in Hloc.
    by ordered.
  - by [].
  - rewrite /=.
    by move/eqP in Heqe; rewrite Heqe.
Defined.

Definition makeNewRange {b pos e} (H : b <= pos < e)
  (upos : UsePos) (Hodd : odd upos) (Heqe : uloc upos == pos.*2.+1) :
  match uvar upos with
  | Input  => BoundedRange b.*2.+1   pos.*2.+1
  | Temp   => BoundedRange pos.*2.+1 pos.*2.+2
  | Output => BoundedRange pos.*2.+1 e.*2.+1
  end.
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

  case V: (uvar upos) in rd *;
  apply: exist _ _ _.

  - apply: exist _ _ _.
    exact: rd.
    constructor=> /=.
    + move/eqP in Heqe.
      rewrite Heqe.
      case: (uvar upos) in V *;
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

  - apply: exist _ _ _.
    exact: rd.
    constructor=> /=.
    + move/eqP in Heqe.
      rewrite Heqe.
      case: (uvar upos) in V *;
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

  - apply: exist _ _ _.
    exact: rd.
    constructor=> /=.
    + move/eqP in Heqe.
      rewrite Heqe.
      case: (uvar upos) in V *;
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

  (* rewrite /=. *)
  (* move/eqP in Heqe; rewrite {}Heqe. *)
  (* case: (uvar upos). *)
  (* - by case U: (pos.*2.+1 == pos.*2.+2) => //=. *)
  (* - case U: (pos.*2.+1 == pos.*2.+2) => //=. *)
  (*   move/eqP in U. *)
  (*   by ordered. *)
  (* - rewrite /=. *)
  (*   case U: (pos.*2.+1 == e.*2.+1) => //. *)
  (*   move/eqP in U. *)
  (*   move/andP: H => [_ H]. *)
  (*   rewrite -ltn_double in H. *)
  (*   move/ltn_addn1 in H. *)
  (*   by ordered. *)
Defined.

Definition insertOrAddRange {b pos e} (Hlt : b <= pos < e)
  (upos : UsePos) (Hodd : odd upos) (Heqe : uloc upos == pos.*2.+1)
  (cursor : option (BoundedCursor b pos e)) :
  option (BoundedCursor b pos e).
Proof.
  apply: Some _.

  case: cursor => [c|]; last first.
    (* There was no prior cursor, so start by creating a new range to contain
       the use position. *)
    have r := makeNewRange Hlt Hodd Heqe.
    case: (uvar upos) in r.

    apply: exist2 _ _ _ _ _.
    - apply: {| cursorMid     := pos
              ; cursorPending := r
              ; cursorRanges  := exist2 _ _ [::] _ _
              |} => //=.
      + clear -Hlt Heqe.
        destruct r.
        admit.
      + by constructor.
      + by undoubled.
    - rewrite /=.
      case: (uvar upos).
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.

  (* If the (possibly shifted) range begins at or before [upos], add the use
     position to it. *)
  case E: (rbeg (cursorPending c.1).1.1 <= upos).
    (* Verify that the use position occurs before the end of the current pending
       range. *)
    exact: (insertIntoRange Hodd E Heqe).

  move: c => [[mid br Hpos ranges Hend] Hupos ?] in E *.

  (* Otherwise, create a new range to contain the use position. *)
  have H3 : b <= pos < pos.+1 by ordered.
  pose r3 := makeNewRange H3 Hodd Heqe.

  have Hspan: b.*2.+1 <= (pos.+1).*2.+1 <= rbeg br.1.1.
    clear r3.
    rewrite doubleS.
    rewrite /= {Hupos} in E.
    move/eqP in Heqe.
    rewrite -Heqe.
    apply/andP; split.
      admit.
    move: (Range_beg_odd br.1.2) => Hbegodd.
    clear -E Heqe Hodd Hbegodd.
    move/negbT in E; rewrite -ltnNge /= in E.
    apply: ltn_odd => //.
    by apply/andP; split.
  clear E.

  admit.
(*
  apply: {| cursorMid     := pos.+1
          ; cursorPending := r3.1
          ; cursorRanges  := (prependRange ranges Hspan).1
         |} => //=.
  - clear -Hlt Heqe.
    move/eqP: Heqe => ->.
    by undoubled.
  - case: (prependRange ranges Hspan) => [p /= spec].
    move: br => [r Hr] /= in Hspan spec Hpos Hupos *.
    have H4: rend r.1 <= mid.*2.+1.
      pose Hlt' := Hlt.
      by ordered.
    have Hleq := last_leq Hend H4.
    rewrite -2!last_map -map_comp in spec.
    rewrite spec /= in Hleq.
    rewrite -2!last_map -map_comp in Hleq.
    apply: (last_leq Hleq _).
    move: (Range_bounded r.2).
    simpl in *.
    by ordered.

  rewrite /= {r3}.
  move/eqP in Heqe; rewrite {}Heqe.
  case: (uvar upos) => //=.
  - case U: (pos.*2.+1 == pos.*2.+2) => //=.
    move/eqP in U.
    by ordered.
  - rewrite /=.
    case U: (pos.*2.+1 == (pos.+1).*2.+1) => //.
    move/eqP in U.
    rewrite doubleS in U.
    by ordered.
*)
Defined.

Definition handleOutputVar {b pos e} (H : b <= pos < e)
  (cursor : option (RangeCursor b pos e)) (var : VarInfo maxReg) :
  option (RangeCursor b pos e).
Proof.
  case E: (varKind var != Input); last exact: cursor.

  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired var
               ; uvar   := varKind var |}.
  have Hodd : odd upos by rewrite /= odd_double.

  have H1 : b <= pos by ordered.
  have c1 := if varKind var is Output
             then option_map (fun c => (shiftRangeCursor H1 c).1) cursor
             else cursor.

  admit.
  (* exact (option_map sval (insertOrAddRange H Hodd _ undefined)). *)
Defined.

Definition handleInputVar {b pos e} (H : b <= pos < e)
  (cursor : option (RangeCursor b pos e)) (var : VarInfo maxReg) :
  option (RangeCursor b pos e).
Proof.
  case E: (varKind var == Input); last exact: cursor.

  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired var
               ; uvar   := varKind var |}.
  have Hodd : odd upos by rewrite /= odd_double.

  have c1 := cursor.

  have Hupos :
    if c1 is Some c
    then (if uvar upos is Input
          then leq
          else ltn) upos (head_or_end (cursorPending c).1.1)
    else true.
    rewrite [uvar _]/=.
    case: c1 => // [c].
    case V: (varKind var).
    - move: (cursorHpos c).
      by move/andP=> [_ H1].
    - by rewrite V in E.
    - by rewrite V in E.

  admit.
  (* exact: (insertOrAddRange H Hodd _ Hupos). *)
Defined.

Definition handleVars_combine {b pos e} (H : b <= pos < e) (vid : nat)
  (vars : seq (VarInfo maxReg))
  (c0 : RangeCursor b pos.+1 e) : option (RangeCursor b pos e).
Proof.
  have H1 : b <= pos <= pos.+1 by ordered.
  have c1 := Some (transportRangeCursor H1 c0).1.
  have c2 := foldl (handleOutputVar H) c1 [seq k <- vars | varKind k != Input].
  have c3 := foldl (handleInputVar H)  c2 [seq k <- vars | varKind k == Input].
  exact: c3.
Defined.

(* If there is no variable reference at this position, do nothing. *)
Definition handleVars_onlyRanges {b pos e} (H : b <= pos < e) :
  IntMap (RangeCursor b pos.+1 e) -> IntMap (RangeCursor b pos e).
Proof.
  have H1 : b <= pos <= pos.+1 by ordered.
  exact (IntMap_map (fun c => (transportRangeCursor H1 c).1)).
Defined.

(* If a variable referenced for which no reservation was made (for example, an
   input variable that is not used as an output later in the block), we simply
   add it.

   jww (2015-03-01): Note that it should be provably impossible for an output
   variable to be seen here for the first time, unless it is not a member of
   the live out set. *)
Definition handleVars_onlyVars {b pos e} (H : b <= pos < e) (vid : nat) :
  IntMap (seq (VarInfo maxReg)) -> IntMap (RangeCursor b pos e).
Proof.
  apply: IntMap_foldl _ emptyIntMap => m vars.
  have c2 :=
    foldl (handleOutputVar H) None [seq k <- vars | varKind k != Input].
  have c3 := foldl (handleInputVar H)  c2 [seq k <- vars | varKind k == Input].
  case: c3 => [c3|].
    exact: IntMap_insert vid c3 m.
  exact: m.
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
  `(ranges : PendingRanges b pos.+1 e) : PendingRanges b pos e :=
  let vars := IntMap_map extractVarInfo $
              IntMap_groupOn (@nat_of_varId maxReg) varRefs in
  IntMap_mergeWithKey (handleVars_combine Hlt) (handleVars_onlyVars Hlt _)
                      (handleVars_onlyRanges Hlt) vars ranges.

Definition reduceOp {b pos e} (block : blockType1) (op : opType1)
  (ranges : PendingRanges b pos.+1 e) (Hlt : b <= pos < e) :
  PendingRanges b pos e :=
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
  PendingRanges b (pos + sz) e -> PendingRanges b pos e.
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
    by rewrite addn0.
  move=> ranges.

  have H1 : b <= pos + (size os) < e.
    rewrite size_rcons in H.
    have: 0 < (size os).+1 by [].
    move/H=> /andP [H2 H3].
    apply/andP; split.
      exact: leq_plus.
    by rewrite addnS in H3.
  rewrite size_rcons addnS in ranges.
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