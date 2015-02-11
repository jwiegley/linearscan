Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.LiveSets.
Require Import LinearScan.ScanState.

Require Import Coq.Sorting.Sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Build.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Record BuildState (b e : nat) := {
  bsVars : IntMap (SortedRanges e.*2.+1);
  bsRegs : Vec (option (BoundedInterval b.*2.+1)) maxReg
}.

Definition newBuildState {n} : BuildState n n :=
  {| bsVars := emptyIntMap
   ; bsRegs := vconst None |}.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

(* For each register that is explicitly referenced by the operation, build up
   a [Interval] which excludes this register from use, but only at specific
   one-position wide ranges. *)
Definition setIntervalsForRegs
  `(regs : Vec (option (BoundedInterval (pos.+1).*2.+1)) maxReg)
  (regRefs : seq PhysReg) :
  Vec (option (BoundedInterval pos.*2.+1)) maxReg.
Proof.
  have regs' := regs.
  move/(vmap (option_map (transportBoundedInterval _))) in regs'.
  have Hleq : pos.*2.+1 <= (pos.+1).*2.+1.
    by ordered.
  specialize (regs' pos.*2.+1 Hleq).
  apply: foldl _ regs' regRefs => regs' reg.

  set upos := {| uloc   := pos.*2.+1
               ; regReq := true |}.
  have Hodd : odd upos by rewrite /= odd_double.
  have H : pos.*2.+1 <= pos.*2.+1 < pos.*2.+2 by ordered.

  pose rd := {| rbeg := uloc upos
              ; rend := (uloc upos).+1
              ; ups  := [:: upos] |}.
  have r : Range rd.
    rewrite /rd.
    constructor=> //=.
      by constructor; constructor.
    by apply/andP; split.

  apply: (vreplace regs' reg _).
  apply: Some _.
  case: (vnth regs reg) => [[[d i] /= Hlt]|];
    last exact: exist _ (exist _ _ (I_Sing 0 Whole r)) _.

  case: d => [iv ib ie ik rds] in i Hlt *.
  rewrite /= in Hlt.
  have Hrds: rend rd < rbeg (NE_head rds).1.
    by rewrite doubleS in Hlt.
  move: (Interval_exact_beg i)
        (Interval_exact_end i) => /= Hbeg Hend.
  move: Hbeg Hend i => -> -> i.
  rewrite /BoundedInterval.
  by exists (exist _ _ (I_Cons (r:=packRange r) i Hrds)).
Defined.

Definition UsePosList (pos : nat) :=
  { us : seq (UsePos * VarKind)
  | StronglySorted (fun x y => upos_lt (fst x) (fst y)) us
  & if us is u :: _ then pos <= fst u else True
  }.

Definition appendVar (pos : nat) (var : VarInfo)
  (p : UsePosList (pos.+1).*2.+1) : UsePosList pos.*2.+1.
Proof.
  move: p => [us Hsort H].
  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired var |}.
  have Hodd : odd upos by rewrite /= odd_double.
  set knd := varKind var.
  exists ((upos, knd) :: us) => //=.
  constructor=> //.
  case: us => //= [u us] in Hsort H *.
  constructor=> //.
    by ordered.
  inversion Hsort; subst.
  by match_all.
Defined.

Definition RangeCursor b pos mid e :=
  { p : BoundedRange b.*2.+1 mid.*2.+1 * SortedRanges mid.*2.+1
  | let r := (fst p).1.1 in
    [&& last mid.*2.+1 [seq rend i.1 | i <- (snd p).1] <= e.*2.+1
    ,   b.*2.+1 <= pos.*2.+1
    &   pos.*2.+1 <= head_or_end r ] }.

Definition emptyRangeCursor (b pos e : nat) (H : b < pos <= e) :
  RangeCursor b pos pos e.
Proof.
  have Hsz : b.*2.+1 < pos.*2.+1 by undoubled.
  exists (emptyBoundedRange Hsz, emptySortedRanges) => /=.
  by undoubled.
Defined.

Definition transportRangeCursor {b prev base mid e}
  (Hlt : b.*2.+1 <= base.*2.+1 <= prev.*2.+1)
  (c : RangeCursor b prev mid e) :
  RangeCursor b base mid e.
Proof.
  case: c => [[r /= rs] H1] in Hlt *.
  apply: (exist _ (r, rs) _) => /=.
  by case: (ups r.1.1) => /= [|u us] in H1 *; ordered.
Defined.

Definition PendingRanges b pos mid e :=
  { _ : IntMap (RangeCursor b pos mid e)
  | (b.*2.+1 <= pos.*2.+1 <= mid.*2.+1) && (mid.*2.+1 <= e.*2.+1) }.

Definition emptyPendingRanges (b pos e : nat) (H : b < pos <= e)
  (liveOuts : IntSet) : PendingRanges b pos pos e.
Proof.
  have empty    := emptyRangeCursor H.
  have f xs vid := IntMap_insert vid empty xs.
  have cursors  := IntSet_foldl f emptyIntMap liveOuts.
  exists cursors.
  by undoubled.
Defined.

Definition mergeIntoSortedRanges `(H : b <= pos)
  `(pmap : PendingRanges b b mid pos)
  (rmap : IntMap (SortedRanges pos.*2.+1)) :
  IntMap (SortedRanges b.*2.+1).
Proof.
  apply: (IntMap_mergeWithKey _ _ _ pmap.1 rmap).
  - (* The combining function, when entries are present in both maps. *)
    move=> _ [[br ps] /= Hlt] rs.
    move/andP: Hlt => [H1 /andP [H2 H3]].
    pose ps' := prependRange br ps.
    move: ps' => [ps' spec].
    apply: (Some (@SortedRanges_cat _ ps' _ rs _)) => /=.
    move: br => [r Hlt] in H3 ps' spec *.
    have H4: rend r.1 <= mid.*2.+1.
      have Hlt' := Hlt.
      by ordered.
    have p := last_leq H1 H4.
    rewrite /= -2!last_map -map_comp in spec.
    rewrite spec -2!last_map -map_comp in p.
    have H5: b.*2.+1 <= rend r.1.
      have Hlt' := Hlt.
      move: (Range_bounded r.2) => ?.
      by ordered.
    exact: last_leq p H5.

  - (* When no rmap entry are present. *)
    apply: IntMap_map _.
    case=> [[r rs] _].
    exact: (prependRange r rs).1.

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

Definition handleVars_combine {b pos mid e} (H : b <= pos) (vid : nat)
  (range : RangeCursor b pos.+1 mid e) (vars : bool * seq VarKind) :
  option (RangeCursor b pos mid e).
Proof.
  move: range => [[br srs] /= /andP [H1 /andP [H2 H3]]].
  move: vars => [req kinds].

  have srs' := prependRange br srs.
  move: br srs => [r Hr] [rs Hsort Hlt] in H1 H3 srs' *.

  set upos := {| uloc   := pos.*2.+1
               ; regReq := req |}.
  have Hodd : odd upos by rewrite /= odd_double.

  have E: (upos < head_or_end r.1).
    rewrite /=.
    by case: (ups r.1) => /= [|u us] in H3 *; undoubled.

  have Hupos: match ups r.1 with
      | [::]   => upos < rend r.1
      | u :: _ => upos <= u
      end.
    by case: (ups r.1) => /= [|u us] in H3 E *; undoubled.

  case K: ((Output \in kinds) && (Input \notin kinds)).
  - (* If this is an output variable that is not also used as an input
       variable, then rather than creating a new range, we simply insert the
       use position into that range.  We also shift up the beginning of the
       range, since it may begin here.  By doing this iteratively for each
       variable, we determine when the range truly starts. *)
    pose r1 := Range_shiftup (b:=upos) r.2 Hupos.

    have Hloc: rbeg r1.1 <= upos < head_or_end r1.1.
      have Hsh: r1 = Range_shiftup r.2 Hupos by [].
      rewrite /head_or_end /head_or.
      move: (Range_shiftup_spec Hsh) => [-> -> ->].
      clear Hsh r1.
      by case: (ups r.2) => /= [|u us] in H3 H E *; undoubled.
    pose r2 := Range_cons Hodd r1.2 Hloc.

    apply: Some (exist _ (exist _ r2 _, exist2 _ _ rs _ _) _) => /=.
      clear -H Hr.
      by apply/andP; split; undoubled.
    by ordered.

  - (* Otherwise, we must create a new [BoundedRange], and merge the previous
       one into the [SortedRanges]. *)
    pose r1 := r.
               (*   if Input \in kinds *)
               (* then Range_shiftdown (e:=upos) r.2 Hupos. *)

    (* have Hloc: rbeg r1.1 <= upos < head_or_end r1.1. *)
    (*   have Hsh: r1 = Range_shiftup r.2 Hupos by []. *)
    (*   rewrite /head_or_end /head_or. *)
    (*   move: (Range_shiftup_spec Hsh) => [-> -> ->]. *)
    (*   clear Hsh r1. *)
    (*   by case: (ups r.2) => /= [|u us] in H3 H E *; undoubled. *)
    (* pose r2 := Range_cons Hodd r1.2 Hloc. *)
    pose r2 := undefined.

    rewrite /= in srs'.
    apply: Some _.
    rewrite /RangeCursor.

    admit.
    (* apply (Some (exist _ (exist _ r2 _, srs') _)) => /=. *)
    (*   rewrite /r2 /r1 /=. *)
    (*   by apply/andP; split; undoubled. *)
    (* by ordered. *)
Defined.

Definition handleVars_onlyRanges {b pos mid e} :
  b.*2.+1 <= pos.*2.+1 <= (pos.+1).*2.+1
    -> IntMap (RangeCursor b pos.+1 mid e)
    -> IntMap (RangeCursor b pos mid e) :=
  IntMap_map \o transportRangeCursor.

Definition handleVars_onlyVars {b pos mid e}
  (H1 : b <= pos < mid) (H2 : mid <= e) :
  IntMap (bool * seq VarKind) -> IntMap (RangeCursor b pos mid e).
Proof.
  (* let H1' : b < pos.+1 <= mid := _ in *)
  (* let Hlt : b < mid <= e := _ in *)
  (* let mk : RangeDesc -> RangeCursor b pos mid e := _ in *)
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
               then mid.*2.+1
               else pos.*2.+2
     ; ups  := [:: {| uloc   := pos.*2.+1
                    ; regReq := req |} ]
     |}.
  apply: exist _ (exist _ (exist _ rd _) _, _) _ => /=.
  - constructor=> /=.
    + case: (Input \in kinds); by undoubled.
    + case: (Output \in kinds); by undoubled.
    + by constructor; constructor.
    + by rewrite odd_double.
  - move=> r.
    case: (Input \in kinds);
    case: (Output \in kinds);
    by undoubled.
  - exists [::] => //.
    by constructor.
  - move=> r H /=.
    by undoubled.
Defined.

Definition extractVarInfo (xs : seq VarInfo) : bool * seq VarKind :=
  (find regRequired xs != size xs,
   sortBy varKindLtn [seq varKind v | v <- xs]).

Program Definition handleVars (varRefs : seq VarInfo) `(Hlt : b <= pos)
  `(ranges : PendingRanges b pos.+1 mid e) : PendingRanges b pos mid e :=
  let vars := IntMap_map extractVarInfo $
              IntMap_groupOn varId varRefs in
  IntMap_mergeWithKey (handleVars_combine Hlt) (handleVars_onlyRanges _)
                      (handleVars_onlyVars _ _) ranges.1 vars.
Obligation 1. by undoubled. Qed.
Obligation 2.
  case: ranges => [ranges H0].
  move/andP: H0 => [/andP [H1 H2] H3].
  apply/andP; split=> //.
  move/ltnW: H2.
  by rewrite doubleS ltnS ltn_double.
Qed.
Obligation 3.
  case: ranges => [ranges H0].
  move/andP: H0 => [/andP [H1 H2] H3].
  move: H3.
  by rewrite ltnS leq_double.
Qed.
Obligation 4.
  case: ranges => [ranges H0].
  by apply/andP; split; undoubled.
Qed.

Definition reduceOp {b pos mid e} (block : blockType1) (op : opType1)
  (ranges : PendingRanges b pos.+1 mid e) (bs : BuildState pos.+1 e)
  (Hlt : b <= pos) :
  PendingRanges b pos mid e * BuildState pos e :=
  let: (varRefs, regRefs) := opRefs oinfo op in

  (* If the operation is a function call, assuming it makes use of every
     register.
     jww (2015-01-30): This needs to be improved to consider the calling
     convention of the operation. *)
  let regRefs' := if opKind oinfo op is IsCall
                  then enum 'I_maxReg
                  else regRefs in

  (handleVars varRefs Hlt ranges,
   {| bsVars := bsVars bs
    ; bsRegs := setIntervalsForRegs (bsRegs bs) regRefs' |}).

Definition reduceBlock {pos mid} (block : blockType1) :
  let sz := size (blockOps binfo block) in
  let b := pos in
  let e := pos + sz in
  forall (ranges : PendingRanges b (pos + sz) mid e)
         (bs : BuildState (pos + sz) e),
    (PendingRanges b pos mid e * BuildState pos e).
Proof.
  move=> sz b e.
  rewrite /sz.
  elim: (blockOps binfo block) => [|o os IHos] /=.
    by rewrite !addn0.
  rewrite !addnS.
  move=> ranges bs.
  case: (reduceOp block o ranges bs _).
    exact: leq_plus.
  exact: IHos.
Defined.

Definition reduceBlocks (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) pos : BuildState pos pos.
Proof.
  elim: blocks => [|b blocks IHbs] in pos *.
    exact: newBuildState.

  have bid  := blockId binfo b.
  have outs := if IntMap_lookup bid liveSets isn't Some ls
               then emptyIntSet
               else blockLiveOut ls.

  pose sz := size (blockOps binfo b).
  case E: (0 < sz);
    last exact: IHbs pos.

  (* For every variable in the live out set, create an empty range covering
     the entire span. *)
  pose endpos := pos + sz.
  have Hsz : pos < endpos.
    exact: ltn_plus.
  have Hsze : pos < endpos <= endpos.
    by apply/andP; split.
  have pending := emptyPendingRanges Hsze outs.

  have bs := IHbs endpos.
  rewrite /endpos /sz in pending bs.
  case: (reduceBlock pending bs) => [ranges bs'].

  exact {| bsVars :=
             mergeIntoSortedRanges (ltnW Hsz) ranges (bsVars bs')
          ; bsRegs := bsRegs bs' |}.
Defined.

Definition buildIntervals (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : ScanStateSig maxReg InUse :=
  (* for each block b in blocks in reverse order do
       int block_from = b.first_op.id
       int block_to = b.last_op.id + 2

       for each operand opr in b.live_out do
         intervals[opr].add_range(block_from, block_to)
       end for

       for each operation op in b.operations in reverse order do
         visitor.visit(op)

         if visitor.has_call then
           for each physical register reg do
             intervals[reg].add_range(op.id, op.id + 1)
           end for
         end if

         for each virtual or physical register opr in visitor.output_oprs do
           intervals[opr].first_range.from = op.id
           intervals[opr].add_use_pos(op.id, use_kind_for(op, opr))
         end for

         for each virtual or physical register opr in visitor.temp_oprs do
           intervals[opr].add_range(op.id, op.id + 1)
           intervals[opr].add_use_pos(op.id, use_kind_for(op, opr))
         end for

         for each virtual or physical register opr in visitor.input_oprs do
           intervals[opr].add_range(block_from, op.id)
           intervals[opr].add_use_pos(op.id, use_kind_for(op, opr))
         end for
       end for
     end for *)
  let mkint
        (vid : VarId)
        (ss  : ScanStateSig maxReg Pending)
        (pos : nat)
        (mrs : SortedRanges pos.*2.+1)
        (f   : forall sd, ScanState Pending sd
                 -> forall d, Interval d -> ScanStateSig maxReg Pending) :=
      match List.destruct_list mrs.1 with
      | inright _ => ss
      | inleft (existT _ (exist _ H)) =>
          f _ ss.2 _ (Interval_fromRanges vid H)
      end in

  let handleVar pos ss vid mrs :=
      mkint vid ss pos mrs $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i I) in

  let s0 := ScanState_nil maxReg in
  if blocks isn't b :: bs
  then packScanState (ScanState_finalize s0)
  else
    (fun (bs : BuildState 0 0) =>
       let f mx := if mx is Some x then Some x.1 else None in
       let regs := vmap f (bsRegs bs) in
       let s1 := ScanState_setFixedIntervals s0 regs in
       let s2 := packScanState s1 in
       let s3 := IntMap_foldlWithKey (handleVar 0) s2 (bsVars bs) in
       let s4 := ScanState_finalize s3.2 in
       packScanState s4)
    (reduceBlocks bs liveSets 0).

End Build.