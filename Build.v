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

Record BuildState (b : nat) := {
  bsVars : IntMap (SortedRanges b.*2.+1)
}.

Definition newBuildState {n} : BuildState n :=
  {| bsVars := emptyIntMap |}.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

(*
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

(*

block   range   first    last      range   ranges   ranges   block
beg     beg     use pos  use pos   end     beg      end      end
|       |       |              |       |   |             |       |
|       |       |              |       |   |             |       |

"block beg" and "block end" are fixed at the beginning of processing of the
block.

"ranges beg" and "ranges end" are fixed whenever a new range is added to that
list.

"range beg" and "range end" start out equal to "block beg" and "ranges beg",
but can contract during the processing of variables.  They may only contract
inward, and only as far as the "first use pos" and "last use pos".

When a [UsePos] is found before "range beg", that range is prepended to
"ranges" and a new range is created.  It extends to "block beg" if it is an
[Input] variable, otherwise it is equal to "first use pos".

When complete, the variable's liveness within the block extends from "range
beg" to "ranges end".

*)

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

Definition RangeCursor_shiftup {b b' pos mid e}
  (c : RangeCursor b pos mid e)
  (Hlt : b.*2.+1 <= b'.*2.+1 <= pos.*2.+1) : RangeCursor b' pos mid e.
Proof.
  move: c => [[[r H] /= rs] /andP [H1 /andP [H2 H3]]] in Hlt *.
  have Hsh: if ups r.1 is u :: _
            then b'.*2.+1 <= u
            else b'.*2.+1 < rend r.1 by admit.
  pose r' := Range_shiftup r.2 Hsh.
  by apply: exist _ (exist _ r' _, rs) _; ordered.
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
    case U: (upos < rbeg r.1).
      pose r1  := newRange Hodd.
      pose br  : BoundedRange b.*2.+1 mid.*2.+1 := exist _ r Hr.
      pose br' : BoundedRange b.*2.+1 mid.*2.+1 := exist _ r Hr.
      (* pose rs' := prependRange () (exist2 _ _ rs Hsort Hlt). *)
      (* have Hloc: b.*2 < pos.*2.+1 < mid.*2.+1 by admit. *)
      (* pose p   := (exist (fun r0 => (b.*2 < rbeg r0.1) && *)
      (*                               (rend r0.1 <= mid.*2.+1)) r1 Hloc, rs'). *)
      (* apply: Some _. *)
      (* rewrite /RangeCursor. *)
      (* rewrite /BoundedRange. simpl in p. *)
      (* apply (exist _ p _) => /=. *)
      admit.
    (* apply (Some (exist _ p _)) => /=. *)

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
  (Hlt : b <= pos) : PendingRanges b pos mid e * BuildState pos e :=
  let: refs := opRefs oinfo op in

  (* If the operation is a function call, assuming it makes use of every
     register.
     jww (2015-01-30): This needs to be improved to consider the calling
     convention of the operation. *)
  let regRefs' := undefined in
      (* if opKind oinfo op is IsCall *)
      (* then enum 'I_maxReg *)
      (* else regRefs in *)

  (handleVars undefined Hlt ranges,
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
*)

Definition computeRanges (b : nat) (block : blockType1) (liveOuts : IntSet) :
  SSError + IntMap (seq (nat * nat) * seq UsePos) :=
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
  let endb := b + size (blockOps binfo block) in

  let m := IntSet_forFold emptyIntMap liveOuts $ fun m vid =>
    IntMap_insert (maxReg + vid) ([:: (b, endb)], [::]) m in

  let go n op rest := if rest isn't inr m1 then rest else
    let pos := (b + n).*2.+1 in
    let: refs := opRefs oinfo op in

    let recordPosRange vid m :=
      let consRange x mxs :=
        if mxs is Some (xs, ys)
        then Some (x :: xs, ys)
        else Some ([:: x], [::]) in
      IntMap_alter (consRange (pos, pos.+1)) vid m in

    (* If this is a call operation, block every register. *)
    let m2 :=
      if opKind oinfo op is IsCall
      then let fix go m n := match n with
        | O => m
        | S n => recordPosRange n (go m n)
        end in
        go m1 maxReg
      else m1 in

    let upos v := {| uloc   := pos
                   ; regReq := regRequired v |} in

    (* First consider the output variables. *)
    let outputs := [seq v <- refs | varKind v == Output] in
    let m3 := forFold (inr m2) outputs $ fun acc v =>
      if acc isn't inr m3 then acc else
      match IntMap_lookup (varId v) m3 with
      | None => inl EOutputVarMissingInput
      | Some (nil, _) => inl EOutputVarMissingInput
      | Some ((b, e) :: ranges, uses) =>
        let x := ((pos, e) :: ranges, (upos v) :: uses) in
        inr (IntMap_insert (varId v) x m3)
      end in
    if m3 isn't inr m3 then m3 else

    let record vid x y m :=
      let go x y ms :=
        if ms is Some (xs, ys)
        then Some (x :: xs, y :: ys)
        else Some ([:: x], [:: y]) in
      IntMap_alter (go x y) vid m in

    (* Next, consider the temp variables. *)
    let temps := [seq v <- refs | varKind v == Temp] in
    let m4 := forFold (inr m3) temps $ fun acc v =>
      if acc isn't inr m4 then acc else
      inr $ record (varId v) (pos, pos.+1) (upos v) m4 in
    if m4 isn't inr m4 then m4 else

    (* Last, consider the input variables. *)
    let inputs := [seq v <- refs | varKind v == Input] in
    forFold (inr m4) inputs $ fun acc v =>
      if acc isn't inr m5 then acc else
      inr $ record (varId v) (b, pos) (upos v) m5 in

  foldr_with_index go (inr m) (blockOps binfo block).

Program Fixpoint mergeContiguousRanges (ranges : seq (nat * nat))
  {measure (size ranges)} : seq (nat * nat) :=
  match ranges with
  | (xb, xe) :: (yb, ye) :: xs =>
    if xe == yb
    then mergeContiguousRanges ((xb, ye) :: xs)
    else (xb, xe) :: mergeContiguousRanges ((yb, ye) :: xs)
  | _ => ranges
  end.

Fixpoint collectUses (ranges : seq (nat * nat)) (uses : seq UsePos) :
  seq ((nat * nat) * seq UsePos) :=
  match ranges with
  | [::] => [::]
  | cons (xb, xe) xs =>
    ((xb, xe), [seq u <- uses | xb <= uloc u < xe])
      :: collectUses xs [seq u <- uses | ~~ (xb <= uloc u < xe)]
  end.

Definition compileRanges (ranges : seq (nat * nat)) (uses : seq UsePos) :
  option { pos : nat & SortedRanges pos }.
Proof.
  case: ranges => [|[xb xe] xs].
    exact: None.
  pose ranges0 := (xb, xe) :: xs.
  pose ranges1 := mergeContiguousRanges ranges0.
  pose ranges2 := collectUses ranges1 uses.
  apply: foldr _ (Some (existT _ xb emptySortedRanges)) ranges2.
  move=> [[rb re] ruses].
  case=> [[pos rest]|]; last exact: None.
  pose rd' := {| rbeg := rb
               ; rend := re
               ; ups  := ruses |}.
  have r': Range rd' by admit.
  case E: (rend rd' < pos); last exact: None.
  apply: Some _.
  exists (minn pos rb).
  move: (consRange r' rest E).
  apply: transportSortedRanges.
  exact: geq_minr.
Defined.

Definition appendBuildState `(bs : BuildState (pos + sz))
  (m : IntMap (seq (nat * nat) * seq UsePos)) : BuildState pos.
Proof.
  apply: {| bsVars := IntMap_mergeWithKey _ _ _ (bsVars bs) m |}.
  - move=> vid ranges [rawRanges rawUses].
    (* jww (2015-02-11): All these uses of [None] here represent invariants
       that should be true of [computeRanges], but which we are not taking the
       time to prove right now.  They should at least be reported to the user,
       although [IntMap_mergeWithKey] makes that impossible here. *)

    (* The [raw] list is a list of ranges and of use positions, which we must
       compile into a list of sorted ranges.  The first step is to join
       contiguous ranges. *)
    move: (compileRanges rawRanges rawUses) => [[b newRanges]|];
      last exact: None.
    case H1: (last b [seq rend r.1 | r <- newRanges.1] <= (pos + sz).*2.+1);
      last exact: None.
    case E: (pos.*2.+1 <= b); last exact: None.
    apply: Some _.
    move: (SortedRanges_cat ranges H1).
    exact: transportSortedRanges.

  - apply: IntMap_map _.
    apply: transportSortedRanges.
    rewrite ltnS leq_double.
    exact: leq_addr.

  - apply: IntMap_map _.
    (* jww (2015-02-11): See note above about these uses of
       [emptySortedRanges], which serve the same role as using [None]
       there. *)
    move/(uncurry compileRanges) => [[b]|];
      last exact: emptySortedRanges.
    case E: (pos.*2.+1 <= b); last first.
      move=> _.
      exact: emptySortedRanges.
    exact: transportSortedRanges.
Defined.

Definition compileIntervals `(bs : BuildState pos) : IntMap IntervalSig.
Proof.
Admitted.

Definition extractFixedIntervals (intervals : IntMap IntervalSig) :
  FixedIntervalsType maxReg.
Proof.
Admitted.

Definition reduceBlocks (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) {pos} : SSError + BuildState pos.
Proof.
  elim: blocks => [|b blocks IHbs] in pos *.
    exact: inr newBuildState.

  have bid  := blockId binfo b.
  have outs := if IntMap_lookup bid liveSets isn't Some ls
               then emptyIntSet
               else blockLiveOut ls.

  pose sz := size (blockOps binfo b).
  case E: (0 < sz);
    last exact: IHbs pos.

  move: (IHbs (pos + sz)) => [err|bs'].
    exact: inl err.
  move: (computeRanges pos b outs) => [err|res].
    exact: inl err.
  exact: inr (appendBuildState bs' res).
Defined.

Definition buildIntervals (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : SSError + ScanStateSig maxReg InUse :=
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
  then inr $ packScanState (ScanState_finalize s0)
  else
    (fun (res : SSError + BuildState 0) =>
       match res with
       | inl err => inl err
       | inr bs =>
         let vars := compileIntervals bs in
         let regs := extractFixedIntervals vars in
         let s1   := ScanState_setFixedIntervals s0 regs in
         let s2   := packScanState s1 in
         let s3   := IntMap_foldlWithKey (handleVar 0) s2 (bsVars bs) in
         let s4   := ScanState_finalize s3.2 in
         inr $ packScanState s4
       end)
    (reduceBlocks bs liveSets).

End Build.