Require Import LinearScan.Lib.
Require Import LinearScan.Ltac.
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

Record BuildState (pos : nat) := {
  bsVars : seq (SortedRanges pos.*2.+1);
  bsRegs : Vec (option (BoundedInterval pos.*2.+1)) maxReg
}.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

(* For each register that is explicitly referenced by the operation, build up
   a [Interval] which excludes this register from use, but only at specific
   one-position wide ranges. *)
Definition setIntervalsForRegs (pos : nat)
  (regs : Vec (option (BoundedInterval (pos.+1).*2.+1)) maxReg)
  (regRefs : seq PhysReg) :
  Vec (option (BoundedInterval pos.*2.+1)) maxReg.
Proof.
  have regs' := regs.
  move/(vmap (option_map (transportBoundedInterval
                            (inner_addn1 pos)))) in regs'.
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
  constructor=> //;
  rewrite doubleS in H.
    by ordered.
  inversion Hsort; subst.
  by match_all.
Defined.

Program Definition reduceOp {pos} (op : opType1) (block : blockType1)
  (bs : BuildState pos.+1) : BuildState pos :=
  let: (varRefs, regRefs) := opRefs oinfo op in

  (* If the operation is a function call, assuming it makes use of every
     register.
     jww (2015-01-30): This needs to be improved to consider the calling
     convention of the operation. *)
  let regRefs' := if opKind oinfo op is IsCall
                  then enum 'I_maxReg
                  else regRefs in

  (* jww (2015-02-06): The next bit of work to be done is to use the list of
     var references to compute a sequence of RangePair's for this block. *)
  let varRefs' := @undefined nat in

  {| bsVars := map (transportSortedRange _) (bsVars bs)
   ; bsRegs := setIntervalsForRegs (bsRegs bs) regRefs' |}.

Definition reduceBlock {pos} (block : blockType1) (liveOut : IntSet)
  (bs : BuildState (pos + size (blockOps binfo block))) : BuildState pos.
  elim: (blockOps binfo block) => [|o os IHos] /= in bs *.
    by rewrite addn0 in bs.
  rewrite addnS in bs.
  exact: (IHos (reduceOp o block bs)).
Defined.

Definition reduceBlocks (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : BuildState 0 :=
  let: highestVar :=
      foldOps binfo (fun n op =>
        foldl (fun m v => maxn m (varId v)) n
              (fst (opRefs oinfo op)))
        0 blocks in
  let fix go b bs pos : BuildState pos :=
      let bid  := blockId binfo b in
      let outs := if IntMap_lookup bid liveSets isn't Some ls
                  then emptyIntSet
                  else blockLiveOut ls in
      reduceBlock outs $ match bs with
        | nil => {| bsVars := nseq highestVar.+1 emptySortedRanges
                  ; bsRegs := vconst None |}
        | cons b' bs' => go b' bs' (pos + size (blockOps binfo b))
        end in
  match blocks with
  | [::] => {| bsVars := nseq highestVar.+1 emptySortedRanges
             ; bsRegs := vconst None |}
  | x :: xs => go x xs 0
  end.

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

  let handleVar pos vid ss mrs :=
      mkint vid ss pos mrs $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i I) in

  (fun (bs : BuildState 0) =>
     let s0 := ScanState_nil maxReg in
     let f mx := if mx is Some x then Some x.1 else None in
     let regs := vmap f (bsRegs bs) in
     let s1 := ScanState_setFixedIntervals s0 regs in
     let s2 := packScanState s1 in
     let s3 := foldl_with_index (handleVar 0) s2 (bsVars bs) in
     let s4 := ScanState_finalize s3.2 in
     packScanState s4)
  (reduceBlocks blocks liveSets).

End Build.