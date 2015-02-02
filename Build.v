Require Import LinearScan.Lib.
Require Import LinearScan.Blocks.
Require Import LinearScan.Interval.
Require Import LinearScan.IntMap.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Machine.
Require Import LinearScan.Proto.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MBuild (Mach : Machine).

Include MLiveSets Mach.

Record BuildState (pos : nat) := {
  bsVars : seq (option (SortedProtoRanges pos.*2.+1));
  bsRegs : Vec (option (BoundedInterval pos.*2.+1)) maxReg
}.

Section Build.

Variables blockType1 blockType2 opType1 opType2 varType accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo accType opType1 opType2 varType.
Variable vinfo : VarInfo varType.

(* Create a proto range to represent a variable reference. *)
Definition protoRangeForVariable pos (block : blockType1) (var : varType)
  (begin : OpId) (Hpos : begin <= pos < begin + blockSize binfo block) :
  SortedProtoRanges
    (match varKind vinfo var with
     | Input  => begin
     | Temp   => pos.*2.+1
     | Output => pos.*2.+1
     end).
Proof.
  move/andP: Hpos => [Hbeg Hend].

  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired vinfo var |}.
  have Hodd : odd upos by rewrite /= odd_double.

  (* For temp variables a single position range is sufficient.  For an input
     variable, it must extend from the beginning of the block to one beyond
     the use position.  For an output variable, it extensd from the use
     position to the end of the block.

     Variables in the [blockLiveOut] set which are not used otherwise cause an
     empty range to be inserted that extends throughout the entire block. *)
  VarKind_cases (destruct (varKind vinfo var)) Case.
  - Case "VarKind_Input".
    have r: ProtoRange begin.
      apply:
        {| prBeg        := begin.*2.+1
         ; prBegOdd     := odd_double_plus begin
         ; prEnd        := (uloc upos).+1
         ; prUseLocs    := [:: upos] |} => //=.
      + exact/leqW/leqW_double.
      + apply/negPn.
        by rewrite odd_double.
      + by rewrite -2![_.*2.+2]addn2 leq_add2r leq_double.
      + by repeat constructor.
      + apply/andP; split=> //.
        by rewrite ltnS leq_double.
      + by apply/andP; split=> //.
    exists (NE_Sing r).
    by constructor.

  - Case "VarKind_Temp".
    have r: ProtoRange upos.
      apply:
        {| prBeg        := uloc upos
         ; prBegOdd     := Hodd
         ; prBegLim     := leqnn _
         ; prEnd        := (uloc upos).+1
         ; prUseLocs    := [:: upos] |} => //=.
      + apply/negPn.
        by rewrite odd_double.
      + by repeat constructor.
      + by apply/andP; split.
      + by apply/andP; split.
    exists (NE_Sing r).
    by constructor.

  - Case "VarKind_Output".
    have r: ProtoRange upos.
      apply:
        {| prBeg        := uloc upos
         ; prBegOdd     := Hodd
         ; prEnd        := (begin + blockSize binfo block).*2
         ; prUseLocs    := [:: upos] |} => //=.
      + apply/negPn.
        by rewrite odd_double.
      + apply: ltn_even.
        by apply/andP; split; rewrite odd_double.
      + by rewrite ltn_double.
      + by repeat constructor.
      + by apply/andP; split=> //.
      + apply/andP; split=> //.
        apply: ltn_even.
          by apply/andP; split; rewrite odd_double.
        by rewrite ltn_double.
    exists (NE_Sing r).
    by constructor.
Defined.

(* For each virtual variable references, add a use position to a [Range]
   corresponding to that variable.  These ranges are concatenated together and
   will form a single [Interval] at the end.  This is different from how
   Wimmer builds them up, and is more simplistic, but is sufficient for now.

   jww (2015-01-30): The more efficient solution would be to implement the
   algorithm from his paper. *)
Definition createRangeForVars (pos : nat) (block : blockType1)
  (vars : seq (option (SortedBoundedRanges (pos.+1).*2.+1)))
  (varRefs : seq varType) : seq (option (SortedBoundedRanges pos.*2.+1)).
Proof.
  have vars' := vars.
  move/(map (option_map (transportSortedBoundedRanges
                           (inner_addn1 pos)))) in vars'.
  apply: foldl _ vars' varRefs => vars' v.

  (* jww (2015-01-30): The [regReq] field is presently not being used. *)
  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired vinfo v |}.
  have Hodd : odd upos by rewrite /= odd_double.

  apply: (set_nth None vars' (varId vinfo v) _).
  apply: Some _.
  rewrite /SortedBoundedRanges.
  rewrite /BoundedRange.
  case: (nth None vars (varId vinfo v)) => [[[r|r rs] /= Hlt]|];
    last first.
  - apply: exist _ (NE_Sing _) _.
    apply: exist _ (exist _ _ (R_Sing Hodd)) _ => //=.
    by constructor.
  - admit.
  - admit.
Defined.

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

  set r := exist _ _ (R_Sing Hodd).
  apply: (vreplace regs' reg _).
  apply: Some _.
  case: (vnth regs reg) => [[[d i] /= Hlt]|];
    last exact: exist _ (exist _ _ (I_Sing 0 Whole r.2)) _.

  case: d => [iv ib ie ik rds] in i Hlt *.
  rewrite /= in Hlt.
  have Hrds: rend r.1 < rbeg (NE_head rds).1.
    rewrite /r /=.
    by rewrite doubleS in Hlt.
  move: (Interval_exact_beg i)
        (Interval_exact_end i) => /= Hbeg Hend.
  move: Hbeg Hend i => -> -> i.
  exact: exist _ (exist _ _ (I_Cons i Hrds)) _ => //=.
Defined.

Definition reduceOp {pos} (op : opType1) (block : blockType1)
  (bs : BuildState pos.+1) : BuildState pos :=
  let: (varRefs, regRefs) := opRefs oinfo op in

  (* If the operation is a function call, assuming it makes use of every
     register.
     jww (2015-01-30): This needs to be improved to consider the calling
     convention of the operation. *)
  let regRefs' := if opKind oinfo op is IsCall
                  then enum 'I_maxReg
                  else regRefs in
  undefined
  (* {| bsVars := map (option_map (transportSortedBoundedRanges (ltnSSn _))) *)
  (*                  (bsVars bs) *)
  (*  ; bsRegs := setIntervalsForRegs (bsRegs bs) regRefs' |} *)
.

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
        foldl (fun m v => maxn m (varId vinfo v)) n
              (fst (opRefs oinfo op)))
        0 blocks in
  let fix go b bs pos : BuildState pos :=
      let bid  := blockId binfo b in
      let outs := if IntMap_lookup bid liveSets isn't Some ls
                  then emptyIntSet
                  else blockLiveOut ls in
      reduceBlock outs $ match bs with
        | nil => {| bsVars := nseq highestVar.+1 None
                  ; bsRegs := vconst None |}
        | cons b' bs' => go b' bs' (pos + size (blockOps binfo b))
        end in
  match blocks with
  | [::] => {| bsVars := nseq highestVar.+1 None
             ; bsRegs := vconst None |}
  | x :: xs => go x xs 0
  end.

Definition buildIntervals (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : ScanStateSig InUse :=
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
        (ss  : ScanStateSig Pending)
        (pos : nat)
        (mrs : option (SortedBoundedRanges pos.*2.+1))
        (f   : forall sd, ScanState Pending sd
                 -> forall d, Interval d -> ScanStateSig Pending) :=
      if mrs is Some rs
      then f _ ss.2 _ (packInterval (Interval_fromRanges vid rs)).2
      else ss in

  let handleVar pos vid ss mrs :=
      mkint vid ss pos mrs $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i I) in

  (fun (bs : BuildState 0) =>
     let s0 := ScanState_nil in
     let f mx := if mx is Some x then Some x.1 else None in
     let regs := vmap f (bsRegs bs) in
     let s1 := ScanState_setFixedIntervals s0 regs in
     let s2 := packScanState s1 in
     let s3 := foldl_with_index (handleVar 0) s2 undefined (* (bsVars bs) *) in
     let s4 := ScanState_finalize s3.2 in
     packScanState s4)
  (reduceBlocks blocks liveSets).

(************************************************************************)

(*
Record BuildState := {
  bsPos  : nat;
  bsVars : seq (option (BoundedRange bsPos.*2.+1));
  bsRegs : Vec (option (BoundedInterval bsPos.*2.+1)) maxReg
}.

(* For each virtual variable references, add a use position to a [Range]
   corresponding to that variable.  These ranges are concatenated together and
   will form a single [Interval] at the end.  This is different from how
   Wimmer builds them up, and is more simplistic, but is sufficient for now.

   jww (2015-01-30): The more efficient solution would be to implement the
   algorithm from his paper. *)
Definition createRangeForVars (pos : nat)
  (vars : seq (option (BoundedRange (pos.+1).*2.+1)))
  (varRefs : seq varType) : seq (option (BoundedRange pos.*2.+1)).
Proof.
  have vars' := vars.
  move/(map (option_map (transportBoundedRange
                           (inner_addn1 pos)))) in vars'.
  apply: foldl _ vars' varRefs => vars' v.

  (* jww (2015-01-30): The [regReq] field is presently not being used. *)
  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired vinfo v |}.
  have Hodd : odd upos by rewrite /= odd_double.

  apply: (set_nth None vars' (varId vinfo v) _).
  apply: Some _.
  case: (nth None vars (varId vinfo v)) => [[r /= Hlt]|];
    last exact: exist _ (exist _ _ (R_Sing Hodd)) _.

  apply: exist _ (exist _ _ (R_Cons Hodd r.2 _)) _ => //=.
  rewrite doubleS in Hlt.
  exact/ltnW.
Defined.

(* For each register that is explicitly referenced by the operation, build up
   a [Interval] which excludes this register from use, but only at specific
   one-position wide ranges. *)
Definition createIntervalForRegs (pos : nat)
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

  set r := exist _ _ (R_Sing Hodd).
  apply: (vreplace regs' reg _).
  apply: Some _.
  case: (vnth regs reg) => [[[d i] /= Hlt]|];
    last exact: exist _ (exist _ _ (I_Sing 0 Whole r.2)) _.

  case: d => [iv ib ie ik rds] in i Hlt *.
  rewrite /= in Hlt.
  have Hrds: rend r.1 < rbeg (NE_head rds).1.
    rewrite /r /=.
    by rewrite doubleS in Hlt.
  move: (Interval_exact_beg i)
        (Interval_exact_end i) => /= Hbeg Hend.
  move: Hbeg Hend i => -> -> i.
  exact: exist _ (exist _ _ (I_Cons i Hrds)) _ => //=.
Defined.

Definition processOperations (blocks : seq blockType1) : BuildState.
  have := foldOps (fun x op => let: (n, m) := x in
    (n.+1, foldl (fun m v => maxn m (varId vinfo v))
                 m (fst (opRefs oinfo op))))
    (0, 0) blocks.
  move=> [opCount highestVar].
  pose z := {| bsPos  := opCount
             ; bsVars := nseq highestVar.+1 None
             ; bsRegs := vconst None |}.
  apply: (foldOpsRev _ z blocks).
  case=> [pos vars regs] op.
  case: pos => [|pos] in vars regs *.
    exact {| bsPos  := 0
           ; bsVars := vars
           ; bsRegs := regs |}.
  move: (opRefs oinfo op) => [varRefs regRefs].
  apply: {| bsPos  := pos |}.
    exact: createRangeForVars.

  (* If the operation is a function call, assuming it makes use of every
     register.

     jww (2015-01-30): This needs to be improved to consider the calling
     convention of the operation. *)
  have regRefs' := if opKind oinfo op is IsCall
                   then enum 'I_maxReg else regRefs.
  clear regRefs.
  exact: createIntervalForRegs.
Defined.

Definition buildIntervals (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : ScanStateSig InUse :=
  let mkint (vid : VarId)
            (ss : ScanStateSig Pending)
            (pos : nat)
            (mx : option (BoundedRange pos.*2.+1))
            (f : forall sd, ScanState Pending sd -> forall d, Interval d
                   -> ScanStateSig Pending) :=
      let: exist _ st := ss in
      if mx is Some (exist r _)
      then f _ st _ (I_Sing vid Whole r.2)
           (* jww (2015-01-20): At the present time there is no use of
              "lifetime holes", and so [I_Cons] is never used here. *)
      else ss in

  let handleVar pos vid ss mx :=
      mkint vid ss pos mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i I) in

  (fun bs =>
     let s0 := ScanState_nil in
     let f mx := if mx is Some x then Some x.1 else None in
     let regs := vmap f (bsRegs bs) in
     let s1 := ScanState_setFixedIntervals s0 regs in
     let s2 := packScanState s1 in
     let s3 := foldl_with_index (handleVar (bsPos bs)) s2 (bsVars bs) in
     let s4 := ScanState_finalize s3.2 in
     packScanState s4)
  (processOperations blocks).
*)

(************************************************************************)

End Build.

End MBuild.
