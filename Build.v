Require Import LinearScan.Lib.
Require Import LinearScan.Ltac.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.Proto.
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
  bsVars : seq (option (BoundedRange pos.*2.+1));
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

  have H: pos.*2.+1 <= pos.*2.+1 < pos.*2.+2 by ordered.
  pose r := packRange (R_cons Hodd (R_nil (ltnSn (uloc upos))) H).
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

(*
(* Create a proto range to represent a variable reference. *)
Definition reduceVar pos (block : blockType1) (var : varType)
  `(Hpos : begin <= pos < begin + blockSize binfo block)
  (p : ProtoRange pos.*2.+1) : ProtoRange pos.*2.+1.
Proof.
  set upos := {| uloc   := pos.*2.+1
               ; regReq := regRequired var |}.

  set knd := varKind var.
  case: (prUseLocs p) => [|u us].
    apply:
      {| prBeg := match knd with
           | Input => begin.*2.+1
           | _     => uloc upos
           end
       ; prEnd := match knd with
           | Output => (begin + blockSize binfo block).*2.+1
           | _      => (uloc upos).+1
           end
       ; prUseLocs := [:: upos] |};
  case: knd => //=;
  repeat by rewrite odd_double.
  - rewrite 2!ltnS leq_double.
    by ordered.
  - rewrite ltnS ltn_double.
    by ordered.
  - constructor.
      exact: prUseSorted p.
    admit.
  - constructor.
      exact: prUseSorted p.
    admit.
  - constructor.
      exact: prUseSorted p.
    admit.
  - apply/andP; split.
      by ordered.
    have H := prUseBounded p.
    match_all H.
  VarKind_cases (case: knd) Case.
  - Case "VarKind_Input".

  - Case "VarKind_Temp".
    apply:
      {| prBeg := match knd with
           | Input => begin.*2.+1
           | _     => uloc upos
           end
       ; prEnd := match knd with
           | Output => (begin + blockSize binfo block).*2.+1
           | _      => (uloc upos).+1
           end
       ; prUseLocs := upos :: prUseLocs p
       |} => //=;

  - Case "VarKind_Output".
    apply:
      {| prBeg := match knd with
           | Input => begin.*2.+1
           | _     => uloc upos
           end
       ; prEnd := match knd with
           | Output => (begin + blockSize binfo block).*2.+1
           | _      => (uloc upos).+1
           end
       ; prUseLocs := upos :: prUseLocs p
       |} => //=;

  (* For temp variables a single position range is sufficient.  For an input
     variable, it must extend from the beginning of the block to one beyond
     the use position.  For an output variable, it extensd from the use
     position to the end of the block.

     Variables in the [blockLiveOut] set which are not used otherwise cause an
     empty range to be inserted that extends throughout the entire block. *)
  case: knd) Case.
    admit.

    + admit.
    + admit.
    + admit.
    + admit.
    (* + exact/leqW/leqnn_double. *)
    (* + apply/negPn. *)
    (*   by rewrite odd_double. *)
    (* + by rewrite -2![_.*2.+2]addn2 leq_add2r leq_double. *)
    (* + by repeat constructor. *)
    (* + apply/andP; split=> //. *)
    (*   by rewrite ltnS leq_double. *)
    (* + by apply/andP; split=> //. *)

  - Case "VarKind_Temp".
    apply:
      {| prBeg        := uloc upos
       ; prBegOdd     := Hodd
       ; prEnd        := (uloc upos).+1
       ; prUseLocs    := [:: upos] |} => //=.
    + admit.
    + admit.
    (* + apply/negPn. *)
    (*   by rewrite odd_double. *)
    (* + by repeat constructor. *)
    (* + by apply/andP; split. *)
    (* + by apply/andP; split. *)

  - Case "VarKind_Output".
    apply:
      {| prBeg        := uloc upos
       ; prBegOdd     := Hodd
       ; prEnd        := (begin + blockSize binfo block).*2
       ; prUseLocs    := [:: upos] |} => //=.
    + admit.
    + admit.
    + admit.
    (* + apply/negPn. *)
    (*   by rewrite odd_double. *)
    (* + apply: ltn_even. *)
    (*   by apply/andP; split; rewrite odd_double. *)
    (* + by rewrite ltn_double. *)
    (* + by repeat constructor. *)
    (* + by apply/andP; split=> //. *)
    (* + apply/andP; split=> //. *)
    (*   apply: ltn_even. *)
    (*     by apply/andP; split; rewrite odd_double. *)
    (*   by rewrite ltn_double. *)
Defined.
*)

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

(*
Lemma uniq_nil {a} : uniq (T:=a) [::].
Proof. by []. Qed.

(* Given a list a of variable uses, it is possible that the same variable is
   used more than once (for example, as both the input and output of an
   instruction that leaves the result in the input register).  In those cases,
   we must combine the multiple [VarInfo] records into the most informative
   version of the collective information. *)
Program Fixpoint refineVars (vars : seq VarInfo) {measure (size vars)} :
  { vs : seq VarInfo | uniq [seq varId v | v <- vs] } :=
  match vars with
  | [::] => exist _ [::] uniq_nil
  | x :: xs =>
      let vs := [seq y <- xs | varId y == varId x] in
      let f v' v :=
          let knd' := match varKind v', varKind v with
            | Input,       Input       => Input
            | Input,       InputOutput => InputOutput
            | Input,       Output      => InputOutput
            | Input,       Temp        => Input
            | Temp,        Input       => Input
            | Temp,        InputOutput => InputOutput
            | Temp,        Output      => Output
            | Temp,        Temp        => Temp
            | Output,      Input       => InputOutput
            | Output,      InputOutput => InputOutput
            | Output,      Output      => Temp
            | Output,      Temp        => Output
            | InputOutput, Input       => InputOutput
            | InputOutput, InputOutput => Temp
            | InputOutput, Output      => InputOutput
            | InputOutput, Temp        => InputOutput
            end in
          {| varId       := varId v
           ; varKind     := knd'
           ; regRequired := regRequired v || regRequired v'
           |} in
      let xs' := refineVars [seq y <- xs | varId y != varId x] in
      exist _ (foldl f x vs :: xs'.1) _
  end.
Obligation 1.
  move=> *.
  apply/ltP.
  rewrite size_filter /= ltnS.
  exact: count_size.
Defined.
Obligation 2.
  set f := (X in foldl X _ _).
  elim: xs => //= [|y ys IHys] in refineVars *.
  set nxs := (X in refineVars X).
  set xs' := (refineVars _ _).
  case: xs' => x0 Huniq /=.
  apply/andP; split=> //.
*)

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

  {| bsVars := undefined
               (* map (option_map (transportSortedProtoRanges (ltnSSn _))) *)
               (*     (bsVars bs) *)
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
        (mrs : option (SortedProtoRanges pos.*2.+1))
        (f   : forall sd, ScanState Pending sd
                 -> forall d, Interval d -> ScanStateSig maxReg Pending) :=
      if mrs is Some rs
      then f _ ss.2 _ (Interval_fromSortedProtoRanges vid rs).2
      else ss in

  let handleVar pos vid ss mrs :=
      mkint vid ss pos mrs $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i I) in

  (fun (bs : BuildState 0) =>
     let s0 := ScanState_nil maxReg in
     let f mx := if mx is Some x then Some x.1 else None in
     let regs := vmap f (bsRegs bs) in
     let s1 := ScanState_setFixedIntervals s0 regs in
     let s2 := packScanState s1 in
     let s3 := foldl_with_index (handleVar 0) s2 undefined (* (bsVars bs) *) in
     let s4 := ScanState_finalize s3.2 in
     packScanState s4)
  (reduceBlocks blocks liveSets).

End Build.