Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.Range.
Require Import LinearScan.ScanState.
Require Import LinearScan.Graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MBlocks (Mach : Machine).

Include MScanState Mach.

Section Blocks.

Open Scope program_scope.

Variables accType    : Set.
Variables blockType1 : Set.
Variables blockType2 : Set.
Variables opType1    : Set.
Variables opType2    : Set.
Variables varType    : Set.

Inductive VarKind : Set := Input | Temp | Output.

Definition VarId := nat.

(* [VarInfo] abstracts information about the caller's notion of variables
   associated with an operation. *)
Record VarInfo (varType : Set) := {
  varId       : varType -> VarId;     (* from 0 to highest var index *)
  varKind     : varType -> VarKind;
  regRequired : varType -> bool
}.

Variable vinfo : VarInfo varType.

Inductive OpKind : Set :=
  IsNormal | IsCall | IsBranch | IsLoopBegin | IsLoopEnd.

(* The [OpInfo] structure is a collection of functions that allow us to
   determine information about each operation coming from the caller's
   side. *)
Record OpInfo (accType opType1 opType2 varType : Set) := {
  opKind      : opType1 -> OpKind;
  opRefs      : opType1 -> seq varType * seq PhysReg;
  moveOp      : PhysReg -> PhysReg -> accType -> seq opType2 * accType;
  swapOp      : PhysReg -> PhysReg -> accType -> seq opType2 * accType;
  saveOp      : PhysReg -> option VarId -> accType -> seq opType2 * accType;
  restoreOp   : option VarId -> PhysReg -> accType -> seq opType2 * accType;
  applyAllocs : opType1 -> seq (VarId * PhysReg) -> seq opType2
}.

Variable oinfo : OpInfo accType opType1 opType2 varType.

Definition BlockId := nat.

Record BlockInfo (blockType1 blockType2 opType1 opType2 : Set) := {
  blockId         : blockType1 -> BlockId;
  blockSuccessors : blockType1 -> seq BlockId;
  blockOps        : blockType1 -> seq opType1;
  setBlockOps     : blockType1 -> seq opType2 -> blockType2
}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.

(* jww (2015-01-12): Some of the things described by Wimmer in the section on
   dealing with computing of intervals have yet to be done:

   - Loop handling (reordering blocks to optimize allocation)
   - Extending of ranges for input/output variables
*)

Definition foldOps {a} (f : a -> opType1 -> a) (z : a) :
  seq blockType1 -> a :=
  foldl (fun bacc blk => foldl f bacc (blockOps binfo blk)) z.

Definition countOps : seq blockType1 -> nat := foldOps (fun acc _ => acc.+1) 0.

Definition foldOpsRev {a} (f : a -> opType1 -> a) (z : a)
  (blocks : seq blockType1) : a :=
  foldl (fun bacc blk => foldl f bacc (rev (blockOps binfo blk)))
        z (rev blocks).

(* jww (2014-11-19): Note that we are currently not computing the block order
   in any intelligent way. This is covered in quite some depth in Christian
   Wimmer's thesis.  At the moment we're simply accepting whatever block order
   is passed to us by the caller.  However, implementing this function
   properly is a strong means of improving the accuracy and efficiency of this
   algorithm. *)
Definition computeBlockOrder (blocks : seq blockType1) : seq blockType1 :=
  blocks.

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations (blocks : seq blockType1) : seq blockType1 :=
  blocks.

Inductive IntMap (a : Type) :=
  | emptyIntMap
  | getIntMap of seq (nat * a).

Arguments emptyIntMap [a].
Arguments getIntMap [a] _.

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntMap_lookup : forall a, nat -> IntMap a -> option a :=
  fun _ _ _ => None.
Definition IntMap_insert : forall a, nat -> a -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.
Definition IntMap_alter : forall a,
  (option a -> option a) -> nat -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.

Definition IntMap_toList {a} (m : IntMap a) : seq (nat * a) :=
  match m with
    | emptyIntMap => nil
    | getIntMap xs => xs
  end.

Definition prepend (a : eqType) (x : a) mxs :=
  if mxs is Some xs
  then if x \notin xs
       then Some (x :: xs)
       else Some xs
  else Some [:: x].

Inductive IntSet :=
  | emptyIntSet
  | getIntSet of seq nat.

Arguments emptyIntSet.
Arguments getIntSet _.

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntSet_member     : nat -> IntSet -> bool      := fun _ _ => false.
Definition IntSet_insert     : nat -> IntSet -> IntSet    := fun _ x => x.
Definition IntSet_union      : IntSet -> IntSet -> IntSet := fun _ x => x.
Definition IntSet_difference : IntSet -> IntSet -> IntSet := fun _ x => x.

Definition IntSet_foldl : forall a, (a -> nat -> a) -> a -> IntSet -> a :=
  fun _ _ z _ => z.

Definition IntSet_forFold {a} (z : a) (m : IntSet) (f: a -> nat -> a) : a :=
  IntSet_foldl f z m.

Definition OpId := nat.

Record BlockLiveSets := {
  blockLiveGen   : IntSet;
  blockLiveKill  : IntSet;
  blockLiveIn    : IntSet;
  blockLiveOut   : IntSet;
  blockFirstOpId : OpId;
  blockLastOpId  : OpId
}.

Definition computeLocalLiveSets (blocks : seq blockType1) :
  IntMap BlockLiveSets :=
  (* for each block b in blocks do
       b.live_gen  = { }
       b.live_kill = { }

       for each operation op in b.operations do
         visitor.visit(op)

         for each virtual register opr in visitor.input_oprs do
           if opr ∉ block.live_kill then
             b.live_gen = b.live_gen ∪ { opr }
         end for

         for each virtual register opr in visitor.temp_oprs do
           b.live_kill = b.live_kill ∪ { opr }
         end for

         for each virtual register opr in visitor.output_oprs do
           b.live_kill = b.live_kill ∪ { opr }
         end for
       end for
     end for *)
  @snd _ _ $
  forFold (1, emptyIntMap) blocks $ fun acc b =>
    let: (idx, m) := acc in
    let liveSet :=
        {| blockLiveGen   := emptyIntSet
         ; blockLiveKill  := emptyIntSet
         ; blockLiveIn    := emptyIntSet
         ; blockLiveOut   := emptyIntSet
         ; blockFirstOpId := idx
         ; blockLastOpId  := idx
         |} in
    let: (lastIdx', liveSet3) :=
      forFold (idx, liveSet) (blockOps binfo b) $ fun acc o =>
        let: (lastIdx, liveSet1) := acc in
        (lastIdx.+2,
         forFold liveSet1 (fst (opRefs oinfo o)) $ fun liveSet2 v =>
           let vid := varId vinfo v in
           if varKind vinfo v is Input
           then
             if ~~ (IntSet_member vid (blockLiveKill liveSet2))
             then {| blockLiveGen   := IntSet_insert vid (blockLiveGen liveSet2)
                   ; blockLiveKill  := blockLiveKill liveSet2
                   ; blockLiveIn    := blockLiveIn liveSet2
                   ; blockLiveOut   := blockLiveOut liveSet2
                   ; blockFirstOpId := blockFirstOpId liveSet2
                   ; blockLastOpId  := lastIdx
                   |}
             else liveSet2
           else
             {| blockLiveGen   := blockLiveGen liveSet2
              ; blockLiveKill  := IntSet_insert vid (blockLiveKill liveSet2)
              ; blockLiveIn    := blockLiveIn liveSet2
              ; blockLiveOut   := blockLiveOut liveSet2
              ; blockFirstOpId := blockFirstOpId liveSet2
              ; blockLastOpId  := lastIdx
              |})
      in
    (lastIdx', IntMap_insert (blockId binfo b) liveSet3 m).

Definition computeGlobalLiveSets (blocks : seq blockType1)
  (liveSets : IntMap BlockLiveSets) : IntMap BlockLiveSets :=
  (* do
       for each block b in blocks in reverse order do
         b.live_out = { }
         for each successor sux of b do
           b.live_out = b.live_out ∪ sux.live_in
         end for

         b.live_in = (b.live_out – b.live_kill) ∪ b.live_gen
       end for
     while change occurred in any live set *)
  forFold liveSets (rev blocks) $ fun liveSets1 b =>
    let bid := blockId binfo b in
    match IntMap_lookup bid liveSets1 with
    | None => liveSets1         (* should never happen *)
    | Some liveSet =>
      let liveSet2 :=
        forFold liveSet (blockSuccessors binfo b) $ fun liveSet1 s_bid =>
          match IntMap_lookup s_bid liveSets1 with
          | None => liveSet1  (* should never happen *)
          | Some sux =>
            {| blockLiveGen   := blockLiveGen liveSet1
             ; blockLiveKill  := blockLiveKill liveSet1
             ; blockLiveIn    := blockLiveIn liveSet1
             ; blockLiveOut   := IntSet_union (blockLiveOut liveSet1)
                                              (blockLiveIn sux)
             ; blockFirstOpId := blockFirstOpId liveSet1
             ; blockLastOpId  := blockLastOpId liveSet1
             |}
          end
        in
      IntMap_insert bid
        {| blockLiveGen   := blockLiveGen liveSet2
         ; blockLiveKill  := blockLiveKill liveSet2
         ; blockLiveIn    :=
             IntSet_union (IntSet_difference (blockLiveOut liveSet2)
                                             (blockLiveKill liveSet2))
                          (blockLiveGen liveSet2)
         ; blockLiveOut   := blockLiveOut liveSet2
         ; blockFirstOpId := blockFirstOpId liveSet2
         ; blockLastOpId  := blockLastOpId liveSet2
         |} liveSets1
    end.

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

Record BuildState (pos : nat) := {
  bsVars : seq (option (SortedBoundedRanges pos.*2.+1));
  bsRegs : Vec (option (BoundedInterval pos.*2.+1)) maxReg
}.

Definition transportSortedBoundedRanges {base : nat} `(Hlt : base < prev)
  (sr : SortedBoundedRanges prev) : SortedBoundedRanges base.
Proof.
  case: sr => [rs Hsort].
  exists (NE_map (transportBoundedRange Hlt) rs).
  elim: rs => [r|r rs IHrs] /= in Hsort *.
    by constructor.
  constructor; inversion Hsort; subst.
    exact: IHrs.
  exact: NE_Forall_transport.
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
  {| bsVars := map (option_map (transportSortedBoundedRanges (ltnSSn _)))
                   (bsVars bs)
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
      foldOps (fun n op =>
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
  | nil => {| bsVars := nseq highestVar.+1 None
            ; bsRegs := vconst None |}
  | cons x xs => go x xs 0
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
     let s3 := foldl_with_index (handleVar 0) s2 (bsVars bs) in
     let s4 := ScanState_finalize s3.2 in
     packScanState s4)
  (reduceBlocks blocks liveSets).

(*
  have [opCount highestVar] :=
      foldOps (fun x op => let: (n, m) := x in
        (n.+1, foldl (fun m v => maxn m (varId vinfo v))
                     m (fst (opRefs oinfo op))))
        (0, 0) blocks.
  have :=
      {| bsPos  := opCount
       ; bsVars := nseq highestVar.+1 [::]
       ; bsRegs := vconst None |}.
  case=> [pos vars regs].
  case: pos => [|pos] in vars regs *.
    exact {| bsPos  := 0
           ; bsVars := vars
           ; bsRegs := regs |}.

  apply: {| bsPos := pos |}.
  move: (opRefs oinfo op) => [varRefs regRefs].
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

  let fix go pos (bst : BuildState pos) bs :=
    if bs isn't b :: bs then bst else
    let bid  := blockId binfo b in
    let outs := if IntMap_lookup bid liveSets isn't Some ls
                then emptyIntSet
                else blockLiveOut ls in
    match pos with
    | 0 => bst
    | S pos' =>
      let Heqe : pos'.+1 = pos := undefined in
      let bst' :=
        forFold bst (rev (blockOps binfo b)) $ fun bst' op =>
          let: (varRefs, regRefs) := opRefs oinfo op in

          (* If the operation is a function call, assuming it makes use of every
             register.
             jww (2015-01-30): This needs to be improved to consider the calling
             convention of the operation. *)
          let regRefs' := if opKind oinfo op is IsCall
                          then enum 'I_maxReg
                          else regRefs in
          let bsRegs' := @setIntervalsForRegs pos' (bsRegs bst') regRefs' in
          {| bsVars := map (map (transportBoundedRange _)) (bsVars bst')
           ; bsRegs := bsRegs' |} in
      bst'
    end in
  go bst0 opCount (rev blocks).

  forFold bst0 (rev blocks) $ fun bst1 b => match bsPos bst1 with
    | 0 =>
        {| bsPos  := 0
         ; bsVars := map (map (transportBoundedRange _)) (bsVars bst1)
         ; bsRegs := vmap (option_map (transportBoundedInterval _))
                          (bsRegs bst1)
         |}
    | S pos =>
      let bid  := blockId binfo b in
      let outs := if IntMap_lookup bid liveSets isn't Some ls
                  then emptyIntSet
                  else blockLiveOut ls in
      let bst4 :=
        forFold bst1 (rev (blockOps binfo b)) $ fun bst2 op =>
          let: (varRefs, regRefs) := opRefs oinfo op in

          (* If the operation is a function call, assuming it makes use of every
             register.
             jww (2015-01-30): This needs to be improved to consider the calling
             convention of the operation. *)
          let regRefs' := if opKind oinfo op is IsCall
                          then enum 'I_maxReg
                          else regRefs in
          let bst3 := @setIntervalsForRegs pos (bsRegs bst2) regRefs' in
          bst3 in
      bst4
    end.

Definition buildIntervals (blocks : seq blockType1) : ScanStateSig InUse :=
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

Definition checkIntervalBoundary `(st : ScanState InUse sd)
  key in_from from to mappings vid :=

  let mfrom_int := lookupInterval st vid (blockLastOpId from) in
  if mfrom_int isn't Some from_interval then mappings else
    (* jww (2015-01-28): Failing case should be provably impossible *)

  let mto_int := lookupInterval st vid (blockFirstOpId to) in
  if mto_int isn't Some to_interval then mappings else
    (* jww (2015-01-28): Failing case should be provably impossible *)

  (* If the interval match, no move resolution is necessary. *)
  if from_interval == to_interval then mappings else

  let msreg := lookupRegister st from_interval in
  let mdreg := lookupRegister st to_interval in

  let addToGraphs e xs :=
      let: (gbeg, gend) := xs in
      if in_from
      then (gbeg, addEdge e gend)
      else (addEdge e gbeg, gend) in
  let f mxs :=
      let e := (msreg, mdreg) in
      @Some _ $ addToGraphs e
              $ if mxs is Some xs
                then xs
                else (emptyGraph, emptyGraph) in
  IntMap_alter f key mappings.

Definition BlockMoves :=
  (Graph (ordinal_eqType maxReg) * Graph (ordinal_eqType maxReg))%type.

Definition resolveDataFlow `(st : ScanState InUse sd)
  (blocks : seq blockType1) (liveSets : IntMap BlockLiveSets) :
  IntMap BlockMoves :=
  (* for each block from in blocks do
       for each successor to of from do
         // collect all resolving moves necessary between the blocks from
         // and to
         for each operand opr in to.live_in do
           Interval parent_interval = intervals[opr]

           Interval from_interval = parent_interval.child_at(from.last_op.id)
           Interval to_interval = parent_interval.child_at(to.first_op.id)

           if from_interval ≠ to_interval then
             // interval was split at the edge between the blocks from and to
             resolver.add_mapping(from_interval, to_interval)
           end if
         end for

         // the moves are inserted either at the end of block from or at the
         // beginning of block to, depending on the control flow
         resolver.find_insert_position(from, to)

         // insert all moves in correct order (without overwriting registers
         // that are used later)
         resolver.resolve_mappings()
       end for
     end for *)
  forFold emptyIntMap blocks $ fun mappings b =>
    let bid := blockId binfo b in
    match IntMap_lookup bid liveSets with
    | None => mappings          (* jww (2015-01-28): Should be impossible *)
    | Some from =>
      (fun successors =>
        let in_from := size successors <= 1 in
        forFold mappings successors $ fun ms s_bid =>
          match IntMap_lookup s_bid liveSets with
          | None => ms          (* jww (2015-01-28): Should be impossible *)
          | Some to =>
              let key := if in_from then bid else s_bid in
              IntSet_forFold ms (blockLiveIn to) $
                checkIntervalBoundary st key in_from from to
          end)
      (blockSuccessors binfo b)
    end.

Section Allocation.

Require Import LinearScan.State.

Record AssnStateInfo := {
  assnOpId : OpId;
  assnAcc  : accType
}.

Definition AssnState := State AssnStateInfo.

Definition moveOpM sreg dreg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (mop, acc') := moveOp oinfo sreg dreg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure mop.

Definition saveOpM vid reg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (sop, acc') := saveOp oinfo vid reg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure sop.

Definition restoreOpM vid reg : AssnState (seq opType2) :=
  assn <-- get ;;
  let: (rop, acc') := restoreOp oinfo vid reg (assnAcc assn) in
  put {| assnOpId := assnOpId assn
       ; assnAcc  := acc' |} ;;
  pure rop.

Definition pairM {A B : Type} (x : AssnState A) (y : AssnState B) :
  AssnState (A * B)%type :=
  x' <-- x ;;
  y' <-- y ;;
  pure (x', y').

Definition savesAndRestores opid vid reg int :
  AssnState (seq opType2 * seq opType2) :=
  let isFirst := firstUsePos int == opid in
  let isLast  := nextUseAfter int opid == None in
  let save    := saveOpM reg (Some vid) in
  let restore := restoreOpM (Some vid) reg in
  match iknd int, isFirst, isLast with
    | Middle,    true,  true  => pairM restore save
    | Middle,    false, true  => pairM (pure [::]) save
    | Middle,    true,  false => pairM restore (pure [::])
    | LeftMost,  _,     true  => pairM (pure [::]) save
    | RightMost, true,  _     => pairM restore (pure [::])
    | _,         _,     _     => pure ([::], [::])
    end.

Definition collectAllocs opid ints acc v :=
  let vid := varId vinfo v in
  let v_ints := [seq x <- ints | isWithin (fst x) vid opid] in
  if v_ints is (int, reg) :: _
  return AssnState (seq (VarId * PhysReg) *
                    seq opType2 * seq opType2)
  then
    let: (allocs', restores', saves') := acc in
    res <-- savesAndRestores opid vid reg int ;;
    let: (rs, ss) := res in
    pure ((vid, reg) :: allocs', rs ++ restores', ss ++ saves')
  else pure acc.

Definition doAllocations ints op : AssnState (seq opType2) :=
  assn <-- get ;;
  let opid := assnOpId assn in
  let vars := fst (opRefs oinfo op) in
  res <-- forFoldM ([::], [::], [::]) vars $ collectAllocs opid ints ;;
  let: (allocs, restores, saves) := res in
  let op' := applyAllocs oinfo op allocs in
  (* With lenses, this would just be: assnOpId += 2 *)
  modify (fun assn' => {| assnOpId := opid.+2
                        ; assnAcc  := assnAcc assn' |}) ;;
  pure $ restores ++ op' ++ saves.

Definition generateMoves (moves : seq (option PhysReg * option PhysReg)) :
  AssnState (seq opType2) :=
  forFoldM [::] moves $ fun acc mv =>
    mops <-- match mv with
      | (Some sreg, Some dreg) => fmap (@Some _) $ moveOpM sreg dreg
      | (Some sreg, None)      => fmap (@Some _) $ saveOpM sreg None
      | (None, Some dreg)      => fmap (@Some _) $ restoreOpM None dreg
      | (None, None)           => pure None
      end ;;
    pure $ if mops is Some ops then ops ++ acc else acc.

Definition resolveMappings bid ops ops' mappings : AssnState (seq opType2) :=
  (* Check whether any boundary transitions require move resolution at the
     beginning or end of the block given by [bid]. *)
  if IntMap_lookup bid mappings isn't Some graphs then pure ops' else

  let: (gbeg, gend) := graphs in

  bmoves <-- generateMoves (topsort gbeg) ;;
  let ops'' := bmoves ++ ops' in

  emoves <-- generateMoves (topsort gend) ;;
  pure $ match ops, ops'' with
    | o :: os, o'' :: os'' =>
        if opKind oinfo (last o os) is IsBranch
        then belast o'' os'' ++ emoves ++ [:: last o'' os'']
        else ops'' ++ emoves
    | _, _ => ops'' ++ emoves
  end.

Definition considerOps (f : opType1 -> AssnState (seq opType2)) mappings :=
  mapM $ fun blk =>
    (* First apply all allocations *)
    let ops := blockOps binfo blk in
    ops' <-- concatMapM f ops ;;
    (* Insert resolving moves based on the mappings *)
    let bid := blockId binfo blk in
    ops'' <-- resolveMappings bid ops ops' mappings ;;
    pure $ setBlockOps binfo blk ops''.

Definition assignRegNum `(st : ScanState InUse sd)
  (mappings : IntMap BlockMoves) (blocks : seq blockType1)
  (acc : accType) : seq blockType2 * accType :=
  let: (blocks', assn) :=
    considerOps
      (doAllocations
         [seq (getIntervalDesc (getInterval (fst x)), snd x)
         | x <- handled sd ++ active sd ++ inactive sd])
      mappings
      blocks
      {| assnOpId := 1
       ; assnAcc := acc |} in
  (blocks', assnAcc assn).

End Allocation.

End Blocks.

End MBlocks.