Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.Ops.
Require Import LinearScan.Range.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MBlocks (Mach : Machine).

Include MOps Mach.
Include MScanState Mach.

Section Blocks.

Open Scope program_scope.

Variable opType : Set.
Variable blockType : Set.

Record BlockInfo := {
  blockToOpList : blockType -> seq opType
}.

Record BlockData := {
  baseBlock : blockType;
  blockInfo : BlockInfo;
  blockOps  : seq (OpData opType)
}.

Inductive BlockList : BlockData -> Prop :=
  | BlockList_newBlock b binfo ops :
      BlockList {| baseBlock := b
                 ; blockInfo := binfo
                 ; blockOps  := ops
                 |}.

(* jww (2014-11-19): Note that we are currently not computing the block order
   in any intelligent way. This is covered in quite some depth in Christian
   Wimmer's thesis.  At the moment we're simply accepting whatever block order
   is passed to us by the caller.  However, implementing this function
   properly is a strong means of improving the accuracy and efficiency of this
   algorithm. *)
Definition computeBlockOrder :
  IState SSError (seq blockType) (seq blockType) unit := return_ tt.

Variable oinfo : OpInfo opType.
Variable binfo : BlockInfo.

Definition wrap_block
  (x : { i : nat | odd i } * seq BlockData) (block : blockType) :=
  let k H op :=
      {| baseOp  := op
       ; opInfo  := oinfo
       ; opId    := H.1
       ; opIdOdd := H.2
       ; opAlloc := nil |} in

  let f x op := match x with
      | (H, ops) => let nop := k H op in
          (exist odd (H.1).+2 (odd_add_2 H.2), nop :: ops)
      end in

  let: (H, blocks) := x in
  let: (H', ops')  := foldl f (H, nil) (blockToOpList binfo block) in
  let blk := {| baseBlock := block
              ; blockInfo := binfo
              ; blockOps  := rev ops' |} in
  (H', blk :: blocks).

(* Confirm that [wrap_block] works for a single block that has three
   operations. *)
Lemma wrap_block_spec : forall x y z b blk,
  [:: x; y; z] = blockToOpList binfo blk
    -> snd (wrap_block (exist odd 1 odd_1, nil) blk) = [:: b]
    -> blockOps b =
       [:: {| baseOp  := x
            ; opInfo  := oinfo
            ; opId    := 1
            ; opIdOdd := odd_1
            ; opAlloc := nil
            |}
       ;   {| baseOp  := y
            ; opInfo  := oinfo
            ; opId    := 3
            ; opIdOdd := odd_add_2 odd_1
            ; opAlloc := nil
            |}
       ;   {| baseOp  := z
            ; opInfo  := oinfo
            ; opId    := 5
            ; opIdOdd := odd_add_2 (odd_add_2 odd_1)
            ; opAlloc := nil
            |}
       ].
Proof.
  move=> x y z b blk Heq.
  rewrite /wrap_block -{}Heq /=.
  by invert.
Qed.

(* Next, check that it works for two blocks, each of which has three
  operations, and that numbering can continue across the blocks. *)
Lemma wrap_block_spec2 :
  forall a b c x y z b1 b2 blk1 blk2 H H',
  [:: a; b; c] = blockToOpList binfo blk1
    -> [:: x; y; z] = blockToOpList binfo blk2
    -> wrap_block (exist odd 1 odd_1, nil) blk1 = (H, [:: b1])
    -> wrap_block (H, nil) blk2 = (H', [:: b2])
    -> blockOps b1 =
       [:: {| baseOp  := a
            ; opInfo  := oinfo
            ; opId    := 1
            ; opIdOdd := odd_1
            ; opAlloc := nil
            |}
       ;   {| baseOp  := b
            ; opInfo  := oinfo
            ; opId    := 3
            ; opIdOdd := odd_add_2 odd_1
            ; opAlloc := nil
            |}
       ;   {| baseOp  := c
            ; opInfo  := oinfo
            ; opId    := 5
            ; opIdOdd := odd_add_2 (odd_add_2 odd_1)
            ; opAlloc := nil
            |}
       ]
    /\ blockOps b2 =
       [:: {| baseOp  := x
            ; opInfo  := oinfo
            ; opId    := 7
            ; opIdOdd := odd_add_2 (odd_add_2 (odd_add_2 odd_1))
            ; opAlloc := nil
            |}
       ;   {| baseOp  := y
            ; opInfo  := oinfo
            ; opId    := 9
            ; opIdOdd := odd_add_2 (odd_add_2 (odd_add_2 (odd_add_2 odd_1)))
            ; opAlloc := nil
            |}
       ;   {| baseOp  := z
            ; opInfo  := oinfo
            ; opId    := 11
            ; opIdOdd := odd_add_2
                           (odd_add_2
                              (odd_add_2 (odd_add_2 (odd_add_2 odd_1))))
            ; opAlloc := nil
            |}
       ].
Proof.
  move=> a b c x y z b1 b2 blk1 blk2 H H' Heq Heq2.
  rewrite /wrap_block /= -{}Heq -{}Heq2 /=.
  by invert; invert.
Qed.

Definition blocksToBlockList : seq blockType -> seq BlockData :=
  @snd _ _ \o foldl wrap_block (exist odd 1 odd_1, nil).

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations :
  IState SSError (seq blockType) (seq BlockData) unit :=
  imodify SSError blocksToBlockList.

Definition BlockState := IState SSError (seq BlockData) (seq BlockData).

(* jww (2014-12-01): The following two functions are used for computing
   accurate live ranges. they constitute a dataflow analysis which determines
   the true live range for variables referenced from loops.  At the moment
   these are being left unimplemented, but this is very likely something that
   will need to be done for the sake of the correctness of the algorithm. *)
Definition computeLocalLiveSets : BlockState unit := return_ tt.
Definition computeGlobalLiveSets : BlockState unit := return_ tt.

Definition buildIntervals : BlockState (seq (OpData opType) * ScanStateSig) :=
  let mkint (vid : nat)
            (ss : ScanStateSig)
            (mx : option RangeSig)
            (f : forall sd, ScanState sd -> forall d, Interval d
                   -> ScanStateSig) :=
      let: (exist sd st) := ss in match mx with
           | Some (exist _ r) => f _ st _ (I_Sing vid r)
           | None => ss
           end in

  let handleVar vid ss mx := mkint vid ss mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i) in

  bxs <<- iget SSError ;;
  let: blocks := bxs in
  let ops := flatten (map (blockToOpList binfo \o baseBlock) blocks) in
  let: (ops', varRanges, regRanges) := processOperations oinfo ops in
  let regs := vmap (fun mr =>
                      if mr is Some r
                      then Some (packInterval (I_Sing 0 r.2))
                      else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  return_ $ (ops', foldl_with_index handleVar s2 varRanges).

Definition surjective `(f : X -> Y) : Prop := forall y, exists x, f x = y.

Goal { n : nat | surjective (plus n) }.
Proof.
  exists 0.
  rewrite /surjective.
  move=> y.
  exists y.
  reflexivity.
Qed.

Definition resolveDataFlow : BlockState unit := return_ tt.

Definition assignRegNum (ops : seq (OpData opType)) `(st : ScanState sd) :
  BlockState (seq (OpData opType)) :=
  let f op :=
      let o := baseOp op in
      let vars := varRefs (opInfo op) o in
      let k acc v :=
          let vid := varId v in
          let g h x :=
              let: (xid, reg) := x in
              let int := getInterval xid in
              if (ivar int == vid) &&
                 (ibeg int <= opId op < iend int)
              then (vid, Register reg) :: h
              else h in
          {| baseOp  := o
           ; opInfo  := opInfo op
           ; opId    := opId op
           ; opIdOdd := opIdOdd op
           ; opAlloc := foldl g nil (handled sd)
           |} in
      foldl k op vars in
  return_ $ map f ops.

End Blocks.

Arguments computeBlockOrder {blockType}.
Arguments numberOperations {opType blockType} oinfo binfo.
Arguments computeLocalLiveSets {opType blockType}.
Arguments computeGlobalLiveSets {opType blockType}.
Arguments buildIntervals {opType _} oinfo binfo.
Arguments resolveDataFlow {opType blockType}.
Arguments assignRegNum {opType blockType} ops {sd} st.

End MBlocks.