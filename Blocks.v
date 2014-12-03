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
  blockOps  : OpList opType
}.

Definition BlockList := seq BlockData.

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
  (x : { i : nat | odd i } * BlockList) (block : blockType) :=
  let: (H, blocks) := x in

  let k H op :=
      {| baseOp  := op
       ; opInfo  := oinfo
       ; opId    := H.1
       ; opIdOdd := H.2
       ; opAlloc := fun _ => Unallocated |} in

  let f x op :=
      match x with
      | (H, ops) =>
        let nop := k H op in
        (exist odd (H.1).+2 (odd_add_2 H.2), nop :: ops)
      end in

  let: (H', ops') := foldl f (H, nil)
                           (blockToOpList binfo block) in
  let blk :=
      {| baseBlock := block
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
            ; opAlloc := fun _ => Unallocated
            |}
       ;   {| baseOp  := y
            ; opInfo  := oinfo
            ; opId    := 3
            ; opIdOdd := odd_add_2 odd_1
            ; opAlloc := fun _ => Unallocated
            |}
       ;   {| baseOp  := z
            ; opInfo  := oinfo
            ; opId    := 5
            ; opIdOdd := odd_add_2 (odd_add_2 odd_1)
            ; opAlloc := fun _ => Unallocated
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
            ; opAlloc := fun _ => Unallocated
            |}
       ;   {| baseOp  := b
            ; opInfo  := oinfo
            ; opId    := 3
            ; opIdOdd := odd_add_2 odd_1
            ; opAlloc := fun _ => Unallocated
            |}
       ;   {| baseOp  := c
            ; opInfo  := oinfo
            ; opId    := 5
            ; opIdOdd := odd_add_2 (odd_add_2 odd_1)
            ; opAlloc := fun _ => Unallocated
            |}
       ]
    /\ blockOps b2 =
       [:: {| baseOp  := x
            ; opInfo  := oinfo
            ; opId    := 7
            ; opIdOdd := odd_add_2 (odd_add_2 (odd_add_2 odd_1))
            ; opAlloc := fun _ => Unallocated
            |}
       ;   {| baseOp  := y
            ; opInfo  := oinfo
            ; opId    := 9
            ; opIdOdd := odd_add_2 (odd_add_2 (odd_add_2 (odd_add_2 odd_1)))
            ; opAlloc := fun _ => Unallocated
            |}
       ;   {| baseOp  := z
            ; opInfo  := oinfo
            ; opId    := 11
            ; opIdOdd := odd_add_2
                           (odd_add_2
                              (odd_add_2 (odd_add_2 (odd_add_2 odd_1))))
            ; opAlloc := fun _ => Unallocated
            |}
       ].
Proof.
  move=> a b c x y z b1 b2 blk1 blk2 H H' Heq Heq2.
  rewrite /wrap_block /= -{}Heq -{}Heq2 /=.
  by invert; invert.
Qed.

Definition blocksToBlockList : seq blockType -> BlockList :=
  @snd _ _ \o foldl wrap_block (exist odd 1 odd_1, nil).

(* This function not only numbers all operations for us, but adds any extra
   administrative information that we need to process the algorithm on this
   side, while maintaining links to the original data that was sent to us from
   the caller.  From this point on, all functions operate on this enriched
   data, which ultimately gets reduced back to the caller's version of the
   data at the very end. *)
Definition numberOperations : IState SSError (seq blockType) BlockList unit :=
  imodify SSError blocksToBlockList.

Inductive relseq {a : Type} (R : rel a) : seq a -> Type :=
  | rl_nil         : relseq R nil
  | rl_sing x      : relseq R [:: x]
  | rl_cons x xs y : relseq R (x :: xs) -> R y x -> relseq R (y :: x :: xs).

Definition is_seqn (x y : OpData opType) := opId x == (opId y).+2.

Definition rel_OpList := { xs : seq (OpData opType) & relseq is_seqn xs }.

Lemma foldl_cons : forall a b f (z : b) (x : a) xs,
  foldl f z (x :: xs) = foldl f (f z x) xs.
Proof. move=> a b f z x; elim=> //=. Qed.

Lemma foldr_cons : forall a b f (z : b) (x : a) xs,
  foldr f z (x :: xs) = f x (foldr f z xs).
Proof. move=> a b f z x; elim=> //=. Qed.

(*
Definition wrap_block' (opInfo : OpInfo opType) (blockInfo : BlockInfo)
  (x : { i : nat | odd i } * BlockList * rel_OpList) (block : blockType) :=
  let: (H, blocks, rops) := x in

  let k H op :=
      {| baseOp  := op
       ; opInfo  := opInfo
       ; opId    := H.1
       ; opIdOdd := H.2
       ; opAlloc := fun _ => Unallocated |} in

  let f (x : { i : nat | odd i } * seq (OpData opType) * rel_OpList) (op : opType) :
      { i : nat | odd i } * seq (OpData opType) * rel_OpList :=
      match x with
      | (H, ops, rops) =>
        let nop := k H op in
        let rops' : rel_OpList :=
            match rops return rel_OpList with
              | existT _ rl_nil =>
                existT (relseq is_seqn) [:: nop] (rl_sing _ nop)
              | existT _ (rl_sing x) =>
                existT (relseq is_seqn) [:: nop; x]
                       (@rl_cons _ is_seqn x nil nop (rl_sing _ x) refl_equal)
              | existT _ (rl_cons x xs y rs r) =>
                undefined
            end in
        (exist odd (H.1).+2 (odd_add_2 H.2), nop :: ops, rops')
      end in

  let: (H', ops', rops') := foldl f (H, nil, rops)
                                  (blockToOpList blockInfo block) in
  let blk :=
      {| baseBlock := block
       ; blockInfo := blockInfo
       ; blockOps  := rev ops' |} in
  (H', blk :: blocks, rops').

Definition allOperations (blocks : seq blockType) :
  let xs := blocksToBlockList blocks in
  let ys := flatten (map blockOps xs) in
  relseq is_sequential ys.
Proof.
  rewrite /= /blocksToBlockList /funcomp.
  elim: blocks => [|b bs IHbs].
    constructor.
  rewrite /=.
  case E: (blockToOpList binfo b) => /=.
    inversion IHbs.
  rewrite foldl_cons.
    constructor.
  constructor.
    exact: IHxs.
Qed.
*)

Definition BlockState := IState SSError BlockList BlockList.

(* jww (2014-12-01): The following two functions are used for computing
   accurate live ranges. they constitute a dataflow analysis which determines
   the true live range for variables referenced from loops.  At the moment
   these are being left unimplemented, but this is very likely something that
   will need to be done for the sake of the correctness of the algorithm. *)
Definition computeLocalLiveSets : BlockState unit := return_ tt.
Definition computeGlobalLiveSets : BlockState unit := return_ tt.

Definition buildIntervals : BlockState ScanStateSig :=
  let mkint (ss : ScanStateSig)
            (mx : option RangeSig)
            (f : forall sd, ScanState sd -> forall d, Interval d
                   -> ScanStateSig) :=
      let: (exist sd st) := ss in match mx with
           | Some (exist _ r) => f _ st _ (I_Sing r)
           | None => ss
           end in

  let handleVar ss mx := mkint ss mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i) in

  bxs <<- iget SSError ;;
  let: blocks := bxs in
  let ops := flatten (map blockOps blocks) in
  let: (varRanges, regRanges) := processOperations ops in
  let regs := vmap (fun mr =>
                      if mr is Some r
                      then Some (packInterval (I_Sing r.2))
                      else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  return_ $ foldl handleVar s2 varRanges.

Definition resolveDataFlow : BlockState unit := return_ tt.

Definition assignRegNum : BlockState unit := return_ tt.

End Blocks.

Arguments computeBlockOrder {blockType}.
Arguments numberOperations {opType blockType} oinfo binfo.
Arguments computeLocalLiveSets {opType blockType}.
Arguments computeGlobalLiveSets {opType blockType}.
Arguments buildIntervals {opType _}.
Arguments resolveDataFlow {opType blockType}.
Arguments assignRegNum {opType blockType}.

End MBlocks.