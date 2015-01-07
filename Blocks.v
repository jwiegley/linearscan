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

(* The predicate which applies to the first operator within the list of
   blocks.  Is there no operators -- meaning it is a list of empty blocks --
   then this function always returns true. *)
Fixpoint firstOpPred (f : OpData opType -> bool)
  (bs : seq BlockData) : bool :=
  match bs with
    | nil => true
    | cons x xs =>
        match blockOps x with
        | nil => firstOpPred f xs
        | cons op _ => f op
        end
    end.

Definition maybeLast a (l : seq a) : option a :=
  let fix go res xs :=
      match xs with
      | nil => res
      | cons x xs => go (Some x) xs
      end in
  go None l.

Example maybeLast_ex1 : maybeLast ([::] : seq nat) == None.
Proof. by []. Qed.

Example maybeLast_ex2 : maybeLast [:: 1] == Some 1.
Proof. by []. Qed.

Example maybeLast_ex3 : maybeLast [:: 1; 2; 3] == Some 3.
Proof. by []. Qed.

Definition lastOpPred (f : OpData opType -> bool)
  (bs : seq BlockData) : bool :=
  let fix go res blks :=
      match blks with
      | nil => res
      | cons x xs =>
          match maybeLast (blockOps x) with
          | None    => go res xs
          | Some op => go (f op) xs
          end
      end in
  go true bs.

Fixpoint opCount (bs : seq BlockData) : nat :=
  match bs with
  | nil => 0
  | cons x xs => size (blockOps x) + opCount xs
  end.

Definition startsAtOne (b : BlockData) : bool :=
  firstOpPred (fun op => opId op == 1) [:: b].

(* ** BlockList

   A [BlockList] maintains its list of blocks in reverse order.  For example,
   if there were two blocks representing instructions 1-10, the block list
   might look like : 6-10, followed by 1-5. *)

Inductive BlockList : seq BlockData -> Type :=
  | BlockList_firstBlock b : startsAtOne b -> BlockList [:: b]
  | BlockList_nextBlock b bs :
      BlockList bs
        -> let f op :=
               if opCount bs == 0
               then opId op == 1
               else let isNext nop := opId op == (opId nop).+2 in
                    lastOpPred isNext bs in
           firstOpPred f [:: b]
        -> BlockList (b :: bs).

Lemma mapBlockOps_spec
  (f : forall op : OpData opType,
         { op' : OpData opType | opId op' == opId op }) :
  forall baseBlock0 blockInfo0 blockOps0,
  startsAtOne
    {|
    baseBlock := baseBlock0;
    blockInfo := blockInfo0;
    blockOps := blockOps0 |} ->
  startsAtOne
    {|
    baseBlock := baseBlock0;
    blockInfo := blockInfo0;
    blockOps := [seq (f op).1 | op <- blockOps0] |}.
Proof.
  move=> ? ?.
  rewrite /startsAtOne.
  elim=> //= [y ys IHys] H.
  case: (f y) => x /= /eqP -> //.
Qed.

Lemma mapBlockOps_spec2
  (f : forall op : OpData opType,
         {op' : OpData opType | opId op' == opId op})
  (zs : seq BlockData) :
  forall baseBlock0 blockInfo0 blockOps0,
  let k op :=
      if opCount zs == 0
      then opId op == 1
      else let isNext nop := opId op == (opId nop).+2 in
           lastOpPred isNext zs in
  firstOpPred k
    [:: {|
        baseBlock := baseBlock0;
        blockInfo := blockInfo0;
        blockOps := blockOps0 |}] ->
  firstOpPred k
    [:: {|
        baseBlock := baseBlock0;
        blockInfo := blockInfo0;
        blockOps := [seq (f op).1 | op <- blockOps0] |}].
Proof.
  move=> ? ?.
  rewrite /firstOpPred.
  elim=> //= [y ys IHys] H.
  case: (f y) => x /= /eqP -> //.
Qed.

Fixpoint foldlBlockOps a (f : a -> OpData opType -> a) (z : a)
  `(xs : BlockList bs) : a :=
  match xs with
    | BlockList_firstBlock b _ => foldl f z (blockOps b)
    | BlockList_nextBlock b _ IHzs _ =>
        foldlBlockOps f (foldl f z (blockOps b)) IHzs
  end.

Definition foldlBlockOpsWithPred a
  (f : a -> option (OpData opType) -> OpData opType -> a) (z : a)
  `(xs : BlockList bs) : a :=
  let fix go zmp blks (blist : BlockList blks) :=
      let k x op : a * option (OpData opType) :=
          let: (z, pre) := x in
          (f z pre op, Some op) in
      match blist with
        | BlockList_firstBlock b _ =>
            foldl k zmp (blockOps b)
        | BlockList_nextBlock b zs IHzs _ =>
            go (foldl k zmp (blockOps b)) zs IHzs
      end in
  fst (go (z, None) bs xs).

Definition mapBlockOps
  (f : forall op : OpData opType,
         { op' : OpData opType | opId op' == opId op })
  `(xs : BlockList bs) : { bs' : seq BlockData & BlockList bs' }.
Proof.
  case: xs => [b H|b zs IHzs k Hfirst].
    case: b => [baseBlock0 blockInfo0 blockOps0] in H *.
    exists [:: {| baseBlock := baseBlock0
                ; blockInfo := blockInfo0
                ; blockOps  := map (fun op => proj1_sig (f op))
                                   blockOps0
                |} ].
    constructor.
    exact: mapBlockOps_spec.
  case: b => [baseBlock0 blockInfo0 blockOps0] in Hfirst *.
  exists [:: {| baseBlock := baseBlock0
              ; blockInfo := blockInfo0
              ; blockOps  := map (fun op => proj1_sig (f op))
                                 blockOps0
              |} & zs].
  constructor.
    exact: IHzs.
  rewrite -[X in firstOpPred X _]/k.
  move: Hfirst.
  exact: mapBlockOps_spec2.
Defined.

Definition mapOpsWithPred
  (f : option (OpData opType) -> OpData opType -> OpData opType)
  (ops : seq (OpData opType)) : seq (OpData opType) :=
  let fix go pre os := match os with
      | nil => nil
      | cons x xs =>
          let newOp := f pre x in
          newOp :: go (Some newOp) xs
      end in
  go None ops.

Definition mapBlockDataOpsWithPred
  (f : BlockData -> option (OpData opType) -> OpData opType
         -> OpData opType)
  (blocks : seq BlockData) : seq BlockData :=
  let fix go pre blks := match blks with
      | nil => nil
      | cons x xs =>
          let k op rest :=
              let: (m, ys) := rest in
              let op' := f x m op in
              (Some op', op' :: ys) in
          let: (lastOp, newOps) :=
               foldr k (pre, [::]) (blockOps x) in
          let x' :=
              {| baseBlock := baseBlock x
               ; blockInfo := blockInfo x
               ; blockOps  := newOps
               |} in
          x' :: go lastOp xs
      end in
  go None blocks.

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

Definition wrap_block (H : { i : nat | odd i })
  (blocks: seq BlockData) (block : blockType) :=
  let k H op :=
      {| baseOp  := op
       ; opInfo  := oinfo
       ; opId    := H.1
       ; opIdOdd := H.2
       ; opAlloc := nil |} in

  let f x op := let: (H, ops) := x in
      (exist odd (H.1).+2 (odd_add_2 H.2), k H op :: ops) in

  let: (H', ops')  := foldl f (H, nil) (blockToOpList binfo block) in
  let blk := {| baseBlock := block
              ; blockInfo := binfo
              ; blockOps  := rev ops' |} in
  (H', blk :: blocks).

(* Confirm that [wrap_block] works for a single block that has three
   operations. *)
Lemma wrap_block_spec : forall x y z b blk,
  [:: x; y; z] = blockToOpList binfo blk
    -> snd (wrap_block (exist odd 1 odd_1) [::] blk) = [:: b]
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
    -> wrap_block (exist odd 1 odd_1) [::] blk1 = (H, [:: b1])
    -> wrap_block H [::] blk2 = (H', [:: b2])
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
  let f acc x := let: (H, blocks) := acc in
                 wrap_block H blocks x in
  @snd _ _ \o foldl f (exist odd 1 odd_1, nil).

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

Definition buildIntervals (blocks : seq BlockData) :
  seq (OpData opType) * ScanStateSig :=
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

  let ops := flatten (map (blockToOpList binfo \o baseBlock) blocks) in
  let: (ops', varRanges, regRanges) := processOperations oinfo ops in
  let regs := vmap (fun mr =>
                      if mr is Some r
                      then Some (packInterval (I_Sing 0 r.2))
                      else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  (ops', foldl_with_index handleVar s2 varRanges).

Definition resolveDataFlow : BlockState unit := return_ tt.

Definition assignRegNum (ops : seq (OpData opType)) `(st : ScanState sd) :
  seq (OpData opType) :=
  let ints := handled sd ++ active sd ++ inactive sd in
  let f op :=
      let o := baseOp op in
      let vars := varRefs (opInfo op) o in
      let k op' v :=
          let vid := varId v in
          let h acc x :=
              let: (xid, reg) := x in
              (fun int =>
                  if (ivar int == vid) &&
                     (ibeg int <= opId op < iend int)
                  then (vid, Register reg) :: acc
                  else acc) (getInterval xid) in
          {| baseOp  := o
           ; opInfo  := opInfo op'
           ; opId    := opId op'
           ; opIdOdd := opIdOdd op'
           ; opAlloc := foldl h nil ints ++ opAlloc op'
           |} in
      foldl k op vars in
  map f ops.

End Blocks.

Arguments computeBlockOrder {blockType}.
Arguments numberOperations {opType blockType} oinfo binfo.
Arguments computeLocalLiveSets {opType blockType}.
Arguments computeGlobalLiveSets {opType blockType}.
Arguments buildIntervals {opType blockType} oinfo binfo blocks.
Arguments resolveDataFlow {opType blockType}.
Arguments assignRegNum {opType} ops {sd} st.

End MBlocks.