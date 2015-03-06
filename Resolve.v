Require Import LinearScan.Lib.
Require Import LinearScan.Graph.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Allocate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Resolve.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

Definition checkIntervalBoundary (allocs : seq (Allocation maxReg))
  (from to vid : nat) (checkIntervalKinds : bool) :
  option (sum_eqType (ordinal_eqType maxReg) nat_eqType *
          sum_eqType (ordinal_eqType maxReg) nat_eqType) :=
  let mfrom_int := lookupInterval vid Output from allocs in
  let mto_int   := lookupInterval vid Input to allocs in

  (* If the intervals match, no move resolution is necessary. *)
  if option_map (@intId maxReg) mfrom_int ==
     option_map (@intId maxReg) mto_int then None else

  let f mr := if mr is Some r then inl r else inr vid in
  let sreg := f (option_map (@intReg maxReg) mfrom_int) in
  let dreg := f (option_map (@intReg maxReg) mto_int) in
  if sreg == dreg
  then None
  else
    if checkIntervalKinds
    then
      let fromk := if mfrom_int is Some i
                   then iknd (intVal i)
                   else Middle in
      let tok   := if mto_int is Some i
                   then iknd (intVal i)
                   else Middle in
      if match fromk, tok with
         | LeftMost, RightMost => true
         | LeftMost, Middle    => true
         | Middle,   Middle    => true
         | Middle,   RightMost => true
         | _,        _         => false
         end
      then Some (sreg, dreg)
      else None
    else Some (sreg, dreg).

Definition checkBlockBoundary (allocs : seq (Allocation maxReg))
  bid in_from from to mappings vid :=
  if checkIntervalBoundary allocs (blockLastOpId from)
                           (blockFirstOpId to) vid false
    isn't Some (sreg, dreg)
  then mappings
  else
    let addToGraphs e xs :=
        let: (gbeg, gend) := xs in
        if in_from
        then (addEdge e gbeg, gend)
        else (gbeg, addEdge e gend) in
    let f mxs :=
        let e := (Some sreg, Some dreg) in
        @Some _ $ addToGraphs e
                $ if mxs is Some xs
                  then xs
                  else (emptyGraph, emptyGraph) in
    IntMap_alter f bid mappings.

Definition BlockMoves :=
  (Graph (sum_eqType (ordinal_eqType maxReg) nat_eqType) *
   Graph (sum_eqType (ordinal_eqType maxReg) nat_eqType))%type.

Definition resolveDataFlow (allocs : seq (Allocation maxReg))
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
    (* jww (2015-01-28): Failure here should be impossible *)
    if IntMap_lookup bid liveSets isn't Some from then mappings else
    (fun successors =>
      (* If [in_from] is [true], resolving moves are inserted at the end of
         the [from] block, rather than the beginning of the [to] block. *)
      let in_from := size successors <= 1 in
      forFold mappings successors $ fun ms s_bid =>
        (* jww (2015-01-28): Failure here should be impossible *)
        if IntMap_lookup s_bid liveSets isn't Some to then ms else
        let key := if in_from then bid else s_bid in
        IntSet_forFold ms (blockLiveIn to) $
          checkBlockBoundary allocs key in_from from to)
    (blockSuccessors binfo b).

End Resolve.