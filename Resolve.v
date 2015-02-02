Require Import LinearScan.Lib.
Require Import LinearScan.Allocate.
Require Import LinearScan.Blocks.
Require Import LinearScan.Graph.
Require Import LinearScan.IntMap.
Require Import LinearScan.LiveSets.
Require Import LinearScan.ScanState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MResolve (Mach : Machine).

Include MAllocate Mach.

Section Resolve.

Variables blockType1 blockType2 opType1 opType2 varType accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo accType opType1 opType2 varType.
Variable vinfo : VarInfo varType.

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

End Resolve.

End MResolve.
