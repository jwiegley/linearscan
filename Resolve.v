Require Import LinearScan.Lib.
Require Import LinearScan.Graph.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.
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

Record Allocation := {
  intId  : nat;
  intVal : IntervalDesc;
  intReg : option PhysReg
}.

Definition determineAllocations (sd : @ScanStateDesc maxReg) : seq Allocation :=
  [seq {| intId  := nat_of_ord (fst x)
        ; intVal := getIntervalDesc (getInterval (fst x))
        ; intReg := snd x |} | x <- handled sd].

Definition RawResolvingMove := (option PhysReg * option PhysReg)%type.

Inductive ResolvingMove :=
  | Move of PhysReg & PhysReg
  | Swap of PhysReg & PhysReg
  | Spill of PhysReg & VarId
  | Restore of VarId & PhysReg
  | Nop.

Definition determineMove vid (x : RawResolvingMove) : ResolvingMove :=
  match x with
  | (Some x, Some y) => Move x y
  | (Some x, None)   => Spill x vid
  | (None,   Some y) => Restore vid y
  | (None,   None)   => Nop
  end.

Definition prepareForGraph vid (x : RawResolvingMove) :
  option (sum_eqType (ordinal_eqType maxReg) nat_eqType) *
  option (sum_eqType (ordinal_eqType maxReg) nat_eqType) :=
  match x with
  | (Some x, Some y) => (Some (inl x), Some (inl y))
  | (Some x, None)   => (Some (inl x), Some (inr vid))
  | (None,   Some y) => (Some (inr vid), Some (inl y))
  | (None,   None)   => (Some (inr vid), Some (inr vid))
  end.

Definition moveFromGraph
  (mv : option (sum_eqType (ordinal_eqType maxReg) nat_eqType) *
        option (sum_eqType (ordinal_eqType maxReg) nat_eqType)) :
  ResolvingMove :=
  match mv with
  | (Some (inl x), Some (inl y)) => Move x y
  | (Some (inl x), Some (inr y)) => Spill x y
  | (Some (inr x), Some (inl y)) => Restore x y
  | _ => Nop
  end.

Definition determineMoves (moves : IntMap RawResolvingMove) :
  seq ResolvingMove :=
  let graph := forFold emptyGraph (IntMap_toList moves) $ fun g mv =>
                 addEdge (prepareForGraph (fst mv) (snd mv)) g in
  map moveFromGraph (topsort graph).

(* Assuming a transition [from] one point in the procedure [to] another --
   where these two positions may be contiguous, or connected via a branch --
   determining the set of resolving moves necessary to maintain a consist view
   of the registers and stack between the two positions.

   For example, if at [from] variable v3 is in register 3, and at [to] it is
   in register 2, this would generate a resolving move from 3 -> 2.  Moves
   will always be one of four types:

    - A move from one register to another
    - A move from the stack to a register
    - A move from a register to the stack
    - A swap between two registers *)
Definition resolvingMoves (allocs : seq Allocation) (from to : nat)
  (checkIntervalKinds : bool) :
  IntMap RawResolvingMove :=

  (* First determine all of the variables which are live at [from] *at the end
     of that instruction*, either in registers or on the stack.  Then gather
     the variables live at [to] *at the beginning of that instruction*. *)
  let liveAtFrom :=
      IntMap_fromList [seq (ivar (intVal i), i) | i <- allocs
                      & ibeg (intVal i) <= from < iend (intVal i)] in
  let liveAtTo :=
      IntMap_fromList [seq (ivar (intVal i), i) | i <- allocs
                      & ibeg (intVal i) <= to <= iend (intVal i)] in

    (* if checkIntervalKinds *)
    (* then *)
    (*   let fromk := iknd (intVal from_int) in *)
    (*   let tok   := iknd (intVal to_int) in *)
    (*   if match fromk, tok with *)
    (*      | LeftMost, RightMost => true *)
    (*      | LeftMost, Middle    => true *)
    (*      | Middle,   Middle    => true *)
    (*      | Middle,   RightMost => true *)
    (*      | _,        _         => false *)
    (*      end *)
    (*   then Some (sreg, dreg) *)
    (*   else None *)

  IntMap_mergeWithKey
    (fun vid x y =>
       if intReg x == intReg y
       then None
       else Some (intReg x, intReg y))
    (fun _ => emptyIntMap)
    (fun _ => emptyIntMap)
    liveAtFrom liveAtTo.

Definition checkBlockBoundary (allocs : seq Allocation)
  bid in_from from to liveIn mappings :=
  let select acc vid x := if IntSet_member vid liveIn
                          then (vid, x) :: acc
                          else acc in
  let moves := IntMap_foldlWithKey select [::] $
               resolvingMoves allocs (blockLastOpId from)
                                     (blockFirstOpId to) false in
  forFold mappings moves $ fun ms mv =>
    let addToGraphs e xs :=
        let: (gbeg, gend) := xs in
        if in_from
        then (gbeg, addEdge e gend)
        else (addEdge e gbeg, gend) in
    let f mxs :=
        addToGraphs (prepareForGraph (fst mv) (snd mv)) $
          if mxs is Some xs
          then xs
          else (emptyGraph, emptyGraph) in
    IntMap_alter (@Some _ \o f) bid ms.

Definition BlockMoves :=
  (Graph (sum_eqType (ordinal_eqType maxReg) nat_eqType) *
   Graph (sum_eqType (ordinal_eqType maxReg) nat_eqType))%type.

Definition resolveDataFlow (allocs : seq Allocation)
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
        checkBlockBoundary allocs key in_from from to (blockLiveIn to) ms)
    (blockSuccessors binfo b).

End Resolve.