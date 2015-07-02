Require Import LinearScan.Lib.
Require Import LinearScan.Graph.
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
Definition PhysReg := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg opType1 opType2.

Definition RawResolvingMove := (option PhysReg * option PhysReg)%type.

Inductive ResolvingMove :=
  | Move    of PhysReg & PhysReg
  | Swap    of PhysReg & PhysReg
  | Spill   of PhysReg & VarId
  | Restore of VarId   & PhysReg
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
    - A swap between two registers

   Note: if a variable is not live in [from] but is live in [to], or vice
   versa, this is not considered and is just regarded as how the program was
   written. There is no contention in this case, even if it might actually
   mean that the program is assuming the variable is live somehow in a
   register or on the stack. *)
Definition resolvingMoves (allocs : seq (Allocation maxReg)) (from to : nat) :
  IntMap RawResolvingMove :=

  (* First determine all of the variables which are live at [from] *at the end
     of that instruction*, either in registers or on the stack.  Then gather
     the variables live at [to] *at the beginning of that instruction*. *)
  let liveAtFrom :=
      IntMap_fromList [seq (ivar (intVal i), i) | i <- allocs
                      & ibeg (intVal i) <= from < iend (intVal i)] in
  let liveAtTo :=
      IntMap_fromList [seq (ivar (intVal i), i) | i <- allocs
                      & let int := intVal i in
                        (ibeg int <= to) &&
                        (if to == iend int
                         then if lastUsePos int is Some u
                              then to <= u
                              else false
                         else to < iend int)] in

  IntMap_mergeWithKey
    (fun vid x y =>
       if intReg x == intReg y
       then None
       else if match intReg x, intReg y with
               | None,   Some _ => true (* intervalBeginsWithInput (intVal y) *)
               | _, _ => true
               end
            then Some (intReg x, intReg y)
            else None)
    (fun _ => emptyIntMap)
    (fun _ => emptyIntMap)
    liveAtFrom liveAtTo.

Definition checkBlockBoundary (allocs : seq (Allocation maxReg))
  bid in_from from to liveIn mappings :=
  let select acc vid x := if IntSet_member vid liveIn
                          then (vid, x) :: acc
                          else acc in
  let moves := IntMap_foldlWithKey select [::] $
               resolvingMoves allocs (blockLastOpId from)
                                     (blockFirstOpId to) in
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

Definition resolveDataFlow (allocs : seq (Allocation maxReg))
  (blocks : seq blockType1) (liveSets : IntMap BlockLiveSets) :
  mType (IntMap BlockMoves) :=
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
  forFoldM emptyIntMap blocks $ fun mappings b =>
    bid <-- blockId binfo b ;;
    (* jww (2015-01-28): Failure here should be impossible *)
    if IntMap_lookup bid liveSets isn't Some from
    then pure mappings
    else
      suxs <-- blockSuccessors binfo b ;;
      (* If [in_from] is [true], resolving moves are inserted at the end of
         the [from] block, rather than the beginning of the [to] block. *)
      let in_from := size suxs <= 1 in
      pure $ forFold mappings suxs $ fun ms s_bid =>
        (* jww (2015-01-28): Failure here should be impossible *)
        if IntMap_lookup s_bid liveSets isn't Some to then ms else
        let key := if in_from then bid else s_bid in
        checkBlockBoundary allocs key in_from from to (blockLiveIn to) ms.

End Resolve.