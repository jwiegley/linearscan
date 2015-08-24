Require Import LinearScan.Lib.
Require Import Hask.Data.Maybe.
Require Import LinearScan.Graph.
Require Import LinearScan.UsePos.
Require Import LinearScan.Range.
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

Inductive ResolvingMove :=
  | Move       of PhysReg & VarId & PhysReg
  | Transfer   of PhysReg & VarId & PhysReg
  | Spill      of PhysReg & VarId
  | Restore    of VarId & PhysReg
  | AllocReg   of VarId & PhysReg
  | FreeReg    of PhysReg & VarId
  | Looped     of ResolvingMove
  (* | AllocStack of VarId *)
  (* | FreeStack  of VarId *)
.

Inductive ResolvingMoveSet : Set :=
  | RSMove       of nat & VarId & nat
  | RSTransfer   of nat & VarId & nat
  | RSSpill      of nat & VarId
  | RSRestore    of VarId & nat
  | RSAllocReg   of VarId & nat
  | RSFreeReg    of nat & VarId
  | RSAssignReg  of VarId & nat
  | RSClearReg   of nat & VarId
  | RSLooped     of ResolvingMoveSet
  (* | RSAllocStack of VarId *)
  (* | RSFreeStack  of VarId *)
.

Definition mapLeft `(f : a -> c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

Fixpoint weakenResolvingMove (x : ResolvingMove) : ResolvingMoveSet :=
  match x with
  | Move       fr fv tr    => RSMove       fr fv tr
  | Transfer   fr fv tr    => RSTransfer   fr fv tr
  | Spill      fr tv       => RSSpill      fr tv
  | Restore    fv tr       => RSRestore    fv tr
  | AllocReg   fv tr       => RSAllocReg   fv tr
  | FreeReg    fr tv       => RSFreeReg    fr tv
  | Looped     x           => RSLooped     (weakenResolvingMove x)
  (* | AllocStack tv          => RSAllocStack tv *)
  (* | FreeStack  fv          => RSFreeStack  fv *)
  end.

Section EqResolvingMove.

Fixpoint eqResolvingMove s1 s2 :=
  match s1, s2 with
  | Move fr1 fv1 tr1,     Move fr2 fv2 tr2     => [&& fr1 == fr2
                                                  ,   fv1 == fv2 & tr1 == tr2]
  | Transfer fr1 fv1 tr1, Transfer fr2 fv2 tr2 => [&& fr1 == fr2
                                                  ,   fv1 == fv2 & tr1 == tr2]
  | Spill fr1 fv1,        Spill fr2 fv2        => [&& fr1 == fr2 & fv1 == fv2]
  | Restore tv1 tr1,      Restore tv2 tr2      => [&& tv1 == tv2 & tr1 == tr2]
  | AllocReg fv1 tr1,     AllocReg fv2 tr2     => [&& fv1 == fv2 & tr1 == tr2]
  | FreeReg fr1 tv1,      FreeReg fr2 tv2      => [&& fr1 == fr2 & tv1 == tv2]
  | Looped x,             Looped y             => eqResolvingMove x y
  (* | AllocStack tv1,       AllocStack tv2       => tv1 == tv2 *)
  (* | FreeStack fv1,        FreeStack fv2        => fv1 == fv2 *)
  | _, _ => false
  end.

Lemma eqResolvingMoveP : Equality.axiom eqResolvingMove.
Proof.
  move.
  elim=> [fr1 fv1 tr1|fr1 fv1 tr1|fr1 fv1
         |tv1 tr1|fv1 tr1|fr1 tv1|x IHx(* |tv1|fv1 *)];
  case=> [fr2 fv2 tr2|fr2 fv2 tr2|fr2 fv2
         |tv2 tr2|fv2 tr2|fr2 tv2|y(* |tv2|fv2 *)] /=;
  try by constructor.
  - case: (fr1 =P fr2) => [<-|?];
    case: (fv1 =P fv2) => [<-|?];
    case: (tr1 =P tr2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fr1 =P fr2) => [<-|?];
    case: (fv1 =P fv2) => [<-|?];
    case: (tr1 =P tr2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fr1 =P fr2) => [<-|?];
    case: (fv1 =P fv2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (tv1 =P tv2) => [<-|?];
    case: (tr1 =P tr2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fv1 =P fv2) => [<-|?];
    case: (tr1 =P tr2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fr1 =P fr2) => [<-|?];
    case: (tv1 =P tv2) => [<-|?];
    first [ by constructor | by right; case ].
  - specialize (IHx y).
    case: IHx; constructor.
      by rewrite p.
    rewrite /not in n *.
    move=> H.
    inversion H.
    contradiction.
  (* - case: (tv1 =P tv2) => [<-|?]; *)
  (*   first [ by constructor | by right; case ]. *)
  (* - case: (fv1 =P fv2) => [<-|?]; *)
  (*   first [ by constructor | by right; case ]. *)
Qed.

Canonical ResolvingMove_eqMixin := EqMixin eqResolvingMoveP.
Canonical ResolvingMove_eqType :=
  Eval hnf in EqType ResolvingMove ResolvingMove_eqMixin.

End EqResolvingMove.

Definition eqResolvingMoveKind (x y : ResolvingMove) : bool :=
  match x, y with
  | Move       _ _ _,   Move       _ _ _   => true
  | Transfer   _ _ _,   Transfer   _ _ _   => true
  | Spill      _ _,     Spill      _ _     => true
  | Restore    _ _,     Restore    _ _     => true
  | AllocReg   _ _,     AllocReg   _ _     => true
  | FreeReg    _ _,     FreeReg    _ _     => true
  | Looped     _,       Looped     _       => true
  | _,                  _                  => false
  end.

Inductive ResGraphNode :=
  | RegNode of PhysReg
  | VarNode of VarId
  | VirtNode of ResGraphNode.

Section EqResGraphNode.

Fixpoint eqResGraphNode s1 s2 :=
  match s1, s2 with
  | RegNode r1, RegNode r2 => r1 == r2
  | VarNode v1, VarNode v2 => v1 == v2
  | VirtNode n1,
    VirtNode n2 => eqResGraphNode n1 n2
  | _, _ => false
  end.

Lemma eqResGraphNodeP : Equality.axiom eqResGraphNode.
Proof.
  move.
  elim=> [r1|v1|n1 IHn];
  case=> [r2|v2|n2] /=;
  try by constructor.
  - case: (r1 =P r2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (v1 =P v2) => [<-|?];
    first [ by constructor | by right; case ].
  - specialize (IHn n2).
    case: IHn; constructor.
      by rewrite p.
    rewrite /not in n *.
    move=> H.
    inversion H.
    contradiction.
Qed.

Canonical ResGraphNode_eqMixin := EqMixin eqResGraphNodeP.
Canonical ResGraphNode_eqType :=
  Eval hnf in EqType ResGraphNode ResGraphNode_eqMixin.

End EqResGraphNode.

Record ResGraphEdge := {
  resMove  : ResolvingMove;
  resGhost : bool
}.

Section EqResGraphEdge.

Definition eqResGraphEdge s1 s2 :=
  match s1, s2 with
  | {| resMove  := a1; resGhost := b1 |},
    {| resMove  := a2; resGhost := b2 |} => [&& a1 == a2 & b1 == b2]
  end.

Lemma eqResGraphEdgeP : Equality.axiom eqResGraphEdge.
Proof.
  move.
  case=> [a1 b1].
  case=> [a2 b2] /=.
  case: (a1 =P a2) => [<-|?]; last by right; case.
  case: (b1 =P b2) => [<-|?]; last by right; case.
  by constructor.
Qed.

Canonical ResGraphEdge_eqMixin := EqMixin eqResGraphEdgeP.
Canonical ResGraphEdge_eqType :=
  Eval hnf in EqType ResGraphEdge ResGraphEdge_eqMixin.

End EqResGraphEdge.

(* Determine the lexicographical sorting of edges. This is not done by a flow
   of values, but of inverse dependencies: that is, each pair is (ACQUIRE,
   RELEASE), and we desire that anything acquired has is released first. *)
(* jww (2015-08-23): There should be a way to get rid of [Transfer] *)
Definition determineEdge (x : ResGraphEdge) : ResGraphNode * ResGraphNode :=
  let fix go m := match m with
    (* Instruction            Acquires      Releases *)
    (* -------------------     ----------  ---------- *)
    | Move       fr fv tr => (RegNode tr, RegNode fr)
    | Transfer   fr fv tr => (RegNode tr, RegNode fr)

    | Spill      fr tv    => (VirtNode (VarNode tv), RegNode fr)
    | Restore    fv tr    => (RegNode tr, VarNode fv)

    | FreeReg    fr tv    => (VirtNode (VarNode tv), RegNode fr)
    | AllocReg   fv tr    => (RegNode tr, VarNode fv)

    | Looped     x        => go x
    end in
  go (resMove x).

Definition compareEdges (x y : ResGraphEdge) : bool :=
  let xe := determineEdge x in
  let ye := determineEdge y in
  if snd xe == snd ye
  then ~~ resGhost x && resGhost y
  else false.                   (* retain input ordering *)

Definition splitEdge (x : ResGraphEdge) : seq ResGraphEdge :=
  match resMove x with
  | Move     fr fv tr => [:: {| resMove  := Spill fr fv
                              ; resGhost := false |}
                          ;  {| resMove  := Restore fv tr
                              ; resGhost := resGhost x |} ]
  | Transfer fr fv tr => [:: {| resMove  := FreeReg fr fv
                              ; resGhost := false |}
                          ;  {| resMove  := AllocReg fv tr
                              ; resGhost := resGhost x |} ]
  | Looped _          => [:: x]
  | _                 => [:: {| resMove  := Looped (resMove x)
                              ; resGhost := resGhost x |}]
  end.

Definition sortMoves (x : Graph ResGraphNode_eqType ResGraphEdge_eqType) :
  seq ResGraphEdge := sortBy compareEdges (snd (topsort x splitEdge)).

Definition determineMoves (moves : IntMap ResGraphEdge) : seq ResGraphEdge :=
  sortMoves (IntMap_foldr addEdge (emptyGraph determineEdge) moves).

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

   Note: if a variable is not live in [from] but is live in [to], or vice
   versa, this is not considered and is just regarded as how the program was
   written. There is no contention in this case, even if it might actually
   mean that the program is assuming the variable is live somehow in a
   register or on the stack. *)
Definition resolvingMoves (allocs : seq (Allocation maxReg))
  (liveIn : option IntSet) (from to : nat) :
  IntMap ResGraphEdge :=

  (* First determine all of the variables which are live at [from] *at the end
     of that instruction*, either in registers or on the stack.  Then gather
     the variables live at [to] *at the beginning of that instruction*. *)
  let liveAtFrom :=
      IntMap_fromList [seq (ivar (intVal i), i) | i <- allocs
                      & ibeg (intVal i) <= from < iend (intVal i)] in

  (* This function is greatly complicated by the fact that there are
     zero-length "ephemeral" allocations, where a value is loaded into a
     register only to make it available as input to the next instruction, but
     only for that instruction. These are handled by allocating and then
     immediately freeing the register, so that it lives in the register as
     "ghost" for that one instruction (see Verify.v). *)
  let shouldKeep int pos :=
    if ibeg int <= pos
    then (if pos == iend int
          then (if lastUsePos int is Some u
                then to <= u
                else false, true (* resGhost *))
          else (to < iend int, false))
    else (false, false) in

  let outputBegin int pos := hasOnlyOutputsAt (NE_head (rds int)).1 pos in

  let liveAtTo :=
      IntMap_fromList [seq let int := intVal i in
                           (ivar int,
                            (i, snd (shouldKeep int to), outputBegin int to))
                      | i <- allocs & fst (shouldKeep (intVal i) to)] in

  let varNotLive vid := if liveIn is Some ins
                        then ~~ IntSet_member vid ins
                        else false in

  (* We use an [IntMap] here to easily detect via merge which variables are
     coming into being, and which are being dropped. *)
  IntMap_mergeWithKey
    (fun vid x yp =>
       let: (y, ghost, outb) := yp in
       if intReg x == intReg y
       then if intReg y is Some reg
            then if ghost
                 then Some {| resMove  := FreeReg reg vid
                            ; resGhost := true |}
                 else None
            else None
       else
         let mmv := match intReg x, intReg y with
            | Some xr, Some yr =>
                if outb
                then Some (Transfer xr vid yr)
                else if varNotLive vid
                     then Some (FreeReg xr vid)
                     else Some (Move xr vid yr)
            | Some xr, None    => Some (Spill xr vid)
            | None,    Some yr =>
                if outb || varNotLive vid
                then Some (AllocReg vid yr)
                else Some (Restore vid yr)
            | None,    None    => None
            end in
         if mmv is Some mv
         then Some {| resMove  := mv
                    ; resGhost := ghost |}
         else None)

    (IntMap_foldlWithKey
       (fun acc vid x =>
          if intReg x is Some r
          then IntMap_insert vid
             {| resMove  := FreeReg r vid
              ; resGhost := false |} acc
          else (* FreeStack vid *) acc) emptyIntMap)

    (IntMap_foldlWithKey
       (fun acc vid yp =>
          let: (y, ghost, outb) := yp in
          if intReg y is Some r
          then IntMap_insert vid
             {| resMove  := AllocReg vid r
              ; resGhost := ghost |} acc
          else (* AllocStack vid *) acc) emptyIntMap)

    liveAtFrom liveAtTo.

Definition BlockMoves : Type :=
  (Graph ResGraphNode_eqType ResGraphEdge_eqType *
   Graph ResGraphNode_eqType ResGraphEdge_eqType).

Definition applyMappings (bid : BlockId) (mappings : IntMap BlockMoves)
  (in_from : bool) (moves : IntMap ResGraphEdge) : IntMap BlockMoves :=
  let go ms mv :=
    let addToGraphs e xs :=
        let: (gbeg, gend) := xs in
        if in_from
        then (gbeg, addEdge e gend)
        else (addEdge e gbeg, gend) in
    let eg := emptyGraph determineEdge in
    let f mxs := addToGraphs mv $ if mxs is Some xs
                                  then xs
                                  else (eg, eg) in
    IntMap_alter (@Some _ \o f) bid ms in
  IntMap_foldl go mappings moves.

Definition checkBlockBoundary (allocs : seq (Allocation maxReg))
  bid in_from from to (liveIn : IntSet) (mappings : IntMap BlockMoves) :
  IntMap BlockMoves :=
  applyMappings bid mappings in_from $
                resolvingMoves allocs (Some liveIn)
                               (blockLastOpId from) (blockFirstOpId to).

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
  fmap fst $ forFoldM (emptyIntMap, true) blocks $ fun z b =>
    let: (mappings, isFirst) := z in
    bid <-- blockId binfo b ;;
    (* jww (2015-01-28): Failure here should be impossible *)
    if IntMap_lookup bid liveSets isn't Some from
    then pure (mappings, false)
    else
      let mappings' :=
        if isFirst
        then applyMappings bid mappings false $
                           resolvingMoves allocs None 1 (blockFirstOpId from)
        else mappings in

      (* If [in_from] is [true], resolving moves are inserted at the end of
         the [from] block, rather than the beginning of the [to] block. *)
      suxs <-- blockSuccessors binfo b ;;
      let in_from := size suxs <= 1 in
      let mappings'' :=
        if size suxs == 0
        then
          applyMappings bid mappings' true $
                        resolvingMoves allocs None
                                       (blockLastOpId from)
                                       (blockLastOpId from).+2
        else
          forFold mappings' suxs $ fun ms s_bid =>
            (* jww (2015-01-28): Failure here should be impossible *)
            if IntMap_lookup s_bid liveSets isn't Some to then ms else
            let key := if in_from then bid else s_bid in
            checkBlockBoundary allocs key in_from from to (blockLiveIn to) ms in
      pure (mappings'', false).

End Resolve.