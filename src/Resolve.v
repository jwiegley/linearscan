Set Warnings "-notation-overridden".

Require Import LinearScan.Lib.
Require Import LinearScan.Graph.
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
Definition PhysReg := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 : Set.
Variables mType : Type -> Type.
Context `{mDict : Monad mType}.
Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.

Inductive ResolvingMove : Type :=
  | Move       of PhysReg & VarId & PhysReg
  | Spill      of PhysReg & VarId & bool (* true if resulting from a split *)
  | Restore    of VarId & PhysReg & bool
  | AllocReg   of VarId & PhysReg
  | FreeReg    of PhysReg & VarId
  | AssignReg  of VarId & PhysReg
  | ClearReg   of PhysReg & VarId
  | AllocStack of VarId
  | FreeStack  of VarId
  | Looped     of ResolvingMove.

Inductive ResolvingMoveSet : Set :=
  | RSMove       of nat & VarId & nat
  | RSSpill      of nat & VarId & bool
  | RSRestore    of VarId & nat & bool
  | RSAllocReg   of VarId & nat
  | RSFreeReg    of nat & VarId
  | RSAssignReg  of VarId & nat
  | RSClearReg   of nat & VarId
  | RSAllocStack of VarId
  | RSFreeStack  of VarId
  | RSLooped     of ResolvingMoveSet.

Fixpoint weakenResolvingMove (x : ResolvingMove) : ResolvingMoveSet :=
  match x with
  | Move       fr fv tr => RSMove       fr fv tr
  | Spill      fr tv b  => RSSpill      fr tv b
  | Restore    fv tr b  => RSRestore    fv tr b
  | AllocReg   fv tr    => RSAllocReg   fv tr
  | FreeReg    fr tv    => RSFreeReg    fr tv
  | AssignReg  fv tr    => RSAssignReg  fv tr
  | ClearReg   fr tv    => RSClearReg   fr tv
  | AllocStack tv       => RSAllocStack tv
  | FreeStack  fv       => RSFreeStack  fv
  | Looped     x        => RSLooped     (weakenResolvingMove x)
  end.

Section EqResolvingMove.

Fixpoint eqResolvingMove s1 s2 :=
  match s1, s2 with
  | Move fr1 fv1 tr1,    Move fr2 fv2 tr2    => [&& fr1 == fr2, fv1 == fv2
                                                &   tr1 == tr2]
  | Spill fr1 fv1 b1,    Spill fr2 fv2 b2    => [&& fr1 == fr2, fv1 == fv2
                                                &   b1  == b2]
  | Restore tv1 tr1 b1,  Restore tv2 tr2 b2  => [&& tv1 == tv2, tr1 == tr2
                                                &   b1  == b2]
  | AllocReg fv1 tr1,    AllocReg fv2 tr2    => [&& fv1 == fv2 & tr1 == tr2]
  | FreeReg fr1 tv1,     FreeReg fr2 tv2     => [&& fr1 == fr2 & tv1 == tv2]
  | AssignReg fv1 tr1,   AssignReg fv2 tr2   => [&& fv1 == fv2 & tr1 == tr2]
  | ClearReg fr1 tv1,    ClearReg fr2 tv2    => [&& fr1 == fr2 & tv1 == tv2]
  | AllocStack tv1,      AllocStack tv2      => tv1 == tv2
  | FreeStack fv1,       FreeStack fv2       => fv1 == fv2
  | Looped x,            Looped y            => eqResolvingMove x y
  | _, _ => false
  end.

Lemma eqResolvingMoveP : Equality.axiom eqResolvingMove.
Proof.
  move.
  elim=> [fr1 fv1 tr1|fr1 fv1 b1|tv1 tr1 b1|fv1 tr1
         |fr1 tv1|fr1 tv1|fr1 tv1|tv1|fv1|x IHx];
  case=> [fr2 fv2 tr2|fr2 fv2 b2|tv2 tr2 b2|fv2 tr2
         |fr2 tv2|fr2 tv2|fr2 tv2|tv2|fv2|y] /=;
  try by constructor.
  - case: (fr1 =P fr2) => [<-|?];
    case: (fv1 =P fv2) => [<-|?];
    case: (tr1 =P tr2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fr1 =P fr2) => [<-|?];
    case: (fv1 =P fv2) => [<-|?];
    case: (b1  =P b2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (tv1 =P tv2) => [<-|?];
    case: (tr1 =P tr2) => [<-|?];
    case: (b1  =P b2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fv1 =P fv2) => [<-|?];
    case: (tr1 =P tr2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fr1 =P fr2) => [<-|?];
    case: (tv1 =P tv2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fr1 =P fr2) => [<-|?];
    case: (tv1 =P tv2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fr1 =P fr2) => [<-|?];
    case: (tv1 =P tv2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (tv1 =P tv2) => [<-|?];
    first [ by constructor | by right; case ].
  - case: (fv1 =P fv2) => [<-|?];
    first [ by constructor | by right; case ].
  - specialize (IHx y).
    case: IHx; constructor.
      by rewrite p.
    rewrite /not in n *.
    move=> H.
    inversion H.
    contradiction.
Qed.

Canonical ResolvingMove_eqMixin := EqMixin eqResolvingMoveP.
Canonical ResolvingMove_eqType :=
  Eval hnf in EqType ResolvingMove ResolvingMove_eqMixin.

End EqResolvingMove.

Definition shouldAddResolvingEdge (x y : ResolvingMove) : bool :=
  match x, y with
  | Move fr1 _ _,      Move _ _ tr2      => fr1 == tr2
  | Move fr1 _ _,      Restore _ tr2 _   => fr1 == tr2
  | Move _ fv1 tr1,    Spill fr2 fv2 _   => [&& fv1 == fv2 & tr1 == fr2]
  | Move _ fv1 tr1,    AssignReg fv2 tr2 => [&& fv1 == fv2 & tr1 == tr2]
  | Move fr1 fv1 _,    FreeReg fr2 tv2   => [&& fv1 == tv2 & fr1 == fr2]
  | AllocReg fv1 tr1,  Move _ fv2 tr2    => [&& fv1 == fv2 & tr1 == tr2]

  | Spill fr1 _ _,     Restore _ tr2 _   => fr1 == tr2
  | Spill fr1 _ _,     AllocReg _ tr2    => fr1 == tr2
  | Spill fr1 fv1 _,   FreeReg fr2 tv2   => [&& fv1 == tv2 & fr1 == fr2]
  | AllocStack tv1,    Spill _ fv2   _   => tv1 == fv2

  | Restore tv1 tr1 _, Move fr2 fv2 _    => [&& tv1 == fv2 & tr1 == fr2]
  | Restore tv1 tr1 _, Spill fr2 fv2 _   => [&& tv1 == fv2 & tr1 == fr2]
  | Restore tv1 tr1 _, AssignReg fv2 tr2 => [&& tv1 == fv2 & tr1 == tr2]
  | Restore tv1 _ _,   FreeStack fv2     => tv1 == fv2
  | AllocReg fv1 tr1,  Restore tv2 tr2 _ => [&& fv1 == tv2 & tr1 == tr2]

  | FreeReg fr1 _,     AllocReg _ tr2    => fr1 == tr2
  | FreeReg fr1 _,     Restore _ tr2 _   => fr1 == tr2
  | AllocReg fv2 tr2,  FreeReg fr1 tv1   => [&& tv1 == fv2 & fr1 == tr2]

  | _, _ => false
  end.

Definition addResolution (x : ResolvingMove) (g : Graph ResolvingMove_eqType) :
  Graph ResolvingMove_eqType :=
  let f x y z := if shouldAddResolvingEdge x y
                 then addEdge (x, y) z
                 else z in
  foldr (fun y => f y x \o f x y) (addVertex x g) (vertices g).

Definition addResolutions : Graph ResolvingMove_eqType -> seq ResolvingMove
  -> Graph ResolvingMove_eqType := foldr addResolution.

Definition isMoveSplittable (x : ResolvingMove) : bool :=
  if x is Move _ _ _ then true else false.

Definition splitMove (x : ResolvingMove) (g : Graph ResolvingMove_eqType) :
  Graph ResolvingMove_eqType :=
  match x with
  | Move fr fv tr => addResolutions (removeVertex x g)
                                    [:: Spill fr fv true
                                    ;   Restore fv tr true]
  | Looped _      => g
  | _             => addVertex (Looped x) (removeVertex x g)
  end.

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
  (liveIn : option IntSet) (from to : nat) : IntMap (seq ResolvingMove) :=

  (* First determine all of the variables which are live at [from] *at the end
     of that instruction*, either in registers or on the stack.  Then gather
     the variables live at [to] *at the beginning of that instruction*. *)
  let allocsAt pos : IntMap (Allocation maxReg) :=
    foldr (fun a rest =>
             let i := intVal a in
             if ibeg i <= pos < iend i
             then IntMap_insert (ivar i) a rest
             else rest) emptyIntMap allocs in

  let varNotLive vid := if liveIn is Some ins
                        then ~~ IntSet_member vid ins
                        else false in

  (* We use an [IntMap] here to detect via merge which variables are coming
     into being, and which are being dropped. *)
  IntMap_combine
    (fun vid mx my => match mx, my with
       | Some x, Some y =>
           if intReg x == intReg y then None else
           match intReg x, intReg y with
           | Some xr, Some yr =>
               Some (if varNotLive vid || ~~ odd to
                     then [:: FreeReg xr vid
                          ;   AllocReg vid yr]
                     else [:: FreeReg xr vid
                          ;   AllocReg vid yr
                          ;   Move xr vid yr
                          ;   AssignReg vid yr])
           | Some xr, None    =>
               Some [:: FreeReg xr vid
                    ;   AllocStack vid
                    ;   Spill xr vid false]
           | None,    Some yr =>
               Some (if varNotLive vid || ~~ odd to
                     then [:: AllocReg vid yr]
                     else [:: AllocReg vid yr
                          ;   Restore vid yr false
                          ;   AssignReg vid yr
                          ;   FreeStack vid])
           | None,    None    =>
               None
           end
       | Some x, None =>
           if intReg x is Some r
           then Some [:: FreeReg r vid]
           else Some [:: FreeStack vid]
       | None, Some y =>
           if intReg y is Some r
           then Some [:: AllocReg vid r]
           else Some [:: AllocStack vid]
       | None, None => None
       end)
    (allocsAt from) (allocsAt to).

Definition determineMoves (allocs : seq (Allocation maxReg))
  (liveIn : option IntSet) (from to : nat) : seq ResolvingMove :=
  let sortMoves := topsort isMoveSplittable splitMove in
  sortMoves (IntMap_foldr (flip addResolutions) emptyGraph
                          (resolvingMoves allocs liveIn from to)).

Definition BlockMoves : Type := (seq ResolvingMove * seq ResolvingMove)%type.

Definition checkBlockBoundary (allocs : seq (Allocation maxReg))
  (liveIn : IntSet) bid in_from mfrom to (mappings : IntMap BlockMoves) :
  IntMap BlockMoves :=
  let moves := determineMoves allocs (Some liveIn)
                              (if mfrom is Some from
                               then blockLastOpId from
                               else 0) (blockFirstOpId to) in
  IntMap_alter (fun mx => let: (begs, ends) := if mx is Some x
                                               then x
                                               else ([::], [::]) in
                          Some (if in_from
                                then (begs, moves)
                                else (moves, ends))) bid mappings.

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
  fst (forFold (emptyIntMap, true) blocks $ fun z b =>
    let: (mappings, isFirst) := z in
    let bid := blockId binfo b in
    if IntMap_lookup bid liveSets isn't Some from
    then (mappings, false)
    else
      let mappings' :=
        if isFirst
        then checkBlockBoundary allocs (blockLiveIn from) bid false
                                None from mappings
        else mappings in

      (* If [in_from] is [true], resolving moves are inserted at the end of
         the [from] block, rather than the beginning of the [to] block. *)
      let suxs := blockSuccessors binfo b in
      let in_from := size suxs <= 1 in
      let mappings'' :=
        if size suxs == 0
        then mappings'
        else forFold mappings' suxs $ fun ms s_bid =>
          if IntMap_lookup s_bid liveSets isn't Some to then ms else
          let key := if in_from then bid else s_bid in
          checkBlockBoundary allocs (blockLiveIn to) key in_from
                             (Some from) to ms in
      (mappings'', false)).

End Resolve.
