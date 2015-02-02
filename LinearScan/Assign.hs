{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Assign where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Blocks as Blocks
import qualified LinearScan.Graph as Graph
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Resolve as Resolve
import qualified LinearScan.ScanState as ScanState
import qualified LinearScan.State as State
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Seq as Seq
import qualified LinearScan.Ssrnat as Ssrnat



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

type PhysReg = Prelude.Int

data AssnStateInfo accType =
   Build_AssnStateInfo Blocks.OpId accType

assnOpId :: (AssnStateInfo a1) -> Blocks.OpId
assnOpId a =
  case a of {
   Build_AssnStateInfo assnOpId0 assnAcc0 -> assnOpId0}

assnAcc :: (AssnStateInfo a1) -> a1
assnAcc a =
  case a of {
   Build_AssnStateInfo assnOpId0 assnAcc0 -> assnAcc0}

type AssnState accType a = State.State (AssnStateInfo accType) a

moveOpM :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) -> Blocks.PhysReg ->
           Blocks.PhysReg -> AssnState a4 ([] a2)
moveOpM maxReg oinfo sreg dreg =
  State.bind (\assn ->
    case Blocks.moveOp maxReg oinfo sreg dreg (assnAcc assn) of {
     (,) mop acc' ->
      State.bind (\x -> State.pure mop)
        (State.put (Build_AssnStateInfo (assnOpId assn) acc'))}) State.get

saveOpM :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) -> Blocks.PhysReg ->
           (Prelude.Maybe Blocks.VarId) -> AssnState a4 ([] a2)
saveOpM maxReg oinfo vid reg =
  State.bind (\assn ->
    case Blocks.saveOp maxReg oinfo vid reg (assnAcc assn) of {
     (,) sop acc' ->
      State.bind (\x -> State.pure sop)
        (State.put (Build_AssnStateInfo (assnOpId assn) acc'))}) State.get

restoreOpM :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) -> (Prelude.Maybe
              Blocks.VarId) -> Blocks.PhysReg -> AssnState a4 ([] a2)
restoreOpM maxReg oinfo vid reg =
  State.bind (\assn ->
    case Blocks.restoreOp maxReg oinfo vid reg (assnAcc assn) of {
     (,) rop acc' ->
      State.bind (\x -> State.pure rop)
        (State.put (Build_AssnStateInfo (assnOpId assn) acc'))}) State.get

pairM :: (AssnState a1 a2) -> (AssnState a1 a3) -> AssnState a1 ((,) a2 a3)
pairM x y =
  State.bind (\x' -> State.bind (\y' -> State.pure ((,) x' y')) y) x

savesAndRestores :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) ->
                    Eqtype.Equality__Coq_sort -> Blocks.VarId ->
                    Blocks.PhysReg -> Interval.IntervalDesc -> AssnState 
                    a4 ((,) ([] a2) ([] a2))
savesAndRestores maxReg oinfo opid vid reg int =
  let {
   isFirst = Eqtype.eq_op Ssrnat.nat_eqType
               (unsafeCoerce (Interval.firstUsePos int)) opid}
  in
  let {
   isLast = Eqtype.eq_op (Eqtype.option_eqType Ssrnat.nat_eqType)
              (unsafeCoerce (Interval.nextUseAfter int (unsafeCoerce opid)))
              (unsafeCoerce Prelude.Nothing)}
  in
  let {save = saveOpM maxReg oinfo reg (Prelude.Just vid)} in
  let {restore = restoreOpM maxReg oinfo (Prelude.Just vid) reg} in
  case Interval.iknd int of {
   Interval.Whole -> State.pure ((,) [] []);
   Interval.LeftMost ->
    case isLast of {
     Prelude.True -> pairM (State.pure []) save;
     Prelude.False -> State.pure ((,) [] [])};
   Interval.Middle ->
    case isFirst of {
     Prelude.True ->
      case isLast of {
       Prelude.True -> pairM restore save;
       Prelude.False -> pairM restore (State.pure [])};
     Prelude.False ->
      case isLast of {
       Prelude.True -> pairM (State.pure []) save;
       Prelude.False -> State.pure ((,) [] [])}};
   Interval.RightMost ->
    case isFirst of {
     Prelude.True -> pairM restore (State.pure []);
     Prelude.False -> State.pure ((,) [] [])}}

collectAllocs :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) ->
                 (Blocks.VarInfo a3) -> Prelude.Int -> ([]
                 ((,) Interval.IntervalDesc PhysReg)) -> ((,)
                 ((,) ([] ((,) Blocks.VarId PhysReg)) ([] a2)) ([] a2)) -> a3
                 -> AssnState a4
                 ((,) ((,) ([] ((,) Blocks.VarId PhysReg)) ([] a2)) ([] a2))
collectAllocs maxReg oinfo vinfo opid ints acc v =
  let {vid = Blocks.varId vinfo v} in
  let {
   v_ints = Prelude.filter (\x ->
              ScanState.isWithin (Prelude.fst x) vid opid) ints}
  in
  case v_ints of {
   [] -> State.pure acc;
   (:) p l ->
    case p of {
     (,) int reg ->
      case acc of {
       (,) p0 saves' ->
        case p0 of {
         (,) allocs' restores' ->
          State.bind (\res ->
            case res of {
             (,) rs ss ->
              State.pure ((,) ((,) ((:) ((,) vid reg) allocs')
                ((Prelude.++) rs restores')) ((Prelude.++) ss saves'))})
            (savesAndRestores maxReg oinfo (unsafeCoerce opid) vid reg int)}}}}

doAllocations :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) ->
                 (Blocks.VarInfo a3) -> ([]
                 ((,) Interval.IntervalDesc PhysReg)) -> a1 -> AssnState 
                 a4 ([] a2)
doAllocations maxReg oinfo vinfo ints op =
  State.bind (\assn ->
    let {opid = assnOpId assn} in
    let {vars = Prelude.fst (Blocks.opRefs maxReg oinfo op)} in
    State.bind (\res ->
      case res of {
       (,) y saves ->
        case y of {
         (,) allocs restores ->
          let {op' = Blocks.applyAllocs maxReg oinfo op allocs} in
          State.bind (\x ->
            State.pure ((Prelude.++) restores ((Prelude.++) op' saves)))
            (State.modify (\assn' -> Build_AssnStateInfo ((Prelude.succ)
              ((Prelude.succ) opid)) (assnAcc assn')))}})
      (State.forFoldM ((,) ((,) [] []) []) vars
        (collectAllocs maxReg oinfo vinfo opid ints))) State.get

generateMoves :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) -> ([]
                 ((,) (Prelude.Maybe PhysReg) (Prelude.Maybe PhysReg))) ->
                 AssnState a4 ([] a2)
generateMoves maxReg oinfo moves =
  State.forFoldM [] moves (\acc mv ->
    State.bind (\mops ->
      State.pure
        (case mops of {
          Prelude.Just ops -> (Prelude.++) ops acc;
          Prelude.Nothing -> acc}))
      (case mv of {
        (,) o o0 ->
         case o of {
          Prelude.Just sreg ->
           case o0 of {
            Prelude.Just dreg ->
             State.fmap (\x -> Prelude.Just x)
               (moveOpM maxReg oinfo sreg dreg);
            Prelude.Nothing ->
             State.fmap (\x -> Prelude.Just x)
               (saveOpM maxReg oinfo sreg Prelude.Nothing)};
          Prelude.Nothing ->
           case o0 of {
            Prelude.Just dreg ->
             State.fmap (\x -> Prelude.Just x)
               (restoreOpM maxReg oinfo Prelude.Nothing dreg);
            Prelude.Nothing -> State.pure Prelude.Nothing}}}))

resolveMappings :: Prelude.Int -> (Blocks.OpInfo a4 a1 a2 a3) -> Prelude.Int
                   -> ([] a1) -> ([] a2) -> (Data.IntMap.IntMap
                   ((,) Graph.Graph Graph.Graph)) -> AssnState a4 ([] a2)
resolveMappings maxReg oinfo bid ops ops' mappings =
  case Data.IntMap.lookup bid mappings of {
   Prelude.Just graphs ->
    case graphs of {
     (,) gbeg gend ->
      State.bind (\bmoves ->
        let {ops'' = (Prelude.++) bmoves ops'} in
        State.bind (\emoves ->
          State.pure
            (case ops of {
              [] -> (Prelude.++) ops'' emoves;
              (:) o os ->
               case ops'' of {
                [] -> (Prelude.++) ops'' emoves;
                (:) o'' os'' ->
                 case Blocks.opKind maxReg oinfo (Seq.last o os) of {
                  Blocks.IsBranch ->
                   (Prelude.++) (Seq.belast o'' os'')
                     ((Prelude.++) emoves ((:) (Seq.last o'' os'') []));
                  _ -> (Prelude.++) ops'' emoves}}}))
          (generateMoves maxReg oinfo
            (unsafeCoerce
              (Graph.topsort (Fintype.ordinal_eqType maxReg) gend))))
        (generateMoves maxReg oinfo
          (unsafeCoerce (Graph.topsort (Fintype.ordinal_eqType maxReg) gbeg)))};
   Prelude.Nothing -> State.pure ops'}

considerOps :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
               (Blocks.OpInfo a6 a3 a4 a5) -> (a3 -> AssnState a6 ([] a4)) ->
               (Data.IntMap.IntMap ((,) Graph.Graph Graph.Graph)) -> ([] 
               a1) -> State.State (AssnStateInfo a6) ([] a2)
considerOps maxReg binfo oinfo f mappings =
  State.mapM (\blk ->
    let {ops = Blocks.blockOps binfo blk} in
    State.bind (\ops' ->
      let {bid = Blocks.blockId binfo blk} in
      State.bind (\ops'' -> State.pure (Blocks.setBlockOps binfo blk ops''))
        (resolveMappings maxReg oinfo bid ops ops' mappings))
      (State.concatMapM f ops))

assignRegNum :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
                (Blocks.OpInfo a6 a3 a4 a5) -> (Blocks.VarInfo a5) ->
                ScanState.ScanStateDesc -> (Data.IntMap.IntMap
                Resolve.BlockMoves) -> ([] a1) -> a6 -> (,) ([] a2) a6
assignRegNum maxReg binfo oinfo vinfo sd mappings blocks acc =
  case considerOps maxReg binfo oinfo
         (doAllocations maxReg oinfo vinfo
           (Prelude.map (\x -> (,)
             (Interval.getIntervalDesc
               (
                 (LinearScan.Utils.nth (ScanState.nextInterval maxReg sd)
                   (ScanState.intervals maxReg sd) (Prelude.fst x))))
             (Prelude.snd x))
             ((Prelude.++) (ScanState.handled maxReg sd)
               ((Prelude.++) (ScanState.active maxReg sd)
                 (ScanState.inactive maxReg sd))))) mappings blocks
         (Build_AssnStateInfo ((Prelude.succ) 0) acc) of {
   (,) blocks' assn -> (,) blocks' (assnAcc assn)}

