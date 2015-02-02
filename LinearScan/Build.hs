module LinearScan.Build where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Blocks as Blocks
import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Lib as Lib
import qualified LinearScan.LiveSets as LiveSets
import qualified LinearScan.Proto as Proto
import qualified LinearScan.Range as Range
import qualified LinearScan.ScanState as ScanState
import qualified LinearScan.Seq as Seq


__ :: any
__ = Prelude.error "Logical or arity value used"

data BuildState =
   Build_BuildState ([] (Prelude.Maybe Proto.SortedProtoRanges)) ([]
                                                                 (Prelude.Maybe
                                                                 Interval.BoundedInterval))

bsRegs :: Prelude.Int -> Prelude.Int -> BuildState -> []
          (Prelude.Maybe Interval.BoundedInterval)
bsRegs maxReg pos b =
  case b of {
   Build_BuildState bsVars bsRegs0 -> bsRegs0}

reduceOp :: Prelude.Int -> (Blocks.OpInfo a5 a2 a3 a4) -> Prelude.Int -> a2
            -> a1 -> BuildState -> BuildState
reduceOp maxReg oinfo pos op block bs =
  Lib.undefined

reduceBlock :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
               (Blocks.OpInfo a6 a3 a4 a5) -> Prelude.Int -> a1 ->
               Data.IntSet.IntSet -> BuildState -> BuildState
reduceBlock maxReg binfo oinfo pos block liveOut bs =
  let {_evar_0_ = \bs0 -> let {_evar_0_ = \bs1 -> bs1} in  _evar_0_ bs0} in
  let {
   _evar_0_0 = \o os iHos bs0 ->
    let {
     _evar_0_0 = \bs1 ->
      iHos
        (reduceOp maxReg oinfo ((Prelude.+) pos (Data.List.length os)) o
          block bs1)}
    in
     _evar_0_0 bs0}
  in
  Datatypes.list_rect _evar_0_ _evar_0_0 (Blocks.blockOps binfo block) bs

reduceBlocks :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
                (Blocks.OpInfo a6 a3 a4 a5) -> (Blocks.VarInfo a5) -> ([] 
                a1) -> (Data.IntMap.IntMap LiveSets.BlockLiveSets) ->
                BuildState
reduceBlocks maxReg binfo oinfo vinfo blocks liveSets =
  let {
   go = let {
         go b bs pos =
           let {bid = Blocks.blockId binfo b} in
           let {
            outs = case Data.IntMap.lookup bid liveSets of {
                    Prelude.Just ls -> LiveSets.blockLiveOut ls;
                    Prelude.Nothing -> Data.IntSet.empty}}
           in
           reduceBlock maxReg binfo oinfo pos b outs
             (case bs of {
               [] -> Build_BuildState
                (Seq.nseq ((Prelude.succ)
                  (Blocks.foldOps binfo (\n op ->
                    Data.List.foldl' (\m v ->
                      Prelude.max m (Blocks.varId vinfo v)) n
                      (Prelude.fst (Blocks.opRefs maxReg oinfo op))) 0
                    blocks)) Prelude.Nothing)
                (Data.List.replicate maxReg Prelude.Nothing);
               (:) b' bs' ->
                go b' bs'
                  ((Prelude.+) pos
                    (Data.List.length (Blocks.blockOps binfo b)))})}
        in go}
  in
  case blocks of {
   [] -> Build_BuildState
    (Seq.nseq ((Prelude.succ)
      (Blocks.foldOps binfo (\n op ->
        Data.List.foldl' (\m v -> Prelude.max m (Blocks.varId vinfo v)) n
          (Prelude.fst (Blocks.opRefs maxReg oinfo op))) 0 blocks))
      Prelude.Nothing) (Data.List.replicate maxReg Prelude.Nothing);
   (:) x xs -> go x xs 0}

buildIntervals :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
                  (Blocks.OpInfo a6 a3 a4 a5) -> (Blocks.VarInfo a5) -> ([]
                  a1) -> (Data.IntMap.IntMap LiveSets.BlockLiveSets) ->
                  ScanState.ScanStateSig
buildIntervals maxReg binfo oinfo vinfo blocks liveSets =
  let {
   mkint = \vid ss pos mrs f ->
    case mrs of {
     Prelude.Just rs ->
      f ( ss) __
        (
          (Interval.packInterval (Interval.Build_IntervalDesc vid
            (Range.rbeg ( ( (Prelude.head ( rs)))))
            (Range.rend ( ( (Prelude.last ( rs))))) Interval.Whole
            rs))) __;
     Prelude.Nothing -> ss}}
  in
  let {
   handleVar = \pos vid ss mrs ->
    mkint vid ss pos mrs (\sd _ d _ ->
      ScanState.packScanState maxReg ScanState.Pending
        (ScanState.Build_ScanStateDesc ((Prelude.succ)
        (ScanState.nextInterval maxReg sd))
        (LinearScan.Utils.snoc (ScanState.nextInterval maxReg sd)
          (ScanState.intervals maxReg sd) d)
        (ScanState.fixedIntervals maxReg sd)
        (Data.List.insertBy (Data.Ord.comparing Prelude.snd) ((,)
          ( (ScanState.nextInterval maxReg sd)) (Interval.ibeg d))
          (Prelude.map Prelude.id (ScanState.unhandled maxReg sd)))
        (Prelude.map Prelude.id (ScanState.active maxReg sd))
        (Prelude.map Prelude.id (ScanState.inactive maxReg sd))
        (Prelude.map Prelude.id (ScanState.handled maxReg sd))))}
  in
  let {bs = reduceBlocks maxReg binfo oinfo vinfo blocks liveSets} in
  let {
   f = \mx ->
    case mx of {
     Prelude.Just x -> Prelude.Just ( x);
     Prelude.Nothing -> Prelude.Nothing}}
  in
  let {regs = LinearScan.Utils.vmap maxReg f (bsRegs maxReg 0 bs)} in
  let {
   s2 = ScanState.packScanState maxReg ScanState.Pending
          (ScanState.Build_ScanStateDesc
          (ScanState.nextInterval maxReg (ScanState.Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] [] []))
          (ScanState.intervals maxReg (ScanState.Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] [] [])) regs
          (ScanState.unhandled maxReg (ScanState.Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] [] []))
          (ScanState.active maxReg (ScanState.Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] [] []))
          (ScanState.inactive maxReg (ScanState.Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] [] []))
          (ScanState.handled maxReg (ScanState.Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] [] [])))}
  in
  let {s3 = Lib.foldl_with_index (handleVar 0) s2 Lib.undefined} in
  ScanState.packScanState maxReg ScanState.InUse ( s3)

