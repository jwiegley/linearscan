{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Trace where


import Debug.Trace (trace, traceShow)
import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Blocks as Blocks
import qualified LinearScan.IntMap as IntMap
import qualified LinearScan.Interval as Interval
import qualified LinearScan.LiveSets as LiveSets
import qualified LinearScan.ScanState as ScanState
import qualified LinearScan.State as State
import qualified LinearScan.String0 as String0
import qualified LinearScan.Eqtype as Eqtype
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

showOps1 :: Prelude.Int -> (Blocks.OpInfo a3 a1 a2) ->
            ScanState.ScanStateDesc -> Prelude.Int -> ([] a1) ->
            Prelude.String
showOps1 maxReg oinfo sd startPos ops =
  case ops of {
   [] -> [];
   (:) o os ->
    let {refs = Blocks.opRefs maxReg oinfo o} in
    let {
     collectVarRefs = \p ->
      State.concat
        (Prelude.map (\v ->
          let {vid = Blocks.varId maxReg v} in
          case vid of {
           Prelude.Left p0 -> [];
           Prelude.Right vid0 ->
            let {
             k = \idx acc i ->
              case p vid0 i of {
               Prelude.True -> (:) ((,) ( idx) (Prelude.Right vid0)) acc;
               Prelude.False -> acc}}
            in
            (LinearScan.Utils.vfoldl'_with_index)
              (ScanState.nextInterval maxReg sd) k []
              (ScanState.intervals maxReg sd)}) refs)}
    in
    let {
     collectRegRefs = \p ->
      State.concat
        (Prelude.map (\v ->
          let {vid = Blocks.varId maxReg v} in
          case vid of {
           Prelude.Left vid0 ->
            let {
             k = \idx acc i ->
              case p vid0 i of {
               Prelude.True -> (:) ((,) ( idx) (Prelude.Left vid0)) acc;
               Prelude.False -> acc}}
            in
            (LinearScan.Utils.vfoldl'_with_index) maxReg k []
              (ScanState.fixedIntervals maxReg sd);
           Prelude.Right v0 -> []}) refs)}
    in
    let {
     startingP = \vid i ->
      (Prelude.&&)
        (Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Interval.ivar ( i)))
          vid)
        (Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Interval.ibeg ( i)))
          (unsafeCoerce ((Prelude.succ) (Ssrnat.double startPos))))}
    in
    let {
     endingP = \vid i ->
      (Prelude.&&)
        (Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Interval.ivar ( i)))
          vid)
        (Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Interval.iend ( i)))
          (unsafeCoerce ((Prelude.succ) (Ssrnat.double startPos))))}
    in
    let {
     checkReg = \p vid mi ->
      case mi of {
       Prelude.Just i -> p vid i;
       Prelude.Nothing -> Prelude.False}}
    in
    let {
     startingAtPos = (Prelude.++) (unsafeCoerce collectVarRefs startingP)
                       (collectRegRefs (\vid ->
                         unsafeCoerce checkReg startingP ( vid)))}
    in
    let {
     endingAtPos = (Prelude.++) (unsafeCoerce collectVarRefs endingP)
                     (collectRegRefs (\vid ->
                       unsafeCoerce checkReg endingP ( vid)))}
    in
    String0.append
      (Blocks.showOp1 maxReg oinfo ((Prelude.succ) (Ssrnat.double startPos))
        startingAtPos endingAtPos o)
      (showOps1 maxReg oinfo sd ((Prelude.succ) startPos) os)}

showBlocks1 :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
               (Blocks.OpInfo a5 a3 a4) -> ScanState.ScanStateDesc ->
               (IntMap.IntMap LiveSets.BlockLiveSets) -> ([] a1) ->
               Prelude.String
showBlocks1 maxReg binfo oinfo sd liveSets blocks =
  let {
   go pos bs =
     case bs of {
      [] -> [];
      (:) b bs0 ->
       let {bid = Blocks.blockId binfo b} in
       case IntMap.coq_IntMap_lookup bid liveSets of {
        Prelude.Just ls ->
         let {liveIn = LiveSets.blockLiveIn ls} in
         let {liveOut = LiveSets.blockLiveOut ls} in
         String0.append
           (Blocks.showBlock1 binfo bid pos liveIn liveOut
             (showOps1 maxReg oinfo sd) b)
           (go ((Prelude.+) pos (Blocks.blockSize binfo b)) bs0);
        Prelude.Nothing ->
         String0.append
           (Blocks.showBlock1 binfo bid pos IntMap.emptyIntSet
             IntMap.emptyIntSet (showOps1 maxReg oinfo sd) b)
           (go ((Prelude.+) pos (Blocks.blockSize binfo b)) bs0)}}}
  in go 0 blocks

traceBlocksHere :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
                   (Blocks.OpInfo a5 a3 a4) -> ScanState.ScanStateDesc ->
                   (IntMap.IntMap LiveSets.BlockLiveSets) -> ([] a1) -> [] 
                   a1
traceBlocksHere maxReg binfo oinfo sd liveSets blocks =
  Blocks.traceBlocks binfo
    (showBlocks1 maxReg binfo oinfo sd liveSets blocks) blocks

