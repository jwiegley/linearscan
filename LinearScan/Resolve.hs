{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Resolve where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Blocks as Blocks
import qualified LinearScan.Graph as Graph
import qualified LinearScan.IntMap as IntMap
import qualified LinearScan.Lib as Lib
import qualified LinearScan.LiveSets as LiveSets
import qualified LinearScan.ScanState as ScanState
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

checkIntervalBoundary :: Prelude.Int -> ScanState.ScanStateDesc ->
                         Prelude.Int -> Prelude.Bool ->
                         LiveSets.BlockLiveSets -> LiveSets.BlockLiveSets ->
                         (Data.IntMap.IntMap ((,) Graph.Graph Graph.Graph))
                         -> Prelude.Int -> Data.IntMap.IntMap
                         ((,) Graph.Graph Graph.Graph)
checkIntervalBoundary maxReg sd key in_from from to mappings vid =
  let {
   mfrom_int = ScanState.lookupInterval maxReg sd __ vid
                 (LiveSets.blockLastOpId from)}
  in
  case mfrom_int of {
   Prelude.Just from_interval ->
    let {
     mto_int = ScanState.lookupInterval maxReg sd __ vid
                 (LiveSets.blockFirstOpId to)}
    in
    case mto_int of {
     Prelude.Just to_interval ->
      case Eqtype.eq_op
             (Fintype.ordinal_eqType (ScanState.nextInterval maxReg sd))
             (unsafeCoerce from_interval) (unsafeCoerce to_interval) of {
       Prelude.True -> mappings;
       Prelude.False ->
        let {
         msreg = ScanState.lookupRegister maxReg sd __
                   (unsafeCoerce from_interval)}
        in
        let {
         mdreg = ScanState.lookupRegister maxReg sd __
                   (unsafeCoerce to_interval)}
        in
        let {
         addToGraphs = \e xs ->
          case xs of {
           (,) gbeg gend ->
            case in_from of {
             Prelude.True -> (,) gbeg
              (Graph.addEdge (Fintype.ordinal_eqType maxReg) e gend);
             Prelude.False -> (,)
              (Graph.addEdge (Fintype.ordinal_eqType maxReg) e gbeg) gend}}}
        in
        let {
         f = \mxs ->
          let {e = (,) msreg mdreg} in
          Prelude.Just
          (unsafeCoerce addToGraphs e
            (case mxs of {
              Prelude.Just xs -> xs;
              Prelude.Nothing -> (,)
               (Graph.emptyGraph (Fintype.ordinal_eqType maxReg))
               (Graph.emptyGraph (Fintype.ordinal_eqType maxReg))}))}
        in
        Data.IntMap.alter f key mappings};
     Prelude.Nothing -> mappings};
   Prelude.Nothing -> mappings}

type BlockMoves = (,) Graph.Graph Graph.Graph

resolveDataFlow :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
                   ScanState.ScanStateDesc -> ([] a1) -> (Data.IntMap.IntMap
                   LiveSets.BlockLiveSets) -> Data.IntMap.IntMap BlockMoves
resolveDataFlow maxReg binfo sd blocks liveSets =
  Lib.forFold Data.IntMap.empty blocks (\mappings b ->
    let {bid = Blocks.blockId binfo b} in
    case Data.IntMap.lookup bid liveSets of {
     Prelude.Just from ->
      let {successors = Blocks.blockSuccessors binfo b} in
      let {
       in_from = (Prelude.<=) (Data.List.length successors) ((Prelude.succ)
                   0)}
      in
      Lib.forFold mappings successors (\ms s_bid ->
        case Data.IntMap.lookup s_bid liveSets of {
         Prelude.Just to ->
          let {
           key = case in_from of {
                  Prelude.True -> bid;
                  Prelude.False -> s_bid}}
          in
          IntMap.coq_IntSet_forFold ms (LiveSets.blockLiveIn to)
            (checkIntervalBoundary maxReg sd key in_from from to);
         Prelude.Nothing -> ms});
     Prelude.Nothing -> mappings})

