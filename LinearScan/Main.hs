module LinearScan.Main where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Allocate as Allocate
import qualified LinearScan.Assign as Assign
import qualified LinearScan.Blocks as Blocks
import qualified LinearScan.Build as Build
import qualified LinearScan.LiveSets as LiveSets
import qualified LinearScan.Morph as Morph
import qualified LinearScan.Order as Order
import qualified LinearScan.Resolve as Resolve


linearScan :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) -> (Blocks.OpInfo
              a6 a3 a4 a5) -> (Blocks.VarInfo a5) -> ([] a1) -> a6 ->
              Prelude.Either Morph.SSError ((,) ([] a2) a6)
linearScan maxReg binfo oinfo vinfo blocks accum =
  let {blocks' = Order.computeBlockOrder blocks} in
  let {
   liveSets = LiveSets.computeLocalLiveSets maxReg binfo oinfo vinfo blocks'}
  in
  let {liveSets' = LiveSets.computeGlobalLiveSets binfo blocks' liveSets} in
  let {ssig = Build.buildIntervals maxReg binfo oinfo vinfo blocks liveSets'}
  in
  case Allocate.walkIntervals maxReg ( ssig) ((Prelude.succ)
         (Blocks.countOps binfo blocks)) of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right ssig' ->
    let {
     mappings = Resolve.resolveDataFlow maxReg binfo ( ssig') blocks
                  liveSets'}
    in
    Prelude.Right
    (Assign.assignRegNum maxReg binfo oinfo vinfo ( ssig') mappings blocks
      accum)}

