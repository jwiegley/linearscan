module LinearScan.Main where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


linearScan :: (BlockInfo a1 a2 a3 a4) -> (OpInfo a6 a3 a4 a5) -> (VarInfo 
              a5) -> ([] a1) -> a6 -> Prelude.Either SSError ((,) ([] a2) a6)
linearScan binfo oinfo vinfo blocks accum =
  let {blocks' = computeBlockOrder blocks} in
  let {liveSets = computeLocalLiveSets binfo oinfo vinfo blocks'} in
  let {liveSets' = computeGlobalLiveSets binfo blocks' liveSets} in
  let {ssig = buildIntervals binfo oinfo vinfo blocks liveSets'} in
  case walkIntervals ( ssig) ((Prelude.succ) (countOps binfo blocks)) of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right ssig' ->
    let {mappings = resolveDataFlow binfo ( ssig') blocks liveSets'} in
    Prelude.Right
    (assignRegNum binfo oinfo vinfo ( ssig') mappings blocks accum)}

