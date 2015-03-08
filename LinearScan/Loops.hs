module LinearScan.Loops where


import Debug.Trace (trace, traceShow)
import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Blocks as Blocks


computeBlockOrder :: (Blocks.BlockInfo a1 a2 a3 a4) -> ([] a1) -> [] a1
computeBlockOrder binfo blocks =
  case blocks of {
   [] -> [];
   (:) b bs -> blocks}

