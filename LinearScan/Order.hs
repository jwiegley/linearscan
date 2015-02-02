module LinearScan.Order where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


computeBlockOrder :: ([] a1) -> [] a1
computeBlockOrder blocks =
  blocks

