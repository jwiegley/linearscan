module LinearScan.IntMap where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


coq_IntSet_forFold :: a1 -> Data.IntSet.IntSet -> (a1 -> Prelude.Int -> a1)
                      -> a1
coq_IntSet_forFold z m f =
  Data.IntSet.foldl' f z m

