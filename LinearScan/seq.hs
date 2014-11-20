module LinearScan.Seq where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


flatten :: ([] ([] a1)) -> [] a1
flatten =
  Prelude.foldr (Prelude.++) []

