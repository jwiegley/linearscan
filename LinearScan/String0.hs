module LinearScan.String0 where


import Debug.Trace (trace, traceShow)
import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   [] -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

