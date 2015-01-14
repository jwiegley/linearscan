module LinearScan.NonEmpty0 where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


coq_NE_mapAccumL :: (a1 -> a2 -> (,) a1 a3) -> a1 -> ([] a2) -> (,) a1
                    ([] a3)
coq_NE_mapAccumL f s v =
  (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
    (\x ->
    case f s x of {
     (,) s' y -> (,) s' ((:[]) y)})
    (\x xs ->
    case f s x of {
     (,) s' y ->
      case coq_NE_mapAccumL f s' xs of {
       (,) s'' ys -> (,) s'' ((:) y ys)}})
    v

