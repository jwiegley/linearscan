module LinearScan.NonEmpty0 where

import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

coq_NonEmpty_rect :: (a1 -> a2) -> (a1 -> ([] a1) -> a2 -> a2) -> ([] 
                     a1) -> a2
coq_NonEmpty_rect f f0 n =
  (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
    (\y ->
    f y)
    (\y n0 ->
    f0 y n0 (coq_NonEmpty_rect f f0 n0))
    n

coq_NonEmpty_rec :: (a1 -> a2) -> (a1 -> ([] a1) -> a2 -> a2) -> ([] 
                    a1) -> a2
coq_NonEmpty_rec =
  coq_NonEmpty_rect

