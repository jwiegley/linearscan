module Data.Range where

import qualified Prelude
import qualified Data.List
import qualified Data.NPeano as NPeano
import qualified Data.NonEmpty0 as NonEmpty0
import qualified Data.Peano as Peano


data UsePos =
   Build_UsePos Prelude.Int Prelude.Bool

data RangeDesc =
   Build_RangeDesc Prelude.Int Prelude.Int (NonEmpty0.NonEmpty UsePos)

rbeg :: RangeDesc -> Prelude.Int
rbeg r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups -> rbeg0}

rend :: RangeDesc -> Prelude.Int
rend r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups -> rend0}

rangesIntersect :: RangeDesc -> RangeDesc -> Prelude.Bool
rangesIntersect x y =
  case NPeano.ltb (rbeg x) (rbeg y) of {
   Prelude.True -> NPeano.ltb (rbeg y) (rend x);
   Prelude.False -> NPeano.ltb (rbeg x) (rend y)}

rangesIntersectionPoint :: RangeDesc -> RangeDesc -> Prelude.Maybe
                           Prelude.Int
rangesIntersectionPoint x y =
  case rangesIntersect x y of {
   Prelude.True -> Prelude.Just (Peano.min (rbeg x) (rbeg y));
   Prelude.False -> Prelude.Nothing}

