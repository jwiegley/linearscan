module Data.Range where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.NPeano as NPeano
import qualified Data.NonEmpty as NonEmpty
import qualified Data.Peano as Peano


data UsePos =
   Build_UsePos Datatypes.Coq_nat Datatypes.Coq_bool

data RangeDesc =
   Build_RangeDesc Datatypes.Coq_nat Datatypes.Coq_nat (NonEmpty.NonEmpty
                                                       UsePos)

rbeg :: RangeDesc -> Datatypes.Coq_nat
rbeg r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups -> rbeg0}

rend :: RangeDesc -> Datatypes.Coq_nat
rend r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups -> rend0}

data Range =
   R_Sing UsePos
 | R_Cons UsePos RangeDesc Range
 | R_Extend RangeDesc Datatypes.Coq_nat Datatypes.Coq_nat Range

rangesIntersect :: RangeDesc -> Range -> RangeDesc -> Range ->
                   Datatypes.Coq_bool
rangesIntersect x range0 y range1 =
  case NPeano.ltb (rbeg x) (rbeg y) of {
   Datatypes.Coq_true -> NPeano.ltb (rbeg y) (rend x);
   Datatypes.Coq_false -> NPeano.ltb (rbeg x) (rend y)}

rangesIntersectionPoint :: RangeDesc -> Range -> RangeDesc -> Range ->
                           Datatypes.Coq_option Datatypes.Coq_nat
rangesIntersectionPoint x xr y yr =
  case rangesIntersect x xr y yr of {
   Datatypes.Coq_true -> Datatypes.Some (Peano.min (rbeg x) (rbeg y));
   Datatypes.Coq_false -> Datatypes.None}

