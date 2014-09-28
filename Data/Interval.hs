module Data.Interval where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.List as List
import qualified Data.NPeano as NPeano
import qualified Data.NonEmpty as NonEmpty
import qualified Data.Peano as Peano
import qualified Data.Range as Range
import qualified Data.Specif as Specif


data IntervalDesc =
   Build_IntervalDesc Datatypes.Coq_nat Datatypes.Coq_nat (NonEmpty.NonEmpty
                                                          (Specif.Coq_sigT
                                                          Range.RangeDesc
                                                          Range.Range))

ibeg :: IntervalDesc -> Datatypes.Coq_nat
ibeg i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> ibeg0}

iend :: IntervalDesc -> Datatypes.Coq_nat
iend i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> iend0}

rds :: IntervalDesc -> NonEmpty.NonEmpty
       (Specif.Coq_sigT Range.RangeDesc Range.Range)
rds i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> rds0}

data Interval =
   I_Sing Range.RangeDesc Range.Range
 | I_Cons1 (Specif.Coq_sigT Range.RangeDesc Range.Range) Datatypes.Coq_nat 
 Datatypes.Coq_nat Interval Range.RangeDesc Range.Range
 | I_Consn (Specif.Coq_sigT Range.RangeDesc Range.Range) (NonEmpty.NonEmpty
                                                         (Specif.Coq_sigT
                                                         Range.RangeDesc
                                                         Range.Range)) 
 Datatypes.Coq_nat Datatypes.Coq_nat Interval Range.RangeDesc Range.Range

intervalStart :: IntervalDesc -> Interval -> Datatypes.Coq_nat
intervalStart i interval0 =
  ibeg i

intervalEnd :: IntervalDesc -> Interval -> Datatypes.Coq_nat
intervalEnd i interval0 =
  iend i

intervalCoversPos :: IntervalDesc -> Interval -> Datatypes.Coq_nat ->
                     Datatypes.Coq_bool
intervalCoversPos d i pos =
  Datatypes.andb (NPeano.leb (intervalStart d i) pos)
    (NPeano.ltb pos (intervalEnd d i))

intervalExtent :: IntervalDesc -> Interval -> Datatypes.Coq_nat
intervalExtent d i =
  Peano.minus (intervalEnd d i) (intervalStart d i)

anyRangeIntersects :: IntervalDesc -> Interval -> IntervalDesc -> Interval ->
                      Datatypes.Coq_bool
anyRangeIntersects i interval0 j interval1 =
  let {
   f = \x y ->
    Range.rangesIntersect (Specif.projT1 x) (Specif.projT2 x)
      (Specif.projT1 y) (Specif.projT2 y)}
  in
  List.fold_right (\r b ->
    Datatypes.orb b (List.existsb (f r) (NonEmpty.coq_NE_to_list (rds j))))
    Datatypes.Coq_false (NonEmpty.coq_NE_to_list (rds i))

firstIntersectionPoint :: IntervalDesc -> Interval -> IntervalDesc ->
                          Interval -> Datatypes.Coq_option Datatypes.Coq_nat
firstIntersectionPoint i interval0 j interval1 =
  NonEmpty.coq_NE_fold_left (\acc rd ->
    case acc of {
     Datatypes.Some x -> Datatypes.Some x;
     Datatypes.None ->
      NonEmpty.coq_NE_fold_left (\acc' rd' ->
        case acc' of {
         Datatypes.Some x -> Datatypes.Some x;
         Datatypes.None ->
          Range.rangesIntersectionPoint (Specif.projT1 rd) (Specif.projT2 rd)
            (Specif.projT1 rd') (Specif.projT2 rd')}) (rds j) Datatypes.None})
    (rds i) Datatypes.None

type FixedInterval = Interval

