module Data.Interval where

import qualified Prelude
import qualified Data.List as List
import qualified Data.NPeano as NPeano
import qualified Data.NonEmpty as NonEmpty
import qualified Data.Peano as Peano
import qualified Data.Range as Range
import qualified Data.Specif as Specif


data IntervalDesc =
   Build_IntervalDesc Prelude.Int Prelude.Int (NonEmpty.NonEmpty
                                              (Specif.Coq_sigT
                                              Range.RangeDesc Range.Range))

ibeg :: IntervalDesc -> Prelude.Int
ibeg i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> ibeg0}

iend :: IntervalDesc -> Prelude.Int
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
 | I_Cons1 (Specif.Coq_sigT Range.RangeDesc Range.Range) Prelude.Int 
 Prelude.Int Interval Range.RangeDesc Range.Range
 | I_Consn (Specif.Coq_sigT Range.RangeDesc Range.Range) (NonEmpty.NonEmpty
                                                         (Specif.Coq_sigT
                                                         Range.RangeDesc
                                                         Range.Range)) 
 Prelude.Int Prelude.Int Interval Range.RangeDesc Range.Range

intervalStart :: IntervalDesc -> Interval -> Prelude.Int
intervalStart i interval0 =
  ibeg i

intervalEnd :: IntervalDesc -> Interval -> Prelude.Int
intervalEnd i interval0 =
  iend i

intervalCoversPos :: IntervalDesc -> Interval -> Prelude.Int -> Prelude.Bool
intervalCoversPos d i pos =
  (Prelude.&&) (NPeano.leb (intervalStart d i) pos)
    (NPeano.ltb pos (intervalEnd d i))

intervalExtent :: IntervalDesc -> Interval -> Prelude.Int
intervalExtent d i =
  Peano.minus (intervalEnd d i) (intervalStart d i)

anyRangeIntersects :: IntervalDesc -> Interval -> IntervalDesc -> Interval ->
                      Prelude.Bool
anyRangeIntersects i interval0 j interval1 =
  let {
   f = \x y ->
    Range.rangesIntersect (Specif.projT1 x) (Specif.projT2 x)
      (Specif.projT1 y) (Specif.projT2 y)}
  in
  List.fold_right (\r b ->
    (Prelude.||) b (List.existsb (f r) (NonEmpty.coq_NE_to_list (rds j))))
    Prelude.False (NonEmpty.coq_NE_to_list (rds i))

firstIntersectionPoint :: IntervalDesc -> Interval -> IntervalDesc ->
                          Interval -> Prelude.Maybe Prelude.Int
firstIntersectionPoint i interval0 j interval1 =
  NonEmpty.coq_NE_fold_left (\acc rd ->
    case acc of {
     Prelude.Just x -> Prelude.Just x;
     Prelude.Nothing ->
      NonEmpty.coq_NE_fold_left (\acc' rd' ->
        case acc' of {
         Prelude.Just x -> Prelude.Just x;
         Prelude.Nothing ->
          Range.rangesIntersectionPoint (Specif.projT1 rd) (Specif.projT2 rd)
            (Specif.projT1 rd') (Specif.projT2 rd')}) (rds j) Prelude.Nothing})
    (rds i) Prelude.Nothing

type FixedInterval = Interval

