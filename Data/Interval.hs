module Data.Interval where

import qualified Prelude
import qualified Data.List
import qualified Data.NPeano as NPeano
import qualified Data.NonEmpty0 as NonEmpty0
import qualified Data.Peano as Peano
import qualified Data.Range as Range
import qualified Data.Specif as Specif


data IntervalDesc =
   Build_IntervalDesc Prelude.Int Prelude.Int (NonEmpty0.NonEmpty
                                              Range.RangeDesc)

ibeg :: IntervalDesc -> Prelude.Int
ibeg i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> ibeg0}

iend :: IntervalDesc -> Prelude.Int
iend i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> iend0}

rds :: IntervalDesc -> NonEmpty0.NonEmpty Range.RangeDesc
rds i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> rds0}

intervalStart :: IntervalDesc -> Prelude.Int
intervalStart i =
  ibeg i

intervalEnd :: IntervalDesc -> Prelude.Int
intervalEnd i =
  iend i

intervalCoversPos :: IntervalDesc -> Prelude.Int -> Prelude.Bool
intervalCoversPos d pos =
  (Prelude.&&) (NPeano.leb (intervalStart d) pos)
    (NPeano.ltb pos (intervalEnd d))

intervalExtent :: IntervalDesc -> Prelude.Int
intervalExtent d =
  Peano.minus (intervalEnd d) (intervalStart d)

anyRangeIntersects :: IntervalDesc -> IntervalDesc -> Prelude.Bool
anyRangeIntersects i j =
  let {
   f = \x y ->
    Range.rangesIntersect (Specif.proj1_sig x) (Specif.proj1_sig y)}
  in
  Prelude.foldr (\r b ->
    (Prelude.||) b ((Prelude.any) (f r) (NonEmpty0.coq_NE_to_list (rds j))))
    Prelude.False (NonEmpty0.coq_NE_to_list (rds i))

firstIntersectionPoint :: IntervalDesc -> IntervalDesc -> Prelude.Maybe
                          Prelude.Int
firstIntersectionPoint i j =
  NonEmpty0.coq_NE_fold_left (\acc rd ->
    case acc of {
     Prelude.Just x -> Prelude.Just x;
     Prelude.Nothing ->
      NonEmpty0.coq_NE_fold_left (\acc' rd' ->
        case acc' of {
         Prelude.Just x -> Prelude.Just x;
         Prelude.Nothing ->
          Range.rangesIntersectionPoint (Specif.proj1_sig rd)
            (Specif.proj1_sig rd')}) (rds j) Prelude.Nothing}) (rds i)
    Prelude.Nothing

