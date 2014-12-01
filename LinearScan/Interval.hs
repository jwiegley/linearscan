module LinearScan.Interval where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Range as Range


data IntervalDesc =
   Build_IntervalDesc Prelude.Int Prelude.Int ([] Range.RangeDesc)

ibeg :: IntervalDesc -> Prelude.Int
ibeg i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds -> ibeg0}

iend :: IntervalDesc -> Prelude.Int
iend i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds -> iend0}

packInterval :: IntervalDesc -> IntervalDesc
packInterval d =
  d

intervalStart :: IntervalDesc -> Prelude.Int
intervalStart i =
  ibeg i

intervalEnd :: IntervalDesc -> Prelude.Int
intervalEnd i =
  iend i

intervalExtent :: IntervalDesc -> Prelude.Int
intervalExtent d =
  (Prelude.-) (intervalEnd d) (intervalStart d)

