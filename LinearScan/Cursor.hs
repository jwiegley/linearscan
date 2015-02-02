module LinearScan.Cursor where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Interval as Interval
import qualified LinearScan.Morph as Morph
import qualified LinearScan.ScanState as ScanState


__ :: any
__ = Prelude.error "Logical or arity value used"

curId :: Prelude.Int -> ScanState.ScanStateDesc -> (,) ScanState.IntervalId
         Prelude.Int
curId maxReg sd =
  Prelude.head (ScanState.unhandled maxReg sd)

curIntDetails :: Prelude.Int -> ScanState.ScanStateDesc ->
                 Interval.IntervalDesc
curIntDetails maxReg sd =
  LinearScan.Utils.nth (ScanState.nextInterval maxReg sd)
    (ScanState.intervals maxReg sd) (Prelude.fst (curId maxReg sd))

curPosition :: Prelude.Int -> ScanState.ScanStateDesc -> Prelude.Int
curPosition maxReg sd =
  Interval.intervalStart ( (curIntDetails maxReg sd))

withCursor :: Prelude.Int -> ScanState.ScanStateDesc ->
              (ScanState.ScanStateDesc -> () -> Morph.SState () a1 a2) ->
              Morph.SState () a1 a2
withCursor maxReg pre f x =
  case x of {
   Morph.Build_SSInfo thisDesc _ ->
    f thisDesc __ (Morph.Build_SSInfo thisDesc __)}

