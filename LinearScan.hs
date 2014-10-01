module LinearScan
    ( Graph
    , VirtReg
    , ScanState
    , allocateRegisters
    , IntervalId
    , handledIntervalIds
    , Interval
    , PhysReg
    , registerAssignment
    ) where

import           Control.Applicative
import           Data.Fin0
import qualified Data.Interval as I
import           Data.Main

type    VirtReg    = Int
newtype Graph a    = Graph (LinearScan__Graph a)
newtype ScanState  = ScanState LinearScan__ScanStateDesc
newtype Interval   = Interval I.IntervalDesc
newtype PhysReg    = PhysReg LinearScan__PhysReg
type    IntervalId = Int

allocateRegisters :: Graph VirtReg -> ScanState
allocateRegisters (Graph g) = ScanState (_LinearScan__allocateRegisters g)

-- nextInterval :: ScanState -> Int
-- nextInterval (LinearScan__Build_ScanStateDesc ni _ _ _ _ _ _ _) = ni

handledIntervalIds :: ScanState -> [IntervalId]
handledIntervalIds (ScanState (LinearScan__Build_ScanStateDesc ni _ _ _ hnd _ _ _)) =
    map (fin_to_nat ni) hnd

-- getInterval :: ScanState -> IntervalId -> Interval
-- getInterval (ScanState (LinearScan__Build_ScanStateDesc ni _ _ _ _ f _ _)) n =
--     Interval (f (from_nat ni n))

registerAssignment :: ScanState -> IntervalId -> Maybe PhysReg
registerAssignment (ScanState (LinearScan__Build_ScanStateDesc ni _ _ _ _ _ f _)) n =
    -- jww (2014-10-01): Allow the Haskell caller to specific the maximum
    -- number of registers.
    PhysReg <$> _LinearScan__V__nth _LinearScan__maxReg f (from_nat ni n)
