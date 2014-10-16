module LinearScan
    ( VirtReg
    , ScanState
    , allocateRegisters
    , IntervalId
    , handledIntervalIds
    , PhysReg
    , registerAssignment
    ) where

import           Control.Applicative
import           Data.Fin0
import           Data.NonEmpty0
import qualified Data.List.NonEmpty as NE
import           Data.Main

type    VirtReg    = Int
newtype ScanState  = ScanState LinearScan__ScanStateDesc
newtype PhysReg    = PhysReg { getPhysReg :: LinearScan__PhysReg }
type    IntervalId = Int

toNonEmpty :: NE.NonEmpty a -> NonEmpty a
toNonEmpty (x NE.:| []) = NE_Sing x
toNonEmpty (x NE.:| (y:ys)) = NE_Cons x (toNonEmpty (y NE.:| ys))

allocateRegisters
    :: (block -> Bool)
    -> (block -> Bool)
    -> (block -> [Either VirtReg PhysReg])
    -> NE.NonEmpty block
    -> ScanState
allocateRegisters starts ends refs blocks =
    ScanState (_LinearScan__allocateRegisters
                   (toNonEmpty (NE.map gather blocks)))
  where
    gather b = LinearScan__Build_Block (starts b) (ends b)
               (map (fmap getPhysReg) (refs b))

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
