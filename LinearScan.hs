module LinearScan
    ( VirtReg
    , StartsLoop(..)
    , EndsLoop(..)
    , ScanState
    , allocateRegisters
    , IntervalId
    , handledIntervalIds
    , PhysReg
    ) where

import           Control.Arrow (second)
import qualified Data.List.NonEmpty as NE
import           LinearScan.Lib
import           LinearScan.Main
import           LinearScan.NonEmpty0

type    VirtReg    = Int
newtype ScanState  = ScanState LinearScan__ScanStateDesc
newtype PhysReg    = PhysReg { getPhysReg :: LinearScan__PhysReg }
newtype StartsLoop = StartsLoop { getStartsLoop :: Bool }
newtype EndsLoop   = EndsLoop { getEndsLoop :: Bool }
type    IntervalId = Int

toNonEmpty :: NE.NonEmpty a -> NonEmpty a
toNonEmpty (x NE.:| []) = NE_Sing x
toNonEmpty (x NE.:| (y:ys)) = NE_Cons x (toNonEmpty (y NE.:| ys))

toCoqV :: [a] -> V__Coq_t a
toCoqV [] = V__Coq_nil
toCoqV (x:xs) = V__Coq_cons x 0 (toCoqV xs)

-- fromCoqV :: LinearScan__V__Coq_t a -> [a]
-- fromCoqV LinearScan__V__Coq_nil = []
-- fromCoqV (LinearScan__V__Coq_cons x _ xs) = x : fromCoqV xs

allocateRegisters
    :: Int
    -> (block -> (StartsLoop, EndsLoop, [Either VirtReg PhysReg]))
    -> NE.NonEmpty block -> ScanState
allocateRegisters maxVirtReg blockInfo blocks =
    ScanState $ _LinearScan__allocateRegisters
        maxVirtReg (toNonEmpty (NE.map gather blocks))
  where
    gather b =
        let (starts, ends, refs) = blockInfo b in
        LinearScan__Build_Block b (getStartsLoop starts) (getEndsLoop ends)
            (length refs) (toCoqV (fmap (fmap getPhysReg) refs))

handledIntervalIds :: ScanState -> [(IntervalId, PhysReg)]
handledIntervalIds
    (ScanState (LinearScan__Build_ScanStateDesc _ni _ _ _ _ _ hnd)) =
  map (second PhysReg) hnd
