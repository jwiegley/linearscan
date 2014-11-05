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

import Control.Arrow ((***))
import Data.Functor.Identity
import LinearScan.Lib
import LinearScan.Main
import LinearScan.NonEmpty0
import LinearScan.Vector0

type    VirtReg    = Identity Int
newtype ScanState  = ScanState LinearScan__ScanStateDesc
newtype PhysReg    = PhysReg { getPhysReg :: LinearScan__PhysReg }
newtype StartsLoop = StartsLoop { getStartsLoop :: Bool }
newtype EndsLoop   = EndsLoop { getEndsLoop :: Bool }
type    IntervalId = Int

toCoqV :: [a] -> V__Coq_t a
toCoqV [] = V__Coq_nil
toCoqV (x:xs) = V__Coq_cons x 0 (toCoqV xs)

allocateRegisters
    :: Int
    -> (block -> (StartsLoop, EndsLoop, [Either VirtReg PhysReg]))
    -> NonEmpty block -> ScanState
allocateRegisters maxVirtReg blockInfo blocks =
    ScanState $ _LinearScan__allocateRegisters
        maxVirtReg (coq_NE_map gather blocks)
  where
    gather b =
        let (starts, ends, refs) = blockInfo b in
        LinearScan__Build_Block b (getStartsLoop starts) (getEndsLoop ends)
            (length refs) (toCoqV (fmap (fmap getPhysReg) refs))

handledIntervalIds :: ScanState -> [(IntervalId, PhysReg)]
handledIntervalIds
    (ScanState (LinearScan__Build_ScanStateDesc _ni _ _ _ _ _ hnd)) =
  map (runIdentity *** PhysReg) hnd
