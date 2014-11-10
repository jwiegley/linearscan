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

import Control.Arrow (second)
import LinearScan.Lib
import LinearScan.Main
import LinearScan.NonEmpty0
import LinearScan.Vector0

type    VirtReg    = Int
newtype ScanState  = ScanState LinearScan__MLS__MS__ScanStateDesc
newtype PhysReg    = PhysReg { getPhysReg :: LinearScan__MLS__MS__PhysReg }
newtype StartsLoop = StartsLoop { getStartsLoop :: Bool }
newtype EndsLoop   = EndsLoop { getEndsLoop :: Bool }
type    IntervalId = Int

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
            (length refs) (map (fmap getPhysReg) refs)

handledIntervalIds :: ScanState -> [(IntervalId, PhysReg)]
handledIntervalIds
    (ScanState (LinearScan__MLS__MS__Build_ScanStateDesc _ni _ _ _ _ _ hnd)) =
  map (second PhysReg) hnd
