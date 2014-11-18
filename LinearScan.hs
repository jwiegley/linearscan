{-# OPTIONS_GHC -Wall -Werror #-}

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
import LinearScan.Main

type    VirtReg    = Int
newtype ScanState  = ScanState LinearScan__MLS__MS__ScanStateDesc
newtype PhysReg    = PhysReg { getPhysReg :: LinearScan__MLS__MS__PhysReg }
newtype StartsLoop = StartsLoop { getStartsLoop :: Bool }
newtype EndsLoop   = EndsLoop { getEndsLoop :: Bool }
type    IntervalId = Int

allocateRegisters
    :: Int
    -> (block -> (StartsLoop, EndsLoop, [Either VirtReg PhysReg]))
    -> [block]
    -> Either String ScanState
allocateRegisters _ _ [] = Left "No basic blocks were provided"
allocateRegisters maxVirtReg blockInfo blocks =
    case _LinearScan__allocateRegisters maxVirtReg (map gather blocks) of
        Left x -> Left $ case x of
            LinearScan__ECurrentIsSingleton ->
                "Current interval is a singleton"
            LinearScan__ENoIntervalsToSplit ->
                "There are no intervals to split"
            LinearScan__EFailedToAllocateRegister ->
                "Failed to allocate register for current interval"
            LinearScan__ESpillingNotYetImplemented ->
                "Spilling is not yet implemented!"
        Right x -> Right $ ScanState x
  where
    gather b =
        let (starts, ends, refs) = blockInfo b in
        LinearScan__Build_Block b (getStartsLoop starts) (getEndsLoop ends)
            (length refs) (map (fmap getPhysReg) refs)

handledIntervalIds :: ScanState -> [(IntervalId, PhysReg)]
handledIntervalIds
    (ScanState (LinearScan__MLS__MS__Build_ScanStateDesc _ni _ _ _ _ _ hnd)) =
  map (second PhysReg) hnd
