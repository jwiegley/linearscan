{-# OPTIONS_GHC -Wall -Werror #-}

module LinearScan
    ( allocate
    , OpListFromBlock
    , OperationInfo
    , AllocationInfo
    ) where

import LinearScan.Main

allocate :: [block] -> OpListFromBlock op block
         -> Either String [AllocationInfo op]
allocate [] _ = Left "No basic blocks were provided"
allocate blocks getInfo =
    case allocateRegisters (concatMap getInfo blocks) of
        Left x -> Left $ case x of
            ECurrentIsSingleton ->
                "Current interval is a singleton"
            ENoIntervalsToSplit ->
                "There are no intervals to split"
            EFailedToAllocateRegister ->
                "Failed to allocate register for current interval"
            ESpillingNotYetImplemented ->
                "Spilling is not yet implemented!"
        Right z -> Right z
