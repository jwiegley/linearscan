{-# OPTIONS_GHC -Wall -Werror #-}

module LinearScan
    ( allocate
    , OpInfo(..)
    , AllocationInfo(..)
    ) where

import LinearScan.Main
    ( allocateRegisters
    , SSError(..)
    , OpInfo(..)
    , AllocationInfo(..)
    )

allocate :: [block] -> (block -> [op]) -> OpInfo op
         -> Either String [AllocationInfo op]
allocate [] _ _ = Left "No basic blocks were provided"
allocate blocks blockToOpList opInfo =
    case allocateRegisters blockToOpList opInfo blocks of
        Left x -> Left $ case x of
            ECurrentIsSingleton ->
                "Current interval is a singleton"
            ENoIntervalsToSplit ->
                "There are no intervals to split"
            EFailedToAllocateRegister ->
                "Failed to allocate register for current interval"
        Right z -> Right z
