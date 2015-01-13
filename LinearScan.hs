{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module LinearScan
    ( allocate
    , VarInfo(..)
    , VarKind(..)
    , Allocation(..)
    , OpInfo(..)
    , OpKind(..)
    , BlockInfo(..)
    ) where

import qualified LinearScan.Main as LS
import LinearScan.Main
    ( VarId
    , VarKind(..)
    , Allocation(..)
    , OpId
    , OpKind(..)
    , PhysReg
    , BlockId
    )

data VarInfo = VarInfo
    { varId       :: VarId
    , varKind     :: VarKind
    , varAlloc    :: Allocation
    , regRequired :: Bool
    }
    deriving (Eq, Show)

deriving instance Eq VarKind
deriving instance Show VarKind

toVarInfo :: LS.VarInfo -> VarInfo
toVarInfo (LS.Build_VarInfo a b c d) = VarInfo a b c d

fromVarInfo :: VarInfo -> LS.VarInfo
fromVarInfo (VarInfo a b c d) = LS.Build_VarInfo a b c d

data OpInfo = OpInfo
    { opId    :: OpId
    , opKind  :: OpKind
    , varRefs :: [VarInfo]
    , regRefs :: [PhysReg]
    }
    deriving (Eq, Show)

deriving instance Eq OpKind
deriving instance Show OpKind

toOpInfo :: LS.OpInfo -> OpInfo
toOpInfo (LS.Build_OpInfo a b c d) = OpInfo a b (map toVarInfo c) d

fromOpInfo :: OpInfo -> LS.OpInfo
fromOpInfo (OpInfo a b c d) = LS.Build_OpInfo a b (map fromVarInfo c) d

data BlockInfo = BlockInfo
    { blockId  :: BlockId
    , blockOps :: [OpInfo]
    }
    deriving (Eq, Show)

toBlockInfo :: LS.BlockInfo -> BlockInfo
toBlockInfo (LS.Build_BlockInfo a b) = BlockInfo a (map toOpInfo b)

fromBlockInfo :: BlockInfo -> LS.BlockInfo
fromBlockInfo (BlockInfo a b) = LS.Build_BlockInfo a (map fromOpInfo b)

allocate :: [BlockInfo] -> Either String [BlockInfo]
allocate [] = Left "No basic blocks were provided"
allocate blocks =
    case LS.linearScan (map fromBlockInfo blocks) of
        Left x -> Left $ case x of
            LS.ECannotSplitSingleton n ->
                "Current interval is a singleton (" ++ show n ++ ")"
            LS.ECannotSplitAssignedSingleton n ->
                "Current interval is an assigned singleton (" ++ show n ++ ")"
            LS.ENoIntervalsToSplit ->
                "There are no intervals to split"
            LS.ERegisterAlreadyAssigned n ->
                "Register is already assigned (" ++ show n ++ ")"
            LS.ERegisterAssignmentsOverlap n ->
                "Register assignments overlap (" ++ show n ++ ")"
        Right z -> Right (map toBlockInfo z)
