{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module LinearScan
    ( -- * Main entry point
      allocate
      -- * Blocks
    , BlockInfo(..)
    , defaultBlockInfo
      -- * Operations
    , OpInfo(..)
    , OpKind(..)
    , defaultOpInfo
      -- * Variables
    , VarInfo(..)
    , VarKind(..)
    , Allocation(..)
    , PhysReg
    , defaultVarInfo
    ) where

import qualified LinearScan.Main as LS
import LinearScan.Main
    ( VarKind(..)
    , Allocation(..)
    , OpKind(..)
    , PhysReg
    )

-- | Each variable has associated allocation details, and a flag to indicate
--   whether it must be loaded into a register at its point of use.  Variables
--   are also distinguished by their kind, which allows for restricting the
--   scope of their lifetime.  For example, output variables are not needed in a
--   basic block until the first point of use, while the lifetime of input
--   variables extends until their final use.
data VarInfo = VarInfo
    { varId       :: Int
    , varKind     :: VarKind
    , varAlloc    :: Allocation
    , regRequired :: Bool
    }
    deriving (Eq, Show)

deriving instance Eq VarKind
deriving instance Show VarKind

defaultVarInfo :: VarInfo
defaultVarInfo = VarInfo
    { varId       = 0
    , varKind     = Temp
    , varAlloc    = Unallocated
    , regRequired = False
    }

toVarInfo :: LS.VarInfo -> VarInfo
toVarInfo (LS.Build_VarInfo a b c d) = VarInfo a b c d

fromVarInfo :: VarInfo -> LS.VarInfo
fromVarInfo (VarInfo a b c d) = LS.Build_VarInfo a b c d

-- | Every operation may reference multiple variables and/or specific physical
--   registers.  If a physical register is referenced, then that register is
--   considered unavailable for allocation over the range of such references.
--
--   Certain operations have special significance as to how basic blocks are
--   organized, and the lifetime of allocations.  Thus, if an operation begins
--   or ends a loop, or represents a method call, it should be indicated using
--   the 'OpKind' field.  Indication of calls is necessary in order to save
--   and restore all registers around a call, but indication of loops is
--   optional, as it's merely avoids reloading of spilled variables inside
--   loop bodies.
data OpInfo = OpInfo
    { opId    :: Int
    , opMeta  :: Int
    , opKind  :: OpKind
    , varRefs :: [VarInfo]
    , regRefs :: [PhysReg]
    }
    deriving (Eq, Show)

deriving instance Eq OpKind
deriving instance Show OpKind

defaultOpInfo :: OpInfo
defaultOpInfo = OpInfo
    { opId    = 0
    , opMeta  = 0
    , opKind  = Normal
    , varRefs = []
    , regRefs = []
    }

toOpInfo :: LS.OpInfo -> OpInfo
toOpInfo (LS.Build_OpInfo a b c d e) = OpInfo a b c (map toVarInfo d) e

fromOpInfo :: OpInfo -> LS.OpInfo
fromOpInfo (OpInfo a b c d e) = LS.Build_OpInfo a b c (map fromVarInfo d) e

-- | From the point of view of this library, a basic block is nothing more
--   than an ordered sequence of operations.
data BlockInfo = BlockInfo
    { blockId  :: Int
    , blockOps :: [OpInfo]
    }
    deriving (Eq, Show)

defaultBlockInfo :: BlockInfo
defaultBlockInfo = BlockInfo
    { blockId  = 0
    , blockOps = []
    }

toBlockInfo :: LS.BlockInfo -> BlockInfo
toBlockInfo (LS.Build_BlockInfo a b) = BlockInfo a (map toOpInfo b)

fromBlockInfo :: BlockInfo -> LS.BlockInfo
fromBlockInfo (BlockInfo a b) = LS.Build_BlockInfo a (map fromOpInfo b)

-- | Transform a list of basic blocks containing variable references, into an
--   equivalent list where each reference is associated with a register
--   allocation.  Artificial save and restore instructions may also be
--   inserted into blocks to indicate spilling and reloading of variables.
--
--   In order to call this function, the caller must transform their own basic
--   block representation into a linear series of 'BlockInfo' structures.
--   Each of these structures may be associated with a unique identifier, to
--   assist with processing allocation info afterward.
--
--   If allocation is found to be impossible -- for example if there are
--   simply not enough registers -- a 'Left' value is returned, with a string
--   describing the error.
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
