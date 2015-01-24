{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module LinearScan
    ( -- * Main entry point
      allocate
      -- * Blocks
    , BlockInfo(..)
      -- * Operations
    , OpInfo(..)
    , OpKind(..)
      -- * Variables
    , VarInfo(..)
    , VarKind(..)
    , VarAction(..)
    , LS.AllocInfo(..)
    , PhysReg
    ) where

import qualified LinearScan.Main as LS
import LinearScan.Main
    ( VarKind(..)
    , VarAction(..)
    , OpKind(..)
    , PhysReg
    )

-- | Each variable has associated allocation details, and a flag to indicate
--   whether it must be loaded into a register at its point of use.  Variables
--   are also distinguished by their kind, which allows for restricting the
--   scope of their lifetime.  For example, output variables are not needed in a
--   basic block until the first point of use, while the lifetime of input
--   variables extends until their final use.
data VarInfo v = VarInfo
    { varId       :: v -> Int
    , varKind     :: v -> VarKind
    , regRequired :: v -> Bool
    }

deriving instance Eq VarKind
deriving instance Show VarKind

fromVarInfo :: VarInfo v -> LS.VarInfo v
fromVarInfo (VarInfo a b c) = LS.Build_VarInfo a b c

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
data OpInfo o v a b = OpInfo
    { opKind      :: o a -> OpKind
    , opRefs      :: o a -> ([v], [PhysReg])
    , applyAllocs :: o a -> [(Int, LS.AllocInfo)] -> o b
    }

deriving instance Eq OpKind
deriving instance Show OpKind

deriving instance Eq VarAction
deriving instance Show VarAction

deriving instance Eq LS.AllocInfo
deriving instance Show LS.AllocInfo

fromOpInfo :: OpInfo o v a b -> LS.OpInfo (o a) (o b) v
fromOpInfo (OpInfo a b c) = LS.Build_OpInfo a b c

-- | From the point of view of this library, a basic block is nothing more
--   than an ordered sequence of operations.
data BlockInfo blk o a b = BlockInfo
    { blockOps    :: blk a -> [o a]
    , setBlockOps :: blk a -> [o b] -> blk b
    }

fromBlockInfo :: BlockInfo blk o a b -> LS.BlockInfo (blk a) (blk b) (o a) (o b)
fromBlockInfo (BlockInfo a b) = LS.Build_BlockInfo a b

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
allocate :: BlockInfo blk o a b -> OpInfo o v a b -> VarInfo v
         -> [blk a] -> Int -> Either String ([blk b], Int)
allocate _ _ _ [] _ = Left "No basic blocks were provided"
allocate (fromBlockInfo -> binfo) (fromOpInfo -> oinfo)
         (fromVarInfo -> vinfo) blocks offset =
    case LS.linearScan binfo oinfo vinfo blocks offset of
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
            LS.EFuelExhausted -> "Fuel was exhausted"
            LS.EUnexpectedNoMoreUnhandled ->
                "The unexpected happened: no more unhandled intervals"
        Right z -> Right z
