{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module LinearScan
    ( allocate
    , VarInfo(..)
    , VarKind(..)
    , BlockInfo(..)
    , OpInfo(..)
    , OpData(..)
    ) where

import qualified LinearScan.Main as LS
import LinearScan.Main (PhysReg, VarId, VarKind(..), Allocation(..))

data VarInfo = VarInfo
    { varId       :: VarId
    , varKind     :: VarKind
    , regRequired :: Bool
    }

toVarInfo :: LS.VarInfo -> VarInfo
toVarInfo (LS.Build_VarInfo a b c) = VarInfo a b c

fromVarInfo :: VarInfo -> LS.VarInfo
fromVarInfo (VarInfo a b c) = LS.Build_VarInfo a b c

data BlockInfo opType blockType = BlockInfo
    { blockToOpList :: blockType -> [opType]
    }

data OpInfo opType = OpInfo
    { isLoopBegin :: opType -> Bool
    , isLoopEnd   :: opType -> Bool
    , isCall      :: opType -> Maybe [PhysReg]
    , hasRefs     :: opType -> Bool
    , varRefs     :: opType -> [VarInfo]
    , regRefs     :: opType -> [PhysReg]
    }

data OpData opType = OpData
    { baseOp  :: opType
    , opInfo  :: OpInfo opType
    , opId    :: Int
    , opAlloc :: [(VarId, Allocation)]
    }

instance Eq (OpData opType) where
    OpData _b1 _i1 d1 a1 == OpData _b2 _i2 d2 a2 = d1 == d2 && a1 == a2

instance Show (OpData opType) where
    show (OpData _b _i d a) = "<OpData#" ++ show d ++ " " ++ show a ++ ">"

allocate :: (Show op, Show (LS.OpData op))
         => [block] -> OpInfo op -> BlockInfo op block -> Either String [OpData op]
allocate [] _ _ = Left "No basic blocks were provided"
allocate blocks oinfo binfo =
    let oinfo' = LS.Build_OpInfo
            (isLoopBegin oinfo)
            (isLoopEnd oinfo)
            (isCall oinfo)
            (hasRefs oinfo)
            (map fromVarInfo . varRefs oinfo)
            (regRefs oinfo)
        binfo' = blockToOpList binfo in
    case LS.linearScan oinfo' binfo' blocks of
        Left x -> Left $ case x of
            LS.ECurrentIsSingleton ->
                "Current interval is a singleton"
            LS.ENoIntervalsToSplit ->
                "There are no intervals to split"
            LS.EFailedToAllocateRegister ->
                "Failed to allocate register for current interval"
        Right z -> Right $ map f z
  where
    f (LS.Build_OpData a (LS.Build_OpInfo b1 b2 b3 b4 b5 b6) c d) =
        OpData a (OpInfo b1 b2 b3 b4 (map toVarInfo . b5) b6) c d
