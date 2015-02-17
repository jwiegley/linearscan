{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Hoopl where

import           Compiler.Hoopl as Hoopl hiding ((<*>))
import           Control.Applicative
import           Control.Monad.Trans.State (State, get, put)
import qualified Data.Map as M
import           Data.Monoid
import           LinearScan

class HooplNode n1
      => NodeAlloc s n1 n2 | n1 -> n2, n2 -> n1, n1 -> s, n2 -> s where
    isCall   :: n1 O O -> Bool
    isBranch :: n1 O C -> Bool

    getReferences :: n1 e x -> [VarInfo]
    setRegisters  :: [(Int, PhysReg)] -> n1 e x -> n2 e x

    mkMoveOps    :: PhysReg     -> PhysReg     -> State s [n2 O O]
    mkSwapOps    :: PhysReg     -> PhysReg     -> State s [n2 O O]
    mkSaveOps    :: PhysReg     -> Maybe VarId -> State s [n2 O O]
    mkRestoreOps :: Maybe VarId -> PhysReg     -> State s [n2 O O]

data NodeV n = NodeCO { getNodeCO :: n C O }
             | NodeOO { getNodeOO :: n O O }
             | NodeOC { getNodeOC :: n O C }

blockInfo :: NonLocal n1
          => (Label -> Int)
          -> BlockInfo (Block n1 C C) (Block n2 C C) (NodeV n1) (NodeV n2)
blockInfo getBlockId = BlockInfo
    { blockId = getBlockId . entryLabel

    , blockSuccessors = Prelude.map getBlockId . successors

    , blockOps = \(BlockCC a b z) ->
        ([NodeCO a], Prelude.map NodeOO (blockToList b), [NodeOC z])

    , setBlockOps = \_ [a] b [z] ->
        BlockCC
            (getNodeCO a)
            (blockFromList (Prelude.map getNodeOO b))
            (getNodeOC z)
    }

opInfo :: forall s n1 n2. NodeAlloc s n1 n2 => OpInfo s (NodeV n1) (NodeV n2)
opInfo = OpInfo
    { opKind = \node -> case node of
           NodeOO n | isCall n  -> IsCall
                    | otherwise -> IsNormal
           NodeOC n | isBranch n -> IsBranch
                    | otherwise  -> IsNormal
           _ -> IsNormal

    , opRefs = \node -> case node of
           NodeCO n -> getReferences n
           NodeOO n -> getReferences n
           NodeOC n -> getReferences n

    , moveOp    = \x y -> fmap NodeOO <$> mkMoveOps x y
    , swapOp    = \x y -> fmap NodeOO <$> mkSwapOps x y
    , saveOp    = \x y -> fmap NodeOO <$> mkSaveOps x y
    , restoreOp = \x y -> fmap NodeOO <$> mkRestoreOps x y

    , applyAllocs = \node m -> case node of
           NodeCO n -> [NodeCO (setRegisters m n)]
           NodeOO n -> [NodeOO (setRegisters m n)]
           NodeOC n -> [NodeOC (setRegisters m n)]
    }

data SpillStack = SpillStack
    { stackPtr      :: Int
    , stackSlotSize :: Int
    , stackSlots    :: M.Map (Maybe Int) Int
    }
    deriving (Eq, Show)

newSpillStack :: Int -> Int -> SpillStack
newSpillStack offset slotSize = SpillStack
    { stackPtr      = offset
    , stackSlotSize = slotSize
    , stackSlots    = mempty
    }

getStackSlot :: Maybe VarId -> State SpillStack Int
getStackSlot vid = do
    stack <- get
    case M.lookup vid (stackSlots stack) of
        Just off -> return off
        Nothing -> do
            let off = stackPtr stack
            put stack
                 { stackPtr   = off + stackSlotSize stack
                 , stackSlots =
                     M.insert vid off (stackSlots stack)
                 }
            return off
