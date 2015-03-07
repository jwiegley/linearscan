{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module LinearScan
    ( -- * Main entry point
      allocate
      -- * Blocks
    , LinearScan.BlockInfo(..)
      -- * Operations
    , LinearScan.OpInfo(..)
    , OpKind(..)
      -- * Variables
    , VarId
    , LinearScan.VarInfo(..)
    , LS.VarKind(..)
    , PhysReg
    ) where

import           Control.Monad.State
import           Data.Functor.Identity
import           Data.IntMap (IntMap)
import qualified Data.IntMap as M
import qualified Data.List as L
import           Debug.Trace
import qualified LinearScan.Blocks as LS
import           LinearScan.Blocks as LS
import qualified LinearScan.IntMap as LS
import qualified LinearScan.Interval as LS
import qualified LinearScan.LiveSets as LS
import qualified LinearScan.Main as LS
import qualified LinearScan.Morph as LS
import qualified LinearScan.Range as LS
import qualified LinearScan.ScanState as LS
import qualified LinearScan.UsePos as LS
import qualified LinearScan.Utils as LS

-- | Each variable has associated allocation details, and a flag to indicate
--   whether it must be loaded into a register at its point of use.  Variables
--   are also distinguished by their kind, which allows for restricting the
--   scope of their lifetime.  For example, output variables are not needed in a
--   basic block until the first point of use, while the lifetime of input
--   variables extends until their final use.
data VarInfo = VarInfo
    { varId       :: Either PhysReg VarId
    , varKind     :: LS.VarKind
    , regRequired :: Bool
    }

deriving instance Eq LS.VarKind
deriving instance Show LS.VarKind

fromVarInfo :: LinearScan.VarInfo -> LS.VarInfo
fromVarInfo (VarInfo a b c) = LS.Build_VarInfo a b c

toVarInfo :: LS.VarInfo -> LinearScan.VarInfo
toVarInfo (LS.Build_VarInfo a b c) = VarInfo a b c

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
data OpInfo accType op1 op2 = OpInfo
    { opKind      :: op1 -> OpKind
    , opRefs      :: op1 -> [LinearScan.VarInfo]
    , moveOp      :: PhysReg   -> PhysReg   -> State accType [op2]
    , swapOp      :: PhysReg   -> PhysReg   -> State accType [op2]
    , saveOp      :: PhysReg   -> Maybe Int -> State accType [op2]
    , restoreOp   :: Maybe Int -> PhysReg   -> State accType [op2]
    , applyAllocs :: op1 -> [(Int, PhysReg)] -> [op2]
    , showOp1     :: op1 -> String
    }

showOp1' :: (op1 -> String)
         -> LS.OpId
           -- Interval Id, it's identity, and possible assigned reg
         -> [(Int, Either PhysReg LS.VarId, Maybe PhysReg)]
         -> [(Int, Either PhysReg LS.VarId, Maybe PhysReg)]
         -> op1
         -> String
showOp1' showop pos ins outs o =
    let showerv (Left r)  = "r" ++ show r
        showerv (Right v) = "v" ++ show v in
    let render Nothing = ""
        render (Just r) = "=r" ++ show r in
    let marker label (i, erv, reg) =
            "<" ++ label ++ " " ++ showerv erv ++
            (if i == either id id erv
             then ""
             else "[" ++ show i ++ "]") ++ render reg ++ ">\n" in
    concatMap (marker "End") outs ++
    concatMap (marker "Beg") ins ++
    show pos ++ ": " ++ showop o ++ "\n"

deriving instance Eq OpKind
deriving instance Show OpKind

fromOpInfo :: LinearScan.OpInfo accType op1 op2 -> LS.OpInfo accType op1 op2
fromOpInfo (OpInfo a b c d e f g h) =
    LS.Build_OpInfo a (map fromVarInfo . b)
        ((runState .) . c)
        ((runState .) . d)
        ((runState .) . e)
        ((runState .) . f) g h

toOpInfo :: LS.OpInfo accType op1 op2 -> LinearScan.OpInfo accType op1 op2
toOpInfo (LS.Build_OpInfo a b c d e f g h) =
    OpInfo a (map toVarInfo . b)
        ((StateT .) . fmap (fmap (fmap Identity)) c)
        ((StateT .) . fmap (fmap (fmap Identity)) d)
        ((StateT .) . fmap (fmap (fmap Identity)) e)
        ((StateT .) . fmap (fmap (fmap Identity)) f) g h

-- | From the point of view of this library, a basic block is nothing more
--   than an ordered sequence of operations.
data BlockInfo blk1 blk2 op1 op2 = BlockInfo
    { blockId         :: blk1 -> Int
    , blockSuccessors :: blk1 -> [Int]
    , blockOps        :: blk1 -> ([op1], [op1], [op1])
    , setBlockOps     :: blk1 -> [op2] -> [op2] -> [op2] -> blk2
    }

type IntervalId = Int

data ScanStateDesc = ScanStateDesc
    { _nextInterval  :: Int
    , intervals      :: [LS.IntervalDesc]
    , fixedIntervals :: [Maybe LS.IntervalDesc]
    , unhandled      :: [(IntervalId, Int)]
    , active         :: [(IntervalId, PhysReg)]
    , inactive       :: [(IntervalId, PhysReg)]
    , handled        :: [(IntervalId, Maybe PhysReg)]
    , allocations    :: IntMap PhysReg
    }

deriving instance Show LS.IntervalDesc
deriving instance Show LS.IntervalKind
deriving instance Show LS.RangeDesc
deriving instance Show LS.UsePos

instance Show ScanStateDesc where
    show sd =
        "Unhandled:\n"
            ++ concatMap (\(i, _) -> "  " ++ showInterval i ++ "\n")
                         (unhandled sd) ++
        "Active:\n"
            ++ concatMap (\(i, r) ->
                           "  r" ++ show r ++ showInterval i ++ "\n")
                         (active sd) ++
        "Inactive:\n"
            ++ concatMap (\(i, r) ->
                           "  r" ++ show r ++ showInterval i ++ "\n")
                         (inactive sd) ++
        "Handled:\n"
            ++ concatMap (\(i, r) ->
                           "  " ++ showReg r ++ showInterval i ++ "\n")
                         (handled sd)
      where
        showInterval i = showIntervalDesc i (intervals sd !! i)

        showReg Nothing = "<stack>"
        showReg (Just r) = "r" ++ show r

showIntervalDesc :: Int -> LS.IntervalDesc -> String
showIntervalDesc i (LS.Build_IntervalDesc iv ib ie ik rs) =
    "[" ++ show i ++ "]: " ++ showKind ik ++ " v" ++ show iv ++ " "
          ++ show ib ++ "-" ++ show ie ++ " =>" ++ showRanges rs

showKind :: LS.IntervalKind -> String
showKind LS.Whole     = "W"
showKind LS.LeftMost  = "L"
showKind LS.Middle    = "M"
showKind LS.RightMost = "R"

showRanges :: [LS.RangeDesc] -> String
showRanges [] = ""
showRanges (LS.Build_RangeDesc rb re us:rs) =
    " " ++ show rb ++ "-" ++ show re
      ++ (case us of
               [] -> ""
               _  -> " [" ++ showUsePositions us ++ "]")
      ++ showRanges rs

showUsePositions :: [LS.UsePos] -> String
showUsePositions [] = ""
showUsePositions [u] = go u
  where
    go (LS.Build_UsePos n req _v) = show n ++ (if req then "" else "?")
showUsePositions (u:us) = go u ++ " " ++ showUsePositions us
  where
    go (LS.Build_UsePos n req _v) = show n ++ (if req then "" else "?")

toScanStateDesc :: LS.ScanStateDesc -> ScanStateDesc
toScanStateDesc (LS.Build_ScanStateDesc a b c d e f g) =
    let rs = L.foldl' (\m (k, mx) -> case mx of
                            Nothing -> m
                            Just r -> M.insert k r m)
                 M.empty g in
    let xs = L.foldl' (\m (k, r) -> M.insert k r m) rs (e ++ f) in
    ScanStateDesc a b c d e f g xs

tracer :: String -> a -> a
tracer x = Debug.Trace.trace ("====================\n" ++ x)

showBlock1 :: (blk1 -> [op1])
           -> LS.BlockId
           -> LS.OpId
           -> [Int]
           -> [Int]
           -> (LS.OpId -> [op1] -> String)
           -> blk1
           -> String
showBlock1 getops bid pos liveIns liveOuts showops b =
    "\nBlock " ++ show bid ++
    " => IN:" ++ show liveIns ++ " OUT:" ++ show liveOuts ++ "\n" ++
    showops pos (getops b)

showOps1 :: LinearScan.OpInfo accType op1 op2 -> ScanStateDesc -> Int -> [op1]
         -> String
showOps1 _ _ _ [] = ""
showOps1 oinfo sd pos (o:os) =
    let here = pos*2+1 in
    let allocs = allocations sd in
    let k idx (bacc, eacc) i =
            let mreg = M.lookup idx allocs in
            (if LS.ibeg i == here
             then (idx, Right (LS.ivar i), mreg) : bacc
             else bacc,
             if LS.iend i == here
             then (idx, Right (LS.ivar i), mreg) : eacc
             else eacc) in
    let r _idx acc Nothing = acc
        r idx (bacc, eacc) (Just i) =
            let mreg = M.lookup idx allocs in
            (if LS.ibeg i == here
             then (idx, Left idx, mreg) : bacc
             else bacc,
             if LS.iend i == here
             then (idx, Left idx, mreg) : eacc
             else eacc) in
    let (begs, ends) =
            LS.vfoldl'_with_index (0 :: Int) k ([], []) (intervals sd) in
    let (begs', ends') =
            LS.vfoldl'_with_index (0 :: Int) r (begs, ends)
                                  (fixedIntervals sd) in
    showOp1' (showOp1 oinfo) (pos*2+1) begs' ends' o
        ++ showOps1 oinfo sd (pos+1) os

showBlocks1 :: LinearScan.BlockInfo blk1 blk2 op1 op2
            -> LinearScan.OpInfo accType op1 op2
            -> ScanStateDesc
            -> LS.IntMap LS.BlockLiveSets
            -> [blk1]
            -> String
showBlocks1 binfo oinfo sd ls = go 0
  where
    go _ [] = ""
    go pos (b:bs) =
        let bid = LinearScan.blockId binfo b in
        let (liveIn, liveOut) =
                 case LS.coq_IntMap_lookup bid ls of
                     Nothing -> (LS.emptyIntSet, LS.emptyIntSet)
                     Just s  -> (LS.blockLiveIn s, LS.blockLiveOut s) in
        let allops blk = let (x, y, z) = LinearScan.blockOps binfo blk in
                         x ++ y ++ z in
        showBlock1 allops bid pos liveIn liveOut (showOps1 oinfo sd) b
            ++ go (pos + length (allops b)) bs

fromBlockInfo :: LinearScan.BlockInfo blk1 blk2 op1 op2
              -> LS.BlockInfo blk1 blk2 op1 op2
fromBlockInfo (BlockInfo a b c d) =
    LS.Build_BlockInfo a b (\blk -> let (x, y, z) = c blk in ((x, y), z)) d

toBlockInfo :: LS.BlockInfo blk1 blk2 op1 op2
            -> LinearScan.BlockInfo blk1 blk2 op1 op2
toBlockInfo (LS.Build_BlockInfo a b c d) =
    BlockInfo a b (\blk -> let ((x, y), z) = c blk in (x, y, z)) d

data Details blk1 blk2 op1 op2 accType = Details
    { reason          :: Maybe (LS.SSError, LS.FinalStage)
    , liveSets        :: [(Int, LS.BlockLiveSets)]
    , inputBlocks     :: [blk1]
    , allocatedBlocks :: [blk2]
    , accumulator     :: accType
    , scanStatePre    :: Maybe ScanStateDesc
    , scanStatePost   :: Maybe ScanStateDesc
    , blockInfo       :: LinearScan.BlockInfo blk1 blk2 op1 op2
    , opInfo          :: LinearScan.OpInfo accType op1 op2
    }

instance Show (Details blk1 blk2 op1 op2 accType) where
    show err = show (reason err) ++ "\n"
               ++ showScanStateDesc (scanStatePre err) ++ "\n\n"
               ++ showScanStateDesc (scanStatePost err)
      where
        showScanStateDesc Nothing = ""
        showScanStateDesc (Just sd) =
            showBlocks1 (blockInfo err) (opInfo err) sd
                        (liveSets err) (inputBlocks err)
                ++ "\n" ++ show sd

deriving instance Show LS.SSError
deriving instance Show LS.FinalStage
deriving instance Show LS.BlockLiveSets

toDetails :: LS.Details blk1 blk2 op1 op2 accType
               -> Details blk1 blk2 op1 op2 accType
toDetails (LS.Build_Details a b c d e f g h i) =
    Details a b c d e (fmap toScanStateDesc f) (fmap toScanStateDesc g)
                 (toBlockInfo h) (toOpInfo i)

-- | Transform a list of basic blocks containing variable references, into an
--   equivalent list where each reference is associated with a register
--   allocation.  Artificial save and restore instructions may also be
--   inserted into blocks to indicate spilling and reloading of variables.
--
--   In order to call this function, the caller must provide records that
--   allow viewing and mutating of the original program graph.
--
--   If allocation is found to be impossible -- for example if there are
--   simply not enough registers -- a 'Left' value is returned, with a string
--   describing the error.
allocate :: Int                  -- ^ Maximum number of registers to use
         -> LinearScan.BlockInfo blk1 blk2 op1 op2
         -> LinearScan.OpInfo accType op1 op2
         -> [blk1]
         -> State accType (Either String [blk2])
allocate 0 _ _ _  = return $ Left "Cannot allocate with no registers"
allocate _ _ _ [] = return $ Left "No basic blocks were provided"
allocate maxReg (fromBlockInfo -> binfo) (fromOpInfo -> oinfo) blocks = do
    res <- gets (LS.linearScan maxReg binfo oinfo blocks)
    let res' = toDetails res
    put $ accumulator res'
    case reason res' of
        Just (err, _) -> reportError res' err
        Nothing -> tracer (show res') (return (Right (allocatedBlocks res')))
  where
    reportError res err =
        return $ Left $ tracer (show res) (reasonToStr err)

    reasonToStr r = case r of
        LS.ERegistersExhausted _ ->
            "No registers available for allocation"
        LS.ENoValidSplitPosition _ ->
            "No split position could be found"
        LS.ECannotSplitSingleton1 n ->
            "Current interval is a singleton (err#1) (" ++ show n ++ ")"
        LS.ECannotSplitSingleton2 n ->
            "Current interval is a singleton (err#2) (" ++ show n ++ ")"
        LS.ECannotSplitSingleton3 n ->
            "Current interval is a singleton (err#3) (" ++ show n ++ ")"
        LS.ENoIntervalsToSplit ->
            "There are no intervals to split"
        LS.ERegisterAlreadyAssigned n ->
            "Register is already assigned (" ++ show n ++ ")"
        LS.ERegisterAssignmentsOverlap n ->
            "Register assignments overlap (" ++ show n ++ ")"
        LS.EFuelExhausted -> "Fuel was exhausted"
        LS.EUnexpectedNoMoreUnhandled ->
            "The unexpected happened: no more unhandled intervals"
