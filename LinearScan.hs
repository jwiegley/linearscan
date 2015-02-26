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
    , VarId
    , VarInfo(..)
    , VarKind(..)
    , PhysReg
    ) where

import           Control.Monad.State
import           Data.Functor.Identity
import           Debug.Trace
import qualified LinearScan.Blocks as LS
import qualified LinearScan.IntMap as LS
import qualified LinearScan.Interval as LS
import qualified LinearScan.LiveSets as LS
import qualified LinearScan.Main as LS
import qualified LinearScan.Morph as LS
import qualified LinearScan.Range as LS
import qualified LinearScan.ScanState as LS
import qualified LinearScan.UsePos as LS
import qualified LinearScan.Utils as LS

import           LinearScan.Blocks
    ( VarId
    , VarKind(..)
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
    { varId       :: Either PhysReg VarId
    , varKind     :: VarKind
    , regRequired :: Bool
    }

deriving instance Eq VarKind
-- deriving instance Show VarKind

fromVarInfo :: VarInfo -> LS.VarInfo
fromVarInfo (VarInfo a b c) = LS.Build_VarInfo a b c

toVarInfo :: LS.VarInfo -> VarInfo
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
    , opRefs      :: op1 -> [VarInfo]
    , moveOp      :: PhysReg   -> PhysReg   -> State accType [op2]
    , swapOp      :: PhysReg   -> PhysReg   -> State accType [op2]
    , saveOp      :: PhysReg   -> Maybe Int -> State accType [op2]
    , restoreOp   :: Maybe Int -> PhysReg   -> State accType [op2]
    , applyAllocs :: op1 -> [(Int, PhysReg)] -> [op2]
    , showOp1     :: op1 -> String
    }

showOp1' :: (op1 -> String)
         -> LS.OpId
         -> [(Int, Either PhysReg LS.VarId)]
         -> [(Int, Either PhysReg LS.VarId)]
         -> [(Int, Either PhysReg LS.VarId)]
         -> op1
         -> String
showOp1' showop pos ins mids outs o =
    let showerv (Left r)  = "r" ++ show r
        showerv (Right v) = "v" ++ show v in
    let marker label (i, erv) =
            "<" ++ label ++ " " ++ showerv erv ++
            (if i == either id id erv
             then ""
             else "[" ++ show i ++ "]") ++ ">\n" in
    concatMap (marker "End") mids ++
    concatMap (marker "Beg") ins ++
    show pos ++ ": " ++ showop o ++ "\n" ++
    concatMap (marker "End") outs

deriving instance Eq OpKind
deriving instance Show OpKind

fromOpInfo :: OpInfo accType op1 op2 -> LS.OpInfo accType op1 op2
fromOpInfo (OpInfo a b c d e f g h) =
    LS.Build_OpInfo a (map fromVarInfo . b)
        ((runState .) . c)
        ((runState .) . d)
        ((runState .) . e)
        ((runState .) . f) g h

toOpInfo :: LS.OpInfo accType op1 op2 -> OpInfo accType op1 op2
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
    , handled        :: [(IntervalId, PhysReg)]
    }

deriving instance Show LS.IntervalDesc
deriving instance Show LS.IntervalKind
deriving instance Show LS.RangeDesc
deriving instance Show LS.UsePos

instance Show ScanStateDesc where
    show sd =
        -- "Intervals:\n"       ++
        --     concatMap (\i -> "  " ++ showInterval i ++ "\n")
        --               [0..nextInterval sd] ++
        -- "Fixed Intervals:\n" ++
        "Unhandled:\n"
            ++ concatMap (\(i, _) -> "  " ++ showInterval i ++ "\n")
                         (unhandled sd) ++
        "Active:\n"
            ++ concatMap (\(i, r) -> "  r" ++ show r ++ showInterval i ++ "\n")
                         (active sd) ++
        "Inactive:\n"
            ++ concatMap (\(i, r) -> "  r" ++ show r ++ showInterval i ++ "\n")
                         (inactive sd) ++
        "Handled:\n"
            ++ concatMap (\(i, r) -> "  r" ++ show r ++ showInterval i ++ "\n")
                         (handled sd)
      where
        showInterval i = showIntervalDesc i (intervals sd !! i)

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
    go (LS.Build_UsePos n req) = show n ++ (if req then "" else "?")
showUsePositions (u:us) = go u ++ " " ++ showUsePositions us
  where
    go (LS.Build_UsePos n req) = show n ++ (if req then "" else "?")

toScanStateDesc :: LS.ScanStateDesc -> ScanStateDesc
toScanStateDesc (LS.Build_ScanStateDesc a b c d e f g) =
    ScanStateDesc a b c d e f g

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

showOps1 :: OpInfo accType op1 op2 -> ScanStateDesc -> Int -> [op1] -> String
showOps1 _ _ _ [] = ""
showOps1 oinfo sd pos (o:os) =
    let refs = opRefs oinfo o in
    let handleInts ints p v vid f =
            let k idx acc i =
                    if p v vid i
                    then (idx, f vid) : acc
                    else acc in
            LS.vfoldl'_with_index (0 :: Int) k [] ints in
    let collectVarRefs p = flip concatMap refs $ \v ->
          let evid = varId v in
          case evid of
              Left _ -> []
              Right vid -> handleInts (intervals sd) p v vid Right in
    let collectRegRefs p = flip concatMap refs $ \v ->
          let evid = varId v in
          case evid of
              Right _ -> []
              Left vid -> handleInts (fixedIntervals sd) p v vid Left in
    let startingP _ vid i =
            (LS.ivar i == vid) && (LS.ibeg i == pos*2+1) in
    let endingBeforeP v vid i   =
            (LS.ivar i == vid) &&
            (varKind v == Input) &&
            (LS.iend i == pos*2+1) in
    let endingAfterP v vid i   =
            (LS.ivar i == vid) &&
            (varKind v /= Input) &&
            (LS.iend i == pos*2+1) in
    let checkReg _ _ _ Nothing = False
        checkReg p v vid (Just i) = p v vid i in
    let startingAtPos   = collectVarRefs startingP ++
                          collectRegRefs (checkReg startingP) in
    let endingBeforePos = collectVarRefs endingBeforeP ++
                          collectRegRefs (checkReg endingBeforeP) in
    let endingAtPos     = collectVarRefs endingAfterP ++
                          collectRegRefs (checkReg endingAfterP) in
    showOp1' (showOp1 oinfo) (pos*2+1)
             startingAtPos endingBeforePos endingAtPos o
        ++ showOps1 oinfo sd (pos+1) os

showBlocks1 :: BlockInfo blk1 blk2 op1 op2
            -> OpInfo accType op1 op2
            -> ScanStateDesc
            -> LS.IntMap LS.BlockLiveSets
            -> [blk1]
            -> String
showBlocks1 binfo oinfo sd ls = go 0
  where
    go _ [] = ""
    go pos (b:bs) =
        let bid = blockId binfo b in
        let (liveIn, liveOut) =
                 case LS.coq_IntMap_lookup bid ls of
                     Nothing -> (LS.emptyIntSet, LS.emptyIntSet)
                     Just s  -> (LS.blockLiveIn s, LS.blockLiveOut s) in
        let allBlockOps blk = let (x, y, z) = blockOps binfo blk in
                              x ++ y ++ z in
        showBlock1 allBlockOps bid pos liveIn liveOut (showOps1 oinfo sd) b
            ++ go (pos + length (allBlockOps b)) bs

fromBlockInfo :: BlockInfo blk1 blk2 op1 op2 -> LS.BlockInfo blk1 blk2 op1 op2
fromBlockInfo (BlockInfo a b c d) =
    LS.Build_BlockInfo a b (\blk -> let (x, y, z) = c blk in ((x, y), z)) d

toBlockInfo :: LS.BlockInfo blk1 blk2 op1 op2 -> BlockInfo blk1 blk2 op1 op2
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
    , blockInfo       :: BlockInfo blk1 blk2 op1 op2
    , opInfo          :: OpInfo accType op1 op2
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
         -> BlockInfo blk1 blk2 op1 op2
         -> OpInfo accType op1 op2
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
        LS.ECannotSplitSingleton2 n int splitPos ->
            "Current interval is a singleton (#2) @" ++ show splitPos
                ++ " : " ++ showIntervalDesc n int
        LS.ECannotSplitSingleton3 n ->
            "Current interval is a singleton (err#3) (" ++ show n ++ ")"
        LS.ECannotSplitSingleton4 n ->
            "Current interval is a singleton (err#4) (" ++ show n ++ ")"
        LS.ECannotSplitSingleton5 n ->
            "Current interval is a singleton (err#5) (" ++ show n ++ ")"
        LS.ECannotSplitSingleton6 n ->
            "Current interval is a singleton (err#6) (" ++ show n ++ ")"
        LS.ECannotSplitSingleton7 n ->
            "Current interval is a singleton (err#7) (" ++ show n ++ ")"
        LS.ECannotSplitSingleton8 n ->
            "Current interval is a singleton (err#8) (" ++ show n ++ ")"
        LS.ENoIntervalsToSplit ->
            "There are no intervals to split"
        LS.ERegisterAlreadyAssigned n ->
            "Register is already assigned (" ++ show n ++ ")"
        LS.ERegisterAssignmentsOverlap n ->
            "Register assignments overlap (" ++ show n ++ ")"
        LS.EFuelExhausted -> "Fuel was exhausted"
        LS.EUnexpectedNoMoreUnhandled ->
            "The unexpected happened: no more unhandled intervals"
