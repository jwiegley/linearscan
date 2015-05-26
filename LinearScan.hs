{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

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

import           Control.Applicative
import           Control.Monad.State
import           Data.IntMap (IntMap)
import qualified Data.IntMap as M
import           Data.IntSet (IntSet)
import qualified Data.IntSet as S
import qualified Data.List as L
import           Debug.Trace
import qualified LinearScan.Applicative as LS
import qualified LinearScan.Blocks as LS
import           LinearScan.Blocks as LS
import qualified LinearScan.IntMap as LS
import qualified LinearScan.IntSet as LS
import qualified LinearScan.Interval as LS
import qualified LinearScan.LiveSets as LS
import qualified LinearScan.Loops as LS
import qualified LinearScan.Main as LS
import qualified LinearScan.Monad as LS
import qualified LinearScan.Morph as LS
import qualified LinearScan.Range as LS
import qualified LinearScan.UsePos as LS
import qualified LinearScan.Utils as LS
import           LinearScan.Yoneda (Any)
import qualified Unsafe.Coerce as U

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
data OpInfo m op1 op2 = OpInfo
    { opKind      :: op1 -> OpKind
    , opRefs      :: op1 -> [LinearScan.VarInfo]
    , moveOp      :: PhysReg   -> PhysReg   -> m [op2]
    , swapOp      :: PhysReg   -> PhysReg   -> m [op2]
    , saveOp      :: PhysReg   -> Maybe Int -> m [op2]
    , restoreOp   :: Maybe Int -> PhysReg   -> m [op2]
    , applyAllocs :: op1 -> [(Int, PhysReg)] -> m [op2]
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

fromOpInfo :: Monad m
           => LinearScan.OpInfo m op1 op2 -> LS.OpInfo (m Any) op1 op2
fromOpInfo (OpInfo a b c d e f g h) =
    LS.Build_OpInfo a (map fromVarInfo . b)
        (\r1 r2 _ k -> liftM k (c r1 r2))
        (\r1 r2 _ k -> liftM k (d r1 r2))
        (\r1 r2 _ k -> liftM k (e r1 r2))
        (\r1 r2 _ k -> liftM k (f r1 r2))
        (\r1 r2 _ k -> liftM k (g r1 r2)) h

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
                         (handled sd) ++
        "Fixed:\n"
            ++ concatMap (\(reg, mi) ->
                           case mi of
                           Nothing -> ""
                           Just i -> "  " ++ showIntervalDesc reg i ++ "\n")
                         (zip [0..] (fixedIntervals sd))
      where
        showInterval i = showIntervalDesc i (intervals sd !! i)

        showReg Nothing = "<stack>"
        showReg (Just r) = "r" ++ show r

showIntervalDesc :: Int -> LS.IntervalDesc -> String
showIntervalDesc i (LS.Build_IntervalDesc iv ib ie rs) =
    "[" ++ show i ++ "]: " ++ " v" ++ show iv ++ " "
          ++ show ib ++ "-" ++ show ie ++ " =>" ++ showRanges rs

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

toScanStateDesc :: LS.ScanStateDescSet -> ScanStateDesc
toScanStateDesc (LS.Build_ScanStateDescSet a b c d e f g) =
    let rs = L.foldl' (\m (k, mx) -> case mx of
                            Nothing -> m
                            Just r -> M.insert k r m)
                 M.empty g in
    let xs = L.foldl' (\m (k, r) -> M.insert k r m) rs (e ++ f) in
    ScanStateDesc a b c d e f g xs

data LoopState = LoopState
    { activeBlocks     :: IntSet
    , visitedBlocks    :: IntSet
    , loopHeaderBlocks :: [BlockId]
    , loopEndBlocks    :: IntSet
    , forwardBranches  :: IntMap IntSet
    , backwardBranches :: IntMap IntSet
    , loopIndices      :: IntMap IntSet
    , loopDepths       :: IntMap (Int, Int)
    }

instance Show LoopState where
  show LoopState {..} = "LoopState = " ++
      "\n    activeBlocks     = " ++ show (S.toList activeBlocks) ++
      "\n    visitedBlocks    = " ++ show (S.toList visitedBlocks) ++
      "\n    loopHeaderBlocks = " ++ show loopHeaderBlocks ++
      "\n    loopEndBlocks    = " ++ show (S.toList loopEndBlocks) ++
      "\n    forwardBranches  = " ++ show (map (fmap S.toList) $
                                           M.toList forwardBranches) ++
      "\n    backwardBranches = " ++ show (map (fmap S.toList) $
                                           M.toList backwardBranches) ++
      "\n    loopIndices      = " ++ show (map (fmap S.toList) $
                                           M.toList loopIndices) ++
      "\n    loopDepths       = " ++ show (M.toList loopDepths)

toLoopState :: LS.LoopState -> LinearScan.LoopState
toLoopState (LS.Build_LoopState a b c d e f g h) =
    LoopState (S.fromList a) (S.fromList b) c (S.fromList d)
        (M.fromList (map (fmap S.fromList) e))
        (M.fromList (map (fmap S.fromList) f))
        (M.fromList (map (fmap S.fromList) g))
        (M.fromList h)

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
    -- let r _idx acc Nothing = acc
    --     r idx (bacc, eacc) (Just i) =
    --         let mreg = M.lookup idx allocs in
    --         (if LS.ibeg i == here
    --          then (idx, Left idx, mreg) : bacc
    --          else bacc,
    --          if LS.iend i == here
    --          then (idx, Left idx, mreg) : eacc
    --          else eacc) in
    let (begs, ends) =
            LS.vfoldl'_with_index (0 :: Int) k ([], []) (intervals sd) in
    -- let (begs', ends') =
    --         LS.vfoldl'_with_index (0 :: Int) r (begs, ends)
    --                               (fixedIntervals sd) in
    showOp1' (showOp1 oinfo) (pos*2+1) begs ends o
        ++ showOps1 oinfo sd (pos+1) os

-- | From the point of view of this library, a basic block is nothing more
--   than an ordered sequence of operations.
data BlockInfo m blk1 blk2 op1 op2 = BlockInfo
    { blockId           :: blk1 -> m Int
    , blockSuccessors   :: blk1 -> m [Int]
    , splitCriticalEdge :: blk1 -> blk1 -> m (blk1, blk1)
    , blockOps          :: blk1 -> ([op1], [op1], [op1])
    , setBlockOps       :: blk1 -> [op2] -> [op2] -> [op2] -> blk2
    }

showBlocks1 :: Monad m
            => LinearScan.BlockInfo m blk1 blk2 op1 op2
            -> LinearScan.OpInfo m op1 op2
            -> ScanStateDesc
            -> LS.IntMap LS.BlockLiveSets
            -> [blk1]
            -> m String
showBlocks1 binfo oinfo sd ls = go 0
  where
    go _ [] = return ""
    go pos (b:bs) = do
        bid <- LinearScan.blockId binfo b
        let (liveIn, liveOut) =
                 case LS.coq_IntMap_lookup bid ls of
                     Nothing -> (LS.emptyIntSet, LS.emptyIntSet)
                     Just s  -> (LS.blockLiveIn s, LS.blockLiveOut s)
        let allops blk =
                let (x, y, z) = LinearScan.blockOps binfo blk in
                x ++ y ++ z
        (showBlock1 allops bid pos liveIn liveOut (showOps1 oinfo sd) b ++)
            `liftM` go (pos + length (allops b)) bs

fromBlockInfo :: Monad m
              => LinearScan.BlockInfo m blk1 blk2 op1 op2
              -> LS.BlockInfo (m Any) blk1 blk2 op1 op2
fromBlockInfo (BlockInfo a b c d e) =
    LS.Build_BlockInfo
        (\r1 _ k -> liftM k (a r1))
        (\r1 _ k -> liftM k (b r1))
        (\r1 r2 _ k -> liftM k (c r1 r2))
        (\blk -> let (x, y, z) = d blk in ((x, y), z)) e

data Details m blk1 blk2 op1 op2 = Details
    { reason          :: Maybe ([LS.SSTrace], LS.FinalStage)
    , liveSets        :: [(Int, LS.BlockLiveSets)]
    , _inputBlocks    :: [blk1]
    , orderedBlocks   :: [blk1]
    , allocatedBlocks :: [blk2]
    , scanStatePre    :: Maybe ScanStateDesc
    , scanStatePost   :: Maybe ScanStateDesc
    , blockInfo       :: LinearScan.BlockInfo m blk1 blk2 op1 op2
    , opInfo          :: LinearScan.OpInfo m op1 op2
    , loopState       :: LoopState
    }

showDetails :: Monad m => Details m blk1 blk2 op1 op2 -> m String
showDetails err = do
    pre  <- showPreScanStateDesc (scanStatePre err)
    post <- showPostScanStateDesc (scanStatePost err)
    return $ "Reason: " ++ show (reason err) ++ "\n\n"
          ++ ">>> ScanState before allocation:\n"
          ++ pre ++ "\n"
          ++ ">>> ScanState after allocation:\n"
          ++ post ++ "\n"
          ++ ">>> " ++ show (loopState err) ++ "\n"
  where
    showPreScanStateDesc Nothing = return ""
    showPreScanStateDesc (Just sd) =
        liftM2 (++)
            (showBlocks1 (blockInfo err) (opInfo err) sd
                         (liveSets err) (orderedBlocks err))
            (return ("\n" ++ show sd))

    -- jww (2015-05-23): Show allocatedBlocks here?
    showPostScanStateDesc Nothing = return ""
    showPostScanStateDesc (Just sd) =
        liftM2 (++)
            (showBlocks1 (blockInfo err) (opInfo err) sd
                         (liveSets err) (orderedBlocks err))
            (return ("\n" ++ show sd))

deriving instance Show LS.SSTrace
deriving instance Show LS.FinalStage
deriving instance Show LS.BlockLiveSets

toDetails :: LS.Details blk1 blk2
          -> LinearScan.BlockInfo m blk1 blk2 op1 op2
          -> LinearScan.OpInfo m op1 op2
          -> Details m blk1 blk2 op1 op2
toDetails (LS.Build_Details a b c d e f g h) binfo oinfo =
    Details a b c d e (fmap toScanStateDesc f) (fmap toScanStateDesc g)
            binfo oinfo (toLoopState h)

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
allocate :: forall m blk1 blk2 op1 op2. (Functor m, Applicative m, Monad m)
         => Int        -- ^ Maximum number of registers to use
         -> LinearScan.BlockInfo m blk1 blk2 op1 op2
         -> LinearScan.OpInfo m op1 op2
         -> [blk1] -> m (Either [String] [blk2])
allocate 0 _ _ _  = return $ Left ["Cannot allocate with no registers"]
allocate _ _ _ [] = return $ Left ["No basic blocks were provided"]
allocate maxReg binfo oinfo blocks = do
    x <- LS.linearScan dict maxReg
       (fromBlockInfo binfo) (fromOpInfo oinfo) blocks $ \res ->
       toDetails res binfo oinfo
    let res' = U.unsafeCoerce (x :: Any) :: Details m blk1 blk2 op1 op2
    dets <- showDetails res'
    return $ case reason res' of
        Just (err, _) -> Left  $ tracer dets $ map reasonToStr err
        Nothing       -> Right $ allocatedBlocks res'
  where
    dict :: LS.Monad (m Any)
    dict = LS.Build_Monad
        (LS.Build_Applicative
         (\(_ :: ()) (_ :: ()) (f :: Any -> Any) x ->
           U.unsafeCoerce (fmap f (U.unsafeCoerce x :: m Any)))
         (\(_ :: ()) -> pure)
         (\(_ :: ()) (_ :: ()) f x ->
           U.unsafeCoerce (U.unsafeCoerce f <*> U.unsafeCoerce x :: m Any)))
        (\(_ :: ()) x ->
          U.unsafeCoerce (join (U.unsafeCoerce x :: m (m Any)) :: m Any))

    reasonToStr r = case r of
        LS.ESplitAssignedIntervalForReg reg ->
            "Splitting assigned interval for register " ++ show reg
        LS.ESplitActiveOrInactiveInterval b ->
            "Splitting " ++ (if b then "active" else "inactive") ++ " interval"
        LS.ESpillInterval ->
            "Spilling interval"
        LS.ESplitUnhandledInterval ->
            "Splitting unhandled interval"
        LS.EIntervalHasUsePosReqReg pos ->
            "Interval has use position requiring register at pos " ++ show pos
        LS.EIntervalBeginsAtSplitPosition ->
            "Interval begins at the split position"
        LS.EMoveUnhandledToActive reg ->
            "Allocating unhandled interval at register " ++ show reg
        LS.ESplitActiveIntervalForReg reg ->
            "Splitting active interval for register " ++ show reg
        LS.ESplitAnyInactiveIntervalForReg reg ->
            "Splitting any inactive interval for register " ++ show reg
        LS.ESpillCurrentInterval ->
            "Spilling current interval"
        LS.ESplitCurrentInterval pos ->
            "Spilling current interval before " ++ show pos
        LS.ETryAllocateFreeReg xid ->
            "Trying to allocate free registers for interval " ++ show xid
        LS.EAllocateBlockedReg xid ->
            "Trying to allocate a blocked register for interval " ++ show xid
        LS.ERemoveUnhandledInterval xid ->
            "Removing unhandled interval " ++ show xid

        LS.ECannotInsertUnhandled ->
            "Cannot insert interval onto unhandled list"
        LS.EIntervalBeginsBeforeUnhandled xid ->
            "Cannot spill interval " ++ show xid
                ++ " (begins before current position)"
        LS.ENoValidSplitPosition xid ->
            "No split position found for " ++ show xid
        LS.ECannotSplitSingleton xid ->
            "Interval " ++ show xid ++ " is a singleton"
        LS.ERegisterAlreadyAssigned reg ->
            "Register " ++ show reg ++ " already assigned"
        LS.ERegisterAssignmentsOverlap reg ->
            "Register assignments overlap at " ++ show reg
        LS.EUnexpectedNoMoreUnhandled ->
            "The unexpected happened: no more unhandled intervals"
        LS.ECannotSpillIfRegisterRequired i ->
            "Cannot spill interval " ++ show i
                ++ " with use positions requiring registers"
        LS.EFuelExhausted -> "Fuel was exhausted"
        LS.ENotYetImplemented n -> "Not Yet Implemented (#" ++ show n ++ ")"
