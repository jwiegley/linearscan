{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

module LinearScan
    ( -- * Main entry point
      allocate
      -- * Blocks
    , LinearScan.BlockInfo(..)
    , LS.UseVerifier(..)
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
import           Data.Maybe (fromMaybe)
import           Debug.Trace
import qualified Hask.Utils as LS
import qualified LinearScan.Applicative as Coq
import           LinearScan.Blocks
import qualified LinearScan.Blocks as LS
import qualified LinearScan.Functor as Coq
import qualified LinearScan.Functor as Functor
import qualified LinearScan.Interval as LS
import qualified LinearScan.LiveSets as LS
import qualified LinearScan.Loops as LS
import qualified LinearScan.Main as LS
import qualified LinearScan.Monad as Coq
import qualified LinearScan.Range as LS
import qualified LinearScan.Resolve as LS
import qualified LinearScan.Trace as LS
import qualified LinearScan.UsePos as LS
import qualified LinearScan.Verify as LS
import qualified Unsafe.Coerce as U

type Any = Functor.Any

coqFunctor :: forall f. Functor f => Coq.Functor (f Any)
coqFunctor _ _ g x =
    U.unsafeCoerce (fmap g (U.unsafeCoerce x :: f Any))

coqApplicative :: forall f. Applicative f => Coq.Applicative (f Any)
coqApplicative = Coq.Build_Applicative coqFunctor (const pure)
    (\_ _ g x ->
      U.unsafeCoerce (U.unsafeCoerce g <*> U.unsafeCoerce x :: f Any))

coqMonad :: forall m. (Monad m, Applicative m) => Coq.Monad (m Any)
coqMonad = Coq.Build_Monad coqApplicative
    (\_ x -> U.unsafeCoerce (join (U.unsafeCoerce x :: m (m Any)) :: m Any))

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
-- deriving instance Show LS.VarKind

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
    , moveOp      :: PhysReg  -> LS.VarId -> PhysReg   -> m [op2]
    , swapOp      :: PhysReg  -> LS.VarId -> PhysReg   -> LS.VarId -> m [op2]
    , saveOp      :: PhysReg  -> LS.VarId -> m [op2]
    , restoreOp   :: LS.VarId -> PhysReg   -> m [op2]
    , applyAllocs :: op1 -> [(LS.VarId, PhysReg)] -> m [op2]
    , showOp1     :: op1 -> String
    }

showOp1' :: (op1 -> String)
         -> LS.OpId
           -- Interval Id, it's identity, and possible assigned reg
         -> [(Int, Either PhysReg LS.VarId, Maybe PhysReg)]
         -> [(Int, Either PhysReg LS.VarId, Maybe PhysReg)]
         -> [LS.ResolvingMoveSet]
         -> op1
         -> String
showOp1' showop pos ins outs rms o =
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
    show pos ++ ": " ++ showop o ++ "\n" ++
    concatMap (\x -> show x ++ "\n") rms

deriving instance Eq OpKind
deriving instance Show OpKind

fromOpInfo :: Monad m
           => LinearScan.OpInfo m op1 op2 -> LS.OpInfo (m Any) op1 op2
fromOpInfo (OpInfo a b c d e f g h) =
    LS.Build_OpInfo a (map fromVarInfo . b)
        (\r1 r2 -> U.unsafeCoerce (c r1 r2))
        (\r1 r2 -> U.unsafeCoerce (d r1 r2))
        (\r1 r2 -> U.unsafeCoerce (e r1 r2))
        (\r1 r2 -> U.unsafeCoerce (f r1 r2))
        (\r1 r2 -> U.unsafeCoerce (g r1 r2)) h

data ScanStateDesc = ScanStateDesc
    { _nextInterval  :: Int
    , intervals      :: [LS.IntervalDesc]
    , fixedIntervals :: [Maybe LS.IntervalDesc]
    , unhandled      :: IntMap Int
    , active         :: IntMap PhysReg
    , inactive       :: IntMap PhysReg
    , handled        :: IntMap (Maybe PhysReg)
    , allocations    :: IntMap PhysReg
    }

-- deriving instance Show LS.IntervalDesc
-- deriving instance Show LS.RangeDesc
-- deriving instance Show LS.UsePos

instance Show ScanStateDesc where
    show sd =
        "Unhandled:\n"
            ++ concatMap (\(i, _) -> "  " ++ showInterval i ++ "\n")
                         (M.toList (unhandled sd)) ++
        "Active:\n"
            ++ concatMap (\(i, r) ->
                           "  r" ++ show r ++ showInterval i ++ "\n")
                         (M.toList (active sd)) ++
        "Inactive:\n"
            ++ concatMap (\(i, r) ->
                           "  r" ++ show r ++ showInterval i ++ "\n")
                         (M.toList (inactive sd)) ++
        "Handled:\n"
            ++ concatMap (\(i, r) ->
                           "  " ++ showReg r ++ showInterval i ++ "\n")
                         (M.toList (handled sd)) ++
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
    ScanStateDesc a b c
        (M.fromList d) (M.fromList e) (M.fromList f) (M.fromList g) xs

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
           -> IntSet
           -> IntSet
           -> (LS.OpId -> [op1] -> String)
           -> blk1
           -> String
showBlock1 getops bid pos liveIns liveOuts showops b =
    "\nBlock " ++ show bid ++
    " => IN:" ++ show liveIns ++ " OUT:" ++ show liveOuts ++ "\n" ++
    showops pos (getops b)

showOps1 :: LinearScan.OpInfo accType op1 op2
         -> ScanStateDesc
         -> IntMap [LS.ResolvingMoveSet]
         -> Int
         -> [op1]
         -> String
showOps1 _ _ _ _ [] = ""
showOps1 oinfo sd rms pos (o:os) =
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
            LS.vfoldl'_with_index 0 k ([], []) (intervals sd) in
    -- let (begs', ends') =
    --         LS.vfoldl'_with_index (0 :: Int) r (begs, ends)
    --                               (fixedIntervals sd) in
    showOp1' (showOp1 oinfo) (pos*2+1) begs ends
        (fromMaybe [] (M.lookup (pos*2+1) rms)) o
        ++ showOps1 oinfo sd rms (pos+1) os

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
            -> IntMap LS.BlockLiveSets
            -> IntMap [LS.ResolvingMoveSet]
            -> [blk1]
            -> m String
showBlocks1 binfo oinfo sd ls rms = go 0
  where
    go _ [] = return ""
    go pos (b:bs) = do
        bid <- LinearScan.blockId binfo b
        let (liveIn, liveOut) =
                 case M.lookup bid ls of
                     Nothing -> (S.empty, S.empty)
                     Just s  -> (S.fromList (LS.blockLiveIn s),
                                 S.fromList (LS.blockLiveOut s))
        let allops blk =
                let (x, y, z) = LinearScan.blockOps binfo blk in
                x ++ y ++ z
        (showBlock1 allops bid pos liveIn liveOut (showOps1 oinfo sd rms) b ++)
            `liftM` go (pos + length (allops b)) bs

fromBlockInfo :: Monad m
              => LinearScan.BlockInfo m blk1 blk2 op1 op2
              -> LS.BlockInfo (m Any) blk1 blk2 op1 op2
fromBlockInfo (BlockInfo a b c d e) =
    LS.Build_BlockInfo
        (\r1 -> U.unsafeCoerce (a r1))
        (\r1 -> U.unsafeCoerce (b r1))
        (\r1 r2 -> U.unsafeCoerce (c r1 r2))
        (\blk -> let (x, y, z) = d blk in ((x, y), z)) e

data Details m blk1 blk2 op1 op2 = Details
    { reason          :: Maybe ([LS.SSTrace], LS.FinalStage)
    , liveSets        :: IntMap LS.BlockLiveSets
    , resolvingMoves  :: IntMap [LS.ResolvingMoveSet]
    , _inputBlocks    :: [blk1]
    , orderedBlocks   :: [blk1]
    , allocatedBlocks :: Either (IntMap [LS.AllocError]) [blk2]
    , _scanStatePre   :: Maybe ScanStateDesc
    , scanStatePost   :: Maybe ScanStateDesc
    , blockInfo       :: LinearScan.BlockInfo m blk1 blk2 op1 op2
    , opInfo          :: LinearScan.OpInfo m op1 op2
    , loopState       :: LoopState
    }

deriving instance Show LS.AllocError

instance Show LS.ResolvingMoveSet where
  show (LS.RSMove fr fv tr) =
      "<Move (r" ++ show fr ++ " v" ++ show fv ++ ") " ++
           "(r" ++ show tr ++ " v" ++ show fv ++ ")>"
  show (LS.RSSwap fr fv tr tv) =
      "<Swap (r" ++ show fr ++ " v" ++ show fv ++ ") " ++
           "(r" ++ show tr ++ " v" ++ show tv ++ ")>"
  show (LS.RSSpill fr tv)    =
      "<Spill (r" ++ show fr ++ " v" ++ show tv ++ ")>"
  show (LS.RSRestore fv tr)  =
      "<Restore (r" ++ show tr ++ " v" ++ show fv ++ ")>"
  show (LS.RSAllocReg fv tr) =
      "<AllocReg (r" ++ show tr ++ " v" ++ show fv ++ ")>"
  show (LS.RSFreeReg fr tv)  =
      "<FreeReg (r" ++ show fr ++ " v" ++ show tv ++ ")>"
  -- show (LS.RSAllocStack tv)  = "<AllocStack (v" ++ show tv ++ ")>"
  -- show (LS.RSFreeStack fv)   = "<FreeStack (v" ++ show fv ++ ")>"

-- showResolvingMoves :: IntMap [LS.ResolvingMoveSet] -> String
-- showResolvingMoves =
--     M.foldlWithKey' (\acc k mv ->
--         acc ++ "    " ++ show k ++ " => "
--             ++ L.intercalate "\n         " (map show mv) ++ "\n") ""

showDetails :: Monad m => Details m blk1 blk2 op1 op2 -> m String
showDetails err = do
    -- pre  <- showScanStateDesc (scanStatePre err)
    post <- showScanStateDesc (scanStatePost err)
    return $ "Reason: " ++ show (reason err) ++ "\n\n"
          -- ++ ">>> ScanState before allocation:\n"
          -- ++ pre ++ "\n"
          ++ ">>> ScanState after allocation:\n"
          ++ post ++ "\n"
          -- ++ ">>> ResolvingMoves =\n"
          -- ++ showResolvingMoves (resolvingMoves err) ++ "\n"
          ++ ">>> " ++ show (loopState err) ++ "\n"
  where
    showScanStateDesc Nothing = return ""
    showScanStateDesc (Just sd) =
        liftM2 (++) (showBlocks1 (blockInfo err) (opInfo err) sd
                                 (liveSets err) (resolvingMoves err)
                                 (orderedBlocks err))
                    (return ("\n" ++ show sd))

deriving instance Show LS.FinalStage
deriving instance Show LS.BlockLiveSets

instance Show LS.SpillConditionT where
    show (LS.NewToHandledT uid) = "new interval " ++ show uid
    show (LS.UnhandledToHandledT uid) = "unhandled interval " ++ show uid
    show (LS.ActiveToHandledT xid reg) =
        "active interval "++ show xid ++ " for register " ++ show reg
    show (LS.InactiveToHandledT xid reg) =
        "inactive interval "++ show xid ++ " for register " ++ show reg

instance Show LS.SplitPositionT where
    show (LS.BeforePosT pos)         = "before " ++ show pos
    show (LS.EndOfLifetimeHoleT pos) =
        "at end of lifetime hole after " ++ show pos

deriving instance Show LS.SSTrace

toDetails :: LS.Details blk1 blk2
          -> LinearScan.BlockInfo m blk1 blk2 op1 op2
          -> LinearScan.OpInfo m op1 op2
          -> Details m blk1 blk2 op1 op2
toDetails (LS.Build_Details a b c d e f g h i) binfo oinfo =
    Details a (M.fromList b) (M.fromList c) d e
        (either (Left . M.fromList) Right f)
        (fmap toScanStateDesc g) (fmap toScanStateDesc h)
        binfo oinfo (toLoopState i)

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
         -> LS.UseVerifier
         -> [blk1] -> m (Either [String] [blk2])
allocate 0 _ _ _ _  = return $ Left ["Cannot allocate with no registers"]
allocate _ _ _ _ [] = return $ Left ["No basic blocks were provided"]
allocate maxReg binfo oinfo useVerifier blocks = do
    res <- U.unsafeCoerce $ LS.linearScan coqMonad maxReg
        (fromBlockInfo binfo) (fromOpInfo oinfo) useVerifier blocks
    let res' = toDetails res binfo oinfo
    case reason res' of
        Just (err, _) -> do
            dets <- showDetails res'
            return $ Left $ tracer dets $ map reasonToStr err
        Nothing -> case allocatedBlocks res' of
            Left m -> do
                dets <- showDetails res'
                return $ Left $ tracer dets $
                    -- jww (2015-07-02): NYI
                    concatMap (\(pos, es) ->
                                ("At position " ++ show pos) : map show es)
                              (M.toList m)
            Right blks -> return $ Right blks
  where
    reasonToStr r = case r of
        LS.EIntersectsWithFixedInterval pos reg ->
            "Current interval intersects with " ++
            "fixed interval for register " ++ show reg ++ " at " ++ show pos
        LS.ESplitAssignedIntervalForReg reg ->
            "Splitting assigned interval for register " ++ show reg
        LS.ESplitActiveOrInactiveInterval b ->
            "Splitting " ++ (if b then "active" else "inactive") ++ " interval"
        LS.ESpillInterval cond ->
            "Spilling " ++ show cond
        LS.ESplitUnhandledInterval ->
            "Splitting unhandled interval"
        LS.EIntervalHasUsePosReqReg pos ->
            "Interval has use position requiring register at " ++ show pos
        LS.EIntervalBeginsAtSplitPosition ->
            "Interval begins at split position"
        LS.EMoveUnhandledToActive reg ->
            "Allocating unhandled interval at register " ++ show reg
        LS.ESplitActiveIntervalForReg reg ->
            "Splitting active interval for register " ++ show reg
        LS.ESplitAnyInactiveIntervalForReg reg ->
            "Splitting any inactive interval for register " ++ show reg
        LS.ESpillCurrentInterval ->
            "Spilling current interval"
        LS.ESplitCurrentInterval pos ->
            "Splitting current interval " ++ show pos
        LS.ETryAllocateFreeReg reg mpos xid ->
            "Trying to allocate register " ++ show reg
                ++ " at " ++ show mpos ++ " for interval " ++ show xid
        LS.EAllocateBlockedReg reg mpos xid ->
            "Allocating blocked register " ++ show reg
                ++ " at " ++ show mpos ++ " for interval " ++ show xid
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
