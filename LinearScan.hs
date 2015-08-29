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
    , moveOp      :: PhysReg  -> LS.VarId -> PhysReg -> m [op2]
    , saveOp      :: PhysReg  -> LS.VarId -> m [op2]
    , restoreOp   :: LS.VarId -> PhysReg -> m [op2]
    , applyAllocs :: op1 -> [((LS.VarId, LS.VarKind), PhysReg)] -> m [op2]
    , showOp1     :: op1 -> String
    }

deriving instance Eq OpKind
deriving instance Show OpKind

fromOpInfo :: Monad m
           => LinearScan.OpInfo m op1 op2 -> LS.OpInfo (m Any) op1 op2
fromOpInfo (OpInfo a b c d e f g) =
    LS.Build_OpInfo a (map fromVarInfo . b)
        (\r1 r2 -> U.unsafeCoerce (c r1 r2))
        (\r1 r2 -> U.unsafeCoerce (d r1 r2))
        (\r1 r2 -> U.unsafeCoerce (e r1 r2))
        (\r1 r2 -> U.unsafeCoerce (f r1 r2)) g

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

instance Show ScanStateDesc where
    show sd =
        "Unhandled:\n"
            ++ concatMap (\(i, _) -> "  " ++ showInterval sd i ++ "\n")
                         (M.toList (unhandled sd)) ++
        "Active:\n"
            ++ concatMap (\(i, r) ->
                           "  r" ++ show r ++ showInterval sd i ++ "\n")
                         (M.toList (active sd)) ++
        "Inactive:\n"
            ++ concatMap (\(i, r) ->
                           "  r" ++ show r ++ showInterval sd i ++ "\n")
                         (M.toList (inactive sd)) ++
        "Handled:\n"
            ++ concatMap (\(i, r) ->
                           "  " ++ showReg r ++ showInterval sd i ++ "\n")
                         (M.toList (handled sd)) ++
        "Fixed:\n"
            ++ concatMap (\(reg, mi) ->
                           case mi of
                           Nothing -> ""
                           Just i ->
                               "  " ++ showIntervalDesc reg i True ++ "\n")
                         (zip [0..] (fixedIntervals sd))
      where
        showReg Nothing = "<stack>"
        showReg (Just r) = "r" ++ show r

showInterval :: ScanStateDesc -> Int -> String
showInterval sd i = showIntervalDesc i (intervals sd !! i) False

showIntervalDesc :: Int -> LS.IntervalDesc -> Bool -> String
showIntervalDesc i (LS.Build_IntervalDesc iv ib ie rs) isReg =
    (if isReg
     then "r" ++ show i ++ ": "
     else "[" ++ show i ++ "]: " ++ " v" ++ show iv) ++ " "
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
    go (LS.Build_UsePos n req v) =
        (case v of LS.Input  -> "i"
                   LS.Output -> "o"
                   LS.Temp   -> "T")
            ++ show n ++ (if req then "" else "?")
showUsePositions (u:us) = go u ++ " " ++ showUsePositions us
  where
    go (LS.Build_UsePos n req v) =
        (case v of LS.Input  -> "i"
                   LS.Output -> "o"
                   LS.Temp   -> "T")
            ++ show n ++ (if req then "" else "?")

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

showBlock1 :: (blk1 -> [op1])
           -> LS.BlockId
           -> LS.OpId
           -> IntSet
           -> IntSet
           -> LoopState
           -> Maybe LS.RegStateDescSet
           -> Maybe LS.RegStateDescSet
           -> (LS.OpId -> [op1] -> String)
           -> blk1
           -> String
showBlock1 getops bid pos liveIns liveOuts
           loopInfo initials finals showops b =
    "\n    [ BLOCK " ++ show bid ++ " ]\n"
        ++ "        Live In   => " ++ show (S.toList liveIns) ++ "\n"
        ++ "        Live Kill => " ++ show (S.toList liveKill) ++ "\n"
        ++ "        Live Gen  => " ++ show (S.toList liveGen) ++ "\n"
        ++ "        Live Out  => " ++ show (S.toList liveOuts) ++ "\n"
        ++ "        Incoming  =>" ++ (if null branches
                                      then " Entry"
                                      else branches) ++ "\n"
        ++ (if null loops
            then ""
            else "        Loops     =>" ++ loops ++ "\n")
        ++ (case initials of
                 Nothing -> ""
                 Just xs ->
                     "        Inputs    =>\n"
                         ++ (unlines . map (replicate 12 ' ' ++)
                                     . lines . show $ xs))
        ++ (case finals of
                 Nothing -> ""
                 Just xs ->
                     "        Outputs   =>\n"
                         ++ (unlines . map (replicate 12 ' ' ++)
                                     . lines . show $ xs))
        ++ dotLayout ++ showops pos (getops b)
  where
    liveGen  = liveOuts `S.difference` liveIns
    liveKill = liveIns  `S.difference` liveOuts

    fwds = maybe [] S.toList $ M.lookup bid (forwardBranches loopInfo)
    bwds = maybe [] S.toList $ M.lookup bid (backwardBranches loopInfo)

    fwdsStr = case fwds of
        [] -> ""
        xs -> " Fwd" ++ show xs
    bwdsStr = case bwds of
        [] -> ""
        xs -> " Bkwd" ++ show xs

    branches = fwdsStr ++ bwdsStr

    loops =
        let hdr = if bid `elem` loopHeaderBlocks loopInfo
                  then " Header"
                  else ""
            e   = if S.member bid (loopEndBlocks loopInfo)
                  then " End"
                  else ""
            idxs = case foldr (\(idx, blks) rest ->
                                if S.member bid blks
                                then idx : rest
                                else rest) []
                              (M.toList (loopIndices loopInfo)) of
                       [] -> ""
                       xs -> " Idx" ++ show xs
            d   = case M.lookup bid (loopDepths loopInfo) of
                Nothing -> ""
                Just (_, d') -> " Depth=" ++ show d'
        in hdr ++ e ++ idxs ++ d

    dotLayout =
        let leader = "        DOT       => " in
        (if null branches
         then leader ++ "L" ++ show bid ++ " [shape=box];\n"
         else "") ++
        concatMap (\x -> leader ++ "L" ++ show x
                               ++ " -> L" ++ show bid
                               ++ " [color=green];\n") fwds ++
        concatMap (\x -> leader ++ "L" ++ show x
                               ++ " -> L" ++ show bid
                               ++ " [color=red];\n") bwds

opContext :: Int
          -> ScanStateDesc
          -> IntMap [LS.ResolvingMoveSet]
          -> IntMap (LS.RegStateDescSet, [LS.AllocError])
          -> Int
          -> String
opContext width sd rms aerrs here =
    concatMap (marker "End") outs ++
    concatMap (marker "Beg") ins ++
    (case M.lookup here aerrs of
          Nothing -> ""
          Just (regState, allocErrs) ->
              concatMap
                  (\x -> replicate width ' ' ++ "!!! " ++
                         replicate 8 ' ' ++ show x ++ "\n") allocErrs ++
              (unlines . map (replicate (width + 12) ' ' ++)
                   . lines . show $ regState)) ++
    concatMap (\x -> replicate (width + 8) ' ' ++ show x ++ "\n")
              (fromMaybe [] (M.lookup here rms))
  where
    render Nothing = ""
    render (Just r) = "=r" ++ show r

    marker label (_i, Left r, _reg) =
        "    <" ++ label ++ " r" ++ show r ++ ">\n"
    marker label (i, Right v, reg) =
        "    <" ++ label ++ " v" ++ show v ++
        "[" ++ show i ++ "]" ++ render reg ++ ">\n"

    findInts p f z = foldr k z . zip [0..]
      where
        k (_idx, Nothing) rest = rest
        k (idx, Just i) (brest, erest) =
            let mreg = M.lookup idx (allocations sd) in
            (if LS.ibeg i == p
             then (idx, f idx i, mreg) : brest
             else brest,
             if LS.iend i == p
             then (idx, f idx i, mreg) : erest
             else erest)

    (ins, outs) =
        findInts here (\idx _ -> Left idx)
            (findInts here (\_ i -> Right (LS.ivar i)) ([], [])
                (map Just (intervals sd)))
            (fixedIntervals sd)

showOps1 :: Bool
         -> LinearScan.OpInfo accType op1 op2
         -> ScanStateDesc
         -> IntMap [LS.ResolvingMoveSet]
         -> IntMap (LS.RegStateDescSet, [LS.AllocError])
         -> Int
         -> [op1]
         -> String
showOps1 _ _ _ _ _ _ [] = ""
showOps1 atBeg oinfo sd rms aerrs pos (o:os) =
    showOp1' ++ showOps1 False oinfo sd rms aerrs (pos+1) os
  where
    showop = showOp1 oinfo
    here   = pos*2+1
    leader = show here ++ ": "
    width  = length leader

    showOp1' =
        (if atBeg
         then leader ++ showop o ++ "\n"
         else "") ++
        opContext width sd rms aerrs here ++
        opContext width sd rms aerrs (here+1) ++
        (if not atBeg
         then leader ++ showop o ++ "\n"
         else "")

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
            -> IntMap (LS.RegStateDescSet, [LS.AllocError])
            -> IntMap LS.RegStateDescSet
            -> IntMap LS.RegStateDescSet
            -> LoopState
            -> [blk1]
            -> m String
showBlocks1 binfo oinfo sd ls rms aerrs initials finals loopInfo = go 0
  where
    go _ [] = return ""
    go pos (b:bs) = do
        bid  <- LinearScan.blockId binfo b
        let (liveIn, liveOut) = case M.lookup bid ls of
                Nothing -> (S.empty, S.empty)
                Just s  -> (S.fromList (LS.blockLiveIn s),
                            S.fromList (LS.blockLiveOut s))
        let allops blk = let (x, y, z) = LinearScan.blockOps binfo blk
                         in x ++ y ++ z
        (showBlock1 allops bid pos liveIn liveOut loopInfo
                    (M.lookup bid initials) (M.lookup bid finals)
                    (showOps1 True oinfo sd rms aerrs) b ++)
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
    , allocatedBlocks :: Either (IntMap (LS.RegStateDescSet, [LS.AllocError]),
                                 IntMap LS.RegStateDescSet,
                                 IntMap LS.RegStateDescSet) [blk2]
    , scanStatePre    :: Maybe ScanStateDesc
    , scanStatePost   :: Maybe ScanStateDesc
    , blockInfo       :: LinearScan.BlockInfo m blk1 blk2 op1 op2
    , opInfo          :: LinearScan.OpInfo m op1 op2
    , loopState       :: LoopState
    }

deriving instance Show LS.AllocError

instance Show LS.RegStateDescSet where
  show (LS.Build_RegStateDescSet allocs _stack) =
      foldr (\(reg, (residency, reservation)) rest ->
              let info = (case reservation of
                               Nothing -> ""
                               Just v  -> "v" ++ show v) ++
                         (case residency of
                               Nothing -> ""
                               Just v  -> "=v" ++ show v) in
              (if null info
               then ""
               else "r" ++ show reg ++ " -> " ++ info ++ "\n") ++ rest)
            "" (zip ([0..] :: [Int]) allocs)

showSplit :: Bool -> String
showSplit True  = " {split}"
showSplit False = ""

instance Show LS.ResolvingMoveSet where
  show (LS.RSMove fr fv tr)     =
      "move (r" ++ show fr ++ " v" ++ show fv ++ ") " ++
           "(r" ++ show tr ++ " v" ++ show fv ++ ")"
  show (LS.RSTransfer fr fv tr) =
      "<xfer> (r" ++ show fr ++ " v" ++ show fv ++ ") " ++
           "(r" ++ show tr ++ " v" ++ show fv ++ ")"
  show (LS.RSSpill fr tv b)       =
      "spill (r" ++ show fr ++ " v" ++ show tv ++ ")" ++ showSplit b
  show (LS.RSRestore fv tr b)     =
      "restore (r" ++ show tr ++ " v" ++ show fv ++ ")" ++ showSplit b
  show (LS.RSAllocReg fv tr b)    =
      "<reserve> (r" ++ show tr ++ " v" ++ show fv ++ ")" ++ showSplit b
  show (LS.RSFreeReg fr tv b)     =
      "<release> (r" ++ show fr ++ " v" ++ show tv ++ ")" ++ showSplit b
  show (LS.RSAssignReg fv tr)   =
      "<assign> (r" ++ show tr ++ " v" ++ show fv ++ ")"
  show (LS.RSClearReg fr tv)    =
      "<clear> (r" ++ show fr ++ " v" ++ show tv ++ ")"
  show (LS.RSLooped x)          = "!!!LOOPED! " ++ show x
  show (LS.RSAllocStack tv)     = "<alloc> (v" ++ show tv ++ ")"
  show (LS.RSFreeStack fv)      = "<free> (v" ++ show fv ++ ")"

showDetails :: Monad m
            => Details m blk1 blk2 op1 op2
            -> IntMap (LS.RegStateDescSet, [LS.AllocError])
            -> IntMap LS.RegStateDescSet
            -> IntMap LS.RegStateDescSet
            -> m String
showDetails err allocErrs initials finals = do
    let preUnhandled Nothing = ""
        preUnhandled (Just sd) =
            "Original:\n" ++
                concatMap (\(i, _) -> "  " ++ showInterval sd i ++ "\n")
                          (M.toList (unhandled sd))
    post <- showScanStateDesc (scanStatePost err)
                             (preUnhandled (scanStatePre err))
    return $ "Reason: " ++ show (reason err) ++ "\n\n"
          ++ ">>> ScanState after allocation:\n"
          ++ post ++ "\n"
          ++ ">>> " ++ show (loopState err) ++ "\n"
  where
    showScanStateDesc Nothing _ = return ""
    showScanStateDesc (Just sd) preUnhandled =
        liftM2 (++)
            (showBlocks1 (blockInfo err) (opInfo err) sd
                         (liveSets err) (resolvingMoves err)
                         allocErrs initials finals
                         (loopState err) (orderedBlocks err))
            (return ("\n" ++ preUnhandled ++ show sd))

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
        (either (\((x, y), z) ->
                  Left (M.fromList x, M.fromList y, M.fromList z))
                Right f)
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
         -> [blk1] -> m (String, Either [String] [blk2])
allocate 0 _ _ _ _  = return ("", Left ["Cannot allocate with no registers"])
allocate _ _ _ _ [] = return ("", Left ["No basic blocks were provided"])
allocate maxReg binfo oinfo useVerifier blocks = do
    res <- U.unsafeCoerce $ LS.linearScan coqMonad maxReg
        (fromBlockInfo binfo) (fromOpInfo oinfo) useVerifier blocks
    let res' = toDetails res binfo oinfo
    case reason res' of
        Just (err, _) -> do
            dets <- showDetails res' M.empty M.empty M.empty
            return (dets, Left (map reasonToStr err))
        Nothing -> case allocatedBlocks res' of
            Left (m, initials, finals) -> do
                dets <- showDetails res' m initials finals
                return (dets,
                        Left (concatMap
                                  (\(pos, (_, es)) ->
                                    ("At position " ++ show pos)
                                        : map show es)
                             (M.toList m)))
            Right blks -> do
                dets <- showDetails res' M.empty M.empty M.empty
                return (dets, Right blks)
  where
    reasonToStr r = case r of
        LS.EOverlapsWithFixedInterval pos reg ->
            "Current interval intersects with " ++
            "fixed interval for register " ++ show reg ++ " at " ++ show pos
        LS.ESplitAssignedIntervalForReg xid reg pos ->
            "Splitting assigned interval " ++ show xid
                ++ " for register " ++ show reg ++ " at position "++ show pos
        LS.ESplitActiveOrInactiveInterval xid b pos ->
            "Splitting " ++ (if b then "active" else "inactive") ++ " interval "
                ++ show xid ++ " at position "++ show pos
        LS.ESpillInterval cond ->
            "Spilling due to " ++ show cond
        LS.ESplitUnhandledInterval uid pos ->
            "Splitting unhandled interval " ++ show uid
                ++ " at position" ++ show pos
        LS.EIntervalHasUsePosReqReg pos ->
            "Interval has use position requiring register at " ++ show pos
        LS.EIntervalBeginsAtSplitPosition ->
            "Interval begins at split position"
        LS.EMoveUnhandledToActive uid reg ->
            "Allocating unhandled interval " ++ show uid
                ++ " at register " ++ show reg
        LS.ESplitActiveIntervalForReg reg pos ->
            "Splitting active interval for register " ++ show reg
                ++ " at position "++ show pos
        LS.ESplitAnyInactiveIntervalForReg reg pos ->
            "Splitting any inactive interval for register " ++ show reg
                ++ " at position "++ show pos
        LS.ESpillCurrentInterval ->
            "Spilling current interval"
        LS.ESplitCurrentInterval uid pos ->
            "Splitting current interval " ++ show uid
                ++ " at position " ++ show pos
        LS.ETryAllocateFreeReg reg mpos xid ->
            "Trying to allocate register " ++ show reg
                ++ " at " ++ show mpos ++ " for interval " ++ show xid
        LS.EAllocateBlockedReg reg mpos xid ->
            "Allocating blocked register " ++ show reg
                ++ " at " ++ show mpos ++ " for interval " ++ show xid
        LS.ERemoveUnhandledInterval xid ->
            "Removing unhandled interval " ++ show xid
        LS.ECannotInsertUnhandled beg ibeg splitPos iend ->
            "Cannot insert onto unhandled: beg " ++ show beg ++ " >= ibeg "
                ++ show ibeg ++ " && (ibeg == splitPos || iend " ++ show iend
                ++ " == splitPos " ++ show splitPos ++ ")"
        LS.EIntervalBeginsBeforeUnhandled xid ->
            "Cannot spill interval " ++ show xid
                ++ " (begins before current position)"
        LS.ENoValidSplitPosition xid ->
            "No split position found for " ++ show xid
        LS.ECannotSplitSingleton xid ->
            "Interval " ++ show xid ++ " is a singleton"
        LS.ERegisterAlreadyAssigned reg ->
            "Register " ++ show reg ++ " already assigned"
        LS.ERegisterAssignmentsOverlap reg i idx ->
            "Register assignments overlap at " ++ show reg
                ++ " for interval " ++ show i ++ " (index " ++ show idx ++ ")"
        LS.EUnexpectedNoMoreUnhandled ->
            "The unexpected happened: no more unhandled intervals"
        LS.ECannotSpillIfRegisterRequired xid ->
            "Cannot spill interval " ++ show xid
                ++ " at position requiring register"
        LS.ECannotSpillIfRegisterRequiredBefore splitPos pos ->
            "Cannot spill interval split at " ++ show splitPos
                ++ " requiring register at  position " ++ show pos
        LS.ECannotModifyHandledInterval i ->
            "Attempt to modify handled interval " ++ show i
        LS.EFuelExhausted -> "Fuel was exhausted"
        LS.EUnhandledIntervalsRemain ->
            "There are unhandled intervals remaining"
        LS.EActiveIntervalsRemain -> "There are active intervals remaining"
        LS.EInactiveIntervalsRemain -> "There are inactive intervals remaining"
        LS.ENotYetImplemented n -> "Not Yet Implemented (#" ++ show n ++ ")"
