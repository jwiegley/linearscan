{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Main where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.IApplicative as IApplicative
import qualified LinearScan.IEndo as IEndo
import qualified LinearScan.IMonad as IMonad
import qualified LinearScan.IState as IState
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Range as Range
import qualified LinearScan.Specif as Specif
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Seq as Seq



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

_MyMachine__maxReg :: Prelude.Int
_MyMachine__maxReg = 32

type MyMachine__PhysReg = Prelude.Int

type VarId = Prelude.Int

data VarKind =
   Input
 | Temp
 | Output

coq_VarKind_rect :: a1 -> a1 -> a1 -> VarKind -> a1
coq_VarKind_rect f f0 f1 v =
  case v of {
   Input -> f;
   Temp -> f0;
   Output -> f1}

coq_VarKind_rec :: a1 -> a1 -> a1 -> VarKind -> a1
coq_VarKind_rec =
  coq_VarKind_rect

data VarInfo =
   Build_VarInfo VarId VarKind Prelude.Bool

coq_VarInfo_rect :: (VarId -> VarKind ->
                             Prelude.Bool -> a1) -> VarInfo -> a1
coq_VarInfo_rect f v =
  case v of {
   Build_VarInfo x x0 x1 -> f x x0 x1}

coq_VarInfo_rec :: (VarId -> VarKind -> Prelude.Bool
                            -> a1) -> VarInfo -> a1
coq_VarInfo_rec =
  coq_VarInfo_rect

varId :: VarInfo -> VarId
varId v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired0 -> varId0}

varKind :: VarInfo -> VarKind
varKind v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired0 -> varKind0}

regRequired :: VarInfo -> Prelude.Bool
regRequired v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired0 -> regRequired0}

data OpInfo opType =
   Build_OpInfo (opType -> Prelude.Bool) (opType -> Prelude.Bool) 
 (opType -> Prelude.Maybe ([] MyMachine__PhysReg)) (opType -> Prelude.Bool) 
 (opType -> [] VarInfo) (opType -> [] MyMachine__PhysReg)

coq_OpInfo_rect :: ((a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool) ->
                            (a1 -> Prelude.Maybe ([] MyMachine__PhysReg)) ->
                            (a1 -> Prelude.Bool) -> (a1 -> []
                            VarInfo) -> (a1 -> [] MyMachine__PhysReg)
                            -> a2) -> (OpInfo a1) -> a2
coq_OpInfo_rect f o =
  case o of {
   Build_OpInfo x x0 x1 x2 x3 x4 -> f x x0 x1 x2 x3 x4}

coq_OpInfo_rec :: ((a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool) ->
                           (a1 -> Prelude.Maybe ([] MyMachine__PhysReg)) ->
                           (a1 -> Prelude.Bool) -> (a1 -> [] VarInfo)
                           -> (a1 -> [] MyMachine__PhysReg) -> a2) ->
                           (OpInfo a1) -> a2
coq_OpInfo_rec =
  coq_OpInfo_rect

isLoopBegin :: (OpInfo a1) -> a1 -> Prelude.Bool
isLoopBegin o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 hasRefs0 varRefs0
    regRefs0 -> isLoopBegin0}

isLoopEnd :: (OpInfo a1) -> a1 -> Prelude.Bool
isLoopEnd o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 hasRefs0 varRefs0
    regRefs0 -> isLoopEnd0}

isCall :: (OpInfo a1) -> a1 -> Prelude.Maybe
                   ([] MyMachine__PhysReg)
isCall o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 hasRefs0 varRefs0
    regRefs0 -> isCall0}

hasRefs :: (OpInfo a1) -> a1 -> Prelude.Bool
hasRefs o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 hasRefs0 varRefs0
    regRefs0 -> hasRefs0}

varRefs :: (OpInfo a1) -> a1 -> [] VarInfo
varRefs o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 hasRefs0 varRefs0
    regRefs0 -> varRefs0}

regRefs :: (OpInfo a1) -> a1 -> [] MyMachine__PhysReg
regRefs o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 hasRefs0 varRefs0
    regRefs0 -> regRefs0}

type OpList opType = [] ((,) Prelude.Int opType)

data AllocationInfo opType =
   Operation opType
 | AllocatedOperation opType (VarId -> Prelude.Maybe
                                     MyMachine__PhysReg)
 | SpillVictim (Prelude.Maybe VarId)

coq_AllocationInfo_rect :: (a1 -> a2) -> (a1 -> (VarId ->
                                    Prelude.Maybe MyMachine__PhysReg) -> a2)
                                    -> ((Prelude.Maybe VarId) -> a2)
                                    -> (AllocationInfo a1) -> a2
coq_AllocationInfo_rect f f0 f1 a =
  case a of {
   Operation x -> f x;
   AllocatedOperation x x0 -> f0 x x0;
   SpillVictim x -> f1 x}

coq_AllocationInfo_rec :: (a1 -> a2) -> (a1 -> (VarId ->
                                   Prelude.Maybe MyMachine__PhysReg) -> a2)
                                   -> ((Prelude.Maybe VarId) -> a2)
                                   -> (AllocationInfo a1) -> a2
coq_AllocationInfo_rec =
  coq_AllocationInfo_rect

type Coq_boundedRange = Specif.Coq_sig2 Range.RangeDesc

type Coq_boundedTriple =
  (,) ((,) (Prelude.Maybe Prelude.Int) (Prelude.Maybe Prelude.Int))
  (Prelude.Maybe Coq_boundedRange)

data Coq_boundedRangeVec =
   Build_boundedRangeVec ([] Coq_boundedTriple) ([]
                                                                Coq_boundedTriple)

boundedRangeVec_rect :: Prelude.Int -> (([]
                                 Coq_boundedTriple) -> ([]
                                 Coq_boundedTriple) -> a1) ->
                                 Coq_boundedRangeVec -> a1
boundedRangeVec_rect pos f b =
  case b of {
   Build_boundedRangeVec x x0 -> f x x0}

boundedRangeVec_rec :: Prelude.Int -> (([]
                                Coq_boundedTriple) -> ([]
                                Coq_boundedTriple) -> a1) ->
                                Coq_boundedRangeVec -> a1
boundedRangeVec_rec pos =
  boundedRangeVec_rect pos

vars :: Prelude.Int -> Coq_boundedRangeVec -> []
                 Coq_boundedTriple
vars pos b =
  case b of {
   Build_boundedRangeVec vars0 regs0 -> vars0}

regs :: Prelude.Int -> Coq_boundedRangeVec -> []
                 Coq_boundedTriple
regs pos b =
  case b of {
   Build_boundedRangeVec vars0 regs0 -> regs0}

transportTriple :: Prelude.Int -> Prelude.Int ->
                            Coq_boundedTriple ->
                            Coq_boundedTriple
transportTriple pos n x =
  x

transportBounds :: Prelude.Int -> Prelude.Int -> ([]
                            Coq_boundedTriple) -> []
                            Coq_boundedTriple
transportBounds pos n =
  Prelude.map (transportTriple pos n)

transportVecBounds :: Prelude.Int -> Prelude.Int -> Prelude.Int ->
                               ([] Coq_boundedTriple) -> []
                               Coq_boundedTriple
transportVecBounds pos m n =
  LinearScan.Utils.vmap m (transportTriple pos n)

boundedSing :: Range.UsePos -> Coq_boundedRange
boundedSing upos =
  Range.getRangeDesc (Range.Build_RangeDesc (Range.uloc upos) ((Prelude.succ)
    (Range.uloc upos)) ((:[]) upos))

boundedCons :: Range.UsePos -> Prelude.Int ->
                        Coq_boundedRange -> Coq_boundedRange
boundedCons upos n xs =
  Range.getRangeDesc (Range.Build_RangeDesc (Range.uloc upos) (Range.rend xs)
    ((:) upos (Range.ups xs)))

withRanges :: Prelude.Int -> Prelude.Bool -> Range.UsePos ->
                       Prelude.Int -> Coq_boundedTriple ->
                       Coq_boundedTriple
withRanges pos req upos n _top_assumption_ =
  let {
   _evar_0_ = \p _top_assumption_0 ->
    let {
     _evar_0_ = \_top_assumption_1 -> (,) p
      (let {_evar_0_ = boundedCons upos n _top_assumption_1} in
       Prelude.Just _evar_0_)}
    in
    let {
     _evar_0_0 = (,) p
      (let {_evar_0_0 = boundedSing upos} in Prelude.Just _evar_0_0)}
    in
    case _top_assumption_0 of {
     Prelude.Just x -> _evar_0_ x;
     Prelude.Nothing -> _evar_0_0}}
  in
  case _top_assumption_ of {
   (,) x x0 -> _evar_0_ x x0}

applyList :: a1 -> ([] a1) -> (Prelude.Int ->
                      Coq_boundedRangeVec) -> (a1 -> Prelude.Int ->
                      () -> Coq_boundedRangeVec ->
                      Coq_boundedRangeVec) -> (,) (OpList a1)
                      Coq_boundedRangeVec
applyList op ops base f =
  let {
   go i x xs =
     case xs of {
      [] -> (,) ((:) ((,) i x) []) (f x i __ (base i));
      (:) y ys ->
       case go ((Prelude.succ) ((Prelude.succ) i)) y ys of {
        (,) ops' next -> (,) ((:) ((,) i x) ops') (f x i __ next)}}}
  in go ((Prelude.succ) 0) op ops

emptyBoundedRangeVec :: Prelude.Int -> Coq_boundedRangeVec
emptyBoundedRangeVec n =
  Build_boundedRangeVec []
    (Data.List.replicate _MyMachine__maxReg ((,) ((,) Prelude.Nothing
      Prelude.Nothing) Prelude.Nothing))

handleOp :: (OpInfo a1) -> a1 -> Prelude.Int ->
                     Coq_boundedRangeVec ->
                     Coq_boundedRangeVec
handleOp opInfo o pos rest =
  let {
   liftOr = \f mx y -> Prelude.Just
    (case mx of {
      Prelude.Just x -> f x y;
      Prelude.Nothing -> y})}
  in
  let {
   savingBound = \x ->
    case (Prelude.||) (isLoopBegin opInfo o)
           (isLoopEnd opInfo o) of {
     Prelude.True ->
      case x of {
       (,) y r ->
        case y of {
         (,) mb me -> (,) ((,) (liftOr Prelude.min mb pos)
          (liftOr Prelude.max me pos)) r}};
     Prelude.False -> x}}
  in
  let {
   consr = \x req ->
    let {upos = Range.Build_UsePos pos req} in
    withRanges pos req upos ((Prelude.succ) ((Prelude.succ) pos)) x}
  in
  let {
   restVars' = Prelude.map savingBound
                 (vars ((Prelude.succ) ((Prelude.succ) pos)) rest)}
  in
  let {
   restRegs' = LinearScan.Utils.vmap _MyMachine__maxReg savingBound
                 (regs ((Prelude.succ) ((Prelude.succ) pos)) rest)}
  in
  let {
   unchanged = LinearScan.Utils.boundedTransport' pos ((Prelude.succ)
                 ((Prelude.succ) pos)) (Build_boundedRangeVec
                 restVars' restRegs')}
  in
  let {
   rest2 = case varRefs opInfo o of {
            [] -> unchanged;
            (:) v vs ->
             let {
              x = consr
                    (Seq.nth ((,) ((,) Prelude.Nothing Prelude.Nothing)
                      Prelude.Nothing) restVars' (varId v))
                    (regRequired v)}
             in
             Build_boundedRangeVec
             (Seq.set_nth ((,) ((,) Prelude.Nothing Prelude.Nothing)
               Prelude.Nothing) (vars pos unchanged)
               (varId v) x) (regs pos unchanged)}}
  in
  case regRefs opInfo o of {
   [] -> rest2;
   (:) r rs ->
    let {
     x = consr (LinearScan.Utils.nth _MyMachine__maxReg restRegs' r)
           Prelude.False}
    in
    Build_boundedRangeVec (vars pos rest2)
    (LinearScan.Utils.set_nth _MyMachine__maxReg
      (transportVecBounds pos _MyMachine__maxReg ((Prelude.succ)
        ((Prelude.succ) pos)) restRegs') r x)}

extractRange :: Coq_boundedTriple -> Prelude.Maybe
                         Range.RangeDesc
extractRange x =
  case x of {
   (,) p mr ->
    case p of {
     (,) mb me ->
      case mr of {
       Prelude.Just b ->
        let {
         mres = case mb of {
                 Prelude.Just b0 ->
                  case me of {
                   Prelude.Just e -> Prelude.Just ((,) b0 e);
                   Prelude.Nothing -> Prelude.Just ((,) b0 (Range.rend b))};
                 Prelude.Nothing ->
                  case me of {
                   Prelude.Just e -> Prelude.Just ((,) (Range.rbeg b) e);
                   Prelude.Nothing -> Prelude.Nothing}}}
        in
        Prelude.Just
        (case mres of {
          Prelude.Just p0 ->
           case p0 of {
            (,) b0 e ->
             Range.packRange (Range.Build_RangeDesc
               (Prelude.min b0 (Range.rbeg b)) (Prelude.max e (Range.rend b))
               (Range.ups b))};
          Prelude.Nothing -> Range.packRange b});
       Prelude.Nothing -> Prelude.Nothing}}}

processOperations :: (OpInfo a1) -> ([] a1) -> (,)
                              ((,) (OpList a1)
                              ([] (Prelude.Maybe Range.RangeDesc)))
                              ([] (Prelude.Maybe Range.RangeDesc))
processOperations opInfo ops =
  case ops of {
   [] -> (,) ((,) [] [])
    (Data.List.replicate _MyMachine__maxReg Prelude.Nothing);
   (:) x xs ->
    case applyList x xs emptyBoundedRangeVec (\x0 x1 _ ->
           handleOp opInfo x0 x1) of {
     (,) ops' b ->
      case b of {
       Build_boundedRangeVec vars' regs' -> (,) ((,) ops'
        (Prelude.map extractRange vars'))
        (LinearScan.Utils.vmap _MyMachine__maxReg extractRange
          regs')}}}

maxReg :: Prelude.Int
maxReg =
  _MyMachine__maxReg

type PhysReg = Prelude.Int

data SSError =
   ECurrentIsSingleton
 | ENoIntervalsToSplit
 | EFailedToAllocateRegister

coq_SSError_rect :: a1 -> a1 -> a1 -> SSError -> a1
coq_SSError_rect f f0 f1 s =
  case s of {
   ECurrentIsSingleton -> f;
   ENoIntervalsToSplit -> f0;
   EFailedToAllocateRegister -> f1}

coq_SSError_rec :: a1 -> a1 -> a1 -> SSError -> a1
coq_SSError_rec =
  coq_SSError_rect

stbind :: (a4 -> IState.IState SSError a2 a3 a5) ->
                   (IState.IState SSError a1 a2 a4) -> IState.IState
                   SSError a1 a3 a5
stbind f x =
  IMonad.ijoin (unsafeCoerce IState.coq_IState_IMonad)
    (IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) f (unsafeCoerce x))

return_ :: a2 -> IState.IState SSError a1 a1 a2
return_ =
  IApplicative.ipure (unsafeCoerce IState.coq_IState_IApplicative)

type Coq_fixedIntervalsType =
  [] (Prelude.Maybe Interval.IntervalDesc)

data ScanStateDesc =
   Build_ScanStateDesc Prelude.Int ([] Interval.IntervalDesc) 
 Coq_fixedIntervalsType ([] ((,) Prelude.Int Prelude.Int)) ([]
                                                                   ((,)
                                                                   Prelude.Int
                                                                   PhysReg)) 
 ([] ((,) Prelude.Int PhysReg)) ([]
                                        ((,) Prelude.Int PhysReg))

coq_ScanStateDesc_rect :: (Prelude.Int -> ([] Interval.IntervalDesc)
                                   -> Coq_fixedIntervalsType -> ([]
                                   ((,) Prelude.Int Prelude.Int)) -> ([]
                                   ((,) Prelude.Int PhysReg)) -> ([]
                                   ((,) Prelude.Int PhysReg)) -> ([]
                                   ((,) Prelude.Int PhysReg)) -> a1)
                                   -> ScanStateDesc -> a1
coq_ScanStateDesc_rect f s =
  case s of {
   Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 -> f x x0 x1 x2 x3 x4 x5}

coq_ScanStateDesc_rec :: (Prelude.Int -> ([] Interval.IntervalDesc)
                                  -> Coq_fixedIntervalsType -> ([]
                                  ((,) Prelude.Int Prelude.Int)) -> ([]
                                  ((,) Prelude.Int PhysReg)) -> ([]
                                  ((,) Prelude.Int PhysReg)) -> ([]
                                  ((,) Prelude.Int PhysReg)) -> a1)
                                  -> ScanStateDesc -> a1
coq_ScanStateDesc_rec =
  coq_ScanStateDesc_rect

nextInterval :: ScanStateDesc -> Prelude.Int
nextInterval s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> nextInterval0}

type IntervalId = Prelude.Int

intervals :: ScanStateDesc -> [] Interval.IntervalDesc
intervals s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> intervals0}

fixedIntervals :: ScanStateDesc ->
                           Coq_fixedIntervalsType
fixedIntervals s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> fixedIntervals0}

unhandled :: ScanStateDesc -> []
                      ((,) IntervalId Prelude.Int)
unhandled s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> unhandled0}

active :: ScanStateDesc -> []
                   ((,) IntervalId PhysReg)
active s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> active0}

inactive :: ScanStateDesc -> []
                     ((,) IntervalId PhysReg)
inactive s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> inactive0}

handled :: ScanStateDesc -> []
                    ((,) IntervalId PhysReg)
handled s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> handled0}

unhandledIds :: ScanStateDesc -> [] IntervalId
unhandledIds s =
  Prelude.map (\i -> Prelude.fst i) (unhandled s)

activeIds :: ScanStateDesc -> [] IntervalId
activeIds s =
  Prelude.map (\i -> Prelude.fst i) (active s)

inactiveIds :: ScanStateDesc -> [] IntervalId
inactiveIds s =
  Prelude.map (\i -> Prelude.fst i) (inactive s)

handledIds :: ScanStateDesc -> [] IntervalId
handledIds s =
  Prelude.map (\i -> Prelude.fst i) (handled s)

all_state_lists :: ScanStateDesc -> [] IntervalId
all_state_lists s =
  (Prelude.++) (unhandledIds s)
    ((Prelude.++) (activeIds s)
      ((Prelude.++) (inactiveIds s) (handledIds s)))

totalExtent :: ScanStateDesc -> ([] IntervalId) ->
                        Prelude.Int
totalExtent sd xs =
  Data.List.sum
    (Prelude.map (\i ->
      Interval.intervalExtent
        (
          (LinearScan.Utils.nth (nextInterval sd)
            (intervals sd) i))) xs)

unhandledExtent :: ScanStateDesc -> Prelude.Int
unhandledExtent sd =
  totalExtent sd
    (Prelude.map (\i -> Prelude.fst i) (unhandled sd))

intervals_for_reg :: ScanStateDesc -> ([]
                              ((,) IntervalId PhysReg)) ->
                              PhysReg -> [] IntervalId
intervals_for_reg sd xs reg =
  Data.List.foldl' (\acc x ->
    case x of {
     (,) xid r ->
      case Eqtype.eq_op (Fintype.ordinal_eqType maxReg)
             (unsafeCoerce r) (unsafeCoerce reg) of {
       Prelude.True -> (:) xid acc;
       Prelude.False -> acc}}) [] xs

registerWithHighestPos :: ([] (Prelude.Maybe Prelude.Int)) -> (,)
                                   Prelude.Int (Prelude.Maybe Prelude.Int)
registerWithHighestPos =
  (LinearScan.Utils.foldl'_with_index) maxReg (\reg res x ->
    case res of {
     (,) r o ->
      case o of {
       Prelude.Just n ->
        case x of {
         Prelude.Just m ->
          case (Prelude.<=) ((Prelude.succ) n) m of {
           Prelude.True -> (,) reg (Prelude.Just m);
           Prelude.False -> (,) r (Prelude.Just n)};
         Prelude.Nothing -> (,) reg Prelude.Nothing};
       Prelude.Nothing -> (,) r Prelude.Nothing}}) ((,) ( 0) (Prelude.Just
    0))

getScanStateDesc :: ScanStateDesc -> ScanStateDesc
getScanStateDesc sd =
  sd

packScanState :: ScanStateDesc -> ScanStateDesc
packScanState sd =
  sd

coq_ScanStateCursor_rect :: ScanStateDesc -> (() -> () ->
                                     a1) -> a1
coq_ScanStateCursor_rect sd f =
  f __ __

coq_ScanStateCursor_rec :: ScanStateDesc -> (() -> () -> a1)
                                    -> a1
coq_ScanStateCursor_rec sd f =
  coq_ScanStateCursor_rect sd f

curId :: ScanStateDesc -> (,) IntervalId Prelude.Int
curId sd =
  Prelude.head (unhandled sd)

curIntDetails :: ScanStateDesc -> Interval.IntervalDesc
curIntDetails sd =
  LinearScan.Utils.nth (nextInterval sd) (intervals sd)
    (Prelude.fst (curId sd))

curPosition :: ScanStateDesc -> Prelude.Int
curPosition sd =
  Interval.intervalStart ( (curIntDetails sd))

data BlockInfo opType blockType a =
   Build_BlockInfo (blockType -> [] a) (blockType -> [] opType)

coq_BlockInfo_rect :: (a3 -> a1) -> ((a2 -> [] a3) -> (a2 -> [] 
                               a1) -> a4) -> (BlockInfo a1 a2 
                               a3) -> a4
coq_BlockInfo_rect p f b =
  case b of {
   Build_BlockInfo x x0 -> f x x0}

coq_BlockInfo_rec :: (a3 -> a1) -> ((a2 -> [] a3) -> (a2 -> [] 
                              a1) -> a4) -> (BlockInfo a1 a2 
                              a3) -> a4
coq_BlockInfo_rec p =
  coq_BlockInfo_rect p

blockElems :: (a3 -> a1) -> (BlockInfo a1 a2 a3) -> a2 -> []
                       a3
blockElems p b =
  case b of {
   Build_BlockInfo blockElems0 blockToOpList0 -> blockElems0}

blockToOpList :: (a3 -> a1) -> (BlockInfo a1 a2 a3) -> a2 ->
                          [] a1
blockToOpList p b =
  case b of {
   Build_BlockInfo blockElems0 blockToOpList0 -> blockToOpList0}

type BlockList opType blockType = [] blockType

type BlockState opType blockType a =
  IState.IState SSError (BlockList opType blockType)
  (BlockList opType blockType) a

computeBlockOrder :: BlockState a1 a2 ()
computeBlockOrder =
  return_ ()

numberOperations :: BlockState a1 a2 ()
numberOperations =
  return_ ()

computeLocalLiveSets :: BlockState a1 a2 ()
computeLocalLiveSets =
  return_ ()

computeGlobalLiveSets :: BlockState a1 a2 ()
computeGlobalLiveSets =
  return_ ()

buildIntervals :: BlockState a1 a2 ()
buildIntervals =
  return_ ()

walkIntervals :: BlockState a1 a2 ()
walkIntervals =
  return_ ()

resolveDataFlow :: BlockState a1 a2 ()
resolveDataFlow =
  return_ ()

assignRegNum :: BlockState a1 a2 ()
assignRegNum =
  return_ ()

determineIntervals :: (OpInfo a1) -> ([] a1) -> (,)
                               (OpList a1) ScanStateDesc
determineIntervals opInfo ops =
  let {
   mkint = \ss mx f ->
    case mx of {
     Prelude.Just s ->
      f ss __ (Interval.Build_IntervalDesc (Range.rbeg s) (Range.rend s)
        ((:[]) s)) __;
     Prelude.Nothing -> ss}}
  in
  let {
   handleVar = \ss mx ->
    (Prelude.$) (mkint ss mx) (\sd _ d _ ->
      packScanState (Build_ScanStateDesc ((Prelude.succ)
        (nextInterval sd))
        (LinearScan.Utils.snoc (nextInterval sd)
          (intervals sd) d) (fixedIntervals sd)
        (Data.List.insertBy (Data.Ord.comparing Prelude.snd) ((,)
          ( (nextInterval sd)) (Interval.ibeg d))
          (Prelude.map Prelude.id (unhandled sd)))
        (Prelude.map Prelude.id (active sd))
        (Prelude.map Prelude.id (inactive sd))
        (Prelude.map Prelude.id (handled sd))))}
  in
  case processOperations opInfo ops of {
   (,) p regRanges ->
    case p of {
     (,) ops' varRanges ->
      let {
       regs0 = LinearScan.Utils.vmap _MyMachine__maxReg (\mr ->
                 case mr of {
                  Prelude.Just r -> Prelude.Just
                   (Interval.packInterval (Interval.Build_IntervalDesc
                     (Range.rbeg ( r)) (Range.rend ( r)) ((:[]) ( r))));
                  Prelude.Nothing -> Prelude.Nothing}) regRanges}
      in
      let {
       s2 = packScanState (Build_ScanStateDesc
              (nextInterval (Build_ScanStateDesc 0 []
                (Data.List.replicate maxReg Prelude.Nothing) [] []
                [] []))
              (intervals (Build_ScanStateDesc 0 []
                (Data.List.replicate maxReg Prelude.Nothing) [] []
                [] [])) regs0
              (unhandled (Build_ScanStateDesc 0 []
                (Data.List.replicate maxReg Prelude.Nothing) [] []
                [] []))
              (active (Build_ScanStateDesc 0 []
                (Data.List.replicate maxReg Prelude.Nothing) [] []
                [] []))
              (inactive (Build_ScanStateDesc 0 []
                (Data.List.replicate maxReg Prelude.Nothing) [] []
                [] []))
              (handled (Build_ScanStateDesc 0 []
                (Data.List.replicate maxReg Prelude.Nothing) [] []
                [] [])))}
      in
      (,) ops' (Data.List.foldl' handleVar s2 varRanges)}}

mainAlgorithm :: BlockState a2 a1 ()
mainAlgorithm =
  stbind (\x ->
    stbind (\x0 ->
      stbind (\x1 ->
        stbind (\x2 ->
          stbind (\x3 ->
            stbind (\x4 ->
              stbind (\x5 -> assignRegNum)
                resolveDataFlow) walkIntervals)
            buildIntervals) computeGlobalLiveSets)
        computeLocalLiveSets) numberOperations)
    computeBlockOrder

linearScan :: ([] a1) -> Prelude.Either SSError ([] a1)
linearScan blocks =
  case IState.runIState mainAlgorithm blocks of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) u res -> Prelude.Right res}}

