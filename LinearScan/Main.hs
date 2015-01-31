{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Main where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Graph as Graph
import qualified LinearScan.IState as IState
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Range as Range
import qualified LinearScan.Specif as Specif
import qualified LinearScan.State as State
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Seq as Seq
import qualified LinearScan.Ssrbool as Ssrbool
import qualified LinearScan.Ssrnat as Ssrnat



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

_MyMachine__regSize :: Prelude.Int
_MyMachine__regSize = 8

type MyMachine__PhysReg = Prelude.Int

maxReg :: Prelude.Int
maxReg =
  _MyMachine__maxReg

regSize :: Prelude.Int
regSize =
  _MyMachine__regSize

type PhysReg = Prelude.Int

data SSError =
   ECannotSplitSingleton Prelude.Int
 | ECannotSplitAssignedSingleton Prelude.Int
 | ENoIntervalsToSplit
 | ERegisterAlreadyAssigned Prelude.Int
 | ERegisterAssignmentsOverlap Prelude.Int
 | EFuelExhausted
 | EUnexpectedNoMoreUnhandled

coq_SSError_rect :: (Prelude.Int -> a1) -> (Prelude.Int -> a1) ->
                               a1 -> (Prelude.Int -> a1) -> (Prelude.Int ->
                               a1) -> a1 -> a1 -> SSError -> a1
coq_SSError_rect f f0 f1 f2 f3 f4 f5 s =
  case s of {
   ECannotSplitSingleton x -> f x;
   ECannotSplitAssignedSingleton x -> f0 x;
   ENoIntervalsToSplit -> f1;
   ERegisterAlreadyAssigned x -> f2 x;
   ERegisterAssignmentsOverlap x -> f3 x;
   EFuelExhausted -> f4;
   EUnexpectedNoMoreUnhandled -> f5}

coq_SSError_rec :: (Prelude.Int -> a1) -> (Prelude.Int -> a1) ->
                              a1 -> (Prelude.Int -> a1) -> (Prelude.Int ->
                              a1) -> a1 -> a1 -> SSError -> a1
coq_SSError_rec =
  coq_SSError_rect

stbind :: (a4 -> IState.IState SSError a2 a3 a5) ->
                     (IState.IState SSError a1 a2 a4) ->
                     IState.IState SSError a1 a3 a5
stbind f x =
  IState.ijoin (IState.imap f x)

error_ :: SSError -> IState.IState SSError 
                     a1 a2 a3
error_ err x =
  Prelude.Left err

return_ :: a3 -> IState.IState a1 a2 a2 a3
return_ =
  IState.ipure

type Coq_fixedIntervalsType =
  [] (Prelude.Maybe Interval.IntervalDesc)

data ScanStateDesc =
   Build_ScanStateDesc Prelude.Int ([] Interval.IntervalDesc) 
 Coq_fixedIntervalsType ([] ((,) Prelude.Int Prelude.Int)) 
 ([] ((,) Prelude.Int PhysReg)) ([]
                                          ((,) Prelude.Int PhysReg)) 
 ([] ((,) Prelude.Int PhysReg))

coq_ScanStateDesc_rect :: (Prelude.Int -> ([]
                                     Interval.IntervalDesc) ->
                                     Coq_fixedIntervalsType -> ([]
                                     ((,) Prelude.Int Prelude.Int)) -> ([]
                                     ((,) Prelude.Int PhysReg)) ->
                                     ([] ((,) Prelude.Int PhysReg))
                                     -> ([]
                                     ((,) Prelude.Int PhysReg)) ->
                                     a1) -> ScanStateDesc -> a1
coq_ScanStateDesc_rect f s =
  case s of {
   Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 -> f x x0 x1 x2 x3 x4 x5}

coq_ScanStateDesc_rec :: (Prelude.Int -> ([]
                                    Interval.IntervalDesc) ->
                                    Coq_fixedIntervalsType -> ([]
                                    ((,) Prelude.Int Prelude.Int)) -> ([]
                                    ((,) Prelude.Int PhysReg)) ->
                                    ([] ((,) Prelude.Int PhysReg))
                                    -> ([]
                                    ((,) Prelude.Int PhysReg)) ->
                                    a1) -> ScanStateDesc -> a1
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

all_state_lists :: ScanStateDesc -> []
                              IntervalId
all_state_lists s =
  (Prelude.++) (unhandledIds s)
    ((Prelude.++) (activeIds s)
      ((Prelude.++) (inactiveIds s) (handledIds s)))

registerWithHighestPos :: ([] (Prelude.Maybe Prelude.Int)) -> (,)
                                     Prelude.Int (Prelude.Maybe Prelude.Int)
registerWithHighestPos =
  (LinearScan.Utils.vfoldl'_with_index) maxReg (\reg res x ->
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

isWithin :: Interval.IntervalDesc -> Prelude.Int -> Prelude.Int ->
                       Prelude.Bool
isWithin int vid opid =
  (Prelude.&&)
    (Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Interval.ivar int))
      (unsafeCoerce vid))
    ((Prelude.&&) ((Prelude.<=) (Interval.ibeg int) opid)
      ((Prelude.<=) ((Prelude.succ) opid) (Interval.iend int)))

lookupInterval :: ScanStateDesc -> a1 -> Prelude.Int ->
                             Prelude.Int -> Prelude.Maybe
                             IntervalId
lookupInterval sd st vid opid =
  let {
   f = \idx acc int ->
    case acc of {
     Prelude.Just x -> Prelude.Just x;
     Prelude.Nothing ->
      case isWithin ( int) vid opid of {
       Prelude.True -> Prelude.Just idx;
       Prelude.False -> Prelude.Nothing}}}
  in
  (LinearScan.Utils.vfoldl'_with_index) (nextInterval sd) f
    Prelude.Nothing (intervals sd)

lookupRegister :: ScanStateDesc -> a1 ->
                             Eqtype.Equality__Coq_sort -> Prelude.Maybe
                             PhysReg
lookupRegister sd st intid =
  Lib.forFold Prelude.Nothing
    ((Prelude.++) (unsafeCoerce (handled sd))
      ((Prelude.++) (unsafeCoerce (active sd))
        (unsafeCoerce (inactive sd)))) (\acc x ->
    case x of {
     (,) xid reg ->
      case acc of {
       Prelude.Just r -> Prelude.Just r;
       Prelude.Nothing ->
        case Eqtype.eq_op
               (Fintype.ordinal_eqType (nextInterval sd)) xid
               intid of {
         Prelude.True -> Prelude.Just reg;
         Prelude.False -> Prelude.Nothing}}})

data ScanStateStatus =
   Pending
 | InUse

coq_ScanStateStatus_rect :: a1 -> a1 -> ScanStateStatus
                                       -> a1
coq_ScanStateStatus_rect f f0 s =
  case s of {
   Pending -> f;
   InUse -> f0}

coq_ScanStateStatus_rec :: a1 -> a1 -> ScanStateStatus
                                      -> a1
coq_ScanStateStatus_rec =
  coq_ScanStateStatus_rect

type ScanStateSig = ScanStateDesc

getScanStateDesc :: ScanStateDesc ->
                               ScanStateDesc
getScanStateDesc sd =
  sd

packScanState :: ScanStateStatus ->
                            ScanStateDesc ->
                            ScanStateDesc
packScanState b sd =
  sd

coq_ScanStateCursor_rect :: ScanStateDesc -> (() -> ()
                                       -> a1) -> a1
coq_ScanStateCursor_rect sd f =
  f __ __

coq_ScanStateCursor_rec :: ScanStateDesc -> (() -> () ->
                                      a1) -> a1
coq_ScanStateCursor_rec sd f =
  coq_ScanStateCursor_rect sd f

curId :: ScanStateDesc -> (,) IntervalId
                    Prelude.Int
curId sd =
  Prelude.head (unhandled sd)

curIntDetails :: ScanStateDesc -> Interval.IntervalDesc
curIntDetails sd =
  LinearScan.Utils.nth (nextInterval sd) (intervals sd)
    (Prelude.fst (curId sd))

curPosition :: ScanStateDesc -> Prelude.Int
curPosition sd =
  Interval.intervalStart ( (curIntDetails sd))

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

type VarId = Prelude.Int

data VarInfo varType =
   Build_VarInfo (varType -> VarId) (varType ->
                                                        VarKind) 
 (varType -> Prelude.Bool)

coq_VarInfo_rect :: ((a1 -> VarId) -> (a1 ->
                               VarKind) -> (a1 -> Prelude.Bool) ->
                               a2) -> (VarInfo a1) -> a2
coq_VarInfo_rect f v =
  case v of {
   Build_VarInfo x x0 x1 -> f x x0 x1}

coq_VarInfo_rec :: ((a1 -> VarId) -> (a1 ->
                              VarKind) -> (a1 -> Prelude.Bool) ->
                              a2) -> (VarInfo a1) -> a2
coq_VarInfo_rec =
  coq_VarInfo_rect

varId :: (VarInfo a1) -> a1 -> VarId
varId v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired0 -> varId0}

varKind :: (VarInfo a1) -> a1 -> VarKind
varKind v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired0 -> varKind0}

regRequired :: (VarInfo a1) -> a1 -> Prelude.Bool
regRequired v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired0 -> regRequired0}

data OpKind =
   IsNormal
 | IsCall
 | IsBranch
 | IsLoopBegin
 | IsLoopEnd

coq_OpKind_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> OpKind
                              -> a1
coq_OpKind_rect f f0 f1 f2 f3 o =
  case o of {
   IsNormal -> f;
   IsCall -> f0;
   IsBranch -> f1;
   IsLoopBegin -> f2;
   IsLoopEnd -> f3}

coq_OpKind_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> OpKind
                             -> a1
coq_OpKind_rec =
  coq_OpKind_rect

data OpInfo accType opType1 opType2 varType =
   Build_OpInfo (opType1 -> OpKind) (opType1 -> (,)
                                                        ([] varType)
                                                        ([]
                                                        PhysReg)) 
 (PhysReg -> PhysReg -> accType -> (,) ([] opType2)
 accType) (PhysReg -> PhysReg -> accType -> (,)
          ([] opType2) accType) (PhysReg -> (Prelude.Maybe
                                VarId) -> accType -> (,)
                                ([] opType2) accType) ((Prelude.Maybe
                                                      VarId) ->
                                                      PhysReg ->
                                                      accType -> (,)
                                                      ([] opType2) accType) 
 (opType1 -> ([] ((,) VarId PhysReg)) -> [] opType2)

coq_OpInfo_rect :: ((a2 -> OpKind) -> (a2 -> (,) 
                              ([] a4) ([] PhysReg)) ->
                              (PhysReg -> PhysReg -> a1
                              -> (,) ([] a3) a1) -> (PhysReg ->
                              PhysReg -> a1 -> (,) ([] a3) 
                              a1) -> (PhysReg -> (Prelude.Maybe
                              VarId) -> a1 -> (,) ([] a3) a1) ->
                              ((Prelude.Maybe VarId) ->
                              PhysReg -> a1 -> (,) ([] a3) 
                              a1) -> (a2 -> ([]
                              ((,) VarId PhysReg)) -> []
                              a3) -> a5) -> (OpInfo a1 a2 a3 
                              a4) -> a5
coq_OpInfo_rect f o =
  case o of {
   Build_OpInfo x x0 x1 x2 x3 x4 x5 -> f x x0 x1 x2 x3 x4 x5}

coq_OpInfo_rec :: ((a2 -> OpKind) -> (a2 -> (,) 
                             ([] a4) ([] PhysReg)) ->
                             (PhysReg -> PhysReg -> a1 ->
                             (,) ([] a3) a1) -> (PhysReg ->
                             PhysReg -> a1 -> (,) ([] a3) a1) ->
                             (PhysReg -> (Prelude.Maybe
                             VarId) -> a1 -> (,) ([] a3) a1) ->
                             ((Prelude.Maybe VarId) ->
                             PhysReg -> a1 -> (,) ([] a3) a1) ->
                             (a2 -> ([]
                             ((,) VarId PhysReg)) -> []
                             a3) -> a5) -> (OpInfo a1 a2 a3 
                             a4) -> a5
coq_OpInfo_rec =
  coq_OpInfo_rect

opKind :: (OpInfo a1 a2 a3 a4) -> a2 -> OpKind
opKind o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp0 saveOp0 restoreOp0
    applyAllocs0 -> opKind0}

opRefs :: (OpInfo a1 a2 a3 a4) -> a2 -> (,) ([] a4)
                     ([] PhysReg)
opRefs o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp0 saveOp0 restoreOp0
    applyAllocs0 -> opRefs0}

moveOp :: (OpInfo a1 a2 a3 a4) -> PhysReg ->
                     PhysReg -> a1 -> (,) ([] a3) a1
moveOp o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp0 saveOp0 restoreOp0
    applyAllocs0 -> moveOp0}

swapOp :: (OpInfo a1 a2 a3 a4) -> PhysReg ->
                     PhysReg -> a1 -> (,) ([] a3) a1
swapOp o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp0 saveOp0 restoreOp0
    applyAllocs0 -> swapOp0}

saveOp :: (OpInfo a1 a2 a3 a4) -> PhysReg ->
                     (Prelude.Maybe VarId) -> a1 -> (,) ([] a3) 
                     a1
saveOp o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp0 saveOp0 restoreOp0
    applyAllocs0 -> saveOp0}

restoreOp :: (OpInfo a1 a2 a3 a4) -> (Prelude.Maybe
                        VarId) -> PhysReg -> a1 -> (,)
                        ([] a3) a1
restoreOp o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp0 saveOp0 restoreOp0
    applyAllocs0 -> restoreOp0}

applyAllocs :: (OpInfo a1 a2 a3 a4) -> a2 -> ([]
                          ((,) VarId PhysReg)) -> [] 
                          a3
applyAllocs o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp0 saveOp0 restoreOp0
    applyAllocs0 -> applyAllocs0}

type BlockId = Prelude.Int

data BlockInfo blockType1 blockType2 opType1 opType2 =
   Build_BlockInfo (blockType1 -> BlockId) (blockType1 ->
                                                               []
                                                               BlockId) 
 (blockType1 -> [] opType1) (blockType1 -> ([] opType2) -> blockType2)

coq_BlockInfo_rect :: ((a1 -> BlockId) -> (a1 -> []
                                 BlockId) -> (a1 -> [] a3) -> (a1
                                 -> ([] a4) -> a2) -> a5) ->
                                 (BlockInfo a1 a2 a3 a4) -> a5
coq_BlockInfo_rect f b =
  case b of {
   Build_BlockInfo x x0 x1 x2 -> f x x0 x1 x2}

coq_BlockInfo_rec :: ((a1 -> BlockId) -> (a1 -> []
                                BlockId) -> (a1 -> [] a3) -> (a1 ->
                                ([] a4) -> a2) -> a5) -> (BlockInfo
                                a1 a2 a3 a4) -> a5
coq_BlockInfo_rec =
  coq_BlockInfo_rect

blockId :: (BlockInfo a1 a2 a3 a4) -> a1 ->
                      BlockId
blockId b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0
    setBlockOps0 -> blockId0}

blockSuccessors :: (BlockInfo a1 a2 a3 a4) -> a1 -> []
                              BlockId
blockSuccessors b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0
    setBlockOps0 -> blockSuccessors0}

blockOps :: (BlockInfo a1 a2 a3 a4) -> a1 -> [] a3
blockOps b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0
    setBlockOps0 -> blockOps0}

setBlockOps :: (BlockInfo a1 a2 a3 a4) -> a1 -> ([] 
                          a4) -> a2
setBlockOps b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0
    setBlockOps0 -> setBlockOps0}

type BoundedRange = Range.RangeDesc

transportBoundedRange :: Prelude.Int -> Prelude.Int ->
                                    BoundedRange ->
                                    BoundedRange
transportBoundedRange base prev x =
  x

type BoundedInterval = Interval.IntervalDesc

transportBoundedInterval :: Prelude.Int -> Prelude.Int ->
                                       BoundedInterval ->
                                       BoundedInterval
transportBoundedInterval base prev x =
  x

data BuildState =
   Build_BuildState Prelude.Int ([]
                                          (Prelude.Maybe
                                          BoundedRange)) ([]
                                                                   (Prelude.Maybe
                                                                   BoundedInterval))

coq_BuildState_rect :: (Prelude.Int -> ([]
                                  (Prelude.Maybe BoundedRange)) ->
                                  ([]
                                  (Prelude.Maybe BoundedInterval))
                                  -> a1) -> BuildState -> a1
coq_BuildState_rect f b =
  case b of {
   Build_BuildState x x0 x1 -> f x x0 x1}

coq_BuildState_rec :: (Prelude.Int -> ([]
                                 (Prelude.Maybe BoundedRange)) ->
                                 ([]
                                 (Prelude.Maybe BoundedInterval))
                                 -> a1) -> BuildState -> a1
coq_BuildState_rec =
  coq_BuildState_rect

bsPos :: BuildState -> Prelude.Int
bsPos b =
  case b of {
   Build_BuildState bsPos0 bsVars0 bsRegs0 -> bsPos0}

bsVars :: BuildState -> []
                     (Prelude.Maybe BoundedRange)
bsVars b =
  case b of {
   Build_BuildState bsPos0 bsVars0 bsRegs0 -> bsVars0}

bsRegs :: BuildState -> []
                     (Prelude.Maybe BoundedInterval)
bsRegs b =
  case b of {
   Build_BuildState bsPos0 bsVars0 bsRegs0 -> bsRegs0}

foldOps :: (BlockInfo a1 a2 a3 a4) -> (a5 -> a3 -> a5)
                      -> a5 -> ([] a1) -> a5
foldOps binfo f z =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (blockOps binfo blk)) z

countOps :: (BlockInfo a1 a2 a3 a4) -> ([] a1) ->
                       Prelude.Int
countOps binfo =
  foldOps binfo (\acc x -> (Prelude.succ) acc) 0

foldOpsRev :: (BlockInfo a1 a2 a3 a4) -> (a5 -> a3 ->
                         a5) -> a5 -> ([] a1) -> a5
foldOpsRev binfo f z blocks =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (Seq.rev (blockOps binfo blk))) z
    (Seq.rev blocks)

createRangeForVars :: (VarInfo a1) -> Prelude.Int -> ([]
                                 (Prelude.Maybe BoundedRange)) ->
                                 ([] a1) -> []
                                 (Prelude.Maybe BoundedRange)
createRangeForVars vinfo pos vars varRefs =
  (Prelude.flip (Prelude.$)) vars (\vars' ->
    let {
     vars'0 = Prelude.map
                (Lib.option_map
                  (transportBoundedRange ((Prelude.succ)
                    (Ssrnat.double pos)) ((Prelude.succ)
                    (Ssrnat.double ((Prelude.succ) pos))))) vars'}
    in
    Data.List.foldl' (\vars'1 v ->
      let {
       upos = Range.Build_UsePos ((Prelude.succ) (Ssrnat.double pos))
        (regRequired vinfo v)}
      in
      (Prelude.flip (Prelude.$)) __ (\_ ->
        Seq.set_nth Prelude.Nothing vars'1 (varId vinfo v)
          (Prelude.Just
          (let {
            _evar_0_ = \_top_assumption_ -> Range.Build_RangeDesc
             (Range.uloc upos) (Range.rend ( _top_assumption_)) ((:) upos
             (Range.ups ( _top_assumption_)))}
           in
           let {
            _evar_0_0 = Range.Build_RangeDesc (Range.uloc upos)
             ((Prelude.succ) (Range.uloc upos)) ((:[]) upos)}
           in
           case Seq.nth Prelude.Nothing vars (varId vinfo v) of {
            Prelude.Just x -> _evar_0_ x;
            Prelude.Nothing -> _evar_0_0})))) vars'0 varRefs)

createIntervalForRegs :: Prelude.Int -> ([]
                                    (Prelude.Maybe BoundedInterval))
                                    -> ([] PhysReg) -> []
                                    (Prelude.Maybe BoundedInterval)
createIntervalForRegs pos regs regRefs =
  (Prelude.flip (Prelude.$)) regs (\regs' ->
    let {
     regs'0 = LinearScan.Utils.vmap maxReg
                (Lib.option_map
                  (transportBoundedInterval ((Prelude.succ)
                    (Ssrnat.double pos)) ((Prelude.succ)
                    (Ssrnat.double ((Prelude.succ) pos))))) regs'}
    in
    Data.List.foldl' (\regs'1 reg ->
      let {
       upos = Range.Build_UsePos ((Prelude.succ) (Ssrnat.double pos))
        Prelude.True}
      in
      (Prelude.flip (Prelude.$)) __ (\_ ->
        let {
         r = Range.Build_RangeDesc (Range.uloc upos) ((Prelude.succ)
          (Range.uloc upos)) ((:[]) upos)}
        in
        LinearScan.Utils.set_nth maxReg regs'1 reg (Prelude.Just
          (let {
            _evar_0_ = \_top_assumption_ ->
             let {
              _evar_0_ = \iv ib ie ik rds ->
               (Prelude.flip (Prelude.$)) __ (\_ ->
                 let {
                  _evar_0_ = \_ ->
                   let {
                    _evar_0_ = \_ -> Interval.Build_IntervalDesc iv
                     (Range.rbeg ( r)) (Range.rend ( (Prelude.last rds))) ik
                     ((:) r rds)}
                   in
                    _evar_0_}
                 in
                  _evar_0_ __ __)}
             in
             case _top_assumption_ of {
              Interval.Build_IntervalDesc x x0 x1 x2 x3 ->
               _evar_0_ x x0 x1 x2 x3}}
           in
           let {
            _evar_0_0 = Interval.Build_IntervalDesc 0 (Range.rbeg ( r))
             (Range.rend ( r)) Interval.Whole ((:[]) ( r))}
           in
           case LinearScan.Utils.nth maxReg regs reg of {
            Prelude.Just x -> _evar_0_ x;
            Prelude.Nothing -> _evar_0_0})))) regs'0 regRefs)

processOperations :: (VarInfo a6) -> (OpInfo
                                a1 a4 a5 a6) -> (BlockInfo 
                                a2 a3 a4 a5) -> ([] a2) ->
                                BuildState
processOperations vinfo oinfo binfo blocks =
  (Prelude.flip (Prelude.$))
    (foldOps binfo (\x op ->
      case x of {
       (,) n m -> (,) ((Prelude.succ) n)
        (Data.List.foldl' (\m0 v ->
          Prelude.max m0 (varId vinfo v)) m
          (Prelude.fst (opRefs oinfo op)))}) ((,) 0 0) blocks)
    (\_top_assumption_ ->
    let {
     _evar_0_ = \opCount highestVar ->
      let {
       z = Build_BuildState opCount
        (Seq.nseq ((Prelude.succ) highestVar) Prelude.Nothing)
        (Data.List.replicate maxReg Prelude.Nothing)}
      in
      foldOpsRev binfo (\_top_assumption_0 ->
        let {
         _evar_0_ = \pos vars regs op ->
          let {
           _evar_0_ = \vars0 regs0 -> Build_BuildState 0 vars0
            regs0}
          in
          let {
           _evar_0_0 = \pos0 vars0 regs0 ->
            let {_top_assumption_1 = opRefs oinfo op} in
            let {
             _evar_0_0 = \varRefs regRefs -> Build_BuildState pos0
              (createRangeForVars vinfo pos0 vars0 varRefs)
              ((Prelude.flip (Prelude.$))
                (case opKind oinfo op of {
                  IsCall ->
                   unsafeCoerce
                     (Fintype.enum_mem
                       (Fintype.ordinal_finType maxReg)
                       (Ssrbool.mem Ssrbool.predPredType
                         (Ssrbool.sort_of_simpl_pred Ssrbool.pred_of_argType)));
                  _ -> regRefs}) (\regRefs' ->
                createIntervalForRegs pos0 regs0 regRefs'))}
            in
            case _top_assumption_1 of {
             (,) x x0 -> _evar_0_0 x x0}}
          in
          (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
            (\_ ->
            _evar_0_ vars regs)
            (\x ->
            _evar_0_0 x vars regs)
            pos}
        in
        case _top_assumption_0 of {
         Build_BuildState x x0 x1 -> _evar_0_ x x0 x1}) z blocks}
    in
    case _top_assumption_ of {
     (,) x x0 -> _evar_0_ x x0})

computeBlockOrder :: ([] a1) -> [] a1
computeBlockOrder blocks =
  blocks

numberOperations :: ([] a1) -> [] a1
numberOperations blocks =
  blocks

coq_IntMap_rect :: a2 -> (([] ((,) Prelude.Int a1)) -> a2) ->
                              (Data.IntMap.IntMap a1) -> a2
coq_IntMap_rect f f0 i =
  (\fO fS _ -> fO ())
    (\_ ->
    f)
    (\x ->
    f0 x)
    i

coq_IntMap_rec :: a2 -> (([] ((,) Prelude.Int a1)) -> a2) ->
                             (Data.IntMap.IntMap a1) -> a2
coq_IntMap_rec =
  coq_IntMap_rect

prepend :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort
                      -> (Prelude.Maybe
                      (Ssrbool.Coq_pred_sort Eqtype.Equality__Coq_sort)) ->
                      Prelude.Maybe ([] Eqtype.Equality__Coq_sort)
prepend a x mxs =
  case mxs of {
   Prelude.Just xs ->
    case Prelude.not (Ssrbool.in_mem x (Ssrbool.mem (Seq.seq_predType a) xs)) of {
     Prelude.True -> Prelude.Just ((:) x (unsafeCoerce xs));
     Prelude.False -> Prelude.Just (unsafeCoerce xs)};
   Prelude.Nothing -> Prelude.Just ((:) x [])}

coq_IntSet_rect :: a1 -> (([] Prelude.Int) -> a1) ->
                              Data.IntSet.IntSet -> a1
coq_IntSet_rect f f0 i =
  (\fO fS _ -> fO ())
    (\_ ->
    f)
    (\x ->
    f0 x)
    i

coq_IntSet_rec :: a1 -> (([] Prelude.Int) -> a1) ->
                             Data.IntSet.IntSet -> a1
coq_IntSet_rec =
  coq_IntSet_rect

coq_IntSet_forFold :: a1 -> Data.IntSet.IntSet -> (a1 ->
                                 Prelude.Int -> a1) -> a1
coq_IntSet_forFold z m f =
  Data.IntSet.foldl' f z m

type OpId = Prelude.Int

data BlockLiveSets =
   Build_BlockLiveSets Data.IntSet.IntSet Data.IntSet.IntSet 
 Data.IntSet.IntSet Data.IntSet.IntSet OpId OpId

coq_BlockLiveSets_rect :: (Data.IntSet.IntSet ->
                                     Data.IntSet.IntSet -> Data.IntSet.IntSet
                                     -> Data.IntSet.IntSet -> OpId
                                     -> OpId -> a1) ->
                                     BlockLiveSets -> a1
coq_BlockLiveSets_rect f b =
  case b of {
   Build_BlockLiveSets x x0 x1 x2 x3 x4 -> f x x0 x1 x2 x3 x4}

coq_BlockLiveSets_rec :: (Data.IntSet.IntSet -> Data.IntSet.IntSet
                                    -> Data.IntSet.IntSet ->
                                    Data.IntSet.IntSet -> OpId ->
                                    OpId -> a1) ->
                                    BlockLiveSets -> a1
coq_BlockLiveSets_rec =
  coq_BlockLiveSets_rect

blockLiveGen :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveGen b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveGen0}

blockLiveKill :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveKill b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveKill0}

blockLiveIn :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveIn b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveIn0}

blockLiveOut :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveOut b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveOut0}

blockFirstOpId :: BlockLiveSets -> OpId
blockFirstOpId b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockFirstOpId0}

blockLastOpId :: BlockLiveSets -> OpId
blockLastOpId b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLastOpId0}

computeLocalLiveSets :: (VarInfo a6) ->
                                   (OpInfo a1 a4 a5 a6) ->
                                   (BlockInfo a2 a3 a4 a5) -> ([]
                                   a2) -> Data.IntMap.IntMap
                                   BlockLiveSets
computeLocalLiveSets vinfo oinfo binfo blocks =
  Prelude.snd
    (Lib.forFold ((,) ((Prelude.succ) 0) Data.IntMap.empty) blocks (\acc b ->
      case acc of {
       (,) idx m ->
        let {
         liveSet = Build_BlockLiveSets Data.IntSet.empty
          Data.IntSet.empty Data.IntSet.empty Data.IntSet.empty idx idx}
        in
        case Lib.forFold ((,) idx liveSet) (blockOps binfo b)
               (\acc0 o ->
               case acc0 of {
                (,) lastIdx liveSet1 -> (,) ((Prelude.succ) ((Prelude.succ)
                 lastIdx))
                 (Lib.forFold liveSet1
                   (Prelude.fst (opRefs oinfo o)) (\liveSet2 v ->
                   let {vid = varId vinfo v} in
                   case varKind vinfo v of {
                    Input ->
                     case Prelude.not
                            (Data.IntSet.member vid
                              (blockLiveKill liveSet2)) of {
                      Prelude.True -> Build_BlockLiveSets
                       (Data.IntSet.insert vid
                         (blockLiveGen liveSet2))
                       (blockLiveKill liveSet2)
                       (blockLiveIn liveSet2)
                       (blockLiveOut liveSet2)
                       (blockFirstOpId liveSet2) lastIdx;
                      Prelude.False -> liveSet2};
                    _ -> Build_BlockLiveSets
                     (blockLiveGen liveSet2)
                     (Data.IntSet.insert vid
                       (blockLiveKill liveSet2))
                     (blockLiveIn liveSet2)
                     (blockLiveOut liveSet2)
                     (blockFirstOpId liveSet2) lastIdx}))}) of {
         (,) lastIdx' liveSet3 -> (,) lastIdx'
          (Data.IntMap.insert (blockId binfo b) liveSet3 m)}}))

computeGlobalLiveSets :: (BlockInfo a1 a2 a3 a4) -> ([]
                                    a1) -> (Data.IntMap.IntMap
                                    BlockLiveSets) ->
                                    Data.IntMap.IntMap
                                    BlockLiveSets
computeGlobalLiveSets binfo blocks liveSets =
  Lib.forFold liveSets (Seq.rev blocks) (\liveSets1 b ->
    let {bid = blockId binfo b} in
    case Data.IntMap.lookup bid liveSets1 of {
     Prelude.Just liveSet ->
      let {
       liveSet2 = Lib.forFold liveSet (blockSuccessors binfo b)
                    (\liveSet1 s_bid ->
                    case Data.IntMap.lookup s_bid liveSets1 of {
                     Prelude.Just sux -> Build_BlockLiveSets
                      (blockLiveGen liveSet1)
                      (blockLiveKill liveSet1)
                      (blockLiveIn liveSet1)
                      (Data.IntSet.union (blockLiveOut liveSet1)
                        (blockLiveIn sux))
                      (blockFirstOpId liveSet1)
                      (blockLastOpId liveSet1);
                     Prelude.Nothing -> liveSet1})}
      in
      Data.IntMap.insert bid (Build_BlockLiveSets
        (blockLiveGen liveSet2)
        (blockLiveKill liveSet2)
        (Data.IntSet.union
          (Data.IntSet.difference (blockLiveOut liveSet2)
            (blockLiveKill liveSet2))
          (blockLiveGen liveSet2))
        (blockLiveOut liveSet2)
        (blockFirstOpId liveSet2)
        (blockLastOpId liveSet2)) liveSets1;
     Prelude.Nothing -> liveSets1})

buildIntervals :: (VarInfo a6) -> (OpInfo 
                             a1 a4 a5 a6) -> (BlockInfo a2 
                             a3 a4 a5) -> ([] a2) -> ScanStateSig
buildIntervals vinfo oinfo binfo blocks =
  let {
   mkint = \vid ss pos mx f ->
    case mx of {
     Prelude.Just b ->
      f ss __ (Interval.Build_IntervalDesc vid (Range.rbeg ( b))
        (Range.rend ( b)) Interval.Whole ((:[]) ( b))) __;
     Prelude.Nothing -> ss}}
  in
  let {
   handleVar = \pos vid ss mx ->
    mkint vid ss pos mx (\sd _ d _ ->
      packScanState Pending
        (Build_ScanStateDesc ((Prelude.succ)
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
  let {bs = processOperations vinfo oinfo binfo blocks} in
  let {
   regs = LinearScan.Utils.vmap maxReg (Lib.option_map )
            (bsRegs bs)}
  in
  let {
   s2 = packScanState Pending
          (Build_ScanStateDesc
          (nextInterval (Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] []
            []))
          (intervals (Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] []
            [])) regs
          (unhandled (Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] []
            []))
          (active (Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] []
            []))
          (inactive (Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] []
            []))
          (handled (Build_ScanStateDesc 0 []
            (Data.List.replicate maxReg Prelude.Nothing) [] [] []
            [])))}
  in
  let {
   s3 = Lib.foldl_with_index (handleVar (bsPos bs)) s2
          (bsVars bs)}
  in
  packScanState InUse ( s3)

checkIntervalBoundary :: ScanStateDesc -> Prelude.Int ->
                                    Prelude.Bool -> BlockLiveSets
                                    -> BlockLiveSets ->
                                    (Data.IntMap.IntMap
                                    ((,) Graph.Graph Graph.Graph)) ->
                                    Prelude.Int -> Data.IntMap.IntMap
                                    ((,) Graph.Graph Graph.Graph)
checkIntervalBoundary sd key in_from from to mappings vid =
  let {
   mfrom_int = lookupInterval sd __ vid
                 (blockLastOpId from)}
  in
  case mfrom_int of {
   Prelude.Just from_interval ->
    let {
     mto_int = lookupInterval sd __ vid
                 (blockFirstOpId to)}
    in
    case mto_int of {
     Prelude.Just to_interval ->
      case Eqtype.eq_op (Fintype.ordinal_eqType (nextInterval sd))
             (unsafeCoerce from_interval) (unsafeCoerce to_interval) of {
       Prelude.True -> mappings;
       Prelude.False ->
        let {
         msreg = lookupRegister sd __ (unsafeCoerce from_interval)}
        in
        let {
         mdreg = lookupRegister sd __ (unsafeCoerce to_interval)}
        in
        let {
         addToGraphs = \e xs ->
          case xs of {
           (,) gbeg gend ->
            case in_from of {
             Prelude.True -> (,) gbeg
              (Graph.addEdge (Fintype.ordinal_eqType maxReg) e
                gend);
             Prelude.False -> (,)
              (Graph.addEdge (Fintype.ordinal_eqType maxReg) e
                gbeg) gend}}}
        in
        let {
         f = \mxs ->
          let {e = (,) msreg mdreg} in
          Prelude.Just
          (unsafeCoerce addToGraphs e
            (case mxs of {
              Prelude.Just xs -> xs;
              Prelude.Nothing -> (,)
               (Graph.emptyGraph (Fintype.ordinal_eqType maxReg))
               (Graph.emptyGraph (Fintype.ordinal_eqType maxReg))}))}
        in
        Data.IntMap.alter f key mappings};
     Prelude.Nothing -> mappings};
   Prelude.Nothing -> mappings}

type BlockMoves = (,) Graph.Graph Graph.Graph

resolveDataFlow :: (BlockInfo a1 a2 a3 a4) ->
                              ScanStateDesc -> ([] a1) ->
                              (Data.IntMap.IntMap BlockLiveSets) ->
                              Data.IntMap.IntMap BlockMoves
resolveDataFlow binfo sd blocks liveSets =
  Lib.forFold Data.IntMap.empty blocks (\mappings b ->
    let {bid = blockId binfo b} in
    case Data.IntMap.lookup bid liveSets of {
     Prelude.Just from ->
      let {successors = blockSuccessors binfo b} in
      let {
       in_from = (Prelude.<=) (Data.List.length successors) ((Prelude.succ)
                   0)}
      in
      Lib.forFold mappings successors (\ms s_bid ->
        case Data.IntMap.lookup s_bid liveSets of {
         Prelude.Just to ->
          let {
           key = case in_from of {
                  Prelude.True -> bid;
                  Prelude.False -> s_bid}}
          in
          coq_IntSet_forFold ms (blockLiveIn to)
            (checkIntervalBoundary sd key in_from from to);
         Prelude.Nothing -> ms});
     Prelude.Nothing -> mappings})

data AssnStateInfo accType =
   Build_AssnStateInfo OpId accType

coq_AssnStateInfo_rect :: (OpId -> a1 -> a2) ->
                                     (AssnStateInfo a1) -> a2
coq_AssnStateInfo_rect f a =
  case a of {
   Build_AssnStateInfo x x0 -> f x x0}

coq_AssnStateInfo_rec :: (OpId -> a1 -> a2) ->
                                    (AssnStateInfo a1) -> a2
coq_AssnStateInfo_rec =
  coq_AssnStateInfo_rect

assnOpId :: (AssnStateInfo a1) -> OpId
assnOpId a =
  case a of {
   Build_AssnStateInfo assnOpId0 assnAcc0 -> assnOpId0}

assnAcc :: (AssnStateInfo a1) -> a1
assnAcc a =
  case a of {
   Build_AssnStateInfo assnOpId0 assnAcc0 -> assnAcc0}

type AssnState accType a =
  State.State (AssnStateInfo accType) a

moveOpM :: (OpInfo a1 a2 a3 a4) -> PhysReg ->
                      PhysReg -> AssnState a1 ([] a3)
moveOpM oinfo sreg dreg =
  State.bind (\assn ->
    case moveOp oinfo sreg dreg (assnAcc assn) of {
     (,) mop acc' ->
      State.bind (\x -> State.pure mop)
        (State.put (Build_AssnStateInfo (assnOpId assn)
          acc'))}) State.get

saveOpM :: (OpInfo a1 a2 a3 a4) -> PhysReg ->
                      (Prelude.Maybe VarId) -> AssnState
                      a1 ([] a3)
saveOpM oinfo vid reg =
  State.bind (\assn ->
    case saveOp oinfo vid reg (assnAcc assn) of {
     (,) sop acc' ->
      State.bind (\x -> State.pure sop)
        (State.put (Build_AssnStateInfo (assnOpId assn)
          acc'))}) State.get

restoreOpM :: (OpInfo a1 a2 a3 a4) -> (Prelude.Maybe
                         VarId) -> PhysReg ->
                         AssnState a1 ([] a3)
restoreOpM oinfo vid reg =
  State.bind (\assn ->
    case restoreOp oinfo vid reg (assnAcc assn) of {
     (,) rop acc' ->
      State.bind (\x -> State.pure rop)
        (State.put (Build_AssnStateInfo (assnOpId assn)
          acc'))}) State.get

pairM :: (AssnState a1 a2) -> (AssnState 
                    a1 a3) -> AssnState a1 ((,) a2 a3)
pairM x y =
  State.bind (\x' -> State.bind (\y' -> State.pure ((,) x' y')) y) x

savesAndRestores :: (OpInfo a1 a2 a3 a4) ->
                               Eqtype.Equality__Coq_sort -> VarId
                               -> PhysReg -> Interval.IntervalDesc
                               -> AssnState a1
                               ((,) ([] a3) ([] a3))
savesAndRestores oinfo opid vid reg int =
  let {
   isFirst = Eqtype.eq_op Ssrnat.nat_eqType
               (unsafeCoerce (Interval.firstUsePos int)) opid}
  in
  let {
   isLast = Eqtype.eq_op (Eqtype.option_eqType Ssrnat.nat_eqType)
              (unsafeCoerce (Interval.nextUseAfter int (unsafeCoerce opid)))
              (unsafeCoerce Prelude.Nothing)}
  in
  let {save = saveOpM oinfo reg (Prelude.Just vid)} in
  let {restore = restoreOpM oinfo (Prelude.Just vid) reg} in
  case Interval.iknd int of {
   Interval.Whole -> State.pure ((,) [] []);
   Interval.LeftMost ->
    case isLast of {
     Prelude.True -> pairM (State.pure []) save;
     Prelude.False -> State.pure ((,) [] [])};
   Interval.Middle ->
    case isFirst of {
     Prelude.True ->
      case isLast of {
       Prelude.True -> pairM restore save;
       Prelude.False -> pairM restore (State.pure [])};
     Prelude.False ->
      case isLast of {
       Prelude.True -> pairM (State.pure []) save;
       Prelude.False -> State.pure ((,) [] [])}};
   Interval.RightMost ->
    case isFirst of {
     Prelude.True -> pairM restore (State.pure []);
     Prelude.False -> State.pure ((,) [] [])}}

collectAllocs :: (VarInfo a4) -> (OpInfo 
                            a1 a2 a3 a4) -> Prelude.Int -> ([]
                            ((,) Interval.IntervalDesc PhysReg)) ->
                            ((,)
                            ((,) ([] ((,) VarId PhysReg))
                            ([] a3)) ([] a3)) -> a4 -> AssnState 
                            a1
                            ((,)
                            ((,) ([] ((,) VarId PhysReg))
                            ([] a3)) ([] a3))
collectAllocs vinfo oinfo opid ints acc v =
  let {vid = varId vinfo v} in
  let {
   v_ints = Prelude.filter (\x ->
              isWithin (Prelude.fst x) vid opid) ints}
  in
  case v_ints of {
   [] -> State.pure acc;
   (:) p l ->
    case p of {
     (,) int reg ->
      case acc of {
       (,) p0 saves' ->
        case p0 of {
         (,) allocs' restores' ->
          State.bind (\res ->
            case res of {
             (,) rs ss ->
              State.pure ((,) ((,) ((:) ((,) vid reg) allocs')
                ((Prelude.++) rs restores')) ((Prelude.++) ss saves'))})
            (savesAndRestores oinfo (unsafeCoerce opid) vid reg
              int)}}}}

doAllocations :: (VarInfo a4) -> (OpInfo 
                            a1 a2 a3 a4) -> ([]
                            ((,) Interval.IntervalDesc PhysReg)) ->
                            a2 -> AssnState a1 ([] a3)
doAllocations vinfo oinfo ints op =
  State.bind (\assn ->
    let {opid = assnOpId assn} in
    let {vars = Prelude.fst (opRefs oinfo op)} in
    State.bind (\res ->
      case res of {
       (,) y saves ->
        case y of {
         (,) allocs restores ->
          let {op' = applyAllocs oinfo op allocs} in
          State.bind (\x ->
            State.pure ((Prelude.++) restores ((Prelude.++) op' saves)))
            (State.modify (\assn' -> Build_AssnStateInfo
              ((Prelude.succ) ((Prelude.succ) opid))
              (assnAcc assn')))}})
      (State.forFoldM ((,) ((,) [] []) []) vars
        (collectAllocs vinfo oinfo opid ints))) State.get

generateMoves :: (OpInfo a1 a2 a3 a4) -> ([]
                            ((,) (Prelude.Maybe PhysReg)
                            (Prelude.Maybe PhysReg))) ->
                            AssnState a1 ([] a3)
generateMoves oinfo moves =
  State.forFoldM [] moves (\acc mv ->
    State.bind (\mops ->
      State.pure
        (case mops of {
          Prelude.Just ops -> (Prelude.++) ops acc;
          Prelude.Nothing -> acc}))
      (case mv of {
        (,) o o0 ->
         case o of {
          Prelude.Just sreg ->
           case o0 of {
            Prelude.Just dreg ->
             State.fmap (\x -> Prelude.Just x)
               (moveOpM oinfo sreg dreg);
            Prelude.Nothing ->
             State.fmap (\x -> Prelude.Just x)
               (saveOpM oinfo sreg Prelude.Nothing)};
          Prelude.Nothing ->
           case o0 of {
            Prelude.Just dreg ->
             State.fmap (\x -> Prelude.Just x)
               (restoreOpM oinfo Prelude.Nothing dreg);
            Prelude.Nothing -> State.pure Prelude.Nothing}}}))

resolveMappings :: (OpInfo a1 a2 a3 a4) -> Prelude.Int
                              -> ([] a2) -> ([] a3) -> (Data.IntMap.IntMap
                              ((,) Graph.Graph Graph.Graph)) ->
                              AssnState a1 ([] a3)
resolveMappings oinfo bid ops ops' mappings =
  case Data.IntMap.lookup bid mappings of {
   Prelude.Just graphs ->
    case graphs of {
     (,) gbeg gend ->
      State.bind (\bmoves ->
        let {ops'' = (Prelude.++) bmoves ops'} in
        State.bind (\emoves ->
          State.pure
            (case ops of {
              [] -> (Prelude.++) ops'' emoves;
              (:) o os ->
               case ops'' of {
                [] -> (Prelude.++) ops'' emoves;
                (:) o'' os'' ->
                 case opKind oinfo (Seq.last o os) of {
                  IsBranch ->
                   (Prelude.++) (Seq.belast o'' os'')
                     ((Prelude.++) emoves ((:) (Seq.last o'' os'') []));
                  _ -> (Prelude.++) ops'' emoves}}}))
          (generateMoves oinfo
            (unsafeCoerce
              (Graph.topsort (Fintype.ordinal_eqType maxReg) gend))))
        (generateMoves oinfo
          (unsafeCoerce
            (Graph.topsort (Fintype.ordinal_eqType maxReg) gbeg)))};
   Prelude.Nothing -> State.pure ops'}

considerOps :: (OpInfo a1 a4 a5 a6) ->
                          (BlockInfo a2 a3 a4 a5) -> (a4 ->
                          AssnState a1 ([] a5)) ->
                          (Data.IntMap.IntMap ((,) Graph.Graph Graph.Graph))
                          -> ([] a2) -> State.State
                          (AssnStateInfo a1) ([] a3)
considerOps oinfo binfo f mappings =
  State.mapM (\blk ->
    let {ops = blockOps binfo blk} in
    State.bind (\ops' ->
      let {bid = blockId binfo blk} in
      State.bind (\ops'' ->
        State.pure (setBlockOps binfo blk ops''))
        (resolveMappings oinfo bid ops ops' mappings))
      (State.concatMapM f ops))

assignRegNum :: (VarInfo a6) -> (OpInfo 
                           a1 a4 a5 a6) -> (BlockInfo a2 a3 
                           a4 a5) -> ScanStateDesc ->
                           (Data.IntMap.IntMap BlockMoves) -> ([]
                           a2) -> a1 -> (,) ([] a3) a1
assignRegNum vinfo oinfo binfo sd mappings blocks acc =
  case considerOps oinfo binfo
         (doAllocations vinfo oinfo
           (Prelude.map (\x -> (,)
             (Interval.getIntervalDesc
               (
                 (LinearScan.Utils.nth (nextInterval sd)
                   (intervals sd) (Prelude.fst x))))
             (Prelude.snd x))
             ((Prelude.++) (handled sd)
               ((Prelude.++) (active sd) (inactive sd)))))
         mappings blocks (Build_AssnStateInfo ((Prelude.succ) 0)
         acc) of {
   (,) blocks' assn -> (,) blocks' (assnAcc assn)}

coq_SSMorph_rect :: ScanStateDesc ->
                               ScanStateDesc -> (() -> a1) -> a1
coq_SSMorph_rect sd1 sd2 f =
  f __

coq_SSMorph_rec :: ScanStateDesc ->
                              ScanStateDesc -> (() -> a1) -> a1
coq_SSMorph_rec sd1 sd2 f =
  coq_SSMorph_rect sd1 sd2 f

coq_SSMorphLen_rect :: ScanStateDesc ->
                                  ScanStateDesc -> (() -> () -> a1)
                                  -> a1
coq_SSMorphLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphLen_rec :: ScanStateDesc ->
                                 ScanStateDesc -> (() -> () -> a1)
                                 -> a1
coq_SSMorphLen_rec sd1 sd2 f =
  coq_SSMorphLen_rect sd1 sd2 f

coq_SSMorphHasLen_rect :: ScanStateDesc ->
                                     ScanStateDesc -> (() -> () ->
                                     a1) -> a1
coq_SSMorphHasLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphHasLen_rec :: ScanStateDesc ->
                                    ScanStateDesc -> (() -> () ->
                                    a1) -> a1
coq_SSMorphHasLen_rec sd1 sd2 f =
  coq_SSMorphHasLen_rect sd1 sd2 f

data SSInfo p =
   Build_SSInfo ScanStateDesc p

coq_SSInfo_rect :: ScanStateDesc ->
                              (ScanStateDesc -> a1 -> () -> a2) ->
                              (SSInfo a1) -> a2
coq_SSInfo_rect startDesc f s =
  case s of {
   Build_SSInfo x x0 -> f x x0 __}

coq_SSInfo_rec :: ScanStateDesc ->
                             (ScanStateDesc -> a1 -> () -> a2) ->
                             (SSInfo a1) -> a2
coq_SSInfo_rec startDesc =
  coq_SSInfo_rect startDesc

thisDesc :: ScanStateDesc -> (SSInfo a1) ->
                       ScanStateDesc
thisDesc startDesc s =
  case s of {
   Build_SSInfo thisDesc0 thisHolds0 -> thisDesc0}

thisHolds :: ScanStateDesc -> (SSInfo 
                        a1) -> a1
thisHolds startDesc s =
  case s of {
   Build_SSInfo thisDesc0 thisHolds0 -> thisHolds0}

type SState p q a =
  IState.IState SSError (SSInfo p) (SSInfo q) a

withScanState :: ScanStateDesc ->
                            (ScanStateDesc -> () ->
                            SState a2 a3 a1) -> SState 
                            a2 a3 a1
withScanState pre f =
  stbind (\i -> f (thisDesc pre i) __) IState.iget

withScanStatePO :: ScanStateDesc ->
                              (ScanStateDesc -> () ->
                              SState () () a1) -> SState
                              () () a1
withScanStatePO pre f i =
  case i of {
   Build_SSInfo thisDesc0 _ ->
    let {f0 = f thisDesc0 __} in
    let {x = Build_SSInfo thisDesc0 __} in
    let {x0 = f0 x} in
    case x0 of {
     Prelude.Left s -> Prelude.Left s;
     Prelude.Right p -> Prelude.Right
      (case p of {
        (,) a0 s -> (,) a0
         (case s of {
           Build_SSInfo thisDesc1 _ -> Build_SSInfo
            thisDesc1 __})})}}

liftLen :: ScanStateDesc -> (ScanStateDesc ->
                      SState () () a1) -> SState 
                      () () a1
liftLen pre f _top_assumption_ =
  let {
   _evar_0_ = \sd ->
    let {ss = Build_SSInfo sd __} in
    let {_evar_0_ = \err -> Prelude.Left err} in
    let {
     _evar_0_0 = \_top_assumption_0 ->
      let {
       _evar_0_0 = \x _top_assumption_1 ->
        let {
         _evar_0_0 = \sd' -> Prelude.Right ((,) x (Build_SSInfo sd'
          __))}
        in
        case _top_assumption_1 of {
         Build_SSInfo x0 x1 -> _evar_0_0 x0}}
      in
      case _top_assumption_0 of {
       (,) x x0 -> _evar_0_0 x x0}}
    in
    case f sd ss of {
     Prelude.Left x -> _evar_0_ x;
     Prelude.Right x -> _evar_0_0 x}}
  in
  case _top_assumption_ of {
   Build_SSInfo x x0 -> _evar_0_ x}

weakenHasLen_ :: ScanStateDesc -> SState 
                            () () ()
weakenHasLen_ pre hS =
  Prelude.Right ((,) ()
    (case hS of {
      Build_SSInfo thisDesc0 _ -> Build_SSInfo thisDesc0
       __}))

strengthenHasLen :: ScanStateDesc ->
                               ScanStateDesc -> Prelude.Maybe 
                               ()
strengthenHasLen pre sd =
  let {_evar_0_ = \_ -> Prelude.Nothing} in
  let {_evar_0_0 = \_a_ _l_ -> Prelude.Just __} in
  case unhandled sd of {
   [] -> _evar_0_ __;
   (:) x x0 -> _evar_0_0 x x0}

withCursor :: ScanStateDesc -> (ScanStateDesc
                         -> () -> SState () a1 a2) ->
                         SState () a1 a2
withCursor pre f x =
  case x of {
   Build_SSInfo thisDesc0 _ ->
    f thisDesc0 __ (Build_SSInfo thisDesc0 __)}

moveUnhandledToActive :: ScanStateDesc ->
                                    PhysReg -> SState 
                                    () () ()
moveUnhandledToActive pre reg x =
  case x of {
   Build_SSInfo thisDesc0 _ ->
    case thisDesc0 of {
     Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
      unhandled0 active0 inactive0 handled0 ->
      case unhandled0 of {
       [] -> Logic.coq_False_rect;
       (:) p unhandled1 ->
        let {
         _evar_0_ = \_ -> Prelude.Right ((,) () (Build_SSInfo
          (Build_ScanStateDesc nextInterval0 intervals0
          fixedIntervals0 unhandled1 ((:) ((,) (Prelude.fst p) reg) active0)
          inactive0 handled0) __))}
        in
        let {
         _evar_0_0 = \_ -> Prelude.Left (ERegisterAlreadyAssigned
          ( reg))}
        in
        case Prelude.not
               (Ssrbool.in_mem (unsafeCoerce reg)
                 (Ssrbool.mem
                   (Seq.seq_predType
                     (Fintype.ordinal_eqType maxReg))
                   (unsafeCoerce (Prelude.map (\i -> Prelude.snd i) active0)))) of {
         Prelude.True -> _evar_0_ __;
         Prelude.False -> _evar_0_0 __}}}}

moveActiveToHandled :: ScanStateDesc ->
                                  Eqtype.Equality__Coq_sort ->
                                  Specif.Coq_sig2 ScanStateDesc
moveActiveToHandled sd x =
  Build_ScanStateDesc (nextInterval sd)
    (intervals sd) (fixedIntervals sd)
    (unhandled sd)
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (nextInterval sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (active sd)))) (inactive sd) ((:)
    (unsafeCoerce x) (handled sd))

moveActiveToInactive :: ScanStateDesc ->
                                   Eqtype.Equality__Coq_sort ->
                                   Specif.Coq_sig2 ScanStateDesc
moveActiveToInactive sd x =
  Build_ScanStateDesc (nextInterval sd)
    (intervals sd) (fixedIntervals sd)
    (unhandled sd)
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (nextInterval sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (active sd)))) ((:) (unsafeCoerce x)
    (inactive sd)) (handled sd)

moveInactiveToActive :: ScanStateDesc ->
                                   Eqtype.Equality__Coq_sort ->
                                   Specif.Coq_sig2 ScanStateDesc
moveInactiveToActive sd x =
  Build_ScanStateDesc (nextInterval sd)
    (intervals sd) (fixedIntervals sd)
    (unhandled sd) ((:) (unsafeCoerce x) (active sd))
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (nextInterval sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (inactive sd)))) (handled sd)

moveInactiveToHandled :: ScanStateDesc ->
                                    Eqtype.Equality__Coq_sort ->
                                    Specif.Coq_sig2 ScanStateDesc
moveInactiveToHandled sd x =
  Build_ScanStateDesc (nextInterval sd)
    (intervals sd) (fixedIntervals sd)
    (unhandled sd) (active sd)
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (nextInterval sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (inactive sd)))) ((:) (unsafeCoerce x)
    (handled sd))

splitInterval :: ScanStateDesc -> IntervalId
                            -> Interval.SplitPosition -> Prelude.Bool ->
                            Prelude.Either SSError
                            (Prelude.Maybe ScanStateSig)
splitInterval sd uid pos forCurrent =
  let {
   _evar_0_ = \_nextInterval_ ints _fixedIntervals_ unh _active_ _inactive_ _handled_ uid0 ->
    let {int = LinearScan.Utils.nth _nextInterval_ ints uid0} in
    let {
     _evar_0_ = \_ -> Prelude.Left (ECannotSplitSingleton ( uid0))}
    in
    let {
     _evar_0_0 = \_top_assumption_ ->
      let {
       _evar_0_0 = \u beg us ->
        let {
         _evar_0_0 = \splitPos ->
          let {
           _evar_0_0 = \_ ->
            (Prelude.flip (Prelude.$)) __ (\_ ->
              let {
               _evar_0_0 = \iv ib ie _iknd_ rds ->
                let {
                 _top_assumption_0 = Interval.intervalSpan rds splitPos iv ib
                                       ie _iknd_}
                in
                let {
                 _evar_0_0 = \_top_assumption_1 ->
                  let {
                   _evar_0_0 = \_top_assumption_2 _top_assumption_3 ->
                    let {
                     _evar_0_0 = \_top_assumption_4 ->
                      let {
                       _evar_0_0 = \_ ->
                        let {
                         _evar_0_0 = \_ ->
                          let {
                           _evar_0_0 = \_ ->
                            (Prelude.flip (Prelude.$)) __
                              (let {
                                new_unhandled = Build_ScanStateDesc
                                 ((Prelude.succ) _nextInterval_)
                                 (LinearScan.Utils.snoc _nextInterval_
                                   (LinearScan.Utils.set_nth _nextInterval_
                                     ints uid0 _top_assumption_2)
                                   _top_assumption_4) _fixedIntervals_
                                 (Data.List.insertBy
                                   (Data.Ord.comparing Prelude.snd) ((,)
                                   ( _nextInterval_)
                                   (Interval.ibeg _top_assumption_4)) ((:)
                                   (Prelude.id ((,) u beg))
                                   (Prelude.map Prelude.id us)))
                                 (Prelude.map Prelude.id _active_)
                                 (Prelude.map Prelude.id _inactive_)
                                 (Prelude.map Prelude.id _handled_)}
                               in
                               \_ -> Prelude.Right (Prelude.Just
                               (packScanState InUse
                                 new_unhandled)))}
                          in
                           _evar_0_0 __}
                        in
                         _evar_0_0 __}
                      in
                      let {
                       _evar_0_1 = \_ -> Prelude.Left
                        (ECannotSplitSingleton ( uid0))}
                      in
                      case (Prelude.<=) ((Prelude.succ) beg)
                             (Interval.ibeg _top_assumption_4) of {
                       Prelude.True -> _evar_0_0 __;
                       Prelude.False -> _evar_0_1 __}}
                    in
                    let {
                     _evar_0_1 = \_ ->
                      let {
                       _evar_0_1 = Prelude.Left
                        (ECannotSplitSingleton ( uid0))}
                      in
                      let {
                       _evar_0_2 = let {
                                    _evar_0_2 = \_ ->
                                     let {
                                      _evar_0_2 = \_ ->
                                       let {
                                        set_int_desc = Build_ScanStateDesc
                                         _nextInterval_
                                         (LinearScan.Utils.set_nth
                                           _nextInterval_ ints uid0
                                           _top_assumption_2)
                                         _fixedIntervals_ ((:) ((,) u beg)
                                         us) _active_ _inactive_ _handled_}
                                       in
                                       Prelude.Right (Prelude.Just
                                       (packScanState
                                         InUse set_int_desc))}
                                     in
                                      _evar_0_2 __}
                                   in
                                    _evar_0_2 __}
                      in
                      case forCurrent of {
                       Prelude.True -> _evar_0_1;
                       Prelude.False -> _evar_0_2}}
                    in
                    case _top_assumption_3 of {
                     Prelude.Just x -> (\_ -> _evar_0_0 x);
                     Prelude.Nothing -> _evar_0_1}}
                  in
                  let {
                   _evar_0_1 = \_top_assumption_2 ->
                    let {
                     _evar_0_1 = \_top_assumption_3 ->
                      let {
                       _evar_0_1 = \_ ->
                        (Prelude.flip (Prelude.$)) __
                          (let {
                            new_unhandled = Build_ScanStateDesc
                             ((Prelude.succ) _nextInterval_)
                             (LinearScan.Utils.snoc _nextInterval_ ints
                               _top_assumption_3) _fixedIntervals_
                             (Data.List.insertBy
                               (Data.Ord.comparing Prelude.snd) ((,)
                               ( _nextInterval_)
                               (Interval.ibeg _top_assumption_3)) ((:)
                               (Prelude.id ((,) u beg))
                               (Prelude.map Prelude.id us)))
                             (Prelude.map Prelude.id _active_)
                             (Prelude.map Prelude.id _inactive_)
                             (Prelude.map Prelude.id _handled_)}
                           in
                           \_ -> Prelude.Right (Prelude.Just
                           (packScanState InUse
                             new_unhandled)))}
                      in
                      let {
                       _evar_0_2 = \_ -> Prelude.Left
                        (ECannotSplitSingleton ( uid0))}
                      in
                      case (Prelude.<=) ((Prelude.succ) beg)
                             (Interval.ibeg _top_assumption_3) of {
                       Prelude.True -> _evar_0_1 __;
                       Prelude.False -> _evar_0_2 __}}
                    in
                    let {_evar_0_2 = \_ -> Logic.coq_False_rect} in
                    case _top_assumption_2 of {
                     Prelude.Just x -> (\_ -> _evar_0_1 x);
                     Prelude.Nothing -> _evar_0_2}}
                  in
                  case _top_assumption_1 of {
                   Prelude.Just x -> _evar_0_0 x;
                   Prelude.Nothing -> _evar_0_1}}
                in
                case _top_assumption_0 of {
                 (,) x x0 -> _evar_0_0 x x0 __}}
              in
              case int of {
               Interval.Build_IntervalDesc x x0 x1 x2 x3 ->
                _evar_0_0 x x0 x1 x2 x3})}
          in
          let {
           _evar_0_1 = \_ -> Prelude.Left (ECannotSplitSingleton
            ( uid0))}
          in
          case (Prelude.&&)
                 ((Prelude.<=) ((Prelude.succ) (Interval.ibeg ( int)))
                   splitPos)
                 ((Prelude.<=) ((Prelude.succ) splitPos)
                   (Interval.iend ( int))) of {
           Prelude.True -> _evar_0_0 __;
           Prelude.False -> _evar_0_1 __}}
        in
        let {_evar_0_1 = Prelude.Right Prelude.Nothing} in
        case Interval.splitPosition ( int) pos of {
         Prelude.Just x -> _evar_0_0 x;
         Prelude.Nothing -> _evar_0_1}}
      in
      (\us _ ->
      case _top_assumption_ of {
       (,) x x0 -> _evar_0_0 x x0 us})}
    in
    case unh of {
     [] -> _evar_0_ __;
     (:) x x0 -> _evar_0_0 x x0 __}}
  in
  case sd of {
   Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
    _evar_0_ x x0 x1 x2 x3 x4 x5 uid}

splitCurrentInterval :: ScanStateDesc ->
                                   Interval.SplitPosition -> SState
                                   () () ()
splitCurrentInterval pre pos ssi =
  let {
   _evar_0_ = \desc ->
    let {
     _evar_0_ = \_nextInterval_ intervals0 _fixedIntervals_ unhandled0 _active_ _inactive_ _handled_ ->
      let {_evar_0_ = \_ _ _ _ _ -> Logic.coq_False_rect} in
      let {
       _evar_0_0 = \_top_assumption_ ->
        let {
         _evar_0_0 = \uid beg us ->
          let {
           desc0 = Build_ScanStateDesc _nextInterval_ intervals0
            _fixedIntervals_ ((:) ((,) uid beg) us) _active_ _inactive_
            _handled_}
          in
          (\_ _ _ _ ->
          let {
           _top_assumption_0 = splitInterval desc0 uid pos
                                 Prelude.True}
          in
          let {_evar_0_0 = \err -> Prelude.Left err} in
          let {
           _evar_0_1 = \_top_assumption_1 ->
            let {
             _evar_0_1 = \_top_assumption_2 -> Prelude.Right ((,) ()
              (Build_SSInfo _top_assumption_2 __))}
            in
            let {
             _evar_0_2 = Prelude.Left (ECannotSplitSingleton
              ( uid))}
            in
            case _top_assumption_1 of {
             Prelude.Just x -> _evar_0_1 x;
             Prelude.Nothing -> _evar_0_2}}
          in
          case _top_assumption_0 of {
           Prelude.Left x -> _evar_0_0 x;
           Prelude.Right x -> _evar_0_1 x})}
        in
        (\us _ ->
        case _top_assumption_ of {
         (,) x x0 -> _evar_0_0 x x0 us})}
      in
      case unhandled0 of {
       [] -> _evar_0_ __;
       (:) x x0 -> _evar_0_0 x x0 __}}
    in
    case desc of {
     Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
      _evar_0_ x x0 x1 x2 x3 x4 x5 __ __ __}}
  in
  case ssi of {
   Build_SSInfo x x0 -> _evar_0_ x __}

splitAssignedIntervalForReg :: ScanStateDesc ->
                                          PhysReg ->
                                          Interval.SplitPosition ->
                                          Prelude.Bool -> SState 
                                          () () ()
splitAssignedIntervalForReg pre reg pos trueForActives ssi =
  let {
   _evar_0_ = \desc ->
    let {
     intlist = case trueForActives of {
                Prelude.True -> active desc;
                Prelude.False -> inactive desc}}
    in
    (Prelude.flip (Prelude.$)) __ (\_ ->
      let {
       intids = Prelude.map (\i -> Prelude.fst i)
                  (Prelude.filter (\i ->
                    Eqtype.eq_op (Fintype.ordinal_eqType maxReg)
                      (Prelude.snd (unsafeCoerce i)) (unsafeCoerce reg))
                    intlist)}
      in
      (Prelude.flip (Prelude.$)) __ (\_ ->
        let {
         _evar_0_ = \_nextInterval_ intervals0 _fixedIntervals_ _unhandled_ active0 inactive0 _handled_ intlist0 intids0 ->
          let {
           desc0 = Build_ScanStateDesc _nextInterval_ intervals0
            _fixedIntervals_ _unhandled_ active0 inactive0 _handled_}
          in
          (\_ _ _ _ ->
          let {_evar_0_ = \_ -> Prelude.Left ENoIntervalsToSplit}
          in
          let {
           _evar_0_0 = \aid aids iHaids ->
            let {
             _top_assumption_ = splitInterval desc0 aid pos
                                  Prelude.False}
            in
            let {_evar_0_0 = \err -> Prelude.Left err} in
            let {
             _evar_0_1 = \_top_assumption_0 ->
              let {
               _evar_0_1 = \_top_assumption_1 -> Prelude.Right ((,) ()
                (let {
                  _evar_0_1 = \_ ->
                   (Prelude.flip (Prelude.$)) __
                     (let {
                       act_to_inact = Build_ScanStateDesc
                        (nextInterval _top_assumption_1)
                        (intervals _top_assumption_1)
                        (fixedIntervals _top_assumption_1)
                        (unhandled _top_assumption_1)
                        (unsafeCoerce
                          (Seq.rem
                            (Eqtype.prod_eqType
                              (Fintype.ordinal_eqType
                                (nextInterval _top_assumption_1))
                              (Fintype.ordinal_eqType maxReg))
                            (unsafeCoerce ((,) ( aid) reg))
                            (unsafeCoerce
                              (active _top_assumption_1)))) ((:)
                        ((,) ( aid) reg)
                        (inactive _top_assumption_1))
                        (handled _top_assumption_1)}
                      in
                      \_ -> Build_SSInfo act_to_inact __)}
                 in
                 let {
                  _evar_0_2 = \_ -> Build_SSInfo _top_assumption_1
                   __}
                 in
                 case Ssrbool.in_mem (unsafeCoerce ((,) ( aid) reg))
                        (Ssrbool.mem
                          (Seq.seq_predType
                            (Eqtype.prod_eqType
                              (Fintype.ordinal_eqType
                                (nextInterval _top_assumption_1))
                              (Fintype.ordinal_eqType maxReg)))
                          (unsafeCoerce
                            (active _top_assumption_1))) of {
                  Prelude.True -> _evar_0_1 __;
                  Prelude.False -> _evar_0_2 __}))}
              in
              let {
               _evar_0_2 = Prelude.Left (ECannotSplitSingleton
                ( aid))}
              in
              case _top_assumption_0 of {
               Prelude.Just x -> _evar_0_1 x;
               Prelude.Nothing -> _evar_0_2}}
            in
            case _top_assumption_ of {
             Prelude.Left x -> _evar_0_0 x;
             Prelude.Right x -> _evar_0_1 x}}
          in
          Datatypes.list_rect _evar_0_ (\aid aids iHaids _ ->
            _evar_0_0 aid aids iHaids) intids0 __)}
        in
        case desc of {
         Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
          _evar_0_ x x0 x1 x2 x3 x4 x5 intlist intids})) __ __ __}
  in
  case ssi of {
   Build_SSInfo x x0 -> _evar_0_ x __}

splitActiveIntervalForReg :: ScanStateDesc ->
                                        PhysReg -> Prelude.Int ->
                                        SState () () ()
splitActiveIntervalForReg pre reg pos =
  splitAssignedIntervalForReg pre reg (Interval.BeforePos pos)
    Prelude.True

splitAnyInactiveIntervalForReg :: ScanStateDesc ->
                                             PhysReg ->
                                             SState () () ()
splitAnyInactiveIntervalForReg pre reg ss =
  (Prelude.flip (Prelude.$)) (\s ->
    splitAssignedIntervalForReg s reg Interval.EndOfLifetimeHole
      Prelude.False) (\_top_assumption_ ->
    let {_top_assumption_0 = _top_assumption_ pre ss} in
    let {_evar_0_ = \err -> Prelude.Right ((,) () ss)} in
    let {
     _evar_0_0 = \_top_assumption_1 ->
      let {_evar_0_0 = \_the_1st_wildcard_ ss' -> Prelude.Right ((,) () ss')}
      in
      case _top_assumption_1 of {
       (,) x x0 -> _evar_0_0 x x0}}
    in
    case _top_assumption_0 of {
     Prelude.Left x -> _evar_0_ x;
     Prelude.Right x -> _evar_0_0 x})

intersectsWithFixedInterval :: ScanStateDesc ->
                                          PhysReg ->
                                          SState () ()
                                          (Prelude.Maybe Prelude.Int)
intersectsWithFixedInterval pre reg =
  withCursor pre (\sd _ ->
    let {int = curIntDetails sd} in
    return_
      (LinearScan.Utils.vfoldl' maxReg (\mx v ->
        Lib.option_choose mx
          (case v of {
            Prelude.Just i -> Interval.intervalIntersectionPoint ( int) ( i);
            Prelude.Nothing -> Prelude.Nothing})) Prelude.Nothing
        (fixedIntervals sd)))

updateRegisterPos :: Prelude.Int -> ([]
                                (Prelude.Maybe Prelude.Int)) -> Prelude.Int
                                -> (Prelude.Maybe Prelude.Int) -> []
                                (Prelude.Maybe Prelude.Int)
updateRegisterPos n v r p =
  case p of {
   Prelude.Just x ->
    LinearScan.Utils.set_nth n v r (Prelude.Just
      (case LinearScan.Utils.nth n v r of {
        Prelude.Just n0 -> Prelude.min n0 x;
        Prelude.Nothing -> x}));
   Prelude.Nothing -> v}

tryAllocateFreeReg :: ScanStateDesc -> SState
                                 () ()
                                 (Prelude.Maybe
                                 (SState () () PhysReg))
tryAllocateFreeReg pre =
  withCursor pre (\sd _ ->
    let {
     go = \f v p ->
      case p of {
       (,) i r -> updateRegisterPos maxReg v r (f i)}}
    in
    let {
     freeUntilPos' = Data.List.foldl' (go (\x -> Prelude.Just 0))
                       (Data.List.replicate maxReg
                         Prelude.Nothing) (active sd)}
    in
    let {
     intersectingIntervals = Prelude.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (curIntDetails sd))
                                 (
                                   (LinearScan.Utils.nth
                                     (nextInterval sd)
                                     (intervals sd)
                                     (Prelude.fst x))))
                               (inactive sd)}
    in
    let {
     freeUntilPos = Data.List.foldl'
                      (go (\i ->
                        Interval.intervalIntersectionPoint
                          (
                            (LinearScan.Utils.nth
                              (nextInterval sd)
                              (intervals sd) i))
                          ( (curIntDetails sd)))) freeUntilPos'
                      intersectingIntervals}
    in
    case registerWithHighestPos freeUntilPos of {
     (,) reg mres ->
      let {
       success = stbind (\x -> return_ reg)
                   (moveUnhandledToActive pre reg)}
      in
      let {
       maction = case mres of {
                  Prelude.Just n ->
                   case Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce n)
                          (unsafeCoerce 0) of {
                    Prelude.True -> Prelude.Nothing;
                    Prelude.False -> Prelude.Just
                     (case (Prelude.<=) ((Prelude.succ)
                             (Interval.intervalEnd
                               ( (curIntDetails sd)))) n of {
                       Prelude.True -> success;
                       Prelude.False ->
                        stbind (\x ->
                          stbind (\x0 -> return_ reg)
                            (moveUnhandledToActive pre reg))
                          (splitCurrentInterval pre
                            (Interval.BeforePos n))})};
                  Prelude.Nothing -> Prelude.Just success}}
      in
      return_ maction})

allocateBlockedReg :: ScanStateDesc -> SState
                                 () () (Prelude.Maybe PhysReg)
allocateBlockedReg pre =
  withCursor pre (\sd _ ->
    let {start = Interval.intervalStart ( (curIntDetails sd))} in
    let {pos = curPosition sd} in
    let {
     go = \v p ->
      case p of {
       (,) i r ->
        let {
         atPos = \u ->
          Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce pos)
            (unsafeCoerce (Range.uloc u))}
        in
        let {
         pos' = case Interval.findIntervalUsePos
                       (Interval.getIntervalDesc
                         (
                           (LinearScan.Utils.nth (nextInterval sd)
                             (intervals sd) i))) atPos of {
                 Prelude.Just p0 -> Prelude.Just 0;
                 Prelude.Nothing ->
                  Interval.nextUseAfter
                    (Interval.getIntervalDesc
                      (
                        (LinearScan.Utils.nth (nextInterval sd)
                          (intervals sd) i))) start}}
        in
        updateRegisterPos maxReg v r pos'}}
    in
    let {
     nextUsePos' = Data.List.foldl' go
                     (Data.List.replicate maxReg Prelude.Nothing)
                     (active sd)}
    in
    let {
     intersectingIntervals = Prelude.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (curIntDetails sd))
                                 (
                                   (LinearScan.Utils.nth
                                     (nextInterval sd)
                                     (intervals sd)
                                     (Prelude.fst x))))
                               (inactive sd)}
    in
    let {nextUsePos = Data.List.foldl' go nextUsePos' intersectingIntervals}
    in
    case registerWithHighestPos nextUsePos of {
     (,) reg mres ->
      case case mres of {
            Prelude.Just n -> (Prelude.<=) ((Prelude.succ) n) start;
            Prelude.Nothing -> Prelude.False} of {
       Prelude.True ->
        stbind (\x ->
          stbind (\mloc ->
            stbind (\x0 ->
              stbind (\x1 -> return_ Prelude.Nothing)
                (weakenHasLen_ pre))
              (case mloc of {
                Prelude.Just n ->
                 splitCurrentInterval pre (Interval.BeforePos n);
                Prelude.Nothing -> return_ ()}))
            (intersectsWithFixedInterval pre reg))
          (splitCurrentInterval pre
            Interval.BeforeFirstUsePosReqReg);
       Prelude.False ->
        stbind (\x ->
          stbind (\x0 ->
            stbind (\mloc ->
              stbind (\x1 ->
                stbind (\x2 ->
                  return_ (Prelude.Just reg))
                  (moveUnhandledToActive pre reg))
                (case mloc of {
                  Prelude.Just n ->
                   splitCurrentInterval pre (Interval.BeforePos n);
                  Prelude.Nothing -> return_ ()}))
              (intersectsWithFixedInterval pre reg))
            (splitActiveIntervalForReg pre reg pos))
          (splitAnyInactiveIntervalForReg pre reg)}})

morphlen_transport :: ScanStateDesc ->
                                 ScanStateDesc ->
                                 IntervalId -> IntervalId
morphlen_transport b b' = GHC.Base.id
  

mt_fst :: ScanStateDesc -> ScanStateDesc ->
                     ((,) IntervalId PhysReg) -> (,)
                     IntervalId PhysReg
mt_fst b b' x =
  case x of {
   (,) xid reg -> (,) (morphlen_transport b b' xid) reg}

type Coq_int_reg_seq =
  [] ((,) IntervalId PhysReg)

type Coq_intermediate_result =
  Specif.Coq_sig2 ScanStateDesc

goActive :: Prelude.Int -> ScanStateDesc ->
                       ScanStateDesc -> ((,) IntervalId
                       PhysReg) -> Coq_int_reg_seq ->
                       Coq_intermediate_result
goActive pos sd z x xs =
  case (Prelude.<=) ((Prelude.succ)
         (Interval.intervalEnd
           (
             (LinearScan.Utils.nth (nextInterval z)
               (intervals z) (Prelude.fst x))))) pos of {
   Prelude.True -> moveActiveToHandled z (unsafeCoerce x);
   Prelude.False ->
    case Prelude.not
           (Interval.intervalCoversPos
             (
               (LinearScan.Utils.nth (nextInterval z)
                 (intervals z) (Prelude.fst x))) pos) of {
     Prelude.True -> moveActiveToInactive z (unsafeCoerce x);
     Prelude.False -> z}}

checkActiveIntervals :: ScanStateDesc -> Prelude.Int ->
                                   SState () () ()
checkActiveIntervals pre pos =
  withScanStatePO pre (\sd _ ->
    let {
     res = Lib.dep_foldl_inv (\s ->
             Eqtype.prod_eqType
               (Fintype.ordinal_eqType (nextInterval s))
               (Fintype.ordinal_eqType maxReg)) sd
             (unsafeCoerce (active sd))
             (Data.List.length (active sd))
             (unsafeCoerce active)
             (unsafeCoerce (\x x0 _ -> mt_fst x x0))
             (unsafeCoerce (\x _ x0 x1 _ ->
               goActive pos sd x x0 x1))}
    in
    IState.iput (Build_SSInfo res __))

moveInactiveToActive' :: ScanStateDesc -> ((,)
                                    IntervalId PhysReg)
                                    -> Coq_int_reg_seq ->
                                    Prelude.Either SSError
                                    (Specif.Coq_sig2 ScanStateDesc)
moveInactiveToActive' z x xs =
  let {
   filtered_var = Prelude.not
                    (Ssrbool.in_mem (Prelude.snd (unsafeCoerce x))
                      (Ssrbool.mem
                        (Seq.seq_predType
                          (Fintype.ordinal_eqType maxReg))
                        (unsafeCoerce
                          (Prelude.map (\i -> Prelude.snd i)
                            (active z)))))}
  in
  case filtered_var of {
   Prelude.True ->
    let {filtered_var0 = moveInactiveToActive z (unsafeCoerce x)}
    in
    Prelude.Right filtered_var0;
   Prelude.False -> Prelude.Left (ERegisterAssignmentsOverlap
    ( (Prelude.snd x)))}

goInactive :: Prelude.Int -> ScanStateDesc ->
                         ScanStateDesc -> ((,) IntervalId
                         PhysReg) -> Coq_int_reg_seq ->
                         Prelude.Either SSError
                         Coq_intermediate_result
goInactive pos sd z x xs =
  let {f = \sd' -> Prelude.Right sd'} in
  case (Prelude.<=) ((Prelude.succ)
         (Interval.intervalEnd
           (
             (LinearScan.Utils.nth (nextInterval z)
               (intervals z) (Prelude.fst x))))) pos of {
   Prelude.True ->
    let {filtered_var = moveInactiveToHandled z (unsafeCoerce x)}
    in
    f filtered_var;
   Prelude.False ->
    case Interval.intervalCoversPos
           (
             (LinearScan.Utils.nth (nextInterval z)
               (intervals z) (Prelude.fst x))) pos of {
     Prelude.True ->
      let {filtered_var = moveInactiveToActive' z x xs} in
      case filtered_var of {
       Prelude.Left err -> Prelude.Left err;
       Prelude.Right s -> f s};
     Prelude.False -> f z}}

checkInactiveIntervals :: ScanStateDesc -> Prelude.Int
                                     -> SState () () ()
checkInactiveIntervals pre pos =
  withScanStatePO pre (\sd _ ->
    let {
     eres = Lib.dep_foldl_invE (\s ->
              Eqtype.prod_eqType
                (Fintype.ordinal_eqType (nextInterval s))
                (Fintype.ordinal_eqType maxReg)) sd
              (unsafeCoerce (inactive sd))
              (Data.List.length (inactive sd))
              (unsafeCoerce inactive)
              (unsafeCoerce (\x x0 _ -> mt_fst x x0))
              (unsafeCoerce (\x _ x0 x1 _ ->
                goInactive pos sd x x0 x1))}
    in
    case eres of {
     Prelude.Left err -> IState.ierr err;
     Prelude.Right s -> IState.iput (Build_SSInfo s __)})

handleInterval :: ScanStateDesc -> SState 
                             () () (Prelude.Maybe PhysReg)
handleInterval pre =
  withCursor pre (\sd _ ->
    let {position = curPosition sd} in
    stbind (\x ->
      stbind (\x0 ->
        stbind (\mres ->
          case mres of {
           Prelude.Just x1 -> IState.imap (\x2 -> Prelude.Just x2) x1;
           Prelude.Nothing -> allocateBlockedReg pre})
          (tryAllocateFreeReg pre))
        (liftLen pre (\sd0 ->
          checkInactiveIntervals sd0 position)))
      (liftLen pre (\sd0 ->
        checkActiveIntervals sd0 position)))

walkIntervals :: ScanStateDesc -> Prelude.Int ->
                            Prelude.Either SSError
                            ScanStateSig
walkIntervals sd positions =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Left
    EFuelExhausted)
    (\n ->
    let {
     go = let {
           go count0 ss =
             (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
               (\_ -> Prelude.Right (Build_SSInfo
               (thisDesc sd ss)
               __))
               (\cnt ->
               case handleInterval sd ss of {
                Prelude.Left err -> Prelude.Left err;
                Prelude.Right p ->
                 case p of {
                  (,) o ss' ->
                   case strengthenHasLen sd
                          (thisDesc sd ss') of {
                    Prelude.Just _ ->
                     go cnt (Build_SSInfo
                       (thisDesc sd ss') __);
                    Prelude.Nothing ->
                     (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
                       (\_ -> Prelude.Right
                       ss')
                       (\n0 -> Prelude.Left
                       EUnexpectedNoMoreUnhandled)
                       cnt}}})
               count0}
          in go}
    in
    case LinearScan.Utils.uncons (unhandled sd) of {
     Prelude.Just s ->
      case s of {
       (,) x s0 ->
        case x of {
         (,) i pos ->
          case go
                 (Seq.count (\x0 ->
                   Eqtype.eq_op Ssrnat.nat_eqType
                     (Prelude.snd (unsafeCoerce x0)) (unsafeCoerce pos))
                   (unhandled sd)) (Build_SSInfo sd __) of {
           Prelude.Left err -> Prelude.Left err;
           Prelude.Right ss ->
            walkIntervals (thisDesc sd ss) n}}};
     Prelude.Nothing -> Prelude.Right
      (packScanState InUse sd)})
    positions

linearScan :: (BlockInfo a2 a3 a4 a5) -> (OpInfo 
              a1 a4 a5 a6) -> (VarInfo a6) -> ([] a2) -> a1 ->
              Prelude.Either SSError ((,) ([] a3) a1)
linearScan binfo oinfo vinfo blocks accum =
  let {blocks' = computeBlockOrder blocks} in
  let {liveSets = computeLocalLiveSets vinfo oinfo binfo blocks'}
  in
  let {liveSets' = computeGlobalLiveSets binfo blocks' liveSets}
  in
  let {ssig = buildIntervals vinfo oinfo binfo blocks} in
  case walkIntervals ( ssig) ((Prelude.succ)
         (countOps binfo blocks)) of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right ssig' ->
    let {
     mappings = resolveDataFlow binfo ( ssig') blocks liveSets'}
    in
    Prelude.Right
    (assignRegNum vinfo oinfo binfo ( ssig') mappings blocks
      accum)}

