{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Main where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.IApplicative as IApplicative
import qualified LinearScan.IEndo as IEndo
import qualified LinearScan.IMonad as IMonad
import qualified LinearScan.IState as IState
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Range as Range
import qualified LinearScan.Specif as Specif
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
  IMonad.ijoin (unsafeCoerce IState.coq_IState_IMonad)
    (IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) f (unsafeCoerce x))

error_ :: SSError -> IState.IState SSError 
                     a1 a2 a3
error_ err x =
  Prelude.Left err

return_ :: (IApplicative.IApplicative
                      (IState.IState SSError () () ())) -> a2 ->
                      IState.IState SSError a1 a1 a2
return_ i =
  IApplicative.ipure (unsafeCoerce i)

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
 (VarId -> opType2) (VarId -> opType2) (opType1 ->
                                                           accType -> ([]
                                                           ((,)
                                                           VarId
                                                           PhysReg))
                                                           -> (,) accType
                                                           opType2)

coq_OpInfo_rect :: ((a2 -> OpKind) -> (a2 -> (,) 
                              ([] a4) ([] PhysReg)) ->
                              (VarId -> a3) -> (VarId ->
                              a3) -> (a2 -> a1 -> ([]
                              ((,) VarId PhysReg)) -> (,)
                              a1 a3) -> a5) -> (OpInfo a1 a2 
                              a3 a4) -> a5
coq_OpInfo_rect f o =
  case o of {
   Build_OpInfo x x0 x1 x2 x3 -> f x x0 x1 x2 x3}

coq_OpInfo_rec :: ((a2 -> OpKind) -> (a2 -> (,) 
                             ([] a4) ([] PhysReg)) ->
                             (VarId -> a3) -> (VarId ->
                             a3) -> (a2 -> a1 -> ([]
                             ((,) VarId PhysReg)) -> (,)
                             a1 a3) -> a5) -> (OpInfo a1 a2 
                             a3 a4) -> a5
coq_OpInfo_rec =
  coq_OpInfo_rect

opKind :: (OpInfo a1 a2 a3 a4) -> a2 -> OpKind
opKind o =
  case o of {
   Build_OpInfo opKind0 opRefs0 saveOp0 restoreOp0 applyAllocs0 ->
    opKind0}

opRefs :: (OpInfo a1 a2 a3 a4) -> a2 -> (,) ([] a4)
                     ([] PhysReg)
opRefs o =
  case o of {
   Build_OpInfo opKind0 opRefs0 saveOp0 restoreOp0 applyAllocs0 ->
    opRefs0}

saveOp :: (OpInfo a1 a2 a3 a4) -> VarId -> a3
saveOp o =
  case o of {
   Build_OpInfo opKind0 opRefs0 saveOp0 restoreOp0 applyAllocs0 ->
    saveOp0}

restoreOp :: (OpInfo a1 a2 a3 a4) -> VarId ->
                        a3
restoreOp o =
  case o of {
   Build_OpInfo opKind0 opRefs0 saveOp0 restoreOp0 applyAllocs0 ->
    restoreOp0}

applyAllocs :: (OpInfo a1 a2 a3 a4) -> a2 -> a1 -> ([]
                          ((,) VarId PhysReg)) -> (,) 
                          a1 a3
applyAllocs o =
  case o of {
   Build_OpInfo opKind0 opRefs0 saveOp0 restoreOp0 applyAllocs0 ->
    applyAllocs0}

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

type BlockList blockType1 = [] blockType1

type BoundedRange = Range.RangeDesc

transportBoundedRange :: Prelude.Int -> Prelude.Int ->
                                    BoundedRange ->
                                    BoundedRange
transportBoundedRange base prev x =
  x

data BuildState =
   Build_BuildState Prelude.Int ([]
                                          (Prelude.Maybe
                                          BoundedRange)) ([]
                                                                   (Prelude.Maybe
                                                                   BoundedRange))

coq_BuildState_rect :: (Prelude.Int -> ([]
                                  (Prelude.Maybe BoundedRange)) ->
                                  ([] (Prelude.Maybe BoundedRange))
                                  -> a1) -> BuildState -> a1
coq_BuildState_rect f b =
  case b of {
   Build_BuildState x x0 x1 -> f x x0 x1}

coq_BuildState_rec :: (Prelude.Int -> ([]
                                 (Prelude.Maybe BoundedRange)) ->
                                 ([] (Prelude.Maybe BoundedRange))
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
                     (Prelude.Maybe BoundedRange)
bsRegs b =
  case b of {
   Build_BuildState bsPos0 bsVars0 bsRegs0 -> bsRegs0}

foldOps :: (BlockInfo a1 a2 a3 a4) -> (a5 -> a3 -> a5)
                      -> a5 -> (BlockList a1) -> a5
foldOps binfo f z =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (blockOps binfo blk)) z

countOps :: (BlockInfo a1 a2 a3 a4) ->
                       (BlockList a1) -> Prelude.Int
countOps binfo =
  foldOps binfo (\acc x -> (Prelude.succ) acc) 0

foldOpsRev :: (BlockInfo a1 a2 a3 a4) -> (a5 -> a3 ->
                         a5) -> a5 -> (BlockList a1) -> a5
foldOpsRev binfo f z blocks =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (Seq.rev (blockOps binfo blk))) z
    (Seq.rev blocks)

processOperations :: (VarInfo a6) -> (OpInfo
                                a1 a4 a5 a6) -> (BlockInfo 
                                a2 a3 a4 a5) -> (BlockList 
                                a2) -> BuildState
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
          (Prelude.flip (Prelude.$)) __ (\_ ->
            let {
             _evar_0_ = \vars0 regs0 -> Build_BuildState 0 vars0
              regs0}
            in
            let {
             _evar_0_0 = \pos0 vars0 regs0 ->
              let {_top_assumption_1 = opRefs oinfo op} in
              let {
               _evar_0_0 = \varRefs regRefs -> Build_BuildState
                pos0
                ((Prelude.flip (Prelude.$))
                  ((Prelude.flip (Prelude.$)) vars0 (\vars' ->
                    let {
                     vars'0 = Prelude.map
                                (Lib.option_map
                                  (transportBoundedRange
                                    ((Prelude.succ) (Ssrnat.double pos0))
                                    ((Prelude.succ)
                                    (Ssrnat.double ((Prelude.succ) pos0)))))
                                vars'}
                    in
                    Data.List.foldl' (\vars'1 v ->
                      let {
                       upos = Range.Build_UsePos ((Prelude.succ)
                        (Ssrnat.double pos0))
                        (regRequired vinfo v)}
                      in
                      (Prelude.flip (Prelude.$)) __ (\_ ->
                        Seq.set_nth Prelude.Nothing vars'1
                          (varId vinfo v) (Prelude.Just
                          (let {
                            _evar_0_0 = \_top_assumption_2 ->
                             Range.Build_RangeDesc (Range.uloc upos)
                             (Range.rend ( _top_assumption_2)) ((:) upos
                             (Range.ups ( _top_assumption_2)))}
                           in
                           let {
                            _evar_0_1 = Range.Build_RangeDesc
                             (Range.uloc upos) ((Prelude.succ)
                             (Range.uloc upos)) ((:[]) upos)}
                           in
                           case Seq.nth Prelude.Nothing vars0
                                  (varId vinfo v) of {
                            Prelude.Just x -> _evar_0_0 x;
                            Prelude.Nothing -> _evar_0_1})))) vars'0 varRefs))
                  (\x -> x))
                ((Prelude.flip (Prelude.$))
                  ((Prelude.flip (Prelude.$)) regs0 (\regs' ->
                    let {
                     regs'0 = LinearScan.Utils.vmap maxReg
                                (Lib.option_map
                                  (transportBoundedRange
                                    ((Prelude.succ) (Ssrnat.double pos0))
                                    ((Prelude.succ)
                                    (Ssrnat.double ((Prelude.succ) pos0)))))
                                regs'}
                    in
                    Data.List.foldl' (\regs'1 reg ->
                      let {
                       upos = Range.Build_UsePos ((Prelude.succ)
                        (Ssrnat.double pos0)) Prelude.True}
                      in
                      (Prelude.flip (Prelude.$)) __ (\_ ->
                        LinearScan.Utils.set_nth maxReg regs'1 reg
                          (Prelude.Just
                          (let {
                            _evar_0_0 = \_top_assumption_2 ->
                             Range.Build_RangeDesc (Range.uloc upos)
                             (Range.rend ( _top_assumption_2)) ((:) upos
                             (Range.ups ( _top_assumption_2)))}
                           in
                           let {
                            _evar_0_1 = Range.Build_RangeDesc
                             (Range.uloc upos) ((Prelude.succ)
                             (Range.uloc upos)) ((:[]) upos)}
                           in
                           case LinearScan.Utils.nth maxReg regs0
                                  reg of {
                            Prelude.Just x -> _evar_0_0 x;
                            Prelude.Nothing -> _evar_0_1})))) regs'0 regRefs))
                  (\x -> x))}
              in
              case _top_assumption_1 of {
               (,) x x0 -> _evar_0_0 x x0}}
            in
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ ->
              _evar_0_ vars regs)
              (\x ->
              _evar_0_0 x vars regs)
              pos)}
        in
        case _top_assumption_0 of {
         Build_BuildState x x0 x1 -> _evar_0_ x x0 x1}) z blocks}
    in
    case _top_assumption_ of {
     (,) x x0 -> _evar_0_ x x0})

type BlockState blockType1 a =
  IState.IState SSError (BlockList blockType1)
  (BlockList blockType1) a

computeBlockOrder :: BlockState a1 ()
computeBlockOrder =
  return_ IState.coq_IState_IApplicative ()

numberOperations :: BlockState a1 ()
numberOperations =
  return_ IState.coq_IState_IApplicative ()

type OpId = Prelude.Int

data BlockLiveSets =
   Build_BlockLiveSets ([] VarId) ([] VarId) 
 ([] VarId) ([] VarId) OpId OpId

coq_BlockLiveSets_rect :: (([] VarId) -> ([]
                                     VarId) -> ([] VarId)
                                     -> ([] VarId) ->
                                     OpId -> OpId -> a1)
                                     -> BlockLiveSets -> a1
coq_BlockLiveSets_rect f b =
  case b of {
   Build_BlockLiveSets x x0 x1 x2 x3 x4 -> f x x0 x1 x2 x3 x4}

coq_BlockLiveSets_rec :: (([] VarId) -> ([]
                                    VarId) -> ([] VarId)
                                    -> ([] VarId) -> OpId
                                    -> OpId -> a1) ->
                                    BlockLiveSets -> a1
coq_BlockLiveSets_rec =
  coq_BlockLiveSets_rect

blockLiveGen :: BlockLiveSets -> [] VarId
blockLiveGen b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveGen0}

blockLiveKill :: BlockLiveSets -> [] VarId
blockLiveKill b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveKill0}

blockLiveIn :: BlockLiveSets -> [] VarId
blockLiveIn b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveIn0}

blockLiveOut :: BlockLiveSets -> [] VarId
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

union :: Eqtype.Equality__Coq_type -> ([]
                    Eqtype.Equality__Coq_sort) -> ([]
                    Eqtype.Equality__Coq_sort) -> []
                    Eqtype.Equality__Coq_sort
union a m1 m2 =
  Seq.undup a ((Prelude.++) m1 m2)

relative_complement :: Eqtype.Equality__Coq_type -> ([]
                                  Eqtype.Equality__Coq_sort) -> ([]
                                  Eqtype.Equality__Coq_sort) -> []
                                  Eqtype.Equality__Coq_sort
relative_complement a m1 m2 =
  Prelude.filter (\i ->
    Prelude.not
      (Ssrbool.in_mem i (Ssrbool.mem (Seq.seq_predType a) (unsafeCoerce m2))))
    m1

forFold :: a2 -> ([] a1) -> (a2 -> a1 -> a2) -> a2
forFold b v f =
  Data.List.foldl' f b v

computeLocalLiveSets :: (VarInfo a6) ->
                                   (OpInfo a1 a4 a5 a6) ->
                                   (BlockInfo a2 a3 a4 a5) ->
                                   (BlockList a2) ->
                                   Data.IntMap.IntMap BlockLiveSets
computeLocalLiveSets vinfo oinfo binfo blocks =
  Prelude.snd
    (forFold ((,) ((Prelude.succ) 0) Data.IntMap.empty) blocks
      (\acc b ->
      case acc of {
       (,) idx m ->
        let {liveSet = Build_BlockLiveSets [] [] [] [] idx idx} in
        case forFold ((,) idx liveSet)
               (blockOps binfo b) (\acc0 o ->
               case acc0 of {
                (,) lastIdx liveSet1 -> (,) ((Prelude.succ) ((Prelude.succ)
                 lastIdx))
                 (forFold liveSet1
                   (Prelude.fst (opRefs oinfo o)) (\liveSet2 v ->
                   let {vid = varId vinfo v} in
                   case varKind vinfo v of {
                    Input ->
                     case Prelude.not
                            (Ssrbool.in_mem (unsafeCoerce vid)
                              (Ssrbool.mem
                                (Seq.seq_predType Ssrnat.nat_eqType)
                                (unsafeCoerce
                                  (blockLiveKill liveSet2)))) of {
                      Prelude.True -> Build_BlockLiveSets ((:) vid
                       (blockLiveGen liveSet2))
                       (blockLiveKill liveSet2)
                       (blockLiveIn liveSet2)
                       (blockLiveOut liveSet2)
                       (blockFirstOpId liveSet2) lastIdx;
                      Prelude.False -> liveSet2};
                    _ -> Build_BlockLiveSets
                     (blockLiveGen liveSet2) ((:) vid
                     (blockLiveKill liveSet2))
                     (blockLiveIn liveSet2)
                     (blockLiveOut liveSet2)
                     (blockFirstOpId liveSet2) lastIdx}))}) of {
         (,) lastIdx' liveSet3 -> (,) lastIdx'
          (Data.IntMap.insert (blockId binfo b) liveSet3 m)}}))

computeGlobalLiveSets :: (BlockInfo a1 a2 a3 a4) ->
                                    (BlockList a1) ->
                                    (Data.IntMap.IntMap
                                    BlockLiveSets) ->
                                    Data.IntMap.IntMap
                                    BlockLiveSets
computeGlobalLiveSets binfo blocks liveSets =
  forFold liveSets (Seq.rev blocks) (\liveSets1 b ->
    let {bid = blockId binfo b} in
    case Data.IntMap.lookup bid liveSets1 of {
     Prelude.Just liveSet ->
      let {
       liveSet2 = forFold liveSet
                    (blockSuccessors binfo b) (\liveSet1 s_bid ->
                    case Data.IntMap.lookup s_bid liveSets1 of {
                     Prelude.Just sux -> Build_BlockLiveSets
                      (blockLiveGen liveSet1)
                      (blockLiveKill liveSet1)
                      (blockLiveIn liveSet1)
                      (unsafeCoerce
                        (union Ssrnat.nat_eqType
                          (unsafeCoerce (blockLiveOut liveSet1))
                          (unsafeCoerce (blockLiveIn sux))))
                      (blockFirstOpId liveSet1)
                      (blockLastOpId liveSet1);
                     Prelude.Nothing -> liveSet1})}
      in
      Data.IntMap.insert bid (Build_BlockLiveSets
        (blockLiveGen liveSet2)
        (blockLiveKill liveSet2)
        (unsafeCoerce
          (union Ssrnat.nat_eqType
            (relative_complement Ssrnat.nat_eqType
              (unsafeCoerce (blockLiveOut liveSet2))
              (unsafeCoerce (blockLiveKill liveSet2)))
            (unsafeCoerce (blockLiveGen liveSet2))))
        (blockLiveOut liveSet2)
        (blockFirstOpId liveSet2)
        (blockLastOpId liveSet2)) liveSets1;
     Prelude.Nothing -> liveSets1})

buildIntervals :: (VarInfo a6) -> (OpInfo 
                             a1 a4 a5 a6) -> (BlockInfo a2 
                             a3 a4 a5) -> BlockState a2
                             ScanStateSig
buildIntervals vinfo oinfo binfo =
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
  stbind (\blocks ->
    let {bs = processOperations vinfo oinfo binfo blocks} in
    let {
     regs = LinearScan.Utils.vmap maxReg (\mr ->
              case mr of {
               Prelude.Just y -> Prelude.Just
                (Interval.packInterval (Interval.Build_IntervalDesc 0
                  (Range.rbeg ( y)) (Range.rend ( y)) Interval.Whole ((:[])
                  ( y))));
               Prelude.Nothing -> Prelude.Nothing}) (bsRegs bs)}
    in
    let {
     s2 = packScanState Pending
            (Build_ScanStateDesc
            (nextInterval (Build_ScanStateDesc 0 []
              (Data.List.replicate maxReg Prelude.Nothing) [] []
              [] []))
            (intervals (Build_ScanStateDesc 0 []
              (Data.List.replicate maxReg Prelude.Nothing) [] []
              [] [])) regs
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
    let {
     s3 = Lib.foldl_with_index (handleVar (bsPos bs)) s2
            (bsVars bs)}
    in
    let {s5 = packScanState InUse ( s3)} in
    return_ IState.coq_IState_IApplicative s5) IState.iget

data InsertPos =
   AtBegin VarId
 | AtEnd VarId

coq_InsertPos_rect :: (VarId -> a1) -> (VarId
                                 -> a1) -> InsertPos -> a1
coq_InsertPos_rect f f0 i =
  case i of {
   AtBegin x -> f x;
   AtEnd x -> f0 x}

coq_InsertPos_rec :: (VarId -> a1) -> (VarId
                                -> a1) -> InsertPos -> a1
coq_InsertPos_rec =
  coq_InsertPos_rect

eqact :: InsertPos -> InsertPos ->
                    Prelude.Bool
eqact v1 v2 =
  case v1 of {
   AtBegin r1 ->
    case v2 of {
     AtBegin r2 ->
      Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce r1) (unsafeCoerce r2);
     AtEnd v -> Prelude.False};
   AtEnd r1 ->
    case v2 of {
     AtBegin v -> Prelude.False;
     AtEnd r2 ->
      Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce r1) (unsafeCoerce r2)}}

eqactP :: Eqtype.Equality__Coq_axiom InsertPos
eqactP _top_assumption_ =
  let {
   _evar_0_ = \r1 _top_assumption_0 ->
    let {
     _evar_0_ = \r2 ->
      let {
       _evar_0_ = \_ ->
        let {_evar_0_ = let {_evar_0_ = Ssrbool.ReflectT} in  _evar_0_} in
         _evar_0_}
      in
      let {
       _evar_0_0 = \_ -> let {_evar_0_0 = Ssrbool.ReflectF} in  _evar_0_0}
      in
      case Eqtype.eqP Ssrnat.nat_eqType r1 r2 of {
       Ssrbool.ReflectT -> _evar_0_ __;
       Ssrbool.ReflectF -> _evar_0_0 __}}
    in
    let {
     _evar_0_0 = \r2 ->
      let {
       _evar_0_0 = \_ -> let {_evar_0_0 = Ssrbool.ReflectF} in  _evar_0_0}
      in
      let {_evar_0_1 = \_ -> Ssrbool.ReflectF} in
      case Eqtype.eqP Ssrnat.nat_eqType r1 r2 of {
       Ssrbool.ReflectT -> _evar_0_0 __;
       Ssrbool.ReflectF -> _evar_0_1 __}}
    in
    case _top_assumption_0 of {
     AtBegin x -> unsafeCoerce _evar_0_ x;
     AtEnd x -> unsafeCoerce _evar_0_0 x}}
  in
  let {
   _evar_0_0 = \r1 _top_assumption_0 ->
    let {
     _evar_0_0 = \r2 ->
      let {
       _evar_0_0 = \_ -> let {_evar_0_0 = Ssrbool.ReflectF} in  _evar_0_0}
      in
      let {_evar_0_1 = \_ -> Ssrbool.ReflectF} in
      case Eqtype.eqP Ssrnat.nat_eqType r1 r2 of {
       Ssrbool.ReflectT -> _evar_0_0 __;
       Ssrbool.ReflectF -> _evar_0_1 __}}
    in
    let {
     _evar_0_1 = \r2 ->
      let {
       _evar_0_1 = \_ ->
        let {_evar_0_1 = let {_evar_0_1 = Ssrbool.ReflectT} in  _evar_0_1} in
         _evar_0_1}
      in
      let {
       _evar_0_2 = \_ -> let {_evar_0_2 = Ssrbool.ReflectF} in  _evar_0_2}
      in
      case Eqtype.eqP Ssrnat.nat_eqType r1 r2 of {
       Ssrbool.ReflectT -> _evar_0_1 __;
       Ssrbool.ReflectF -> _evar_0_2 __}}
    in
    case _top_assumption_0 of {
     AtBegin x -> unsafeCoerce _evar_0_0 x;
     AtEnd x -> unsafeCoerce _evar_0_1 x}}
  in
  case _top_assumption_ of {
   AtBegin x -> unsafeCoerce _evar_0_ x;
   AtEnd x -> unsafeCoerce _evar_0_0 x}

act_eqMixin :: Eqtype.Equality__Coq_mixin_of InsertPos
act_eqMixin =
  Eqtype.Equality__Mixin eqact eqactP

act_eqType :: Eqtype.Equality__Coq_type
act_eqType =
  unsafeCoerce act_eqMixin

coq_InsertPos_eqType :: Eqtype.Equality__Coq_type ->
                                   Eqtype.Equality__Coq_type
coq_InsertPos_eqType a =
  unsafeCoerce act_eqMixin

resolveDataFlow :: (BlockInfo a1 a2 a3 a4) ->
                              ScanStateDesc -> (BlockList
                              a1) -> (Data.IntMap.IntMap
                              BlockLiveSets) -> Data.IntMap.IntMap
                              ([] InsertPos)
resolveDataFlow binfo sd blocks liveSets =
  forFold Data.IntMap.empty blocks (\mappings b ->
    let {bid = blockId binfo b} in
    case Data.IntMap.lookup bid liveSets of {
     Prelude.Just from ->
      let {successors = blockSuccessors binfo b} in
      forFold mappings successors (\ms s_bid ->
        case Data.IntMap.lookup s_bid liveSets of {
         Prelude.Just to ->
          forFold ms (blockLiveIn to) (\ms' vid ->
            case lookupInterval sd __ vid
                   (blockLastOpId from) of {
             Prelude.Just from_interval ->
              case lookupInterval sd __ vid
                     (blockFirstOpId to) of {
               Prelude.Just to_interval ->
                case Prelude.not
                       (Eqtype.eq_op
                         (Fintype.ordinal_eqType
                           (nextInterval sd))
                         (unsafeCoerce from_interval)
                         (unsafeCoerce to_interval)) of {
                 Prelude.True ->
                  let {
                   in_from = (Prelude.<=) (Data.List.length successors)
                               ((Prelude.succ) 0)}
                  in
                  let {
                   ins = case in_from of {
                          Prelude.True -> AtEnd vid;
                          Prelude.False -> AtBegin vid}}
                  in
                  let {
                   f = \mxs ->
                    case mxs of {
                     Prelude.Just xs ->
                      case Prelude.not
                             (Ssrbool.in_mem (unsafeCoerce ins)
                               (Ssrbool.mem
                                 (Seq.seq_predType act_eqType) xs)) of {
                       Prelude.True -> Prelude.Just ((:) ins
                        (unsafeCoerce xs));
                       Prelude.False -> Prelude.Just (unsafeCoerce xs)};
                     Prelude.Nothing -> Prelude.Just ((:) ins [])}}
                  in
                  let {
                   key = case in_from of {
                          Prelude.True -> bid;
                          Prelude.False -> s_bid}}
                  in
                  Data.IntMap.alter (unsafeCoerce f) key ms';
                 Prelude.False -> ms'};
               Prelude.Nothing -> ms'};
             Prelude.Nothing -> ms'});
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
  IState.IState SSError (AssnStateInfo accType)
  (AssnStateInfo accType) a

savesAndRestores :: (OpInfo a1 a2 a3 a4) ->
                               OpId -> VarId ->
                               Interval.IntervalDesc -> (,) ([] a3) ([] a3)
savesAndRestores oinfo opid vid int =
  let {
   isFirst = Eqtype.eq_op Ssrnat.nat_eqType
               (unsafeCoerce (Interval.firstUsePos int)) (unsafeCoerce opid)}
  in
  let {
   isLast = Eqtype.eq_op (Eqtype.option_eqType Ssrnat.nat_eqType)
              (unsafeCoerce (Interval.nextUseAfter int opid))
              (unsafeCoerce Prelude.Nothing)}
  in
  let {save = (:) (saveOp oinfo vid) []} in
  let {restore = (:) (restoreOp oinfo vid) []} in
  case Interval.iknd int of {
   Interval.Whole -> (,) [] [];
   Interval.LeftMost ->
    case isLast of {
     Prelude.True -> (,) [] save;
     Prelude.False -> (,) [] []};
   Interval.Middle ->
    case isFirst of {
     Prelude.True ->
      case isLast of {
       Prelude.True -> (,) restore save;
       Prelude.False -> (,) restore []};
     Prelude.False ->
      case isLast of {
       Prelude.True -> (,) [] save;
       Prelude.False -> (,) [] []}};
   Interval.RightMost ->
    case isFirst of {
     Prelude.True -> (,) restore [];
     Prelude.False -> (,) [] []}}

doAllocations :: (VarInfo a4) -> (OpInfo 
                            a1 a2 a3 a4) -> ([]
                            ((,) Interval.IntervalDesc PhysReg)) ->
                            a2 -> AssnState a1 ([] a3)
doAllocations vinfo oinfo ints op =
  stbind (\assn ->
    let {opid = assnOpId assn} in
    let {vars = Prelude.fst (opRefs oinfo op)} in
    case forFold ((,) ((,) [] []) []) vars (\acc v ->
           let {vid = varId vinfo v} in
           let {
            v_ints = Prelude.filter (\x ->
                       isWithin (Prelude.fst x) vid
                         (assnOpId assn)) ints}
           in
           forFold acc v_ints (\acc' ir ->
             case ir of {
              (,) int reg ->
               case acc' of {
                (,) p saves' ->
                 case p of {
                  (,) allocs' restores' ->
                   case savesAndRestores oinfo opid vid int of {
                    (,) ss rs -> (,) ((,) ((:) ((,) vid reg) allocs')
                     ((Prelude.++) rs restores')) ((Prelude.++) ss saves')}}}})) of {
     (,) p saves ->
      case p of {
       (,) allocs restores ->
        case applyAllocs oinfo op (assnAcc assn) allocs of {
         (,) acc' op' ->
          stbind (\x ->
            return_ IState.coq_IState_IApplicative
              ((Prelude.++) restores ((:) op' saves)))
            (IState.iput (Build_AssnStateInfo ((Prelude.succ)
              ((Prelude.succ) (assnOpId assn))) acc'))}}})
    IState.iget

considerOps :: (OpInfo a1 a4 a5 a6) ->
                          (BlockInfo a2 a3 a4 a5) -> (a4 ->
                          AssnState a1 ([] a5)) ->
                          (Data.IntMap.IntMap ([] InsertPos)) ->
                          ([] a2) -> IState.IState SSError
                          (AssnStateInfo a1)
                          (AssnStateInfo a1) ([] a3)
considerOps oinfo binfo f mappings =
  IMonad.mapM (unsafeCoerce IState.coq_IState_IMonad) (\blk ->
    let {ops = blockOps binfo blk} in
    stbind (\ops' ->
      let {bid = blockId binfo blk} in
      let {
       ops'' = case Data.IntMap.lookup bid mappings of {
                Prelude.Just inss ->
                 forFold ops' inss (\ops'' ins ->
                   case ins of {
                    AtBegin vid -> (:)
                     (restoreOp oinfo vid) ops'';
                    AtEnd vid ->
                     let {sop = saveOp oinfo vid} in
                     case ops of {
                      [] -> (:) sop [];
                      (:) o os ->
                       case ops'' of {
                        [] -> (:) sop [];
                        (:) o'' os'' ->
                         case opKind oinfo (Seq.last o os) of {
                          IsBranch ->
                           (Prelude.++) (Seq.belast o'' os'') ((:) sop ((:)
                             (Seq.last o'' os'') []));
                          _ -> (Prelude.++) ops' ((:) sop [])}}}});
                Prelude.Nothing -> ops'}}
      in
      return_ IState.coq_IState_IApplicative
        (setBlockOps (unsafeCoerce binfo) blk ops''))
      (IMonad.concatMapM (unsafeCoerce IState.coq_IState_IMonad) f ops))

assignRegNum :: (VarInfo a6) -> (OpInfo 
                           a1 a4 a5 a6) -> (BlockInfo a2 a3 
                           a4 a5) -> ScanStateDesc ->
                           (Data.IntMap.IntMap ([] InsertPos)) ->
                           a1 -> IState.IState SSError ([] a2)
                           ([] a3) a1
assignRegNum vinfo oinfo binfo sd mappings acc =
  let {
   ints = Prelude.map (\x -> (,)
            (Interval.getIntervalDesc
              (
                (LinearScan.Utils.nth (nextInterval sd)
                  (intervals sd) (Prelude.fst x))))
            (Prelude.snd x))
            ((Prelude.++) (handled sd)
              ((Prelude.++) (active sd) (inactive sd)))}
  in
  stbind (\blocks ->
    case considerOps oinfo binfo
           (doAllocations vinfo oinfo ints) mappings blocks
           (Build_AssnStateInfo ((Prelude.succ) 0) acc) of {
     Prelude.Left err -> IState.ierr err;
     Prelude.Right p ->
      case p of {
       (,) blocks' assn ->
        stbind (\x ->
          return_ IState.coq_IState_IApplicative
            (assnAcc assn)) (IState.iput blocks')}}) IState.iget

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

data HasBase p =
   Build_HasBase

coq_HasBase_rect :: (() -> a2) -> a2
coq_HasBase_rect f =
  f __

coq_HasBase_rec :: (() -> a2) -> a2
coq_HasBase_rec f =
  coq_HasBase_rect f

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

data HasWork p =
   Build_HasWork

coq_HasWork_rect :: (() -> a2) -> a2
coq_HasWork_rect f =
  f __

coq_HasWork_rec :: (() -> a2) -> a2
coq_HasWork_rec f =
  coq_HasWork_rect f

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
                         -> () -> SState a1 a2 a3) ->
                         SState a1 a2 a3
withCursor pre f x =
  case x of {
   Build_SSInfo thisDesc0 thisHolds0 ->
    f thisDesc0 __ (Build_SSInfo thisDesc0 thisHolds0)}

moveUnhandledToActive :: ScanStateDesc ->
                                    PhysReg -> SState 
                                    a1 () ()
moveUnhandledToActive pre reg x =
  case x of {
   Build_SSInfo thisDesc0 thisHolds0 ->
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
                                   a1 () ()
splitCurrentInterval pre pos ssi =
  let {
   _evar_0_ = \desc holds ->
    let {
     _evar_0_ = \_nextInterval_ intervals0 _fixedIntervals_ unhandled0 _active_ _inactive_ _handled_ ->
      let {_evar_0_ = \holds0 -> Logic.coq_False_rect} in
      let {
       _evar_0_0 = \_top_assumption_ ->
        let {
         _evar_0_0 = \uid beg us ->
          let {
           desc0 = Build_ScanStateDesc _nextInterval_ intervals0
            _fixedIntervals_ ((:) ((,) uid beg) us) _active_ _inactive_
            _handled_}
          in
          (\_ _ _holds_ _ _ ->
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
       [] -> (\_ _ holds0 _ _ -> _evar_0_ holds0);
       (:) x x0 -> _evar_0_0 x x0 __}}
    in
    case desc of {
     Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
      _evar_0_ x x0 x1 x2 x3 x4 x5 __ __ holds __}}
  in
  case ssi of {
   Build_SSInfo x x0 -> _evar_0_ x x0 __}

splitAssignedIntervalForReg :: ScanStateDesc ->
                                          PhysReg ->
                                          Interval.SplitPosition ->
                                          Prelude.Bool -> SState 
                                          a1 () ()
splitAssignedIntervalForReg pre reg pos trueForActives ssi =
  let {
   _evar_0_ = \desc holds ->
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
          (\_ _ holds0 _ _ ->
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
          _evar_0_ x x0 x1 x2 x3 x4 x5 intlist intids})) __ __ holds __}
  in
  case ssi of {
   Build_SSInfo x x0 -> _evar_0_ x x0 __}

splitActiveIntervalForReg :: ScanStateDesc ->
                                        PhysReg -> Prelude.Int ->
                                        SState a1 () ()
splitActiveIntervalForReg pre reg pos =
  splitAssignedIntervalForReg pre reg (Interval.BeforePos pos)
    Prelude.True

splitAnyInactiveIntervalForReg :: ScanStateDesc ->
                                             PhysReg ->
                                             SState a1 () ()
splitAnyInactiveIntervalForReg pre reg ss =
  (Prelude.flip (Prelude.$)) (\s _ _ ->
    splitAssignedIntervalForReg s reg Interval.EndOfLifetimeHole
      Prelude.False) (\_top_assumption_ ->
    let {_top_assumption_0 = _top_assumption_ pre __ __} in
    let {_top_assumption_1 = _top_assumption_0 ss} in
    let {
     _evar_0_ = \err -> Prelude.Right ((,) () (Build_SSInfo
      (thisDesc pre ss) __))}
    in
    let {
     _evar_0_0 = \_top_assumption_2 ->
      let {_evar_0_0 = \_the_1st_wildcard_ ss' -> Prelude.Right ((,) () ss')}
      in
      case _top_assumption_2 of {
       (,) x x0 -> _evar_0_0 x x0}}
    in
    case _top_assumption_1 of {
     Prelude.Left x -> _evar_0_ x;
     Prelude.Right x -> _evar_0_0 x})

intersectsWithFixedInterval :: ScanStateDesc ->
                                          PhysReg ->
                                          SState a1 a1
                                          (Prelude.Maybe Prelude.Int)
intersectsWithFixedInterval pre reg =
  withCursor pre (\sd _ ->
    let {int = curIntDetails sd} in
    return_ IState.coq_IState_IApplicative
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
                                 a1 a1
                                 (Prelude.Maybe
                                 (SState a1 () PhysReg))
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
       success = stbind (\x ->
                   return_ IState.coq_IState_IApplicative reg)
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
                          stbind (\x0 ->
                            return_ IState.coq_IState_IApplicative
                              reg) (moveUnhandledToActive pre reg))
                          (splitCurrentInterval pre
                            (Interval.BeforePos n))})};
                  Prelude.Nothing -> Prelude.Just success}}
      in
      return_ IState.coq_IState_IApplicative maction})

allocateBlockedReg :: ScanStateDesc -> SState
                                 a1 () (Prelude.Maybe PhysReg)
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
              stbind (\x1 ->
                return_ IState.coq_IState_IApplicative
                  Prelude.Nothing) (weakenHasLen_ pre))
              (case mloc of {
                Prelude.Just n ->
                 splitCurrentInterval pre (Interval.BeforePos n);
                Prelude.Nothing ->
                 return_ IState.coq_IState_IApplicative ()}))
            (intersectsWithFixedInterval pre reg))
          (splitCurrentInterval pre
            Interval.BeforeFirstUsePosReqReg);
       Prelude.False ->
        stbind (\x ->
          stbind (\x0 ->
            stbind (\mloc ->
              stbind (\x1 ->
                return_ IState.coq_IState_IApplicative
                  (Prelude.Just reg))
                (case mloc of {
                  Prelude.Just n ->
                   stbind (\x1 ->
                     moveUnhandledToActive pre reg)
                     (splitCurrentInterval pre (Interval.BeforePos
                       n));
                  Prelude.Nothing -> moveUnhandledToActive pre reg}))
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
           Prelude.Just x1 ->
            IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) (\x2 ->
              Prelude.Just x2) (unsafeCoerce x1);
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
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Left
    EFuelExhausted)
    (\n ->
    let {
     go = let {
           go count0 ss =
             (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
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
                     (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
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
              a1 a4 a5 a6) -> (VarInfo a6) -> a1 -> IState.IState
              SSError ([] a2) ([] a3) a1
linearScan binfo oinfo vinfo accum =
  stbind (\x ->
    stbind (\x0 ->
      stbind (\blocks ->
        let {
         liveSets = computeLocalLiveSets vinfo oinfo binfo blocks}
        in
        let {
         liveSets' = computeGlobalLiveSets binfo blocks liveSets}
        in
        stbind (\ssig ->
          stbind (\blocks0 ->
            case walkIntervals ( ssig) ((Prelude.succ)
                   (countOps binfo blocks0)) of {
             Prelude.Left err -> error_ err;
             Prelude.Right ssig' ->
              let {
               mappings = resolveDataFlow binfo ( ssig') blocks0
                            liveSets'}
              in
              assignRegNum vinfo oinfo binfo ( ssig') mappings
                accum}) IState.iget)
          (buildIntervals vinfo oinfo binfo)) IState.iget)
      numberOperations) computeBlockOrder

