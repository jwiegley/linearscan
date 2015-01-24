{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Main where


import qualified Prelude
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
import qualified LinearScan.NonEmpty0 as NonEmpty0
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

type MyMachine__PhysReg = Prelude.Int

maxReg :: Prelude.Int
maxReg =
  _MyMachine__maxReg

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
                     a1 a1 a2
error_ err x =
  Prelude.Left err

return_ :: a2 -> IState.IState SSError a1 a1 a2
return_ =
  IApplicative.ipure (unsafeCoerce IState.coq_IState_IApplicative)

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

data VarAction =
   Spill
 | Restore
 | RestoreAndSpill

coq_VarAction_rect :: a1 -> a1 -> a1 -> VarAction -> a1
coq_VarAction_rect f f0 f1 v =
  case v of {
   Spill -> f;
   Restore -> f0;
   RestoreAndSpill -> f1}

coq_VarAction_rec :: a1 -> a1 -> a1 -> VarAction -> a1
coq_VarAction_rec =
  coq_VarAction_rect

data VarInfo varType =
   Build_VarInfo (varType -> Prelude.Int) (varType ->
                                                    VarKind) 
 (varType -> Prelude.Bool)

coq_VarInfo_rect :: ((a1 -> Prelude.Int) -> (a1 ->
                               VarKind) -> (a1 -> Prelude.Bool) ->
                               a2) -> (VarInfo a1) -> a2
coq_VarInfo_rect f v =
  case v of {
   Build_VarInfo x x0 x1 -> f x x0 x1}

coq_VarInfo_rec :: ((a1 -> Prelude.Int) -> (a1 ->
                              VarKind) -> (a1 -> Prelude.Bool) ->
                              a2) -> (VarInfo a1) -> a2
coq_VarInfo_rec =
  coq_VarInfo_rect

varId :: (VarInfo a1) -> a1 -> Prelude.Int
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
   Normal
 | LoopBegin
 | LoopEnd
 | Call

coq_OpKind_rect :: a1 -> a1 -> a1 -> a1 -> OpKind -> a1
coq_OpKind_rect f f0 f1 f2 o =
  case o of {
   Normal -> f;
   LoopBegin -> f0;
   LoopEnd -> f1;
   Call -> f2}

coq_OpKind_rec :: a1 -> a1 -> a1 -> a1 -> OpKind -> a1
coq_OpKind_rec =
  coq_OpKind_rect

data AllocInfo =
   Build_AllocInfo PhysReg (Prelude.Maybe
                                               VarAction)

coq_AllocInfo_rect :: (PhysReg -> (Prelude.Maybe
                                 VarAction) -> a1) ->
                                 AllocInfo -> a1
coq_AllocInfo_rect f a =
  case a of {
   Build_AllocInfo x x0 -> f x x0}

coq_AllocInfo_rec :: (PhysReg -> (Prelude.Maybe
                                VarAction) -> a1) ->
                                AllocInfo -> a1
coq_AllocInfo_rec =
  coq_AllocInfo_rect

allocReg :: AllocInfo -> PhysReg
allocReg a =
  case a of {
   Build_AllocInfo allocReg0 allocAction0 -> allocReg0}

allocAction :: AllocInfo -> Prelude.Maybe
                          VarAction
allocAction a =
  case a of {
   Build_AllocInfo allocReg0 allocAction0 -> allocAction0}

data OpInfo opType1 opType2 varType =
   Build_OpInfo (opType1 -> OpKind) (opType1 -> []
                                                        varType) (opType1 ->
                                                                 ([]
                                                                 ((,)
                                                                 Prelude.Int
                                                                 AllocInfo))
                                                                 -> opType2) 
 (opType1 -> [] PhysReg)

coq_OpInfo_rect :: ((a1 -> OpKind) -> (a1 -> [] 
                              a3) -> (a1 -> ([]
                              ((,) Prelude.Int AllocInfo)) -> a2)
                              -> (a1 -> [] PhysReg) -> a4) ->
                              (OpInfo a1 a2 a3) -> a4
coq_OpInfo_rect f o =
  case o of {
   Build_OpInfo x x0 x1 x2 -> f x x0 x1 x2}

coq_OpInfo_rec :: ((a1 -> OpKind) -> (a1 -> [] a3) ->
                             (a1 -> ([]
                             ((,) Prelude.Int AllocInfo)) -> a2) ->
                             (a1 -> [] PhysReg) -> a4) ->
                             (OpInfo a1 a2 a3) -> a4
coq_OpInfo_rec =
  coq_OpInfo_rect

opKind :: (OpInfo a1 a2 a3) -> a1 -> OpKind
opKind o =
  case o of {
   Build_OpInfo opKind0 varRefs0 applyAllocs0 regRefs0 -> opKind0}

varRefs :: (OpInfo a1 a2 a3) -> a1 -> [] a3
varRefs o =
  case o of {
   Build_OpInfo opKind0 varRefs0 applyAllocs0 regRefs0 -> varRefs0}

applyAllocs :: (OpInfo a1 a2 a3) -> a1 -> ([]
                          ((,) Prelude.Int AllocInfo)) -> a2
applyAllocs o =
  case o of {
   Build_OpInfo opKind0 varRefs0 applyAllocs0 regRefs0 ->
    applyAllocs0}

regRefs :: (OpInfo a1 a2 a3) -> a1 -> []
                      PhysReg
regRefs o =
  case o of {
   Build_OpInfo opKind0 varRefs0 applyAllocs0 regRefs0 -> regRefs0}

data BlockInfo blockType1 blockType2 opType1 opType2 =
   Build_BlockInfo (blockType1 -> [] opType1) (blockType1 -> ([]
                                                        opType2) ->
                                                        blockType2)

coq_BlockInfo_rect :: ((a1 -> [] a3) -> (a1 -> ([] a4) -> a2) ->
                                 a5) -> (BlockInfo a1 a2 a3 
                                 a4) -> a5
coq_BlockInfo_rect f b =
  case b of {
   Build_BlockInfo x x0 -> f x x0}

coq_BlockInfo_rec :: ((a1 -> [] a3) -> (a1 -> ([] a4) -> a2) ->
                                a5) -> (BlockInfo a1 a2 a3 
                                a4) -> a5
coq_BlockInfo_rec =
  coq_BlockInfo_rect

blockOps :: (BlockInfo a1 a2 a3 a4) -> a1 -> [] a3
blockOps b =
  case b of {
   Build_BlockInfo blockOps0 setBlockOps0 -> blockOps0}

setBlockOps :: (BlockInfo a1 a2 a3 a4) -> a1 -> ([] 
                          a4) -> a2
setBlockOps b =
  case b of {
   Build_BlockInfo blockOps0 setBlockOps0 -> setBlockOps0}

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

foldOpsRev :: (BlockInfo a1 a2 a3 a4) -> (a5 -> a3 ->
                         a5) -> a5 -> (BlockList a1) -> a5
foldOpsRev binfo f z blocks =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (Seq.rev (blockOps binfo blk))) z
    (Seq.rev ( blocks))

countOps :: (BlockInfo a1 a2 a3 a4) ->
                       (BlockList a1) -> Prelude.Int
countOps binfo =
  foldOps binfo (\acc x -> (Prelude.succ) acc) 0

mapAccumLOps :: (BlockInfo a1 a2 a3 a4) -> (a5 -> a3 ->
                           (,) a5 a4) -> a5 -> (BlockList a1) ->
                           (,) a5 ([] a2)
mapAccumLOps binfo f =
  NonEmpty0.coq_NE_mapAccumL (\z blk ->
    case Lib.mapAccumL f z (blockOps binfo blk) of {
     (,) z' ops -> (,) z' (setBlockOps binfo blk ops)})

processOperations :: (VarInfo a5) -> (OpInfo
                                a3 a4 a5) -> (BlockInfo a1 
                                a2 a3 a4) -> (BlockList a1) ->
                                BuildState
processOperations vinfo oinfo binfo blocks =
  (Prelude.flip (Prelude.$))
    (foldOps binfo (\x op ->
      case x of {
       (,) n m -> (,) ((Prelude.succ) n)
        (Data.List.foldl' (\m0 v ->
          Prelude.max m0 (varId vinfo v)) m
          (varRefs oinfo op))}) ((,) 0 0) blocks)
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
             _evar_0_0 = \pos0 vars0 regs0 -> Build_BuildState pos0
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
                      (Ssrnat.double pos0)) (regRequired vinfo v)}
                    in
                    (Prelude.flip (Prelude.$)) __ (\_ ->
                      Seq.set_nth Prelude.Nothing vars'1
                        (varId vinfo v) (Prelude.Just
                        (let {
                          _evar_0_0 = \_top_assumption_1 ->
                           Range.Build_RangeDesc (Range.uloc upos)
                           (Range.rend ( _top_assumption_1)) ((:) upos
                           (Range.ups ( _top_assumption_1)))}
                         in
                         let {
                          _evar_0_1 = Range.Build_RangeDesc (Range.uloc upos)
                           ((Prelude.succ) (Range.uloc upos)) ((:[]) upos)}
                         in
                         case Seq.nth Prelude.Nothing vars0
                                (varId vinfo v) of {
                          Prelude.Just x -> _evar_0_0 x;
                          Prelude.Nothing -> _evar_0_1})))) vars'0
                    (varRefs oinfo op))) (\x -> x))
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
                          _evar_0_0 = \_top_assumption_1 ->
                           Range.Build_RangeDesc (Range.uloc upos)
                           (Range.rend ( _top_assumption_1)) ((:) upos
                           (Range.ups ( _top_assumption_1)))}
                         in
                         let {
                          _evar_0_1 = Range.Build_RangeDesc (Range.uloc upos)
                           ((Prelude.succ) (Range.uloc upos)) ((:[]) upos)}
                         in
                         case LinearScan.Utils.nth maxReg regs0
                                reg of {
                          Prelude.Just x -> _evar_0_0 x;
                          Prelude.Nothing -> _evar_0_1})))) regs'0
                    (regRefs oinfo op))) (\x -> x))}
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
  return_ ()

numberOperations :: BlockState a1 ()
numberOperations =
  return_ ()

computeLocalLiveSets :: BlockState a1 ()
computeLocalLiveSets =
  return_ ()

computeGlobalLiveSets :: BlockState a1 ()
computeGlobalLiveSets =
  return_ ()

buildIntervals :: (VarInfo a5) -> (OpInfo 
                             a3 a4 a5) -> (BlockInfo a1 a2 
                             a3 a4) -> BlockState a1
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
    (Prelude.$) (mkint vid ss pos mx) (\sd _ d _ ->
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
    return_ s5) IState.iget

resolveDataFlow :: BlockState a1 ()
resolveDataFlow =
  return_ ()

assignRegNum :: (VarInfo a5) -> (OpInfo 
                           a3 a4 a5) -> (BlockInfo a1 a2 a3 
                           a4) -> ScanStateDesc ->
                           BlockState a1 ([] a2)
assignRegNum vinfo oinfo binfo sd =
  let {
   ints = (Prelude.++) (handled sd)
            ((Prelude.++) (active sd) (inactive sd))}
  in
  let {
   f = \n op ->
    let {
     k = \v ->
      let {
       h = \acc x ->
        case x of {
         (,) xid reg ->
          let {vid = varId vinfo v} in
          let {
           int = Interval.getIntervalDesc
                   (
                     (LinearScan.Utils.nth (nextInterval sd)
                       (intervals sd) xid))}
          in
          case (Prelude.&&)
                 (Eqtype.eq_op Ssrnat.nat_eqType
                   (unsafeCoerce (Interval.ivar int)) (unsafeCoerce vid))
                 ((Prelude.&&) ((Prelude.<=) (Interval.ibeg int) n)
                   ((Prelude.<=) ((Prelude.succ) n) (Interval.iend int))) of {
           Prelude.True ->
            let {
             isFirst = Eqtype.eq_op Ssrnat.nat_eqType
                         (unsafeCoerce (Interval.firstUsePos int))
                         (unsafeCoerce n)}
            in
            let {
             isLast = Eqtype.eq_op (Eqtype.option_eqType Ssrnat.nat_eqType)
                        (unsafeCoerce (Interval.nextUseAfter int n))
                        (unsafeCoerce Prelude.Nothing)}
            in
            (:) ((,) vid (Build_AllocInfo reg
            (case Interval.iknd int of {
              Interval.Whole -> Prelude.Nothing;
              Interval.LeftMost ->
               case isLast of {
                Prelude.True -> Prelude.Just Spill;
                Prelude.False -> Prelude.Nothing};
              Interval.Middle ->
               case isFirst of {
                Prelude.True ->
                 case isLast of {
                  Prelude.True -> Prelude.Just RestoreAndSpill;
                  Prelude.False -> Prelude.Just Restore};
                Prelude.False ->
                 case isLast of {
                  Prelude.True -> Prelude.Just Spill;
                  Prelude.False -> Prelude.Nothing}};
              Interval.RightMost ->
               case isFirst of {
                Prelude.True -> Prelude.Just Restore;
                Prelude.False -> Prelude.Nothing}}))) acc;
           Prelude.False -> acc}}}
      in
      Data.List.foldl' h [] ints}
    in
    (,) ((Prelude.succ) ((Prelude.succ) n))
    (applyAllocs oinfo op
      (Seq.flatten (Prelude.map k (varRefs oinfo op))))}
  in
  stbind (\blocks ->
    return_
      (Prelude.snd
        (mapAccumLOps binfo f ((Prelude.succ) 0) blocks)))
    IState.iget

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
     Prelude.Left s0 -> Prelude.Left s0;
     Prelude.Right p -> Prelude.Right
      (case p of {
        (,) a0 s0 -> (,) a0
         (case s0 of {
           Build_SSInfo thisDesc1 _ -> Build_SSInfo
            thisDesc1 __})})}}

liftLen :: ScanStateDesc -> (ScanStateDesc ->
                      SState () () a1) -> SState 
                      () () a1
liftLen pre f _top_assumption_ =
  let {
   _evar_0_ = \sd ->
    let {ss = Build_SSInfo sd __} in
    let {_top_assumption_0 = f sd} in
    let {_top_assumption_1 = _top_assumption_0 ss} in
    let {_evar_0_ = \err -> Prelude.Left err} in
    let {
     _evar_0_0 = \_top_assumption_2 ->
      let {
       _evar_0_0 = \x _top_assumption_3 ->
        let {
         _evar_0_0 = \sd' -> Prelude.Right ((,) x (Build_SSInfo sd'
          __))}
        in
        case _top_assumption_3 of {
         Build_SSInfo x0 x1 -> _evar_0_0 x0}}
      in
      case _top_assumption_2 of {
       (,) x x0 -> _evar_0_0 x x0}}
    in
    case _top_assumption_1 of {
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
  (Prelude.$) (withCursor pre) (\sd _ ->
    let {int = curIntDetails sd} in
    (Prelude.$) return_
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
  (Prelude.$) (withCursor pre) (\sd _ ->
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
                                 a1 () (Prelude.Maybe PhysReg)
allocateBlockedReg pre =
  (Prelude.$) (withCursor pre) (\sd _ ->
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
                return_ (Prelude.Just reg))
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
  (Prelude.$) (withScanStatePO pre) (\sd _ ->
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
  (Prelude.$) (withScanStatePO pre) (\sd _ ->
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
  (Prelude.$) (unsafeCoerce (withCursor pre)) (\sd _ ->
    let {position = curPosition sd} in
    stbind (\x ->
      stbind (\x0 ->
        stbind (\mres ->
          case mres of {
           Prelude.Just x1 ->
            IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) (\x2 ->
              Prelude.Just x2) x1;
           Prelude.Nothing ->
            unsafeCoerce (allocateBlockedReg pre)})
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
               case IState.runIState (handleInterval sd) ss of {
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

mainAlgorithm :: (BlockInfo a1 a2 a3 a4) -> (OpInfo 
                 a3 a4 a5) -> (VarInfo a5) -> BlockState
                 a1 ([] a2)
mainAlgorithm binfo oinfo vinfo =
  stbind (\x ->
    stbind (\x0 ->
      stbind (\x1 ->
        stbind (\x2 ->
          stbind (\ssig ->
            stbind (\blocks ->
              case walkIntervals ( ssig) ((Prelude.succ)
                     (countOps binfo blocks)) of {
               Prelude.Left err -> error_ err;
               Prelude.Right ssig' ->
                stbind (\x3 ->
                  assignRegNum vinfo oinfo binfo ( ssig'))
                  resolveDataFlow}) IState.iget)
            (buildIntervals vinfo oinfo binfo))
          computeGlobalLiveSets) computeLocalLiveSets)
      numberOperations) computeBlockOrder

linearScan :: (BlockInfo a1 a2 a3 a4) -> (OpInfo 
              a3 a4 a5) -> (VarInfo a5) -> (BlockList 
              a1) -> Prelude.Either SSError
              (BlockList a2)
linearScan binfo oinfo vinfo blocks =
  let {main = mainAlgorithm binfo oinfo vinfo} in
  case IState.runIState main blocks of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) res b -> Prelude.Right res}}

