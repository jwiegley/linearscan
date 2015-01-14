{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Main where

import Debug.Trace
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

coq_SSError_rect :: (Prelude.Int -> a1) -> (Prelude.Int -> a1) ->
                               a1 -> (Prelude.Int -> a1) -> (Prelude.Int ->
                               a1) -> SSError -> a1
coq_SSError_rect f f0 f1 f2 f3 s =
  case s of {
   ECannotSplitSingleton x -> f x;
   ECannotSplitAssignedSingleton x -> f0 x;
   ENoIntervalsToSplit -> f1;
   ERegisterAlreadyAssigned x -> f2 x;
   ERegisterAssignmentsOverlap x -> f3 x}

coq_SSError_rec :: (Prelude.Int -> a1) -> (Prelude.Int -> a1) ->
                              a1 -> (Prelude.Int -> a1) -> (Prelude.Int ->
                              a1) -> SSError -> a1
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

totalExtent :: ScanStateDesc -> ([]
                          IntervalId) -> Prelude.Int
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

getScanStateDesc :: ScanStateDesc ->
                               ScanStateDesc
getScanStateDesc sd =
  sd

packScanState :: ScanStateDesc ->
                            ScanStateDesc
packScanState sd =
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

type VarId = Prelude.Int

data VarKind =
   Input
 | Temp
 | Output
  deriving Prelude.Show

coq_VarKind_rect :: a1 -> a1 -> a1 -> VarKind -> a1
coq_VarKind_rect f f0 f1 v =
  case v of {
   Input -> f;
   Temp -> f0;
   Output -> f1}

coq_VarKind_rec :: a1 -> a1 -> a1 -> VarKind -> a1
coq_VarKind_rec =
  coq_VarKind_rect

data Allocation =
   Unallocated
 | Register PhysReg
 | Spill deriving (Prelude.Show, Prelude.Eq)

coq_Allocation_rect :: a1 -> (PhysReg -> a1) -> a1 ->
                                  Allocation -> a1
coq_Allocation_rect f f0 f1 a =
  case a of {
   Unallocated -> f;
   Register x -> f0 x;
   Spill -> f1}

coq_Allocation_rec :: a1 -> (PhysReg -> a1) -> a1 ->
                                 Allocation -> a1
coq_Allocation_rec =
  coq_Allocation_rect

data VarInfo =
   Build_VarInfo VarId VarKind Allocation 
 Prelude.Bool
  deriving Prelude.Show

coq_VarInfo_rect :: (VarId -> VarKind ->
                               Allocation -> Prelude.Bool -> a1) ->
                               VarInfo -> a1
coq_VarInfo_rect f v =
  case v of {
   Build_VarInfo x x0 x1 x2 -> f x x0 x1 x2}

coq_VarInfo_rec :: (VarId -> VarKind ->
                              Allocation -> Prelude.Bool -> a1) ->
                              VarInfo -> a1
coq_VarInfo_rec =
  coq_VarInfo_rect

varId :: VarInfo -> VarId
varId v =
  case v of {
   Build_VarInfo varId0 varKind0 varAlloc0 regRequired0 -> varId0}

varKind :: VarInfo -> VarKind
varKind v =
  case v of {
   Build_VarInfo varId0 varKind0 varAlloc0 regRequired0 -> varKind0}

varAlloc :: VarInfo -> Allocation
varAlloc v =
  case v of {
   Build_VarInfo varId0 varKind0 varAlloc0 regRequired0 ->
    varAlloc0}

regRequired :: VarInfo -> Prelude.Bool
regRequired v =
  case v of {
   Build_VarInfo varId0 varKind0 varAlloc0 regRequired0 ->
    regRequired0}

type VarList = [] VarInfo

type OpId = Prelude.Int

data OpKind =
   Normal
 | LoopBegin
 | LoopEnd
 | Call
  deriving Prelude.Show

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

data OpInfo =
   Build_OpInfo OpId OpKind VarList 
 ([] PhysReg)
  deriving Prelude.Show

coq_OpInfo_rect :: (OpId -> OpKind ->
                              VarList -> ([] PhysReg) ->
                              a1) -> OpInfo -> a1
coq_OpInfo_rect f o =
  case o of {
   Build_OpInfo x x0 x1 x2 -> f x x0 x1 x2}

coq_OpInfo_rec :: (OpId -> OpKind ->
                             VarList -> ([] PhysReg) ->
                             a1) -> OpInfo -> a1
coq_OpInfo_rec =
  coq_OpInfo_rect

opId :: OpInfo -> OpId
opId o =
  case o of {
   Build_OpInfo opId0 opKind0 varRefs0 regRefs0 -> opId0}

opKind :: OpInfo -> OpKind
opKind o =
  case o of {
   Build_OpInfo opId0 opKind0 varRefs0 regRefs0 -> opKind0}

varRefs :: OpInfo -> VarList
varRefs o =
  case o of {
   Build_OpInfo opId0 opKind0 varRefs0 regRefs0 -> varRefs0}

regRefs :: OpInfo -> [] PhysReg
regRefs o =
  case o of {
   Build_OpInfo opId0 opKind0 varRefs0 regRefs0 -> regRefs0}

type OpList = [] OpInfo

type BlockId = Prelude.Int

data BlockInfo =
   Build_BlockInfo BlockId OpList

coq_BlockInfo_rect :: (BlockId -> OpList ->
                                 a1) -> BlockInfo -> a1
coq_BlockInfo_rect f b =
  case b of {
   Build_BlockInfo x x0 -> f x x0}

coq_BlockInfo_rec :: (BlockId -> OpList -> a1)
                                -> BlockInfo -> a1
coq_BlockInfo_rec =
  coq_BlockInfo_rect

blockId :: BlockInfo -> BlockId
blockId b =
  case b of {
   Build_BlockInfo blockId0 blockOps0 -> blockId0}

blockOps :: BlockInfo -> OpList
blockOps b =
  case b of {
   Build_BlockInfo blockId0 blockOps0 -> blockOps0}

type BlockList = [] BlockInfo

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
                                                                   Range.RangeDesc))

coq_BuildState_rect :: (Prelude.Int -> ([]
                                  (Prelude.Maybe BoundedRange)) ->
                                  ([] (Prelude.Maybe Range.RangeDesc)) -> a1)
                                  -> BuildState -> a1
coq_BuildState_rect f b =
  case b of {
   Build_BuildState x x0 x1 -> f x x0 x1}

coq_BuildState_rec :: (Prelude.Int -> ([]
                                 (Prelude.Maybe BoundedRange)) ->
                                 ([] (Prelude.Maybe Range.RangeDesc)) -> a1)
                                 -> BuildState -> a1
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
                     (Prelude.Maybe Range.RangeDesc)
bsRegs b =
  case b of {
   Build_BuildState bsPos0 bsVars0 bsRegs0 -> bsRegs0}

foldOps :: (a1 -> OpInfo -> a1) -> a1 ->
                      BlockList -> a1
foldOps f z =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (blockOps blk)) z

foldOpsRev :: (a1 -> OpInfo -> a1) -> a1 ->
                         BlockList -> a1
foldOpsRev f z blocks =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (Seq.rev (blockOps blk))) z
    (Seq.rev ( blocks))

mapWithIndex :: (Prelude.Int -> a1 -> a2) -> ([] a1) -> [] a2
mapWithIndex f l =
  Seq.rev
    (Prelude.snd
      (Data.List.foldl' (\acc x ->
        case acc of {
         (,) n xs -> (,) ((Prelude.succ) n) ((:) (f n x) xs)}) ((,) 0 []) l))

mapOps :: (OpInfo -> OpInfo) ->
                     BlockList -> BlockList
mapOps f =
  Prelude.map (\blk -> Build_BlockInfo (blockId blk)
    (Prelude.map f (blockOps blk)))

mapAccumLOps :: (a1 -> OpInfo -> (,) a1
                           OpInfo) -> a1 -> BlockList ->
                           (,) a1 BlockList
mapAccumLOps f =
  NonEmpty0.coq_NE_mapAccumL (\z blk ->
    case Lib.mapAccumL f z (blockOps blk) of {
     (,) z' ops -> (,) z' (Build_BlockInfo (blockId blk)
      ops)})

processOperations :: BlockList -> BuildState
processOperations blocks =
  (Prelude.flip (Prelude.$))
    (foldOps (\x op ->
      case x of {
       (,) n m -> (,) ((Prelude.succ) n)
        (Data.List.foldl' (\m0 v -> Prelude.max m0 (varId v)) m
          (varRefs op))}) ((,) 0 0) blocks) (\_top_assumption_ ->
    let {
     _evar_0_ = \opCount highestVar ->
      let {
       z = Build_BuildState opCount
        (Seq.nseq ((Prelude.succ) highestVar) Prelude.Nothing)
        (Data.List.replicate maxReg Prelude.Nothing)}
      in
      foldOpsRev (\_top_assumption_0 ->
        let {
         _evar_0_ = \pos vars regs op ->
          let {_evar_0_ = \vars0 -> Build_BuildState 0 vars0 regs}
          in
          let {
           _evar_0_0 = \pos0 vars0 -> Build_BuildState pos0
            ((Prelude.flip (Prelude.$))
              ((Prelude.flip (Prelude.$)) __ (\_ ->
                (Prelude.flip (Prelude.$)) vars0 (\vars' ->
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
                      (Ssrnat.double pos0)) (regRequired v)}
                    in
                    (Prelude.flip (Prelude.$)) __ (\_ ->
                      Seq.set_nth Prelude.Nothing vars'1 (varId v)
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
                         case Seq.nth Prelude.Nothing vars0
                                (varId v) of {
                          Prelude.Just x -> _evar_0_0 x;
                          Prelude.Nothing -> _evar_0_1})))) vars'0
                    (varRefs op)))) (\x -> x)) regs}
          in
          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
            (\_ ->
            _evar_0_ vars)
            (\x ->
            _evar_0_0 x vars)
            (traceShow op pos)}
        in
        case _top_assumption_0 of {
         Build_BuildState x x0 x1 -> _evar_0_ x x0 x1}) z blocks}
    in
    case _top_assumption_ of {
     (,) x x0 -> _evar_0_ x x0})

computeBlockOrder :: IState.IState SSError
                                BlockList BlockList 
                                ()
computeBlockOrder =
  return_ ()

numberOperations :: IState.IState SSError
                               BlockList BlockList 
                               ()
numberOperations =
  let {
   f = \n op -> (,) ((Prelude.succ) ((Prelude.succ) n))
    (Build_OpInfo n (opKind op) (varRefs op)
    (regRefs op))}
  in
  IState.imodify
    ((Prelude..) Prelude.snd (mapAccumLOps f ((Prelude.succ) 0)))

type BlockState a =
  IState.IState SSError BlockList BlockList a

computeLocalLiveSets :: BlockState ()
computeLocalLiveSets =
  return_ ()

computeGlobalLiveSets :: BlockState ()
computeGlobalLiveSets =
  return_ ()

buildIntervals :: IState.IState SSError
                             BlockList BlockList
                             ScanStateDesc
buildIntervals =
  let {
   mkint = \vid ss pos mx f ->
    case mx of {
     Prelude.Just b ->
      f ss __ (Interval.Build_IntervalDesc vid (Range.rbeg ( b))
        (Range.rend ( b)) ((:[]) ( b))) __;
     Prelude.Nothing -> ss}}
  in
  let {
   handleVar = \pos vid ss mx ->
    (Prelude.$) (mkint vid ss pos mx) (\sd _ d _ ->
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
  stbind (\blocks ->
    let {bs = processOperations blocks} in
    let {
     regs = LinearScan.Utils.vmap maxReg (\mr ->
              case mr of {
               Prelude.Just r -> Prelude.Just
                (Interval.packInterval (Interval.Build_IntervalDesc 0
                  (Range.rbeg ( r)) (Range.rend ( r)) ((:[]) ( r))));
               Prelude.Nothing -> Prelude.Nothing}) (bsRegs bs)}
    in
    let {
     s2 = packScanState (Build_ScanStateDesc
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
    (Prelude.$) return_
      (Lib.foldl_with_index (handleVar (bsPos bs)) s2
        (bsVars bs))) IState.iget

resolveDataFlow :: BlockState ()
resolveDataFlow =
  return_ ()

assignRegNum :: ScanStateDesc -> IState.IState
                           SSError BlockList
                           BlockList ()
assignRegNum sd =
  let {
   ints = (Prelude.++) (handled sd)
            ((Prelude.++) (active sd) (inactive sd))}
  in
  let {
   f = \op ->
    let {
     k = \v ->
      let {vid = varId v} in
      let {
       h = \acc x ->
        case x of {
         (,) xid reg ->
          let {
           int = Interval.getIntervalDesc
                   (
                     (LinearScan.Utils.nth (nextInterval sd)
                       (intervals sd) xid))}
          in
          case (Prelude.&&)
                 (Eqtype.eq_op Ssrnat.nat_eqType
                   (unsafeCoerce (Interval.ivar int)) (unsafeCoerce vid))
                 ((Prelude.&&)
                   ((Prelude.<=) (Interval.ibeg int) (opId op))
                   ((Prelude.<=) ((Prelude.succ) (opId op))
                     (Interval.iend int))) of {
           Prelude.True -> Build_VarInfo (varId v)
            (varKind v) (Register reg)
            (regRequired v);
           Prelude.False -> acc}}}
      in
      Data.List.foldl' h v ints}
    in
    Build_OpInfo (opId op) (opKind op)
    (Prelude.map k (varRefs op)) (regRefs op)}
  in
  IState.imodify (mapOps f)

coq_SSMorph_rect :: ScanStateDesc ->
                               ScanStateDesc -> (() -> () -> () ->
                               a1) -> a1
coq_SSMorph_rect sd1 sd2 f =
  f __ __ __

coq_SSMorph_rec :: ScanStateDesc ->
                              ScanStateDesc -> (() -> () -> () ->
                              a1) -> a1
coq_SSMorph_rec sd1 sd2 f =
  coq_SSMorph_rect sd1 sd2 f

coq_SSMorphSt_rect :: ScanStateDesc ->
                                 ScanStateDesc -> (() -> () -> a1)
                                 -> a1
coq_SSMorphSt_rect sd1 sd2 f =
  f __ __

coq_SSMorphSt_rec :: ScanStateDesc ->
                                ScanStateDesc -> (() -> () -> a1)
                                -> a1
coq_SSMorphSt_rec sd1 sd2 f =
  coq_SSMorphSt_rect sd1 sd2 f

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

transportation :: ScanStateDesc ->
                             ScanStateDesc -> IntervalId
                             -> IntervalId
transportation sd1 sd2 x =
   x

data HasBase p =
   Build_HasBase

coq_HasBase_rect :: (() -> a2) -> a2
coq_HasBase_rect f =
  f __

coq_HasBase_rec :: (() -> a2) -> a2
coq_HasBase_rec f =
  coq_HasBase_rect f

coq_SSMorphStLen_rect :: ScanStateDesc ->
                                    ScanStateDesc -> (() -> () ->
                                    a1) -> a1
coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphStLen_rec :: ScanStateDesc ->
                                   ScanStateDesc -> (() -> () ->
                                   a1) -> a1
coq_SSMorphStLen_rec sd1 sd2 f =
  coq_SSMorphStLen_rect sd1 sd2 f

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

coq_SSMorphStHasLen_rect :: ScanStateDesc ->
                                       ScanStateDesc -> (() -> ()
                                       -> a1) -> a1
coq_SSMorphStHasLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphStHasLen_rec :: ScanStateDesc ->
                                      ScanStateDesc -> (() -> () ->
                                      a1) -> a1
coq_SSMorphStHasLen_rec sd1 sd2 f =
  coq_SSMorphStHasLen_rect sd1 sd2 f

coq_SSMorphSplit_rect :: ScanStateDesc ->
                                    ScanStateDesc -> (() -> () ->
                                    a1) -> a1
coq_SSMorphSplit_rect sd1 sd2 f =
  f __ __

coq_SSMorphSplit_rec :: ScanStateDesc ->
                                   ScanStateDesc -> (() -> () ->
                                   a1) -> a1
coq_SSMorphSplit_rec sd1 sd2 f =
  coq_SSMorphSplit_rect sd1 sd2 f

data IsSplittable p =
   Build_IsSplittable

coq_IsSplittable_rect :: (() -> a2) -> a2
coq_IsSplittable_rect f =
  f __

coq_IsSplittable_rec :: (() -> a2) -> a2
coq_IsSplittable_rec f =
  coq_IsSplittable_rect f

coq_SSMorphStSplit_rect :: ScanStateDesc ->
                                      ScanStateDesc -> (() -> () ->
                                      a1) -> a1
coq_SSMorphStSplit_rect sd1 sd2 f =
  f __ __

coq_SSMorphStSplit_rec :: ScanStateDesc ->
                                     ScanStateDesc -> (() -> () ->
                                     a1) -> a1
coq_SSMorphStSplit_rec sd1 sd2 f =
  coq_SSMorphStSplit_rect sd1 sd2 f

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

weakenStHasLenToSt :: ScanStateDesc -> SState
                                 () () ()
weakenStHasLenToSt pre hS =
  Prelude.Right ((,) ()
    (case hS of {
      Build_SSInfo thisDesc0 _ -> Build_SSInfo thisDesc0
       __}))

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

distance :: Prelude.Int -> Prelude.Int -> Prelude.Int
distance n m =
  case (Prelude.<=) ((Prelude.succ) n) m of {
   Prelude.True -> (Prelude.-) m n;
   Prelude.False -> (Prelude.-) n m}

splitCurrentInterval :: ScanStateDesc -> (Prelude.Maybe
                                   Prelude.Int) -> SState a1 
                                   () ()
splitCurrentInterval pre before ssi =
  let {
   _evar_0_ = \desc holds ->
    let {
     _evar_0_ = \_nextInterval_ intervals0 _fixedIntervals_ unhandled0 _active_ _inactive_ _handled_ ->
      let {_evar_0_ = \holds0 -> Logic.coq_False_rect} in
      let {
       _evar_0_0 = \_top_assumption_ ->
        let {
         _evar_0_0 = \uid beg us holds0 ->
          let {int = LinearScan.Utils.nth _nextInterval_ intervals0 uid} in
          let {
           _evar_0_0 = \_ -> Prelude.Left (ECannotSplitSingleton
            ( uid))}
          in
          let {
           _evar_0_1 = \_ -> Prelude.Right ((,) ()
            ((Prelude.flip (Prelude.$)) __ (\_ ->
              let {
               _top_assumption_0 = Interval.splitPosition ( int) before
                                     Prelude.True}
              in
              let {
               _top_assumption_1 = Interval.splitInterval _top_assumption_0
                                     ( int)}
              in
              let {
               _evar_0_1 = \_top_assumption_2 _top_assumption_3 ->
                let {
                 _evar_0_1 = \_ ->
                  (Prelude.flip (Prelude.$)) __ (\_ ->
                    (Prelude.flip (Prelude.$)) __
                      ((Prelude.flip (Prelude.$)) __
                        ((Prelude.flip (Prelude.$)) __ (\_ _ _ ->
                          (Prelude.flip (Prelude.$)) __
                            ((Prelude.flip (Prelude.$)) __
                              (let {
                                new_unhandled_added = Build_ScanStateDesc
                                 ((Prelude.succ) _nextInterval_)
                                 (LinearScan.Utils.snoc _nextInterval_
                                   (LinearScan.Utils.set_nth _nextInterval_
                                     intervals0 uid _top_assumption_2)
                                   _top_assumption_3) _fixedIntervals_
                                 (Data.List.insertBy
                                   (Data.Ord.comparing Prelude.snd) ((,)
                                   ( _nextInterval_)
                                   (Interval.ibeg _top_assumption_3)) ((:)
                                   (Prelude.id ((,) uid beg))
                                   (Prelude.map Prelude.id us)))
                                 (Prelude.map Prelude.id _active_)
                                 (Prelude.map Prelude.id _inactive_)
                                 (Prelude.map Prelude.id _handled_)}
                               in
                               \_ _ -> Build_SSInfo
                               new_unhandled_added __))))))}
                in
                 _evar_0_1 __}
              in
              case _top_assumption_1 of {
               (,) x x0 -> _evar_0_1 x x0})))}
          in
          case Interval.coq_Interval_is_singleton ( int) of {
           Prelude.True -> _evar_0_0 __;
           Prelude.False -> _evar_0_1 __}}
        in
        (\us _ _ _ _ _ holds0 _ _ ->
        case _top_assumption_ of {
         (,) x x0 -> _evar_0_0 x x0 us holds0})}
      in
      case unhandled0 of {
       [] -> (\_ _ _ _ holds0 _ _ -> _evar_0_ holds0);
       (:) x x0 -> _evar_0_0 x x0 __}}
    in
    case desc of {
     Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
      _evar_0_ x x0 x1 x2 x3 x4 x5 __ __ __ __ holds __}}
  in
  case ssi of {
   Build_SSInfo x x0 -> _evar_0_ x x0 __}

create_ssinfo :: Prelude.Int -> ([] Interval.IntervalDesc) ->
                            Coq_fixedIntervalsType -> ([]
                            ((,) Prelude.Int Prelude.Int)) -> ([]
                            ((,) Prelude.Int PhysReg)) -> ([]
                            ((,) Prelude.Int PhysReg)) -> ([]
                            ((,) Prelude.Int PhysReg)) ->
                            ScanStateDesc -> Prelude.Int ->
                            Prelude.Int -> Interval.IntervalDesc ->
                            Interval.IntervalDesc -> ([]
                            ((,) Prelude.Int PhysReg)) -> ([]
                            ((,) Prelude.Int PhysReg)) ->
                            SSInfo ()
create_ssinfo ni intervals0 fixedIntervals0 unh active0 inactive0 handled0 pre aid pos' id0 id1 active1 inactive1 =
  let {
   new_inactive_added = Build_ScanStateDesc ((Prelude.succ) ni)
    (LinearScan.Utils.snoc ni
      (LinearScan.Utils.set_nth ni intervals0 aid id0) id1) fixedIntervals0
    (Prelude.map (\i -> Prelude.id i) unh) active1 inactive1
    (Prelude.map (\i -> Prelude.id i) handled0)}
  in
  Build_SSInfo new_inactive_added __

splitAssignedIntervalForReg :: ScanStateDesc ->
                                          PhysReg -> (Prelude.Maybe
                                          Prelude.Int) -> Prelude.Bool ->
                                          SState a1 () ()
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
         _evar_0_ = \_ ->
          let {
           _evar_0_ = \ni intervals0 _fixedIntervals_ unh active0 _inactive_ _handled_ holds0 intlist0 intids0 ->
            let {_evar_0_ = \_ -> Prelude.Left ENoIntervalsToSplit}
            in
            let {
             _evar_0_0 = \aid aids iHaids ->
              let {int = LinearScan.Utils.nth ni intervals0 aid} in
              let {_evar_0_0 = \_ -> iHaids __} in
              let {
               _evar_0_1 = \_ ->
                (Prelude.flip (Prelude.$)) __ (\_ ->
                  let {
                   _top_assumption_ = Interval.splitPosition ( int) pos
                                        Prelude.False}
                  in
                  let {_evar_0_1 = iHaids __} in
                  let {
                   _evar_0_2 = Prelude.Right ((,) ()
                    (let {
                      _top_assumption_0 = Interval.splitInterval
                                            _top_assumption_ ( int)}
                     in
                     let {
                      _evar_0_2 = \_top_assumption_1 _top_assumption_2 ->
                       let {
                        _evar_0_2 = \_ ->
                         (Prelude.flip (Prelude.$)) __ (\_ ->
                           let {
                            _evar_0_2 = \_ _ ->
                             (Prelude.flip (Prelude.$)) __
                               (let {
                                 _evar_0_2 = \_ ->
                                  (Prelude.flip (Prelude.$)) __ (\_ ->
                                    create_ssinfo ni intervals0
                                      _fixedIntervals_ unh active0 _inactive_
                                      _handled_ pre aid _top_assumption_
                                      _top_assumption_1 _top_assumption_2
                                      (Prelude.map (unsafeCoerce Prelude.id)
                                        (Seq.rem
                                          (Eqtype.prod_eqType
                                            (Fintype.ordinal_eqType ni)
                                            (Fintype.ordinal_eqType
                                              maxReg))
                                          (unsafeCoerce ((,) aid reg))
                                          intlist0)) ((:) ((,) ( ni) reg)
                                      ((:) (Prelude.id ((,) aid reg))
                                      (Prelude.map Prelude.id _inactive_))))}
                                in
                                 _evar_0_2)}
                           in
                           let {
                            _evar_0_3 = \_ _ ->
                             (Prelude.flip (Prelude.$)) __ (\_ ->
                               create_ssinfo ni intervals0
                                 _fixedIntervals_ unh active0 _inactive_
                                 _handled_ pre aid _top_assumption_
                                 _top_assumption_1 _top_assumption_2
                                 (Prelude.map Prelude.id active0) ((:) ((,)
                                 ( ni) reg)
                                 (Prelude.map Prelude.id _inactive_)))}
                           in
                           case trueForActives of {
                            Prelude.True -> _evar_0_2 __ __;
                            Prelude.False -> _evar_0_3 __ __})}
                       in
                        _evar_0_2 __}
                     in
                     case _top_assumption_0 of {
                      (,) x x0 -> _evar_0_2 x x0}))}
                  in
                  case Eqtype.eq_op (Eqtype.option_eqType Ssrnat.nat_eqType)
                         (unsafeCoerce pos)
                         (unsafeCoerce (Prelude.Just
                           (Prelude.pred _top_assumption_))) of {
                   Prelude.True -> _evar_0_1;
                   Prelude.False -> _evar_0_2})}
              in
              case Interval.coq_Interval_is_singleton ( int) of {
               Prelude.True -> _evar_0_0 __;
               Prelude.False -> _evar_0_1 __}}
            in
            Datatypes.list_rect _evar_0_ (\aid aids iHaids _ ->
              _evar_0_0 aid aids iHaids) intids0 __}
          in
          (\intlist0 _ intids0 _ ->
          case desc of {
           Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
            _evar_0_ x x0 x1 x2 x3 x4 x5 holds intlist0 intids0})}
        in
        unsafeCoerce _evar_0_ __ intlist __ intids __))}
  in
  case ssi of {
   Build_SSInfo x x0 -> _evar_0_ x x0}

splitActiveIntervalForReg :: ScanStateDesc ->
                                        PhysReg -> Prelude.Int ->
                                        SState a1 () ()
splitActiveIntervalForReg pre reg pos =
  splitAssignedIntervalForReg pre reg (Prelude.Just pos)
    Prelude.True

splitAnyInactiveIntervalForReg :: ScanStateDesc ->
                                             PhysReg ->
                                             SState a1 () ()
splitAnyInactiveIntervalForReg pre reg ss =
  (Prelude.flip (Prelude.$)) (\s _ _ ->
    splitAssignedIntervalForReg s reg Prelude.Nothing
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

tryAllocateFreeReg :: ScanStateDesc -> SState
                                 a1 a1
                                 (Prelude.Maybe
                                 (SState a1 () PhysReg))
tryAllocateFreeReg pre =
  (Prelude.$) (withCursor pre) (\sd _ ->
    let {
     go = \n ->
      Data.List.foldl' (\v p ->
        case p of {
         (,) i r -> LinearScan.Utils.set_nth maxReg v r (n i)})}
    in
    let {
     freeUntilPos' = go (\x -> Prelude.Just 0)
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
     freeUntilPos = go (\i ->
                      Interval.intervalIntersectionPoint
                        (
                          (LinearScan.Utils.nth (nextInterval sd)
                            (intervals sd) i))
                        ( (curIntDetails sd))) freeUntilPos'
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
                          (splitCurrentInterval pre (Prelude.Just
                            n))})};
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
                       (
                         (LinearScan.Utils.nth (nextInterval sd)
                           (intervals sd) i)) atPos of {
                 Prelude.Just p0 -> Prelude.Just 0;
                 Prelude.Nothing ->
                  Interval.nextUseAfter
                    (
                      (LinearScan.Utils.nth (nextInterval sd)
                        (intervals sd) i)) start}}
        in
        LinearScan.Utils.set_nth maxReg v r pos'}}
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
                (weakenStHasLenToSt pre))
              (case mloc of {
                Prelude.Just n ->
                 splitCurrentInterval pre (Prelude.Just n);
                Prelude.Nothing -> return_ ()}))
            (intersectsWithFixedInterval pre reg))
          (splitCurrentInterval pre
            (Interval.firstUseReqReg ( (curIntDetails sd))));
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
                     (splitCurrentInterval pre (Prelude.Just n));
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

walkIntervals_func :: ((,) ScanStateDesc ()) ->
                                 Prelude.Either SSError
                                 ScanStateDesc
walkIntervals_func x =
  let {sd = Prelude.fst x} in
  let {
   walkIntervals0 = \sd0 ->
    let {y = (,) sd0 __} in walkIntervals_func ( y)}
  in
  let {filtered_var = LinearScan.Utils.uncons (unhandled sd)} in
  case filtered_var of {
   Prelude.Just s ->
    let {ssinfo = Build_SSInfo sd __} in
    let {
     filtered_var0 = IState.runIState (handleInterval sd) ssinfo}
    in
    case filtered_var0 of {
     Prelude.Left err -> Prelude.Left err;
     Prelude.Right p ->
      case p of {
       (,) wildcard' ssinfo' ->
        walkIntervals0 (thisDesc sd ssinfo')}};
   Prelude.Nothing -> Prelude.Right (packScanState sd)}

walkIntervals :: ScanStateDesc -> Prelude.Either
                            SSError ScanStateDesc
walkIntervals sd =
  walkIntervals_func ((,) sd __)

mainAlgorithm :: IState.IState SSError BlockList
                 BlockList ()
mainAlgorithm =
  stbind (\x ->
    stbind (\x0 ->
      stbind (\x1 ->
        stbind (\x2 ->
          stbind (\ssig ->
            case walkIntervals ( ssig) of {
             Prelude.Left err -> error_ err;
             Prelude.Right ssig' ->
              stbind (\x3 -> assignRegNum ( ssig'))
                resolveDataFlow}) buildIntervals)
          computeGlobalLiveSets) computeLocalLiveSets)
      numberOperations) computeBlockOrder

linearScan :: BlockList -> Prelude.Either SSError
              BlockList
linearScan blocks =
  case IState.runIState mainAlgorithm blocks of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) u res -> Prelude.Right res}}

