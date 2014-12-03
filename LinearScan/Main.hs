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

coq_VarInfo_rec :: (VarId -> VarKind ->
                              Prelude.Bool -> a1) -> VarInfo -> a1
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

coq_OpInfo_rect :: ((a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool)
                              -> (a1 -> Prelude.Maybe
                              ([] MyMachine__PhysReg)) -> (a1 ->
                              Prelude.Bool) -> (a1 -> [] VarInfo)
                              -> (a1 -> [] MyMachine__PhysReg) -> a2) ->
                              (OpInfo a1) -> a2
coq_OpInfo_rect f o =
  case o of {
   Build_OpInfo x x0 x1 x2 x3 x4 -> f x x0 x1 x2 x3 x4}

coq_OpInfo_rec :: ((a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool) ->
                             (a1 -> Prelude.Maybe ([] MyMachine__PhysReg)) ->
                             (a1 -> Prelude.Bool) -> (a1 -> []
                             VarInfo) -> (a1 -> []
                             MyMachine__PhysReg) -> a2) -> (OpInfo
                             a1) -> a2
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

data Allocation =
   Unallocated
 | Register MyMachine__PhysReg
 | Spill

coq_Allocation_rect :: a1 -> (MyMachine__PhysReg -> a1) -> a1 ->
                                  Allocation -> a1
coq_Allocation_rect f f0 f1 a =
  case a of {
   Unallocated -> f;
   Register x -> f0 x;
   Spill -> f1}

coq_Allocation_rec :: a1 -> (MyMachine__PhysReg -> a1) -> a1 ->
                                 Allocation -> a1
coq_Allocation_rec =
  coq_Allocation_rect

data OpData opType =
   Build_OpData opType (OpInfo opType) Prelude.Int 
 (VarId -> Allocation)

coq_OpData_rect :: (a1 -> (OpInfo a1) -> Prelude.Int ->
                              () -> (VarId -> Allocation)
                              -> a2) -> (OpData a1) -> a2
coq_OpData_rect f o =
  case o of {
   Build_OpData x x0 x1 x2 -> f x x0 x1 __ x2}

coq_OpData_rec :: (a1 -> (OpInfo a1) -> Prelude.Int ->
                             () -> (VarId -> Allocation)
                             -> a2) -> (OpData a1) -> a2
coq_OpData_rec =
  coq_OpData_rect

baseOp :: (OpData a1) -> a1
baseOp o =
  case o of {
   Build_OpData baseOp0 opInfo0 opId0 opAlloc0 -> baseOp0}

opInfo :: (OpData a1) -> OpInfo a1
opInfo o =
  case o of {
   Build_OpData baseOp0 opInfo0 opId0 opAlloc0 -> opInfo0}

opId :: (OpData a1) -> Prelude.Int
opId o =
  case o of {
   Build_OpData baseOp0 opInfo0 opId0 opAlloc0 -> opId0}

opAlloc :: (OpData a1) -> VarId ->
                      Allocation
opAlloc o =
  case o of {
   Build_OpData baseOp0 opInfo0 opId0 opAlloc0 -> opAlloc0}

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
                          Coq_boundedRange ->
                          Coq_boundedRange
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
      (let {_evar_0_0 = boundedSing upos} in
       Prelude.Just _evar_0_0)}
    in
    case _top_assumption_0 of {
     Prelude.Just x -> _evar_0_ x;
     Prelude.Nothing -> _evar_0_0}}
  in
  case _top_assumption_ of {
   (,) x x0 -> _evar_0_ x x0}

emptyBoundedRangeVec :: Prelude.Int ->
                                   Coq_boundedRangeVec
emptyBoundedRangeVec n =
  Build_boundedRangeVec []
    (Data.List.replicate _MyMachine__maxReg ((,) ((,) Prelude.Nothing
      Prelude.Nothing) Prelude.Nothing))

handleOp :: (OpData a1) -> Coq_boundedRangeVec
                       -> Coq_boundedRangeVec
handleOp op rest =
  let {pos = opId op} in
  let {
   liftOr = \f mx y -> Prelude.Just
    (case mx of {
      Prelude.Just x -> f x y;
      Prelude.Nothing -> y})}
  in
  let {
   savingBound = \x ->
    case (Prelude.||)
           (isLoopBegin (opInfo op)
             (baseOp op))
           (isLoopEnd (opInfo op)
             (baseOp op)) of {
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
    withRanges pos req upos ((Prelude.succ) ((Prelude.succ) pos))
      x}
  in
  let {
   restVars' = Prelude.map savingBound
                 (vars ((Prelude.succ) ((Prelude.succ)
                   (opId op))) rest)}
  in
  let {
   restRegs' = LinearScan.Utils.vmap _MyMachine__maxReg savingBound
                 (regs ((Prelude.succ) ((Prelude.succ)
                   (opId op))) rest)}
  in
  let {
   unchanged = LinearScan.Utils.boundedTransport' (opId op)
                 ((Prelude.succ) ((Prelude.succ) (opId op)))
                 (Build_boundedRangeVec restVars' restRegs')}
  in
  let {
   rest2 = case varRefs (opInfo op)
                  (baseOp op) of {
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
               Prelude.Nothing)
               (vars (opId op) unchanged)
               (varId v) x)
             (regs (opId op) unchanged)}}
  in
  case regRefs (opInfo op) (baseOp op) of {
   [] -> rest2;
   (:) r rs ->
    let {
     x = consr (LinearScan.Utils.nth _MyMachine__maxReg restRegs' r)
           Prelude.False}
    in
    Build_boundedRangeVec
    (vars (opId op) rest2)
    (LinearScan.Utils.set_nth _MyMachine__maxReg
      (transportVecBounds (opId op) _MyMachine__maxReg
        ((Prelude.succ) ((Prelude.succ) (opId op))) restRegs') r
      x)}

extractRange :: Prelude.Int -> Coq_boundedTriple ->
                           Prelude.Maybe Range.RangeDesc
extractRange n x =
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

shift_range_vec :: Prelude.Int -> Prelude.Int ->
                              Coq_boundedRangeVec ->
                              Coq_boundedRangeVec
shift_range_vec n m =
  let {_evar_0_ = \x -> x} in  _evar_0_

data Coq_relseq a =
   Coq_rl_nil
 | Coq_rl_cons a ([] a) (Coq_relseq a)

relseq_rect :: (Ssrbool.Coq_rel a1) -> a2 -> (a1 -> ([] a1) ->
                          (Coq_relseq a1) -> a2 -> () -> a2) -> ([]
                          a1) -> (Coq_relseq a1) -> a2
relseq_rect r f f0 l r0 =
  case r0 of {
   Coq_rl_nil -> f;
   Coq_rl_cons x xs r1 ->
    f0 x xs r1 (relseq_rect r f f0 xs r1) __}

relseq_rec :: (Ssrbool.Coq_rel a1) -> a2 -> (a1 -> ([] a1) ->
                         (Coq_relseq a1) -> a2 -> () -> a2) -> ([]
                         a1) -> (Coq_relseq a1) -> a2
relseq_rec r =
  relseq_rect r

is_seqn :: (OpData a1) -> (OpData a1) ->
                      Prelude.Bool
is_seqn x y =
  Eqtype.eq_op Ssrnat.nat_eqType
    (unsafeCoerce ((Prelude.succ) ((Prelude.succ) (opId x))))
    (unsafeCoerce (opId y))

type Coq_rel_OpList opType =
  (,) ([] (OpData opType))
  (Coq_relseq (OpData opType))

cat_relseq :: (Ssrbool.Coq_rel a1) -> a1 -> ([] a1) -> a1 -> ([]
                         a1) -> (Coq_relseq a1) ->
                         (Coq_relseq a1) -> Coq_relseq 
                         a1
cat_relseq r x xs y ys hxs hys =
  let {_evar_0_ = \hxs0 -> Coq_rl_cons x ((:) y ys) hys} in
  let {
   _evar_0_0 = \z zs iHzs hxs0 -> Coq_rl_cons z
    ((Prelude.++) (Seq.rcons zs x) ((:) y ys))
    (iHzs
      (case hxs0 of {
        Coq_rl_nil -> Logic.coq_False_rect;
        Coq_rl_cons x0 xs0 x1 ->  (\_ ->  (\x2 _ -> x2)) __ x1 __}))}
  in
  Datatypes.list_rect _evar_0_ _evar_0_0 xs hxs

applyList :: (OpInfo a1) -> a1 -> ([] a1) ->
                        (Prelude.Int -> Coq_boundedRangeVec) ->
                        ((OpData a1) ->
                        Coq_boundedRangeVec ->
                        Coq_boundedRangeVec) -> (,)
                        ([] (OpData a1))
                        Coq_boundedRangeVec
applyList opInfo0 op ops base f =
  let {
   go i x xs =
     let {
      newop = Build_OpData x opInfo0 i (\x0 ->
       Unallocated)}
     in
     case xs of {
      [] -> (,) ((:) newop []) (f newop (base i));
      (:) y ys ->
       case go ((Prelude.succ) ((Prelude.succ) i)) y ys of {
        (,) ops' next -> (,) ((:) newop ops') (f newop next)}}}
  in go ((Prelude.succ) 0) op ops

processOperations :: (OpInfo a1) -> ([] a1) -> (,)
                                ((,) ([] (OpData a1))
                                ([] (Prelude.Maybe Range.RangeDesc)))
                                ([] (Prelude.Maybe Range.RangeDesc))
processOperations opInfo0 ops =
  case LinearScan.Utils.uncons ops of {
   Prelude.Just s ->
    case s of {
     (,) x s0 ->
      case applyList opInfo0 x s0 emptyBoundedRangeVec
             handleOp of {
       (,) ops' b ->
        case b of {
         Build_boundedRangeVec vars' regs' -> (,) ((,) ops'
          (Prelude.map (extractRange ((Prelude.succ) 0)) vars'))
          (LinearScan.Utils.vmap _MyMachine__maxReg
            (extractRange ((Prelude.succ) 0)) regs')}}};
   Prelude.Nothing -> (,) ((,) [] [])
    (Data.List.replicate _MyMachine__maxReg Prelude.Nothing)}

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

intervals_for_reg :: ScanStateDesc -> ([]
                                ((,) IntervalId PhysReg))
                                -> PhysReg -> []
                                IntervalId
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

type BlockInfo opType blockType =
  blockType -> [] opType
  -- singleton inductive, whose constructor was Build_BlockInfo
  
coq_BlockInfo_rect :: ((a2 -> [] a1) -> a3) ->
                                 (BlockInfo a1 a2) -> a3
coq_BlockInfo_rect f b =
  f b

coq_BlockInfo_rec :: ((a2 -> [] a1) -> a3) -> (BlockInfo
                                a1 a2) -> a3
coq_BlockInfo_rec =
  coq_BlockInfo_rect

blockToOpList :: (BlockInfo a1 a2) -> a2 -> [] a1
blockToOpList b =
  b

data BlockData opType blockType =
   Build_BlockData blockType (BlockInfo opType blockType) 
 ([] (OpData opType))

coq_BlockData_rect :: (a2 -> (BlockInfo a1 a2) -> ([]
                                 (OpData a1)) -> a3) ->
                                 (BlockData a1 a2) -> a3
coq_BlockData_rect f b =
  case b of {
   Build_BlockData x x0 x1 -> f x x0 x1}

coq_BlockData_rec :: (a2 -> (BlockInfo a1 a2) -> ([]
                                (OpData a1)) -> a3) ->
                                (BlockData a1 a2) -> a3
coq_BlockData_rec =
  coq_BlockData_rect

baseBlock :: (BlockData a1 a2) -> a2
baseBlock b =
  case b of {
   Build_BlockData baseBlock0 blockInfo0 blockOps0 -> baseBlock0}

blockInfo :: (BlockData a1 a2) -> BlockInfo 
                        a1 a2
blockInfo b =
  case b of {
   Build_BlockData baseBlock0 blockInfo0 blockOps0 -> blockInfo0}

blockOps :: (BlockData a1 a2) -> []
                       (OpData a1)
blockOps b =
  case b of {
   Build_BlockData baseBlock0 blockInfo0 blockOps0 -> blockOps0}

computeBlockOrder :: IState.IState SSError ([] a1)
                                ([] a1) ()
computeBlockOrder =
  return_ ()

wrap_block :: (OpInfo a1) -> (BlockInfo 
                         a1 a2) -> ((,) Prelude.Int
                         ([] (BlockData a1 a2))) -> a2 -> (,)
                         Prelude.Int ([] (BlockData a1 a2))
wrap_block oinfo binfo x block =
  let {
   k = \h op -> Build_OpData op oinfo ( h) (\x0 ->
    Unallocated)}
  in
  let {
   f = \x0 op ->
    case x0 of {
     (,) h ops ->
      let {nop = k h op} in
      (,) ((Prelude.succ) ((Prelude.succ) ( h))) ((:) nop ops)}}
  in
  case x of {
   (,) h blocks ->
    case Data.List.foldl' f ((,) h []) (blockToOpList binfo block) of {
     (,) h' ops' ->
      let {blk = Build_BlockData block binfo (Seq.rev ops')} in
      (,) h' ((:) blk blocks)}}

blocksToBlockList :: (OpInfo a1) -> (BlockInfo
                                a1 a2) -> ([] a2) -> []
                                (BlockData a1 a2)
blocksToBlockList oinfo binfo =
  (Prelude..) Prelude.snd
    (Data.List.foldl' (wrap_block oinfo binfo) ((,)
      ((Prelude.succ) 0) []))

numberOperations :: (OpInfo a1) -> (BlockInfo
                               a1 a2) -> IState.IState SSError
                               ([] a2) ([] (BlockData a1 a2)) 
                               ()
numberOperations oinfo binfo =
  IState.imodify (blocksToBlockList oinfo binfo)

type BlockState opType blockType a =
  IState.IState SSError ([] (BlockData opType blockType))
  ([] (BlockData opType blockType)) a

computeLocalLiveSets :: BlockState a1 a2 ()
computeLocalLiveSets =
  return_ ()

computeGlobalLiveSets :: BlockState a1 a2 ()
computeGlobalLiveSets =
  return_ ()

buildIntervals :: (OpInfo a1) -> (BlockInfo 
                             a1 a2) -> BlockState a1 a2
                             ScanStateDesc
buildIntervals oinfo binfo =
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
  stbind (\bxs ->
    let {
     ops = Seq.flatten
             (Prelude.map
               ((Prelude..) (blockToOpList binfo)
                 baseBlock) bxs)}
    in
    case processOperations oinfo ops of {
     (,) p regRanges ->
      case p of {
       (,) l varRanges ->
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
                  (Data.List.replicate maxReg Prelude.Nothing) []
                  [] [] []))
                (intervals (Build_ScanStateDesc 0 []
                  (Data.List.replicate maxReg Prelude.Nothing) []
                  [] [] [])) regs0
                (unhandled (Build_ScanStateDesc 0 []
                  (Data.List.replicate maxReg Prelude.Nothing) []
                  [] [] []))
                (active (Build_ScanStateDesc 0 []
                  (Data.List.replicate maxReg Prelude.Nothing) []
                  [] [] []))
                (inactive (Build_ScanStateDesc 0 []
                  (Data.List.replicate maxReg Prelude.Nothing) []
                  [] [] []))
                (handled (Build_ScanStateDesc 0 []
                  (Data.List.replicate maxReg Prelude.Nothing) []
                  [] [] [])))}
        in
        (Prelude.$) return_
          (Data.List.foldl' handleVar s2 varRanges)}}) IState.iget

resolveDataFlow :: BlockState a1 a2 ()
resolveDataFlow =
  return_ ()

assignRegNum :: BlockState a1 a2 ()
assignRegNum =
  return_ ()

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

liftLen :: ScanStateDesc -> (SState () 
                      () a1) -> SState () () a1
liftLen pre x x0 =
  case x0 of {
   Build_SSInfo thisDesc0 _ ->
    let {s = x (Build_SSInfo thisDesc0 __)} in
    case s of {
     Prelude.Left s0 -> Prelude.Left s0;
     Prelude.Right p -> Prelude.Right
      (case p of {
        (,) a0 s0 -> (,) a0 (Build_SSInfo thisDesc0 __)})}}

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
  Prelude.Right ((,) ()
    (case x of {
      Build_SSInfo thisDesc0 thisHolds0 ->
       case thisDesc0 of {
        Build_ScanStateDesc nextInterval0 intervals0
         fixedIntervals0 unhandled0 active0 inactive0 handled0 ->
         case unhandled0 of {
          [] -> Logic.coq_False_rect;
          (:) p unhandled1 -> Build_SSInfo
           (Build_ScanStateDesc nextInterval0 intervals0
           fixedIntervals0 unhandled1 ((:) ((,) (Prelude.fst p) reg) active0)
           inactive0 handled0) __}}}))

moveActiveToHandled :: ScanStateDesc ->
                                  Eqtype.Equality__Coq_sort ->
                                  Specif.Coq_sig2 ScanStateDesc
moveActiveToHandled sd x =
  Build_ScanStateDesc (nextInterval sd)
    (intervals sd) (fixedIntervals sd)
    (unhandled sd)
    (unsafeCoerce
      ((Prelude.const Data.List.delete)
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (nextInterval sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (active sd)))) ((:) (unsafeCoerce x)
    (inactive sd)) (handled sd)

moveActiveToInactive :: ScanStateDesc ->
                                   Eqtype.Equality__Coq_sort ->
                                   Specif.Coq_sig2 ScanStateDesc
moveActiveToInactive sd x =
  Build_ScanStateDesc (nextInterval sd)
    (intervals sd) (fixedIntervals sd)
    (unhandled sd)
    (unsafeCoerce
      ((Prelude.const Data.List.delete)
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
      ((Prelude.const Data.List.delete)
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
      ((Prelude.const Data.List.delete)
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
          let {_evar_0_0 = \_ -> Prelude.Left ECurrentIsSingleton}
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

splitAssignedIntervalForReg :: ScanStateDesc ->
                                          PhysReg -> (Prelude.Maybe
                                          Prelude.Int) -> Prelude.Bool ->
                                          SState a1 () ()
splitAssignedIntervalForReg pre reg pos trueForActives ssi =
  let {
   _evar_0_ = \desc holds ->
    (Prelude.flip (Prelude.$))
      (intervals_for_reg desc
        (case trueForActives of {
          Prelude.True -> active desc;
          Prelude.False -> inactive desc}) reg) (\intids ->
      let {
       _evar_0_ = \ni intervals0 _fixedIntervals_ unh active0 _inactive_ _handled_ holds0 intids0 ->
        let {_evar_0_ = \_ _ _ -> Prelude.Left ENoIntervalsToSplit}
        in
        let {
         _evar_0_0 = \aid _the_1st_wildcard_ ->
          let {int = LinearScan.Utils.nth ni intervals0 aid} in
          let {_evar_0_0 = \_ -> Prelude.Left ECurrentIsSingleton}
          in
          let {
           _evar_0_1 = \_ -> Prelude.Right ((,) ()
            ((Prelude.flip (Prelude.$)) __ (\_ ->
              let {
               _top_assumption_ = Interval.splitPosition ( int) pos
                                    Prelude.False}
              in
              let {
               _top_assumption_0 = Interval.splitInterval _top_assumption_
                                     ( int)}
              in
              let {
               _evar_0_1 = \_top_assumption_1 _top_assumption_2 ->
                let {
                 _evar_0_1 = \_ ->
                  (Prelude.flip (Prelude.$)) __ (\_ ->
                    (Prelude.flip (Prelude.$)) __
                      (let {
                        new_inactive_added = Build_ScanStateDesc
                         ((Prelude.succ) ni)
                         (LinearScan.Utils.snoc ni
                           (LinearScan.Utils.set_nth ni intervals0 aid
                             _top_assumption_1) _top_assumption_2)
                         _fixedIntervals_ (Prelude.map Prelude.id unh)
                         (Prelude.map Prelude.id active0) ((:) ((,) ( ni)
                         reg) (Prelude.map Prelude.id _inactive_))
                         (Prelude.map Prelude.id _handled_)}
                       in
                       \_ -> Build_SSInfo new_inactive_added __))}
                in
                 _evar_0_1 __}
              in
              case _top_assumption_0 of {
               (,) x x0 -> _evar_0_1 x x0})))}
          in
          case Interval.coq_Interval_is_singleton ( int) of {
           Prelude.True -> _evar_0_0 __;
           Prelude.False -> _evar_0_1 __}}
        in
        case intids0 of {
         [] -> _evar_0_;
         (:) x x0 -> (\_ _ _ -> _evar_0_0 x x0)}}
      in
      case desc of {
       Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
        _evar_0_ x x0 x1 x2 x3 x4 x5 holds intids __ __ __})}
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
splitAnyInactiveIntervalForReg pre reg =
  splitAssignedIntervalForReg pre reg Prelude.Nothing
    Prelude.False

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
    let {
     go = Data.List.foldl' (\v p ->
            case p of {
             (,) i r ->
              LinearScan.Utils.set_nth maxReg v r
                (Interval.nextUseAfter
                  (
                    (LinearScan.Utils.nth (nextInterval sd)
                      (intervals sd) i)) start)})}
    in
    let {
     nextUsePos' = go (Data.List.replicate maxReg Prelude.Nothing)
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
    let {nextUsePos = go nextUsePos' intersectingIntervals} in
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
        let {pos = curPosition sd} in
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
            (splitAnyInactiveIntervalForReg pre reg))
          (splitActiveIntervalForReg pre reg pos)}})

checkActiveIntervals :: ScanStateDesc -> Prelude.Int ->
                                   SState () () ()
checkActiveIntervals pre pos =
  let {
   go = let {
         go sd ss ints =
           case ints of {
            [] -> ss;
            (:) x xs ->
             let {
              st1 = case (Prelude.<=) ((Prelude.succ)
                           (Interval.intervalEnd
                             (
                               (LinearScan.Utils.nth
                                 (nextInterval sd)
                                 (intervals sd)
                                 (Prelude.fst ( x)))))) pos of {
                     Prelude.True ->
                      moveActiveToHandled sd ( (unsafeCoerce x));
                     Prelude.False ->
                      case Prelude.not
                             (Interval.intervalCoversPos
                               (
                                 (LinearScan.Utils.nth
                                   (nextInterval sd)
                                   (intervals sd)
                                   (Prelude.fst ( x)))) pos) of {
                       Prelude.True ->
                        moveActiveToInactive sd
                          ( (unsafeCoerce x));
                       Prelude.False -> ss}}}
             in
             go sd st1 xs}}
        in go}
  in
  (Prelude.$) (withScanStatePO pre) (\sd _ ->
    IState.iput (Build_SSInfo
      (unsafeCoerce go sd sd
        (Prelude.const
          (Eqtype.prod_eqType
            (Fintype.ordinal_eqType (nextInterval sd))
            (Fintype.ordinal_eqType maxReg))
          (unsafeCoerce (active sd)))) __))

checkInactiveIntervals :: ScanStateDesc -> Prelude.Int
                                     -> SState () () ()
checkInactiveIntervals pre pos =
  let {
   go = let {
         go sd ss ints =
           case ints of {
            [] -> ss;
            (:) x xs ->
             let {
              st1 = case (Prelude.<=) ((Prelude.succ)
                           (Interval.intervalEnd
                             (
                               (LinearScan.Utils.nth
                                 (nextInterval sd)
                                 (intervals sd)
                                 (Prelude.fst ( x)))))) pos of {
                     Prelude.True ->
                      moveInactiveToHandled sd ( (unsafeCoerce x));
                     Prelude.False ->
                      case Interval.intervalCoversPos
                             (
                               (LinearScan.Utils.nth
                                 (nextInterval sd)
                                 (intervals sd)
                                 (Prelude.fst ( x)))) pos of {
                       Prelude.True ->
                        moveInactiveToActive sd
                          ( (unsafeCoerce x));
                       Prelude.False -> ss}}}
             in
             go sd st1 xs}}
        in go}
  in
  (Prelude.$) (withScanStatePO pre) (\sd _ ->
    IState.iput (Build_SSInfo
      (unsafeCoerce go sd sd
        (Prelude.const
          (Eqtype.prod_eqType
            (Fintype.ordinal_eqType (nextInterval sd))
            (Fintype.ordinal_eqType maxReg))
          (unsafeCoerce (inactive sd)))) __))

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
        ((Prelude.$) (liftLen pre)
          (checkInactiveIntervals pre position)))
      ((Prelude.$) (liftLen pre)
        (checkActiveIntervals pre position)))

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

mainAlgorithm :: (OpInfo a1) -> (BlockInfo a1 a2) ->
                 IState.IState SSError ([] a2)
                 ([] (BlockData a1 a2)) ()
mainAlgorithm opInfo0 blockInfo0 =
  stbind (\x ->
    stbind (\x0 ->
      stbind (\x1 ->
        stbind (\x2 ->
          stbind (\ssig ->
            case walkIntervals ( ssig) of {
             Prelude.Left err -> error_ err;
             Prelude.Right ssig' ->
              stbind (\x3 -> assignRegNum)
                resolveDataFlow})
            (buildIntervals opInfo0 blockInfo0))
          computeGlobalLiveSets) computeLocalLiveSets)
      (numberOperations opInfo0 blockInfo0))
    computeBlockOrder

linearScan :: (OpInfo a1) -> (BlockInfo a1 a2) -> ([] 
              a2) -> Prelude.Either SSError ([] a2)
linearScan opInfo0 blockInfo0 blocks =
  case IState.runIState (mainAlgorithm opInfo0 blockInfo0) blocks of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) u res -> Prelude.Right (Prelude.map baseBlock res)}}

