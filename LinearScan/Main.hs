{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Main where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
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
import qualified LinearScan.Vector0 as Vector0
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Ssreflect as Ssreflect
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
_MyMachine__maxReg =
  Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ 0)))))))))))))))))))))))))))))))

type LinearScan__MLS__MS__PhysReg = Prelude.Int

type LinearScan__MLS__MS__Coq_fixedIntervalsType =
  Vector0.Vec (Prelude.Maybe Interval.IntervalDesc)

data LinearScan__MLS__MS__ScanStateDesc =
   LinearScan__MLS__MS__Build_ScanStateDesc Prelude.Int (Vector0.Vec
                                                        Interval.IntervalDesc) 
 LinearScan__MLS__MS__Coq_fixedIntervalsType ([]
                                             ((,) Prelude.Int Prelude.Int)) 
 ([] ((,) Prelude.Int LinearScan__MLS__MS__PhysReg)) ([]
                                                     ((,) Prelude.Int
                                                     LinearScan__MLS__MS__PhysReg)) 
 ([] ((,) Prelude.Int LinearScan__MLS__MS__PhysReg))

_LinearScan__MLS__MS__coq_ScanStateDesc_rect :: (Prelude.Int -> (Vector0.Vec
                                                Interval.IntervalDesc) ->
                                                LinearScan__MLS__MS__Coq_fixedIntervalsType
                                                -> ([]
                                                ((,) Prelude.Int Prelude.Int))
                                                -> ([]
                                                ((,) Prelude.Int
                                                LinearScan__MLS__MS__PhysReg))
                                                -> ([]
                                                ((,) Prelude.Int
                                                LinearScan__MLS__MS__PhysReg))
                                                -> ([]
                                                ((,) Prelude.Int
                                                LinearScan__MLS__MS__PhysReg))
                                                -> a1) ->
                                                LinearScan__MLS__MS__ScanStateDesc
                                                -> a1
_LinearScan__MLS__MS__coq_ScanStateDesc_rect f s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
    f x x0 x1 x2 x3 x4 x5}

_LinearScan__MLS__MS__coq_ScanStateDesc_rec :: (Prelude.Int -> (Vector0.Vec
                                               Interval.IntervalDesc) ->
                                               LinearScan__MLS__MS__Coq_fixedIntervalsType
                                               -> ([]
                                               ((,) Prelude.Int Prelude.Int))
                                               -> ([]
                                               ((,) Prelude.Int
                                               LinearScan__MLS__MS__PhysReg))
                                               -> ([]
                                               ((,) Prelude.Int
                                               LinearScan__MLS__MS__PhysReg))
                                               -> ([]
                                               ((,) Prelude.Int
                                               LinearScan__MLS__MS__PhysReg))
                                               -> a1) ->
                                               LinearScan__MLS__MS__ScanStateDesc
                                               -> a1
_LinearScan__MLS__MS__coq_ScanStateDesc_rec =
  _LinearScan__MLS__MS__coq_ScanStateDesc_rect

_LinearScan__MLS__MS__nextInterval :: LinearScan__MLS__MS__ScanStateDesc ->
                                      Prelude.Int
_LinearScan__MLS__MS__nextInterval s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
    fixedIntervals0 unhandled0 active0 inactive0 handled0 -> nextInterval0}

type LinearScan__MLS__MS__IntervalId = Prelude.Int

_LinearScan__MLS__MS__intervals :: LinearScan__MLS__MS__ScanStateDesc ->
                                   Vector0.Vec Interval.IntervalDesc
_LinearScan__MLS__MS__intervals s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
    fixedIntervals0 unhandled0 active0 inactive0 handled0 -> intervals0}

_LinearScan__MLS__MS__fixedIntervals :: LinearScan__MLS__MS__ScanStateDesc ->
                                        LinearScan__MLS__MS__Coq_fixedIntervalsType
_LinearScan__MLS__MS__fixedIntervals s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
    fixedIntervals0 unhandled0 active0 inactive0 handled0 -> fixedIntervals0}

_LinearScan__MLS__MS__unhandled :: LinearScan__MLS__MS__ScanStateDesc -> []
                                   ((,) LinearScan__MLS__MS__IntervalId
                                   Prelude.Int)
_LinearScan__MLS__MS__unhandled s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
    fixedIntervals0 unhandled0 active0 inactive0 handled0 -> unhandled0}

_LinearScan__MLS__MS__active :: LinearScan__MLS__MS__ScanStateDesc -> []
                                ((,) LinearScan__MLS__MS__IntervalId
                                LinearScan__MLS__MS__PhysReg)
_LinearScan__MLS__MS__active s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
    fixedIntervals0 unhandled0 active0 inactive0 handled0 -> active0}

_LinearScan__MLS__MS__inactive :: LinearScan__MLS__MS__ScanStateDesc -> []
                                  ((,) LinearScan__MLS__MS__IntervalId
                                  LinearScan__MLS__MS__PhysReg)
_LinearScan__MLS__MS__inactive s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
    fixedIntervals0 unhandled0 active0 inactive0 handled0 -> inactive0}

_LinearScan__MLS__MS__handled :: LinearScan__MLS__MS__ScanStateDesc -> []
                                 ((,) LinearScan__MLS__MS__IntervalId
                                 LinearScan__MLS__MS__PhysReg)
_LinearScan__MLS__MS__handled s =
  case s of {
   LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
    fixedIntervals0 unhandled0 active0 inactive0 handled0 -> handled0}

_LinearScan__MLS__MS__unhandledIds :: LinearScan__MLS__MS__ScanStateDesc ->
                                      [] LinearScan__MLS__MS__IntervalId
_LinearScan__MLS__MS__unhandledIds s =
  Prelude.map (\i -> Prelude.fst i) (_LinearScan__MLS__MS__unhandled s)

_LinearScan__MLS__MS__activeIds :: LinearScan__MLS__MS__ScanStateDesc -> []
                                   LinearScan__MLS__MS__IntervalId
_LinearScan__MLS__MS__activeIds s =
  Prelude.map (\i -> Prelude.fst i) (_LinearScan__MLS__MS__active s)

_LinearScan__MLS__MS__inactiveIds :: LinearScan__MLS__MS__ScanStateDesc -> []
                                     LinearScan__MLS__MS__IntervalId
_LinearScan__MLS__MS__inactiveIds s =
  Prelude.map (\i -> Prelude.fst i) (_LinearScan__MLS__MS__inactive s)

_LinearScan__MLS__MS__handledIds :: LinearScan__MLS__MS__ScanStateDesc -> []
                                    LinearScan__MLS__MS__IntervalId
_LinearScan__MLS__MS__handledIds s =
  Prelude.map (\i -> Prelude.fst i) (_LinearScan__MLS__MS__handled s)

_LinearScan__MLS__MS__all_state_lists :: LinearScan__MLS__MS__ScanStateDesc
                                         -> []
                                         LinearScan__MLS__MS__IntervalId
_LinearScan__MLS__MS__all_state_lists s =
  (Prelude.++) (_LinearScan__MLS__MS__unhandledIds s)
    ((Prelude.++) (_LinearScan__MLS__MS__activeIds s)
      ((Prelude.++) (_LinearScan__MLS__MS__inactiveIds s)
        (_LinearScan__MLS__MS__handledIds s)))

_LinearScan__MLS__MS__totalExtent :: LinearScan__MLS__MS__ScanStateDesc ->
                                     ([] LinearScan__MLS__MS__IntervalId) ->
                                     Prelude.Int
_LinearScan__MLS__MS__totalExtent sd xs =
  Lib.sumlist
    (Prelude.map (\i ->
      Interval.intervalExtent
        (
          (LinearScan.Utils.nth (_LinearScan__MLS__MS__nextInterval sd)
            (_LinearScan__MLS__MS__intervals sd) i))) xs)

_LinearScan__MLS__MS__unhandledExtent :: LinearScan__MLS__MS__ScanStateDesc
                                         -> Prelude.Int
_LinearScan__MLS__MS__unhandledExtent sd =
  _LinearScan__MLS__MS__totalExtent sd
    (Prelude.map (\i -> Prelude.fst i) (_LinearScan__MLS__MS__unhandled sd))

_LinearScan__MLS__MS__registerWithHighestPos :: (Vector0.Vec
                                                (Prelude.Maybe Prelude.Int))
                                                -> (,) Prelude.Int
                                                (Prelude.Maybe Prelude.Int)
_LinearScan__MLS__MS__registerWithHighestPos =
  (LinearScan.Utils.foldl'_with_index) _MyMachine__maxReg (\reg res x ->
    case res of {
     (,) r o ->
      case o of {
       Prelude.Just n ->
        case x of {
         Prelude.Just m ->
          case (Prelude.<=) (Prelude.succ n) m of {
           Prelude.True -> (,) reg (Prelude.Just m);
           Prelude.False -> (,) r (Prelude.Just n)};
         Prelude.Nothing -> (,) reg Prelude.Nothing};
       Prelude.Nothing -> (,) r Prelude.Nothing}}) ((,) ( 0) (Prelude.Just
    0))

_LinearScan__MLS__MS__getScanStateDesc :: LinearScan__MLS__MS__ScanStateDesc
                                          ->
                                          LinearScan__MLS__MS__ScanStateDesc
_LinearScan__MLS__MS__getScanStateDesc sd =
  sd

_LinearScan__MLS__MS__packScanState :: LinearScan__MLS__MS__ScanStateDesc ->
                                       LinearScan__MLS__MS__ScanStateDesc
_LinearScan__MLS__MS__packScanState sd =
  sd

_LinearScan__MLS__MS__coq_ScanStateCursor_rect :: LinearScan__MLS__MS__ScanStateDesc
                                                  -> (() -> () -> a1) -> a1
_LinearScan__MLS__MS__coq_ScanStateCursor_rect sd f =
  f __ __

_LinearScan__MLS__MS__coq_ScanStateCursor_rec :: LinearScan__MLS__MS__ScanStateDesc
                                                 -> (() -> () -> a1) -> a1
_LinearScan__MLS__MS__coq_ScanStateCursor_rec sd f =
  _LinearScan__MLS__MS__coq_ScanStateCursor_rect sd f

_LinearScan__MLS__MS__curId :: LinearScan__MLS__MS__ScanStateDesc -> (,)
                               LinearScan__MLS__MS__IntervalId Prelude.Int
_LinearScan__MLS__MS__curId sd =
  Prelude.head (_LinearScan__MLS__MS__unhandled sd)

_LinearScan__MLS__MS__curIntDetails :: LinearScan__MLS__MS__ScanStateDesc ->
                                       Interval.IntervalDesc
_LinearScan__MLS__MS__curIntDetails sd =
  LinearScan.Utils.nth (_LinearScan__MLS__MS__nextInterval sd)
    (_LinearScan__MLS__MS__intervals sd)
    (Prelude.fst (_LinearScan__MLS__MS__curId sd))

_LinearScan__MLS__MS__curPosition :: LinearScan__MLS__MS__ScanStateDesc ->
                                     Prelude.Int
_LinearScan__MLS__MS__curPosition sd =
  Interval.intervalStart ( (_LinearScan__MLS__MS__curIntDetails sd))

_LinearScan__coq_SSMorph_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                 LinearScan__MLS__MS__ScanStateDesc -> (() ->
                                 () -> () -> a1) -> a1
_LinearScan__coq_SSMorph_rect sd1 sd2 f =
  f __ __ __

_LinearScan__coq_SSMorph_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                LinearScan__MLS__MS__ScanStateDesc -> (() ->
                                () -> () -> a1) -> a1
_LinearScan__coq_SSMorph_rec sd1 sd2 f =
  _LinearScan__coq_SSMorph_rect sd1 sd2 f

_LinearScan__coq_SSMorphSt_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                   LinearScan__MLS__MS__ScanStateDesc -> (()
                                   -> () -> a1) -> a1
_LinearScan__coq_SSMorphSt_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphSt_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                  LinearScan__MLS__MS__ScanStateDesc -> (()
                                  -> () -> a1) -> a1
_LinearScan__coq_SSMorphSt_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphSt_rect sd1 sd2 f

_LinearScan__coq_SSMorphLen_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                    LinearScan__MLS__MS__ScanStateDesc -> (()
                                    -> () -> a1) -> a1
_LinearScan__coq_SSMorphLen_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphLen_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                   LinearScan__MLS__MS__ScanStateDesc -> (()
                                   -> () -> a1) -> a1
_LinearScan__coq_SSMorphLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphLen_rect sd1 sd2 f

_LinearScan__transportation :: LinearScan__MLS__MS__ScanStateDesc ->
                               LinearScan__MLS__MS__ScanStateDesc ->
                               LinearScan__MLS__MS__IntervalId ->
                               LinearScan__MLS__MS__IntervalId
_LinearScan__transportation sd1 sd2 x =
  Fintype.widen_ord (_LinearScan__MLS__MS__nextInterval sd1)
    (_LinearScan__MLS__MS__nextInterval sd2) x

_LinearScan__coq_SSMorphStLen_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                      LinearScan__MLS__MS__ScanStateDesc ->
                                      (() -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __ __

_LinearScan__coq_SSMorphStLen_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                     LinearScan__MLS__MS__ScanStateDesc ->
                                     (() -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphStLen_rect sd1 sd2 f

_LinearScan__coq_SSMorphHasLen_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                       LinearScan__MLS__MS__ScanStateDesc ->
                                       (() -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphHasLen_rect sd1 sd2 f =
  f __ __ __

_LinearScan__coq_SSMorphHasLen_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                      LinearScan__MLS__MS__ScanStateDesc ->
                                      (() -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphHasLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphHasLen_rect sd1 sd2 f

data LinearScan__HasWork p =
   LinearScan__Build_HasWork

_LinearScan__coq_HasWork_rect :: (() -> a2) -> a2
_LinearScan__coq_HasWork_rect f =
  f __

_LinearScan__coq_HasWork_rec :: (() -> a2) -> a2
_LinearScan__coq_HasWork_rec f =
  _LinearScan__coq_HasWork_rect f

_LinearScan__coq_SSMorphStHasLen_rect :: LinearScan__MLS__MS__ScanStateDesc
                                         ->
                                         LinearScan__MLS__MS__ScanStateDesc
                                         -> (() -> () -> () -> () -> a1) ->
                                         a1
_LinearScan__coq_SSMorphStHasLen_rect sd1 sd2 f =
  f __ __ __ __

_LinearScan__coq_SSMorphStHasLen_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                        LinearScan__MLS__MS__ScanStateDesc ->
                                        (() -> () -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphStHasLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphStHasLen_rect sd1 sd2 f

_LinearScan__coq_SSMorphSplit_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                      LinearScan__MLS__MS__ScanStateDesc ->
                                      (() -> () -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphSplit_rect sd1 sd2 f =
  f __ __ __ __

_LinearScan__coq_SSMorphSplit_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                     LinearScan__MLS__MS__ScanStateDesc ->
                                     (() -> () -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphSplit_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphSplit_rect sd1 sd2 f

data LinearScan__IsSplittable p =
   LinearScan__Build_IsSplittable

_LinearScan__coq_IsSplittable_rect :: (() -> a2) -> a2
_LinearScan__coq_IsSplittable_rect f =
  f __

_LinearScan__coq_IsSplittable_rec :: (() -> a2) -> a2
_LinearScan__coq_IsSplittable_rec f =
  _LinearScan__coq_IsSplittable_rect f

_LinearScan__coq_SSMorphStSplit_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                        LinearScan__MLS__MS__ScanStateDesc ->
                                        (() -> () -> () -> () -> () -> () ->
                                        a1) -> a1
_LinearScan__coq_SSMorphStSplit_rect sd1 sd2 f =
  f __ __ __ __ __ __

_LinearScan__coq_SSMorphStSplit_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                                       LinearScan__MLS__MS__ScanStateDesc ->
                                       (() -> () -> () -> () -> () -> () ->
                                       a1) -> a1
_LinearScan__coq_SSMorphStSplit_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphStSplit_rect sd1 sd2 f

data LinearScan__SSInfo p =
   LinearScan__Build_SSInfo LinearScan__MLS__MS__ScanStateDesc p

_LinearScan__coq_SSInfo_rect :: LinearScan__MLS__MS__ScanStateDesc ->
                                (LinearScan__MLS__MS__ScanStateDesc -> a1 ->
                                () -> a2) -> (LinearScan__SSInfo a1) -> a2
_LinearScan__coq_SSInfo_rect startDesc f s =
  case s of {
   LinearScan__Build_SSInfo x x0 -> f x x0 __}

_LinearScan__coq_SSInfo_rec :: LinearScan__MLS__MS__ScanStateDesc ->
                               (LinearScan__MLS__MS__ScanStateDesc -> a1 ->
                               () -> a2) -> (LinearScan__SSInfo a1) -> a2
_LinearScan__coq_SSInfo_rec startDesc =
  _LinearScan__coq_SSInfo_rect startDesc

_LinearScan__thisDesc :: LinearScan__MLS__MS__ScanStateDesc ->
                         (LinearScan__SSInfo a1) ->
                         LinearScan__MLS__MS__ScanStateDesc
_LinearScan__thisDesc startDesc s =
  case s of {
   LinearScan__Build_SSInfo thisDesc0 thisHolds0 -> thisDesc0}

_LinearScan__thisHolds :: LinearScan__MLS__MS__ScanStateDesc ->
                          (LinearScan__SSInfo a1) -> a1
_LinearScan__thisHolds startDesc s =
  case s of {
   LinearScan__Build_SSInfo thisDesc0 thisHolds0 -> thisHolds0}

type LinearScan__SState p q a =
  IState.IState (LinearScan__SSInfo p) (LinearScan__SSInfo q) a

_LinearScan__withScanState :: LinearScan__MLS__MS__ScanStateDesc ->
                              (LinearScan__MLS__MS__ScanStateDesc -> () ->
                              LinearScan__SState a2 a3 a1) ->
                              LinearScan__SState a2 a3 a1
_LinearScan__withScanState pre f =
  IMonad.ibind (unsafeCoerce IState.coq_IState_IMonad) (\i ->
    f (_LinearScan__thisDesc pre i) __) (unsafeCoerce IState.iget)

_LinearScan__withScanStatePO :: LinearScan__MLS__MS__ScanStateDesc ->
                                (LinearScan__MLS__MS__ScanStateDesc -> () ->
                                LinearScan__SState () () a1) ->
                                LinearScan__SState () () a1
_LinearScan__withScanStatePO pre f i =
  case i of {
   LinearScan__Build_SSInfo thisDesc0 _ ->
    let {f0 = f thisDesc0 __} in
    let {x = LinearScan__Build_SSInfo thisDesc0 __} in
    let {x0 = f0 x} in
    case x0 of {
     (,) a0 s -> (,) a0
      (case s of {
        LinearScan__Build_SSInfo thisDesc1 _ -> LinearScan__Build_SSInfo
         thisDesc1 __})}}

_LinearScan__liftLen :: LinearScan__MLS__MS__ScanStateDesc ->
                        (LinearScan__SState () () a1) -> LinearScan__SState
                        () () a1
_LinearScan__liftLen pre x x0 =
  case x0 of {
   LinearScan__Build_SSInfo thisDesc0 _ ->
    let {p = x (LinearScan__Build_SSInfo thisDesc0 __)} in
    case p of {
     (,) a0 s -> (,) a0 (LinearScan__Build_SSInfo thisDesc0 __)}}

_LinearScan__stbind :: (a4 -> IState.IState a2 a3 a5) -> (IState.IState 
                       a1 a2 a4) -> IState.IState a1 a3 a5
_LinearScan__stbind f x =
  IMonad.ijoin (unsafeCoerce IState.coq_IState_IMonad)
    (IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) f (unsafeCoerce x))

_LinearScan__return_ :: a2 -> IState.IState a1 a1 a2
_LinearScan__return_ =
  IApplicative.ipure (unsafeCoerce IState.coq_IState_IApplicative)

_LinearScan__weakenStHasLenToSt :: LinearScan__MLS__MS__ScanStateDesc ->
                                   LinearScan__SState () () ()
_LinearScan__weakenStHasLenToSt pre hS =
  (,) ()
    (case hS of {
      LinearScan__Build_SSInfo thisDesc0 _ -> LinearScan__Build_SSInfo
       thisDesc0 __})

_LinearScan__withCursor :: LinearScan__MLS__MS__ScanStateDesc ->
                           (LinearScan__MLS__MS__ScanStateDesc -> () ->
                           LinearScan__SState a1 a2 a3) -> LinearScan__SState
                           a1 a2 a3
_LinearScan__withCursor pre f i =
  case i of {
   LinearScan__Build_SSInfo thisDesc0 thisHolds0 ->
    f thisDesc0 __ (LinearScan__Build_SSInfo thisDesc0 thisHolds0)}

_LinearScan__moveUnhandledToActive :: LinearScan__MLS__MS__ScanStateDesc ->
                                      LinearScan__MLS__MS__PhysReg ->
                                      LinearScan__SState a1 () ()
_LinearScan__moveUnhandledToActive pre reg x =
  (,) ()
    (case x of {
      LinearScan__Build_SSInfo thisDesc0 thisHolds0 ->
       case thisDesc0 of {
        LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
         fixedIntervals0 unhandled0 active0 inactive0 handled0 ->
         case unhandled0 of {
          [] -> Logic.coq_False_rect;
          (:) p unhandled1 -> LinearScan__Build_SSInfo
           (LinearScan__MLS__MS__Build_ScanStateDesc nextInterval0 intervals0
           fixedIntervals0 unhandled1 ((:) ((,) (Prelude.fst p) reg) active0)
           inactive0 handled0) __}}})

_LinearScan__moveActiveToHandled :: LinearScan__MLS__MS__ScanStateDesc ->
                                    Eqtype.Equality__Coq_sort ->
                                    Specif.Coq_sig2
                                    LinearScan__MLS__MS__ScanStateDesc
_LinearScan__moveActiveToHandled sd x =
  LinearScan__MLS__MS__Build_ScanStateDesc
    (_LinearScan__MLS__MS__nextInterval sd)
    (_LinearScan__MLS__MS__intervals sd)
    (_LinearScan__MLS__MS__fixedIntervals sd)
    (_LinearScan__MLS__MS__unhandled sd)
    (unsafeCoerce
      ((Prelude.const Data.List.delete)
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (_LinearScan__MLS__MS__nextInterval sd))
          (Fintype.ordinal_eqType _MyMachine__maxReg)) x
        (unsafeCoerce (_LinearScan__MLS__MS__active sd)))) ((:)
    (unsafeCoerce x) (_LinearScan__MLS__MS__inactive sd))
    (_LinearScan__MLS__MS__handled sd)

_LinearScan__moveActiveToInactive :: LinearScan__MLS__MS__ScanStateDesc ->
                                     Eqtype.Equality__Coq_sort ->
                                     Specif.Coq_sig2
                                     LinearScan__MLS__MS__ScanStateDesc
_LinearScan__moveActiveToInactive sd x =
  LinearScan__MLS__MS__Build_ScanStateDesc
    (_LinearScan__MLS__MS__nextInterval sd)
    (_LinearScan__MLS__MS__intervals sd)
    (_LinearScan__MLS__MS__fixedIntervals sd)
    (_LinearScan__MLS__MS__unhandled sd)
    (unsafeCoerce
      ((Prelude.const Data.List.delete)
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (_LinearScan__MLS__MS__nextInterval sd))
          (Fintype.ordinal_eqType _MyMachine__maxReg)) x
        (unsafeCoerce (_LinearScan__MLS__MS__active sd)))) ((:)
    (unsafeCoerce x) (_LinearScan__MLS__MS__inactive sd))
    (_LinearScan__MLS__MS__handled sd)

_LinearScan__moveInactiveToActive :: LinearScan__MLS__MS__ScanStateDesc ->
                                     Eqtype.Equality__Coq_sort ->
                                     Specif.Coq_sig2
                                     LinearScan__MLS__MS__ScanStateDesc
_LinearScan__moveInactiveToActive sd x =
  LinearScan__MLS__MS__Build_ScanStateDesc
    (_LinearScan__MLS__MS__nextInterval sd)
    (_LinearScan__MLS__MS__intervals sd)
    (_LinearScan__MLS__MS__fixedIntervals sd)
    (_LinearScan__MLS__MS__unhandled sd) ((:) (unsafeCoerce x)
    (_LinearScan__MLS__MS__active sd))
    (unsafeCoerce
      ((Prelude.const Data.List.delete)
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (_LinearScan__MLS__MS__nextInterval sd))
          (Fintype.ordinal_eqType _MyMachine__maxReg)) x
        (unsafeCoerce (_LinearScan__MLS__MS__inactive sd))))
    (_LinearScan__MLS__MS__handled sd)

_LinearScan__moveInactiveToHandled :: LinearScan__MLS__MS__ScanStateDesc ->
                                      Eqtype.Equality__Coq_sort ->
                                      Specif.Coq_sig2
                                      LinearScan__MLS__MS__ScanStateDesc
_LinearScan__moveInactiveToHandled sd x =
  LinearScan__MLS__MS__Build_ScanStateDesc
    (_LinearScan__MLS__MS__nextInterval sd)
    (_LinearScan__MLS__MS__intervals sd)
    (_LinearScan__MLS__MS__fixedIntervals sd)
    (_LinearScan__MLS__MS__unhandled sd) (_LinearScan__MLS__MS__active sd)
    (unsafeCoerce
      ((Prelude.const Data.List.delete)
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (_LinearScan__MLS__MS__nextInterval sd))
          (Fintype.ordinal_eqType _MyMachine__maxReg)) x
        (unsafeCoerce (_LinearScan__MLS__MS__inactive sd)))) ((:)
    (unsafeCoerce x) (_LinearScan__MLS__MS__handled sd))

_LinearScan__distance :: Prelude.Int -> Prelude.Int -> Prelude.Int
_LinearScan__distance n m =
  case (Prelude.<=) (Prelude.succ n) m of {
   Prelude.True -> (Prelude.-) m n;
   Prelude.False -> (Prelude.-) n m}

_LinearScan__splitCurrentInterval_subproof :: LinearScan__MLS__MS__ScanStateDesc
                                              -> (Prelude.Maybe Prelude.Int)
                                              -> Prelude.Int -> (Vector0.Vec
                                              Interval.IntervalDesc) ->
                                              LinearScan__MLS__MS__Coq_fixedIntervalsType
                                              -> ([]
                                              ((,) Prelude.Int Prelude.Int))
                                              -> ([]
                                              ((,) Prelude.Int
                                              LinearScan__MLS__MS__PhysReg))
                                              -> ([]
                                              ((,) Prelude.Int
                                              LinearScan__MLS__MS__PhysReg))
                                              -> ([]
                                              ((,) Prelude.Int
                                              LinearScan__MLS__MS__PhysReg))
                                              -> a1 -> LinearScan__SSInfo 
                                              ()
_LinearScan__splitCurrentInterval_subproof pre before _nextInterval_ intervals0 _fixedIntervals_ unhandled0 _active_ _inactive_ _handled_ holds =
  _LinearScan__coq_SSMorph_rect pre (LinearScan__MLS__MS__Build_ScanStateDesc
    _nextInterval_ intervals0 _fixedIntervals_ [] _active_ _inactive_
    _handled_) (\_ _ _ -> Logic.coq_False_rect)

_LinearScan__splitCurrentInterval :: LinearScan__MLS__MS__ScanStateDesc ->
                                     (Prelude.Maybe Prelude.Int) ->
                                     LinearScan__SState a1 () ()
_LinearScan__splitCurrentInterval pre before ssi =
  (,) ()
    (let {
      _evar_0_ = \desc holds ->
       let {
        _evar_0_ = \_nextInterval_ intervals0 _fixedIntervals_ unhandled0 _active_ _inactive_ _handled_ ->
         let {
          _evar_0_ = \x ->
           _LinearScan__splitCurrentInterval_subproof pre before
             _nextInterval_ intervals0 _fixedIntervals_ unhandled0 _active_
             _inactive_ _handled_ x}
         in
         let {
          _evar_0_0 = \_top_assumption_ ->
           let {
            _evar_0_0 = \uid beg us holds0 ->
             let {int = LinearScan.Utils.nth _nextInterval_ intervals0 uid}
             in
             Ssreflect.ssr_have __ (\_ ->
               Ssreflect.ssr_have __ (\_ ->
                 let {
                  _top_assumption_0 = Interval.splitPosition ( int) before}
                 in
                 let {
                  _top_assumption_1 = Interval.splitInterval
                                        _top_assumption_0 ( int)}
                 in
                 let {
                  _evar_0_0 = \_top_assumption_2 _top_assumption_3 ->
                   let {
                    _evar_0_0 = \_ ->
                     Ssreflect.ssr_have __ (\_ ->
                       Ssreflect.ssr_have __
                         (Ssreflect.ssr_have __
                           (Ssreflect.ssr_have __ (\_ _ _ ->
                             Ssreflect.ssr_have __
                               (Ssreflect.ssr_have __
                                 (let {
                                   new_unhandled_added = LinearScan__MLS__MS__Build_ScanStateDesc
                                    (Prelude.succ _nextInterval_)
                                    (LinearScan.Utils.snoc _nextInterval_
                                      (LinearScan.Utils.set_nth
                                        _nextInterval_ intervals0 uid
                                        _top_assumption_2) _top_assumption_3)
                                    _fixedIntervals_
                                    (Lib.insert (\x ->
                                      Lib.lebf Prelude.snd x ((,)
                                        (Fintype.ord_max _nextInterval_)
                                        (Interval.ibeg _top_assumption_3)))
                                      ((,) (Fintype.ord_max _nextInterval_)
                                      (Interval.ibeg _top_assumption_3)) ((:)
                                      (Lib.widen_fst _nextInterval_ ((,) uid
                                        beg))
                                      (Prelude.map
                                        (Lib.widen_fst _nextInterval_) us)))
                                    (Prelude.map
                                      (Lib.widen_fst _nextInterval_)
                                      _active_)
                                    (Prelude.map
                                      (Lib.widen_fst _nextInterval_)
                                      _inactive_)
                                    (Prelude.map
                                      (Lib.widen_fst _nextInterval_)
                                      _handled_)}
                                  in
                                  \_ _ -> LinearScan__Build_SSInfo
                                  new_unhandled_added __))))))}
                   in
                   Logic.eq_rect_r
                     (Eqtype.eq_op Ssrnat.nat_eqType
                       (unsafeCoerce (Interval.ibeg _top_assumption_2))
                       (unsafeCoerce (Interval.ibeg ( int)))) _evar_0_0
                     (Eqtype.eq_op Ssrnat.nat_eqType
                       (unsafeCoerce (Interval.ibeg ( int)))
                       (unsafeCoerce (Interval.ibeg _top_assumption_2))) __}
                 in
                 case _top_assumption_1 of {
                  (,) x x0 -> _evar_0_0 x x0}))}
           in
           (\us _ _ _ _ holds0 _ _ _ _ ->
           case _top_assumption_ of {
            (,) x x0 -> _evar_0_0 x x0 us holds0})}
         in
         case unhandled0 of {
          [] -> (\_ _ _ x _ _ _ _ -> _evar_0_ x);
          (:) x x0 -> _evar_0_0 x x0 __}}
       in
       case desc of {
        LinearScan__MLS__MS__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
         _evar_0_ x x0 x1 x2 x3 x4 x5 __ __ __ holds __ __ __}}
     in
     case ssi of {
      LinearScan__Build_SSInfo x x0 -> _evar_0_ x x0 __})

_LinearScan__splitActiveIntervalForReg :: LinearScan__MLS__MS__ScanStateDesc
                                          -> LinearScan__MLS__MS__PhysReg ->
                                          Prelude.Int -> LinearScan__SState
                                          a1 a1 ()
_LinearScan__splitActiveIntervalForReg =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__splitAnyInactiveIntervalForReg :: LinearScan__MLS__MS__ScanStateDesc
                                               ->
                                               LinearScan__MLS__MS__PhysReg
                                               -> LinearScan__SState 
                                               a1 a1 ()
_LinearScan__splitAnyInactiveIntervalForReg =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__intersectsWithFixedInterval :: LinearScan__MLS__MS__ScanStateDesc
                                            -> LinearScan__MLS__MS__PhysReg
                                            -> LinearScan__SState a1 
                                            a1 (Prelude.Maybe Prelude.Int)
_LinearScan__intersectsWithFixedInterval pre reg =
  (Prelude.$) (_LinearScan__withCursor pre) (\sd _ ->
    let {int = _LinearScan__MLS__MS__curIntDetails sd} in
    (Prelude.$) _LinearScan__return_
      (LinearScan.Utils.vfoldl' _MyMachine__maxReg (\mx v ->
        Lib.option_choose mx
          (case v of {
            Prelude.Just i -> Interval.intervalIntersectionPoint ( int) ( i);
            Prelude.Nothing -> Prelude.Nothing})) Prelude.Nothing
        (_LinearScan__MLS__MS__fixedIntervals sd)))

_LinearScan__assignSpillSlotToCurrent :: LinearScan__MLS__MS__ScanStateDesc
                                         -> LinearScan__SState a1 a1 
                                         ()
_LinearScan__assignSpillSlotToCurrent =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__tryAllocateFreeReg :: LinearScan__MLS__MS__ScanStateDesc ->
                                   LinearScan__SState a1 a1
                                   (Prelude.Maybe
                                   (LinearScan__SState a1 ()
                                   LinearScan__MLS__MS__PhysReg))
_LinearScan__tryAllocateFreeReg pre =
  (Prelude.$) (_LinearScan__withCursor pre) (\sd _ ->
    let {
     go = \n ->
      Data.List.foldl' (\v p ->
        case p of {
         (,) i r -> LinearScan.Utils.set_nth _MyMachine__maxReg v r (n i)})}
    in
    let {
     freeUntilPos' = go (\x -> Prelude.Just 0)
                       (Data.List.replicate _MyMachine__maxReg
                         Prelude.Nothing) (_LinearScan__MLS__MS__active sd)}
    in
    let {
     intersectingIntervals = Prelude.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (_LinearScan__MLS__MS__curIntDetails sd))
                                 (
                                   (LinearScan.Utils.nth
                                     (_LinearScan__MLS__MS__nextInterval sd)
                                     (_LinearScan__MLS__MS__intervals sd)
                                     (Prelude.fst x))))
                               (_LinearScan__MLS__MS__inactive sd)}
    in
    let {
     freeUntilPos = go (\i ->
                      Interval.intervalIntersectionPoint
                        (
                          (LinearScan.Utils.nth
                            (_LinearScan__MLS__MS__nextInterval sd)
                            (_LinearScan__MLS__MS__intervals sd) i))
                        ( (_LinearScan__MLS__MS__curIntDetails sd)))
                      freeUntilPos' intersectingIntervals}
    in
    case _LinearScan__MLS__MS__registerWithHighestPos freeUntilPos of {
     (,) reg mres ->
      let {
       success = _LinearScan__stbind (\x -> _LinearScan__return_ reg)
                   (_LinearScan__moveUnhandledToActive pre reg)}
      in
      let {
       maction = case mres of {
                  Prelude.Just n ->
                   case Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce n)
                          (unsafeCoerce 0) of {
                    Prelude.True -> Prelude.Nothing;
                    Prelude.False -> Prelude.Just
                     (case (Prelude.<=) (Prelude.succ
                             (Interval.intervalEnd
                               ( (_LinearScan__MLS__MS__curIntDetails sd))))
                             n of {
                       Prelude.True -> success;
                       Prelude.False ->
                        _LinearScan__stbind (\x ->
                          _LinearScan__stbind (\x0 ->
                            _LinearScan__return_ reg)
                            (_LinearScan__moveUnhandledToActive pre reg))
                          (_LinearScan__splitCurrentInterval pre
                            (Prelude.Just n))})};
                  Prelude.Nothing -> Prelude.Just success}}
      in
      _LinearScan__return_ maction})

_LinearScan__allocateBlockedReg :: LinearScan__MLS__MS__ScanStateDesc ->
                                   LinearScan__SState a1 ()
                                   (Prelude.Maybe
                                   LinearScan__MLS__MS__PhysReg)
_LinearScan__allocateBlockedReg pre =
  (Prelude.$) (_LinearScan__withCursor pre) (\sd _ ->
    let {
     start = Interval.intervalStart
               ( (_LinearScan__MLS__MS__curIntDetails sd))}
    in
    let {
     go = Data.List.foldl' (\v p ->
            case p of {
             (,) i r ->
              LinearScan.Utils.set_nth _MyMachine__maxReg v r
                (Interval.nextUseAfter
                  (
                    (LinearScan.Utils.nth
                      (_LinearScan__MLS__MS__nextInterval sd)
                      (_LinearScan__MLS__MS__intervals sd) i)) start)})}
    in
    let {
     nextUsePos' = go
                     (Data.List.replicate _MyMachine__maxReg Prelude.Nothing)
                     (_LinearScan__MLS__MS__active sd)}
    in
    let {
     intersectingIntervals = Prelude.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (_LinearScan__MLS__MS__curIntDetails sd))
                                 (
                                   (LinearScan.Utils.nth
                                     (_LinearScan__MLS__MS__nextInterval sd)
                                     (_LinearScan__MLS__MS__intervals sd)
                                     (Prelude.fst x))))
                               (_LinearScan__MLS__MS__inactive sd)}
    in
    let {nextUsePos = go nextUsePos' intersectingIntervals} in
    case _LinearScan__MLS__MS__registerWithHighestPos nextUsePos of {
     (,) reg mres ->
      case case mres of {
            Prelude.Just n -> (Prelude.<=) (Prelude.succ n) start;
            Prelude.Nothing -> Prelude.False} of {
       Prelude.True ->
        _LinearScan__stbind (\x ->
          _LinearScan__stbind (\x0 ->
            _LinearScan__stbind (\mloc ->
              _LinearScan__stbind (\x1 ->
                _LinearScan__stbind (\x2 ->
                  _LinearScan__return_ Prelude.Nothing)
                  (_LinearScan__weakenStHasLenToSt pre))
                (case mloc of {
                  Prelude.Just n ->
                   _LinearScan__splitCurrentInterval pre (Prelude.Just n);
                  Prelude.Nothing -> _LinearScan__return_ ()}))
              (_LinearScan__intersectsWithFixedInterval pre reg))
            (_LinearScan__splitCurrentInterval pre
              (Interval.firstUseReqReg
                ( (_LinearScan__MLS__MS__curIntDetails sd)))))
          (_LinearScan__assignSpillSlotToCurrent pre);
       Prelude.False ->
        let {pos = _LinearScan__MLS__MS__curPosition sd} in
        _LinearScan__stbind (\x ->
          _LinearScan__stbind (\x0 ->
            _LinearScan__stbind (\mloc ->
              _LinearScan__stbind (\x1 ->
                _LinearScan__return_ (Prelude.Just reg))
                (case mloc of {
                  Prelude.Just n ->
                   _LinearScan__stbind (\x1 ->
                     _LinearScan__moveUnhandledToActive pre reg)
                     (_LinearScan__splitCurrentInterval pre (Prelude.Just n));
                  Prelude.Nothing ->
                   _LinearScan__moveUnhandledToActive pre reg}))
              (_LinearScan__intersectsWithFixedInterval pre reg))
            (_LinearScan__splitAnyInactiveIntervalForReg pre reg))
          (_LinearScan__splitActiveIntervalForReg pre reg pos)}})

_LinearScan__checkActiveIntervals :: LinearScan__MLS__MS__ScanStateDesc ->
                                     Prelude.Int -> LinearScan__SState 
                                     () () ()
_LinearScan__checkActiveIntervals pre pos =
  let {
   go = let {
         go sd ss ints =
           case ints of {
            [] -> ss;
            (:) x xs ->
             let {
              st1 = case (Prelude.<=) (Prelude.succ
                           (Interval.intervalEnd
                             (
                               (LinearScan.Utils.nth
                                 (_LinearScan__MLS__MS__nextInterval sd)
                                 (_LinearScan__MLS__MS__intervals sd)
                                 (Prelude.fst ( x)))))) pos of {
                     Prelude.True ->
                      _LinearScan__moveActiveToHandled sd ( (unsafeCoerce x));
                     Prelude.False ->
                      case Prelude.not
                             (Interval.intervalCoversPos
                               (
                                 (LinearScan.Utils.nth
                                   (_LinearScan__MLS__MS__nextInterval sd)
                                   (_LinearScan__MLS__MS__intervals sd)
                                   (Prelude.fst ( x)))) pos) of {
                       Prelude.True ->
                        _LinearScan__moveActiveToInactive sd
                          ( (unsafeCoerce x));
                       Prelude.False -> ss}}}
             in
             go sd st1 xs}}
        in go}
  in
  (Prelude.$) (_LinearScan__withScanStatePO pre) (\sd _ ->
    IState.iput (LinearScan__Build_SSInfo
      (unsafeCoerce go sd sd
        (Lib.list_membership
          (Eqtype.prod_eqType
            (Fintype.ordinal_eqType (_LinearScan__MLS__MS__nextInterval sd))
            (Fintype.ordinal_eqType _MyMachine__maxReg))
          (unsafeCoerce (_LinearScan__MLS__MS__active sd)))) __))

_LinearScan__checkInactiveIntervals :: LinearScan__MLS__MS__ScanStateDesc ->
                                       Prelude.Int -> LinearScan__SState 
                                       () () ()
_LinearScan__checkInactiveIntervals pre pos =
  let {
   go = let {
         go sd ss ints =
           case ints of {
            [] -> ss;
            (:) x xs ->
             let {
              st1 = case (Prelude.<=) (Prelude.succ
                           (Interval.intervalEnd
                             (
                               (LinearScan.Utils.nth
                                 (_LinearScan__MLS__MS__nextInterval sd)
                                 (_LinearScan__MLS__MS__intervals sd)
                                 (Prelude.fst ( x)))))) pos of {
                     Prelude.True ->
                      _LinearScan__moveInactiveToHandled sd
                        ( (unsafeCoerce x));
                     Prelude.False ->
                      case Interval.intervalCoversPos
                             (
                               (LinearScan.Utils.nth
                                 (_LinearScan__MLS__MS__nextInterval sd)
                                 (_LinearScan__MLS__MS__intervals sd)
                                 (Prelude.fst ( x)))) pos of {
                       Prelude.True ->
                        _LinearScan__moveInactiveToActive sd
                          ( (unsafeCoerce x));
                       Prelude.False -> ss}}}
             in
             go sd st1 xs}}
        in go}
  in
  (Prelude.$) (_LinearScan__withScanStatePO pre) (\sd _ ->
    IState.iput (LinearScan__Build_SSInfo
      (unsafeCoerce go sd sd
        (Lib.list_membership
          (Eqtype.prod_eqType
            (Fintype.ordinal_eqType (_LinearScan__MLS__MS__nextInterval sd))
            (Fintype.ordinal_eqType _MyMachine__maxReg))
          (unsafeCoerce (_LinearScan__MLS__MS__inactive sd)))) __))

_LinearScan__handleInterval :: LinearScan__MLS__MS__ScanStateDesc ->
                               LinearScan__SState () ()
                               (Prelude.Maybe LinearScan__MLS__MS__PhysReg)
_LinearScan__handleInterval pre =
  (Prelude.$) (unsafeCoerce (_LinearScan__withCursor pre)) (\sd _ ->
    let {position = _LinearScan__MLS__MS__curPosition sd} in
    _LinearScan__stbind (\x ->
      _LinearScan__stbind (\x0 ->
        _LinearScan__stbind (\mres ->
          case mres of {
           Prelude.Just x1 ->
            IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) (\x2 ->
              Prelude.Just x2) x1;
           Prelude.Nothing ->
            unsafeCoerce (_LinearScan__allocateBlockedReg pre)})
          (_LinearScan__tryAllocateFreeReg pre))
        ((Prelude.$) (_LinearScan__liftLen pre)
          (_LinearScan__checkInactiveIntervals pre position)))
      ((Prelude.$) (_LinearScan__liftLen pre)
        (_LinearScan__checkActiveIntervals pre position)))

_LinearScan__linearScan_func :: ((,) LinearScan__MLS__MS__ScanStateDesc 
                                ()) -> LinearScan__MLS__MS__ScanStateDesc
_LinearScan__linearScan_func x =
  let {sd = Prelude.fst x} in
  let {
   linearScan0 = \sd0 ->
    let {y = (,) sd0 __} in _LinearScan__linearScan_func ( y)}
  in
  let {filtered_var = _LinearScan__MLS__MS__unhandled sd} in
  case filtered_var of {
   [] -> sd;
   (:) x0 xs ->
    let {ssinfo = LinearScan__Build_SSInfo sd __} in
    case IState.runIState (_LinearScan__handleInterval sd) ssinfo of {
     (,) x1 ssinfo' -> linearScan0 (_LinearScan__thisDesc sd ssinfo')}}

_LinearScan__linearScan :: LinearScan__MLS__MS__ScanStateDesc ->
                           LinearScan__MLS__MS__ScanStateDesc
_LinearScan__linearScan sd =
  _LinearScan__linearScan_func ((,) sd __)

type LinearScan__SomeVar = Prelude.Either Prelude.Int Prelude.Int

data LinearScan__Block baseType =
   LinearScan__Build_Block baseType Prelude.Bool Prelude.Bool Prelude.Int 
 (Vector0.Vec LinearScan__SomeVar)

_LinearScan__coq_Block_rect :: Prelude.Int -> (a1 -> Prelude.Bool ->
                               Prelude.Bool -> Prelude.Int -> (Vector0.Vec
                               LinearScan__SomeVar) -> a2) ->
                               (LinearScan__Block a1) -> a2
_LinearScan__coq_Block_rect maxVirtReg f b =
  case b of {
   LinearScan__Build_Block x x0 x1 x2 x3 -> f x x0 x1 x2 x3}

_LinearScan__coq_Block_rec :: Prelude.Int -> (a1 -> Prelude.Bool ->
                              Prelude.Bool -> Prelude.Int -> (Vector0.Vec
                              LinearScan__SomeVar) -> a2) ->
                              (LinearScan__Block a1) -> a2
_LinearScan__coq_Block_rec maxVirtReg =
  _LinearScan__coq_Block_rect maxVirtReg

_LinearScan__original :: Prelude.Int -> (LinearScan__Block a1) -> a1
_LinearScan__original maxVirtReg b =
  case b of {
   LinearScan__Build_Block original0 loopBound0 regRequired0 refCount0
    references0 -> original0}

_LinearScan__loopBound :: Prelude.Int -> (LinearScan__Block a1) ->
                          Prelude.Bool
_LinearScan__loopBound maxVirtReg b =
  case b of {
   LinearScan__Build_Block original0 loopBound0 regRequired0 refCount0
    references0 -> loopBound0}

_LinearScan__regRequired :: Prelude.Int -> (LinearScan__Block a1) ->
                            Prelude.Bool
_LinearScan__regRequired maxVirtReg b =
  case b of {
   LinearScan__Build_Block original0 loopBound0 regRequired0 refCount0
    references0 -> regRequired0}

_LinearScan__refCount :: Prelude.Int -> (LinearScan__Block a1) -> Prelude.Int
_LinearScan__refCount maxVirtReg b =
  case b of {
   LinearScan__Build_Block original0 loopBound0 regRequired0 refCount0
    references0 -> refCount0}

_LinearScan__references :: Prelude.Int -> (LinearScan__Block a1) ->
                           Vector0.Vec LinearScan__SomeVar
_LinearScan__references maxVirtReg b =
  case b of {
   LinearScan__Build_Block original0 loopBound0 regRequired0 refCount0
    references0 -> references0}

type LinearScan__Coq_boundedRange = Specif.Coq_sig2 Range.RangeDesc

type LinearScan__Coq_boundedTriple =
  (,) ((,) (Prelude.Maybe Prelude.Int) (Prelude.Maybe Prelude.Int))
  (Prelude.Maybe LinearScan__Coq_boundedRange)

data LinearScan__Coq_boundedRangeVec =
   LinearScan__Build_boundedRangeVec (Vector0.Vec
                                     LinearScan__Coq_boundedTriple) (Vector0.Vec
                                                                    LinearScan__Coq_boundedTriple)

_LinearScan__boundedRangeVec_rect :: Prelude.Int -> Prelude.Int ->
                                     ((Vector0.Vec
                                     LinearScan__Coq_boundedTriple) ->
                                     (Vector0.Vec
                                     LinearScan__Coq_boundedTriple) -> a1) ->
                                     LinearScan__Coq_boundedRangeVec -> a1
_LinearScan__boundedRangeVec_rect maxVirtReg pos f b =
  case b of {
   LinearScan__Build_boundedRangeVec x x0 -> f x x0}

_LinearScan__boundedRangeVec_rec :: Prelude.Int -> Prelude.Int ->
                                    ((Vector0.Vec
                                    LinearScan__Coq_boundedTriple) ->
                                    (Vector0.Vec
                                    LinearScan__Coq_boundedTriple) -> a1) ->
                                    LinearScan__Coq_boundedRangeVec -> a1
_LinearScan__boundedRangeVec_rec maxVirtReg pos =
  _LinearScan__boundedRangeVec_rect maxVirtReg pos

_LinearScan__vars :: Prelude.Int -> Prelude.Int ->
                     LinearScan__Coq_boundedRangeVec -> Vector0.Vec
                     LinearScan__Coq_boundedTriple
_LinearScan__vars maxVirtReg pos b =
  case b of {
   LinearScan__Build_boundedRangeVec vars0 regs0 -> vars0}

_LinearScan__regs :: Prelude.Int -> Prelude.Int ->
                     LinearScan__Coq_boundedRangeVec -> Vector0.Vec
                     LinearScan__Coq_boundedTriple
_LinearScan__regs maxVirtReg pos b =
  case b of {
   LinearScan__Build_boundedRangeVec vars0 regs0 -> regs0}

_LinearScan__transportVecBounds :: Prelude.Int -> Prelude.Int -> Prelude.Int
                                   -> (Vector0.Vec
                                   LinearScan__Coq_boundedTriple) ->
                                   Vector0.Vec LinearScan__Coq_boundedTriple
_LinearScan__transportVecBounds pos m n _top_assumption_ =
  let {
   _evar_0_ = \sz _top_assumption_0 ->
    let {
     _evar_0_ = \p _top_assumption_1 ->
      let {
       _evar_0_ = \_top_assumption_2 xs iHxs -> (,) ((,) p (Prelude.Just
        _top_assumption_2)) iHxs}
      in
      let {_evar_0_0 = \xs iHxs -> (,) ((,) p Prelude.Nothing) iHxs} in
      case _top_assumption_1 of {
       Prelude.Just x -> _evar_0_ x;
       Prelude.Nothing -> _evar_0_0}}
    in
    case _top_assumption_0 of {
     (,) x x0 -> _evar_0_ x x0}}
  in
  LinearScan.Utils.list_rect ([]) (unsafeCoerce _evar_0_) m _top_assumption_

_LinearScan__boundedSing :: Range.UsePos -> LinearScan__Coq_boundedRange
_LinearScan__boundedSing upos =
  Range.Build_RangeDesc (Range.uloc upos) (Prelude.succ (Range.uloc upos))
    (NonEmpty0.NE_Sing upos)

_LinearScan__boundedCons :: Range.UsePos -> Prelude.Int ->
                            LinearScan__Coq_boundedRange ->
                            LinearScan__Coq_boundedRange
_LinearScan__boundedCons upos n _top_assumption_ =
  Range.Build_RangeDesc (Range.uloc upos) (Range.rend _top_assumption_)
    (NonEmpty0.NE_Cons upos (Range.ups _top_assumption_))

_LinearScan__withRanges :: Prelude.Int -> Prelude.Bool -> Range.UsePos ->
                           Prelude.Int -> LinearScan__Coq_boundedTriple ->
                           LinearScan__Coq_boundedTriple
_LinearScan__withRanges pos req upos n _top_assumption_ =
  let {
   _evar_0_ = \p _top_assumption_0 ->
    let {
     _evar_0_ = \_top_assumption_1 -> (,) p
      (let {_evar_0_ = _LinearScan__boundedCons upos n _top_assumption_1} in
       Prelude.Just _evar_0_)}
    in
    let {
     _evar_0_0 = (,) p
      (let {_evar_0_0 = _LinearScan__boundedSing upos} in
       Prelude.Just _evar_0_0)}
    in
    case _top_assumption_0 of {
     Prelude.Just x -> _evar_0_ x;
     Prelude.Nothing -> _evar_0_0}}
  in
  case _top_assumption_ of {
   (,) x x0 -> _evar_0_ x x0}

_LinearScan__applyList :: Prelude.Int -> (NonEmpty0.NonEmpty
                          (LinearScan__Block a1)) -> (Prelude.Int ->
                          LinearScan__Coq_boundedRangeVec) ->
                          ((LinearScan__Block a1) -> Prelude.Int -> () ->
                          LinearScan__Coq_boundedRangeVec ->
                          LinearScan__Coq_boundedRangeVec) ->
                          LinearScan__Coq_boundedRangeVec
_LinearScan__applyList maxVirtReg bs base f =
  let {
   go i bs0 =
     case bs0 of {
      NonEmpty0.NE_Sing x -> f x i __ (base i);
      NonEmpty0.NE_Cons x xs ->
       f x i __ (go (Prelude.succ (Prelude.succ i)) xs)}}
  in go (Prelude.succ 0) bs

_LinearScan__emptyBoundedRangeVec :: Prelude.Int -> Prelude.Int ->
                                     LinearScan__Coq_boundedRangeVec
_LinearScan__emptyBoundedRangeVec maxVirtReg n =
  LinearScan__Build_boundedRangeVec
    (Data.List.replicate maxVirtReg ((,) ((,) Prelude.Nothing
      Prelude.Nothing) Prelude.Nothing))
    (Data.List.replicate _MyMachine__maxReg ((,) ((,) Prelude.Nothing
      Prelude.Nothing) Prelude.Nothing))

_LinearScan__handleBlock :: Prelude.Int -> (LinearScan__Block a1) ->
                            Prelude.Int -> LinearScan__Coq_boundedRangeVec ->
                            LinearScan__Coq_boundedRangeVec
_LinearScan__handleBlock maxVirtReg b pos rest =
  let {
   liftOr = \f mx y -> Prelude.Just
    (case mx of {
      Prelude.Just x -> f x y;
      Prelude.Nothing -> y})}
  in
  let {
   savingBound = \x ->
    case _LinearScan__loopBound maxVirtReg b of {
     Prelude.True ->
      case x of {
       (,) y r ->
        case y of {
         (,) mb me -> (,) ((,) (liftOr Prelude.min mb pos)
          (liftOr Prelude.max me pos)) r}};
     Prelude.False -> x}}
  in
  let {
   consr = \x ->
    let {
     upos = Range.Build_UsePos pos (_LinearScan__regRequired maxVirtReg b)}
    in
    _LinearScan__withRanges pos (_LinearScan__regRequired maxVirtReg b) upos
      (Prelude.succ (Prelude.succ pos)) x}
  in
  let {
   restVars' = LinearScan.Utils.vmap maxVirtReg savingBound
                 (_LinearScan__vars maxVirtReg (Prelude.succ (Prelude.succ
                   pos)) rest)}
  in
  let {
   restRegs' = LinearScan.Utils.vmap _MyMachine__maxReg savingBound
                 (_LinearScan__regs maxVirtReg (Prelude.succ (Prelude.succ
                   pos)) rest)}
  in
  LinearScan.Utils.list_rect
    (LinearScan.Utils.boundedTransport' maxVirtReg pos (Prelude.succ
      (Prelude.succ pos)) (LinearScan__Build_boundedRangeVec restVars'
      restRegs')) (\n x v x0 ->
    case x of {
     Prelude.Left v0 ->
      let {x1 = consr (LinearScan.Utils.nth maxVirtReg restVars' v0)} in
      let {
       restVars'' = LinearScan.Utils.set_nth maxVirtReg
                      (_LinearScan__transportVecBounds pos maxVirtReg
                        (Prelude.succ (Prelude.succ pos)) restVars') v0 x1}
      in
      let {
       restRegs'' = _LinearScan__transportVecBounds pos _MyMachine__maxReg
                      (Prelude.succ (Prelude.succ pos)) restRegs'}
      in
      LinearScan__Build_boundedRangeVec restVars'' restRegs'';
     Prelude.Right r ->
      let {x1 = consr (LinearScan.Utils.nth _MyMachine__maxReg restRegs' r)}
      in
      let {
       restVars'' = _LinearScan__transportVecBounds pos maxVirtReg
                      (Prelude.succ (Prelude.succ pos)) restVars'}
      in
      let {
       restRegs'' = LinearScan.Utils.set_nth _MyMachine__maxReg
                      (_LinearScan__transportVecBounds pos _MyMachine__maxReg
                        (Prelude.succ (Prelude.succ pos)) restRegs') r x1}
      in
      LinearScan__Build_boundedRangeVec restVars'' restRegs''})
    (_LinearScan__refCount maxVirtReg b)
    (_LinearScan__references maxVirtReg b)

_LinearScan__extractRange :: LinearScan__Coq_boundedTriple -> Prelude.Maybe
                             Range.RangeDesc
_LinearScan__extractRange x =
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

_LinearScan__processBlocks :: Prelude.Int -> (NonEmpty0.NonEmpty
                              (LinearScan__Block a1)) -> (,)
                              (Vector0.Vec (Prelude.Maybe Range.RangeDesc))
                              (Vector0.Vec (Prelude.Maybe Range.RangeDesc))
_LinearScan__processBlocks maxVirtReg blocks =
  case _LinearScan__applyList maxVirtReg blocks
         (_LinearScan__emptyBoundedRangeVec maxVirtReg) (\x x0 _ ->
         _LinearScan__handleBlock maxVirtReg x x0) of {
   LinearScan__Build_boundedRangeVec vars' regs' -> (,)
    (LinearScan.Utils.vmap maxVirtReg _LinearScan__extractRange vars')
    (LinearScan.Utils.vmap _MyMachine__maxReg _LinearScan__extractRange
      regs')}

_LinearScan__determineIntervals :: Prelude.Int -> (NonEmpty0.NonEmpty
                                   (LinearScan__Block a1)) ->
                                   LinearScan__MLS__MS__ScanStateDesc
_LinearScan__determineIntervals maxVirtReg blocks =
  let {
   mkint = \ss mx f ->
    case mx of {
     Prelude.Just s ->
      f ss __ (Interval.Build_IntervalDesc (Range.rbeg s) (Range.rend s)
        (NonEmpty0.NE_Sing s)) __;
     Prelude.Nothing -> ss}}
  in
  let {
   handleVar = \ss mx ->
    (Prelude.$) (mkint ss mx) (\sd _ d _ ->
      _LinearScan__MLS__MS__packScanState
        (LinearScan__MLS__MS__Build_ScanStateDesc (Prelude.succ
        (_LinearScan__MLS__MS__nextInterval sd))
        (LinearScan.Utils.snoc (_LinearScan__MLS__MS__nextInterval sd)
          (_LinearScan__MLS__MS__intervals sd) d)
        (_LinearScan__MLS__MS__fixedIntervals sd)
        (Lib.insert (\x ->
          Lib.lebf Prelude.snd x ((,)
            (Fintype.ord_max (_LinearScan__MLS__MS__nextInterval sd))
            (Interval.ibeg d))) ((,)
          (Fintype.ord_max (_LinearScan__MLS__MS__nextInterval sd))
          (Interval.ibeg d))
          (Prelude.map
            (Lib.widen_fst (_LinearScan__MLS__MS__nextInterval sd))
            (_LinearScan__MLS__MS__unhandled sd)))
        (Prelude.map (Lib.widen_fst (_LinearScan__MLS__MS__nextInterval sd))
          (_LinearScan__MLS__MS__active sd))
        (Prelude.map (Lib.widen_fst (_LinearScan__MLS__MS__nextInterval sd))
          (_LinearScan__MLS__MS__inactive sd))
        (Prelude.map (Lib.widen_fst (_LinearScan__MLS__MS__nextInterval sd))
          (_LinearScan__MLS__MS__handled sd))))}
  in
  case _LinearScan__processBlocks maxVirtReg blocks of {
   (,) varRanges regRanges ->
    let {
     regs0 = LinearScan.Utils.vmap _MyMachine__maxReg (\mr ->
               case mr of {
                Prelude.Just r -> Prelude.Just
                 (Interval.packInterval (Interval.Build_IntervalDesc
                   (Range.rbeg ( r)) (Range.rend ( r)) (NonEmpty0.NE_Sing
                   ( r))));
                Prelude.Nothing -> Prelude.Nothing}) regRanges}
    in
    let {
     s2 = _LinearScan__MLS__MS__packScanState
            (LinearScan__MLS__MS__Build_ScanStateDesc
            (_LinearScan__MLS__MS__nextInterval
              (LinearScan__MLS__MS__Build_ScanStateDesc 0 ([])
              (Data.List.replicate _MyMachine__maxReg Prelude.Nothing) [] []
              [] []))
            (_LinearScan__MLS__MS__intervals
              (LinearScan__MLS__MS__Build_ScanStateDesc 0 ([])
              (Data.List.replicate _MyMachine__maxReg Prelude.Nothing) [] []
              [] [])) regs0
            (_LinearScan__MLS__MS__unhandled
              (LinearScan__MLS__MS__Build_ScanStateDesc 0 ([])
              (Data.List.replicate _MyMachine__maxReg Prelude.Nothing) [] []
              [] []))
            (_LinearScan__MLS__MS__active
              (LinearScan__MLS__MS__Build_ScanStateDesc 0 ([])
              (Data.List.replicate _MyMachine__maxReg Prelude.Nothing) [] []
              [] []))
            (_LinearScan__MLS__MS__inactive
              (LinearScan__MLS__MS__Build_ScanStateDesc 0 ([])
              (Data.List.replicate _MyMachine__maxReg Prelude.Nothing) [] []
              [] []))
            (_LinearScan__MLS__MS__handled
              (LinearScan__MLS__MS__Build_ScanStateDesc 0 ([])
              (Data.List.replicate _MyMachine__maxReg Prelude.Nothing) [] []
              [] [])))}
    in
    LinearScan.Utils.vfoldl' maxVirtReg handleVar s2 varRanges}

_LinearScan__allocateRegisters :: Prelude.Int -> (NonEmpty0.NonEmpty
                                  (LinearScan__Block a1)) ->
                                  LinearScan__MLS__MS__ScanStateDesc
_LinearScan__allocateRegisters maxVirtReg blocks =
  
    (Lib.uncurry_sig (\x _ -> _LinearScan__linearScan x)
      (_LinearScan__determineIntervals maxVirtReg blocks))

