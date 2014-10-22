{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Main where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.IApplicative as IApplicative
import qualified LinearScan.IEndo as IEndo
import qualified LinearScan.IMonad as IMonad
import qualified LinearScan.IState as IState
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Lib as Lib
import qualified LinearScan.List0 as List0
import qualified LinearScan.Logic as Logic
import qualified LinearScan.NonEmpty0 as NonEmpty0
import qualified LinearScan.Range as Range
import qualified LinearScan.Specif as Specif
import qualified LinearScan.Vector0 as Vector0
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
_MyMachine__maxReg =
  Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ 0)))))))))))))))))))))))))))))))

_LinearScan__maxReg :: Prelude.Int
_LinearScan__maxReg =
  _MyMachine__maxReg

type LinearScan__PhysReg = Vector0.Coq_fin

data LinearScan__ScanStateDesc =
   LinearScan__Build_ScanStateDesc Prelude.Int ([]
                                               ((,) Vector0.Coq_fin
                                               Prelude.Int)) ([]
                                                             Vector0.Coq_fin) 
 ([] Vector0.Coq_fin) ([] Vector0.Coq_fin) (Lib.Vec Interval.IntervalDesc) 
 (Lib.Vec (Prelude.Maybe LinearScan__PhysReg)) (Lib.Vec
                                               (Prelude.Maybe
                                               Interval.IntervalDesc))

_LinearScan__coq_ScanStateDesc_rect :: (Prelude.Int -> ([]
                                       ((,) Vector0.Coq_fin Prelude.Int)) ->
                                       ([] Vector0.Coq_fin) -> ([]
                                       Vector0.Coq_fin) -> ([]
                                       Vector0.Coq_fin) -> (Lib.Vec
                                       Interval.IntervalDesc) -> (Lib.Vec
                                       (Prelude.Maybe LinearScan__PhysReg))
                                       -> (Lib.Vec
                                       (Prelude.Maybe Interval.IntervalDesc))
                                       -> () -> a1) ->
                                       LinearScan__ScanStateDesc -> a1
_LinearScan__coq_ScanStateDesc_rect f s =
  case s of {
   LinearScan__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6 __}

_LinearScan__coq_ScanStateDesc_rec :: (Prelude.Int -> ([]
                                      ((,) Vector0.Coq_fin Prelude.Int)) ->
                                      ([] Vector0.Coq_fin) -> ([]
                                      Vector0.Coq_fin) -> ([]
                                      Vector0.Coq_fin) -> (Lib.Vec
                                      Interval.IntervalDesc) -> (Lib.Vec
                                      (Prelude.Maybe LinearScan__PhysReg)) ->
                                      (Lib.Vec
                                      (Prelude.Maybe Interval.IntervalDesc))
                                      -> () -> a1) ->
                                      LinearScan__ScanStateDesc -> a1
_LinearScan__coq_ScanStateDesc_rec =
  _LinearScan__coq_ScanStateDesc_rect

_LinearScan__nextInterval :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__nextInterval s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> nextInterval0}

type LinearScan__IntervalId = Vector0.Coq_fin

_LinearScan__unhandled :: LinearScan__ScanStateDesc -> []
                          ((,) LinearScan__IntervalId Prelude.Int)
_LinearScan__unhandled s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> unhandled0}

_LinearScan__active :: LinearScan__ScanStateDesc -> [] LinearScan__IntervalId
_LinearScan__active s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> active0}

_LinearScan__inactive :: LinearScan__ScanStateDesc -> []
                         LinearScan__IntervalId
_LinearScan__inactive s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> inactive0}

_LinearScan__unhandledIds :: LinearScan__ScanStateDesc -> []
                             LinearScan__IntervalId
_LinearScan__unhandledIds s =
  (Prelude.map) (Prelude.fst) (_LinearScan__unhandled s)

_LinearScan__handled :: LinearScan__ScanStateDesc -> []
                        LinearScan__IntervalId
_LinearScan__handled s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> x}

_LinearScan__intervals :: LinearScan__ScanStateDesc -> Lib.Vec
                          Interval.IntervalDesc
_LinearScan__intervals s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> x0}

_LinearScan__assignments :: LinearScan__ScanStateDesc -> Lib.Vec
                            (Prelude.Maybe LinearScan__PhysReg)
_LinearScan__assignments s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> x1}

_LinearScan__fixedIntervals :: LinearScan__ScanStateDesc -> Lib.Vec
                               (Prelude.Maybe Interval.IntervalDesc)
_LinearScan__fixedIntervals s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    x x0 x1 x2 -> x2}

_LinearScan__all_state_lists :: LinearScan__ScanStateDesc -> []
                                LinearScan__IntervalId
_LinearScan__all_state_lists s =
  (Prelude.++) (_LinearScan__unhandledIds s)
    ((Prelude.++) (_LinearScan__active s)
      ((Prelude.++) (_LinearScan__inactive s) (_LinearScan__handled s)))

_LinearScan__getAssignment :: LinearScan__ScanStateDesc ->
                              LinearScan__IntervalId -> Prelude.Maybe
                              LinearScan__PhysReg
_LinearScan__getAssignment sd i =
  Lib._V__nth (_LinearScan__nextInterval sd) (_LinearScan__assignments sd)
    (Vector0.to_vfin (_LinearScan__nextInterval sd) i)

_LinearScan__transportId :: LinearScan__ScanStateDesc ->
                            LinearScan__ScanStateDesc ->
                            LinearScan__IntervalId -> LinearScan__IntervalId
_LinearScan__transportId sd sd' =
  Fintype.widen_ord (_LinearScan__nextInterval sd)
    (_LinearScan__nextInterval sd')

_LinearScan__unhandledExtent :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__unhandledExtent sd =
  case _LinearScan__unhandledIds sd of {
   [] -> 0;
   (:) i l ->
    case l of {
     [] ->
      Interval.intervalExtent
        (
          (Lib._V__nth (_LinearScan__nextInterval sd)
            (_LinearScan__intervals sd)
            (Vector0.to_vfin (_LinearScan__nextInterval sd) i)));
     (:) i0 l0 ->
      let {
       f = \n x ->
        (Prelude.+) n
          (Interval.intervalExtent
            (
              (Lib._V__nth (_LinearScan__nextInterval sd)
                (_LinearScan__intervals sd)
                (Vector0.to_vfin (_LinearScan__nextInterval sd) x))))}
      in
      Data.List.foldl' f 0 ((:) i ((:) i0 l0))}}

_LinearScan__registerWithHighestPos :: (Lib.Vec (Prelude.Maybe Prelude.Int))
                                       -> (,) Vector0.Coq_fin
                                       (Prelude.Maybe Prelude.Int)
_LinearScan__registerWithHighestPos =
  unsafeCoerce
    (Vector0.fold_left_with_index _LinearScan__maxReg (\reg res x ->
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
         Prelude.Nothing -> (,) r Prelude.Nothing}}) ((,) 0 (Prelude.Just
      0)))

_LinearScan__atIntervalReg :: LinearScan__ScanStateDesc ->
                              LinearScan__IntervalId -> (Lib.Vec a1) -> a1 ->
                              Lib.V__Coq_t a1
_LinearScan__atIntervalReg sd i v x =
  case Lib._V__nth (_LinearScan__nextInterval sd)
         (_LinearScan__assignments sd)
         (Vector0.to_vfin (_LinearScan__nextInterval sd) i) of {
   Prelude.Just r ->
    Lib._V__replace _LinearScan__maxReg v
      (Vector0.to_vfin _LinearScan__maxReg r) x;
   Prelude.Nothing -> v}

type LinearScan__ScanStateSig = LinearScan__ScanStateDesc

_LinearScan__getScanStateDesc :: LinearScan__ScanStateDesc ->
                                 LinearScan__ScanStateDesc
_LinearScan__getScanStateDesc sd =
  sd

_LinearScan__coq_ScanStateCursor_rect :: LinearScan__ScanStateDesc -> (() ->
                                         () -> a1) -> a1
_LinearScan__coq_ScanStateCursor_rect sd f =
  f __ __

_LinearScan__coq_ScanStateCursor_rec :: LinearScan__ScanStateDesc -> (() ->
                                        () -> a1) -> a1
_LinearScan__coq_ScanStateCursor_rec sd f =
  _LinearScan__coq_ScanStateCursor_rect sd f

_LinearScan__curId :: LinearScan__ScanStateDesc -> (,) LinearScan__IntervalId
                      Prelude.Int
_LinearScan__curId sd =
  (Prelude.head) (_LinearScan__unhandled sd)

_LinearScan__curIntDetails :: LinearScan__ScanStateDesc ->
                              Interval.IntervalDesc
_LinearScan__curIntDetails sd =
  Lib._V__nth (_LinearScan__nextInterval sd) (_LinearScan__intervals sd)
    (Vector0.to_vfin (_LinearScan__nextInterval sd)
      ((Prelude.fst) (_LinearScan__curId sd)))

_LinearScan__curStateDesc :: LinearScan__ScanStateDesc ->
                             LinearScan__ScanStateDesc
_LinearScan__curStateDesc sd =
  sd

_LinearScan__curIntDesc :: LinearScan__ScanStateDesc -> Interval.IntervalDesc
_LinearScan__curIntDesc sd =
   (_LinearScan__curIntDetails sd)

_LinearScan__curPosition :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__curPosition sd =
  Interval.intervalStart ( (_LinearScan__curIntDetails sd))

type LinearScan__NextScanState =
  LinearScan__ScanStateDesc
  -- singleton inductive, whose constructor was Build_NextScanState
  
_LinearScan__coq_NextScanState_rect :: (LinearScan__ScanStateDesc -> () -> ()
                                       -> a1) -> LinearScan__NextScanState ->
                                       a1
_LinearScan__coq_NextScanState_rect f n =
  f n __ __

_LinearScan__coq_NextScanState_rec :: (LinearScan__ScanStateDesc -> () -> ()
                                      -> a1) -> LinearScan__NextScanState ->
                                      a1
_LinearScan__coq_NextScanState_rec =
  _LinearScan__coq_NextScanState_rect

_LinearScan__nextDesc :: LinearScan__NextScanState ->
                         LinearScan__ScanStateDesc
_LinearScan__nextDesc n =
  n

type LinearScan__NextState = LinearScan__NextScanState

type LinearScan__NextStateDep = LinearScan__NextScanState

type LinearScan__NextStateWith a = (,) a LinearScan__NextScanState

_LinearScan__coq_NSS_transport :: LinearScan__ScanStateDesc ->
                                  LinearScan__ScanStateDesc ->
                                  LinearScan__NextScanState ->
                                  LinearScan__NextScanState
_LinearScan__coq_NSS_transport sd sd' n =
  _LinearScan__nextDesc n

_LinearScan__coq_SSMorph_rect :: LinearScan__ScanStateDesc ->
                                 LinearScan__ScanStateDesc -> (() -> () -> ()
                                 -> a1) -> a1
_LinearScan__coq_SSMorph_rect sd1 sd2 f =
  f __ __ __

_LinearScan__coq_SSMorph_rec :: LinearScan__ScanStateDesc ->
                                LinearScan__ScanStateDesc -> (() -> () -> ()
                                -> a1) -> a1
_LinearScan__coq_SSMorph_rec sd1 sd2 f =
  _LinearScan__coq_SSMorph_rect sd1 sd2 f

_LinearScan__coq_SSMorphSt_rect :: LinearScan__ScanStateDesc ->
                                   LinearScan__ScanStateDesc -> (() -> () ->
                                   a1) -> a1
_LinearScan__coq_SSMorphSt_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphSt_rec :: LinearScan__ScanStateDesc ->
                                  LinearScan__ScanStateDesc -> (() -> () ->
                                  a1) -> a1
_LinearScan__coq_SSMorphSt_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphSt_rect sd1 sd2 f

_LinearScan__coq_SSMorphLen_rect :: LinearScan__ScanStateDesc ->
                                    LinearScan__ScanStateDesc -> (() -> () ->
                                    a1) -> a1
_LinearScan__coq_SSMorphLen_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphLen_rec :: LinearScan__ScanStateDesc ->
                                   LinearScan__ScanStateDesc -> (() -> () ->
                                   a1) -> a1
_LinearScan__coq_SSMorphLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphLen_rect sd1 sd2 f

_LinearScan__transportation :: LinearScan__ScanStateDesc ->
                               LinearScan__ScanStateDesc ->
                               LinearScan__IntervalId ->
                               LinearScan__IntervalId
_LinearScan__transportation sd1 sd2 x =
  _LinearScan__transportId sd1 sd2 x

_LinearScan__coq_SSMorphStLen_rect :: LinearScan__ScanStateDesc ->
                                      LinearScan__ScanStateDesc -> (() -> ()
                                      -> () -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __ __

_LinearScan__coq_SSMorphStLen_rec :: LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc -> (() -> ()
                                     -> () -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphStLen_rect sd1 sd2 f

_LinearScan__coq_SSMorphHasLen_rect :: LinearScan__ScanStateDesc ->
                                       LinearScan__ScanStateDesc -> (() -> ()
                                       -> () -> a1) -> a1
_LinearScan__coq_SSMorphHasLen_rect sd1 sd2 f =
  f __ __ __

_LinearScan__coq_SSMorphHasLen_rec :: LinearScan__ScanStateDesc ->
                                      LinearScan__ScanStateDesc -> (() -> ()
                                      -> () -> a1) -> a1
_LinearScan__coq_SSMorphHasLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphHasLen_rect sd1 sd2 f

data LinearScan__HasWork =
   LinearScan__Build_HasWork

_LinearScan__coq_HasWork_rect :: (() -> a1) -> a1
_LinearScan__coq_HasWork_rect f =
  f __

_LinearScan__coq_HasWork_rec :: (() -> a1) -> a1
_LinearScan__coq_HasWork_rec f =
  _LinearScan__coq_HasWork_rect f

_LinearScan__coq_SSMorphStHasLen_rect :: LinearScan__ScanStateDesc ->
                                         LinearScan__ScanStateDesc -> (() ->
                                         () -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphStHasLen_rect sd1 sd2 f =
  f __ __ __ __

_LinearScan__coq_SSMorphStHasLen_rec :: LinearScan__ScanStateDesc ->
                                        LinearScan__ScanStateDesc -> (() ->
                                        () -> () -> () -> a1) -> a1
_LinearScan__coq_SSMorphStHasLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphStHasLen_rect sd1 sd2 f

type LinearScan__SSInfo =
  LinearScan__ScanStateDesc
  -- singleton inductive, whose constructor was Build_SSInfo
  
_LinearScan__coq_SSInfo_rect :: LinearScan__ScanStateDesc ->
                                (LinearScan__ScanStateDesc -> () -> () -> a1)
                                -> LinearScan__SSInfo -> a1
_LinearScan__coq_SSInfo_rect startDesc f s =
  f s __ __

_LinearScan__coq_SSInfo_rec :: LinearScan__ScanStateDesc ->
                               (LinearScan__ScanStateDesc -> () -> () -> a1)
                               -> LinearScan__SSInfo -> a1
_LinearScan__coq_SSInfo_rec startDesc =
  _LinearScan__coq_SSInfo_rect startDesc

_LinearScan__thisDesc :: LinearScan__ScanStateDesc -> LinearScan__SSInfo ->
                         LinearScan__ScanStateDesc
_LinearScan__thisDesc startDesc s =
  s

type LinearScan__SState a =
  IState.IState LinearScan__SSInfo LinearScan__SSInfo a

_LinearScan__withScanState :: LinearScan__ScanStateDesc ->
                              (LinearScan__ScanStateDesc -> () ->
                              LinearScan__SState a1) -> LinearScan__SState 
                              a1
_LinearScan__withScanState pre f =
  IMonad.ibind (unsafeCoerce IState.coq_IState_IMonad) (\i ->
    f (_LinearScan__thisDesc pre i) __) (unsafeCoerce IState.iget)

_LinearScan__withScanStatePO :: LinearScan__ScanStateDesc ->
                                (LinearScan__ScanStateDesc -> () ->
                                LinearScan__SState a1) -> LinearScan__SState
                                a1
_LinearScan__withScanStatePO pre f i =
  f i __ i

_LinearScan__liftLen :: LinearScan__ScanStateDesc -> (LinearScan__SState 
                        a1) -> LinearScan__SState a1
_LinearScan__liftLen pre x x0 =
  let {p = x x0} in
  case p of {
   (,) a0 s -> (,) a0 x0}

_LinearScan__stbind :: (a4 -> IState.IState a2 a3 a5) -> (IState.IState 
                       a1 a2 a4) -> IState.IState a1 a3 a5
_LinearScan__stbind f x =
  IMonad.ijoin (unsafeCoerce IState.coq_IState_IMonad)
    (IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) f (unsafeCoerce x))

_LinearScan__return_ :: a2 -> IState.IState a1 a1 a2
_LinearScan__return_ =
  IApplicative.ipure (unsafeCoerce IState.coq_IState_IApplicative)

_LinearScan__weakenStHasLenToSt :: LinearScan__ScanStateDesc ->
                                   LinearScan__SState ()
_LinearScan__weakenStHasLenToSt pre hS =
  (,) () hS

_LinearScan__withCursor :: LinearScan__ScanStateDesc ->
                           (LinearScan__ScanStateDesc -> () ->
                           LinearScan__SState a1) -> LinearScan__SState 
                           a1
_LinearScan__withCursor pre f i =
  f i __ i

_LinearScan__moveUnhandledToActive :: LinearScan__ScanStateDesc ->
                                      LinearScan__PhysReg ->
                                      LinearScan__SState ()
_LinearScan__moveUnhandledToActive pre reg x =
  (,) ()
    (case x of {
      LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0
       inactive0 x0 x1 x2 x3 ->
       case unhandled0 of {
        [] -> Logic.coq_False_rect;
        (:) p unhandled1 -> LinearScan__Build_ScanStateDesc nextInterval0
         unhandled1 ((:) ((Prelude.fst) p) active0) inactive0 x0 x1
         (Lib._V__replace nextInterval0 x2
           (Vector0.to_vfin nextInterval0 ((Prelude.fst) p)) (Prelude.Just
           reg)) x3}})

_LinearScan__moveActiveToHandled :: LinearScan__ScanStateDesc ->
                                    LinearScan__IntervalId -> Specif.Coq_sig2
                                    LinearScan__ScanStateDesc
_LinearScan__moveActiveToHandled sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd)
    (unsafeCoerce
      (Seq.rem (Fintype.ordinal_eqType (_LinearScan__nextInterval sd))
        (unsafeCoerce x) (unsafeCoerce (_LinearScan__active sd)))) ((:) x
    (_LinearScan__inactive sd)) (_LinearScan__handled sd)
    (_LinearScan__intervals sd) (_LinearScan__assignments sd)
    (_LinearScan__fixedIntervals sd)

_LinearScan__moveActiveToInactive :: LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId ->
                                     Specif.Coq_sig2
                                     LinearScan__ScanStateDesc
_LinearScan__moveActiveToInactive sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd)
    (unsafeCoerce
      (Seq.rem (Fintype.ordinal_eqType (_LinearScan__nextInterval sd))
        (unsafeCoerce x) (unsafeCoerce (_LinearScan__active sd)))) ((:) x
    (_LinearScan__inactive sd)) (_LinearScan__handled sd)
    (_LinearScan__intervals sd) (_LinearScan__assignments sd)
    (_LinearScan__fixedIntervals sd)

_LinearScan__moveInactiveToActive :: LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId ->
                                     Specif.Coq_sig2
                                     LinearScan__ScanStateDesc
_LinearScan__moveInactiveToActive sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd) ((:) x (_LinearScan__active sd))
    (unsafeCoerce
      (Seq.rem (Fintype.ordinal_eqType (_LinearScan__nextInterval sd))
        (unsafeCoerce x) (unsafeCoerce (_LinearScan__inactive sd))))
    (_LinearScan__handled sd) (_LinearScan__intervals sd)
    (_LinearScan__assignments sd) (_LinearScan__fixedIntervals sd)

_LinearScan__moveInactiveToHandled :: LinearScan__ScanStateDesc ->
                                      LinearScan__IntervalId ->
                                      Specif.Coq_sig2
                                      LinearScan__ScanStateDesc
_LinearScan__moveInactiveToHandled sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd) (_LinearScan__active sd)
    (unsafeCoerce
      (Seq.rem (Fintype.ordinal_eqType (_LinearScan__nextInterval sd))
        (unsafeCoerce x) (unsafeCoerce (_LinearScan__inactive sd)))) ((:) x
    (_LinearScan__handled sd)) (_LinearScan__intervals sd)
    (_LinearScan__assignments sd) (_LinearScan__fixedIntervals sd)

_LinearScan__splitCurrentInterval :: LinearScan__ScanStateDesc ->
                                     (Prelude.Maybe Prelude.Int) ->
                                     LinearScan__SState ()
_LinearScan__splitCurrentInterval =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__splitActiveIntervalForReg :: LinearScan__ScanStateDesc ->
                                          LinearScan__PhysReg -> Prelude.Int
                                          -> LinearScan__SState ()
_LinearScan__splitActiveIntervalForReg =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__splitAnyInactiveIntervalForReg :: LinearScan__ScanStateDesc ->
                                               LinearScan__PhysReg ->
                                               LinearScan__SState ()
_LinearScan__splitAnyInactiveIntervalForReg =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__intersectsWithFixedInterval :: LinearScan__ScanStateDesc ->
                                            LinearScan__PhysReg ->
                                            LinearScan__SState
                                            (Prelude.Maybe Prelude.Int)
_LinearScan__intersectsWithFixedInterval =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__assignSpillSlotToCurrent :: LinearScan__ScanStateDesc ->
                                         LinearScan__SState ()
_LinearScan__assignSpillSlotToCurrent =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__tryAllocateFreeReg :: LinearScan__ScanStateDesc ->
                                   LinearScan__SState
                                   (Prelude.Maybe
                                   (LinearScan__SState LinearScan__PhysReg))
_LinearScan__tryAllocateFreeReg pre =
  (Prelude.$) (_LinearScan__withCursor pre) (\sd _ ->
    let {sd0 = _LinearScan__curStateDesc sd} in
    let {
     go = \n ->
      List0.fold_left (\v i -> _LinearScan__atIntervalReg sd0 i v (n i))}
    in
    let {
     freeUntilPos' = go (\x -> Prelude.Just 0) (_LinearScan__active sd0)
                       (Lib._V__const Prelude.Nothing _LinearScan__maxReg)}
    in
    let {
     intersectingIntervals = List0.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (_LinearScan__curIntDetails sd))
                                 (
                                   (Lib._V__nth
                                     (_LinearScan__nextInterval sd0)
                                     (_LinearScan__intervals sd0)
                                     (Vector0.to_vfin
                                       (_LinearScan__nextInterval sd0) x))))
                               (_LinearScan__inactive sd0)}
    in
    let {
     freeUntilPos = go (\i ->
                      Interval.intervalIntersectionPoint
                        (
                          (Lib._V__nth (_LinearScan__nextInterval sd0)
                            (_LinearScan__intervals sd0)
                            (Vector0.to_vfin (_LinearScan__nextInterval sd0)
                              i))) ( (_LinearScan__curIntDetails sd)))
                      intersectingIntervals freeUntilPos'}
    in
    case _LinearScan__registerWithHighestPos freeUntilPos of {
     (,) reg mres ->
      let {
       success = _LinearScan__stbind (\x -> _LinearScan__return_ reg)
                   (_LinearScan__moveUnhandledToActive pre reg)}
      in
      let {
       maction = case mres of {
                  Prelude.Just n ->
                   case (Prelude.==) n 0 of {
                    Prelude.True -> Prelude.Nothing;
                    Prelude.False -> Prelude.Just
                     (case (Prelude.<=) (Prelude.succ
                             (Interval.intervalEnd
                               ( (_LinearScan__curIntDetails sd)))) n of {
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

_LinearScan__allocateBlockedReg :: LinearScan__ScanStateDesc ->
                                   LinearScan__SState
                                   (Prelude.Maybe LinearScan__PhysReg)
_LinearScan__allocateBlockedReg pre =
  (Prelude.$) (_LinearScan__withCursor pre) (\sd _ ->
    let {start = Interval.intervalStart ( (_LinearScan__curIntDetails sd))}
    in
    let {pos = _LinearScan__curPosition sd} in
    let {
     go = List0.fold_left (\v i ->
            _LinearScan__atIntervalReg sd i v
              (Interval.nextUseAfter
                (
                  (Lib._V__nth (_LinearScan__nextInterval sd)
                    (_LinearScan__intervals sd)
                    (Vector0.to_vfin (_LinearScan__nextInterval sd) i)))
                start))}
    in
    let {
     nextUsePos' = go (_LinearScan__active sd)
                     (Lib._V__const Prelude.Nothing _LinearScan__maxReg)}
    in
    let {
     intersectingIntervals = List0.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (_LinearScan__curIntDetails sd))
                                 (
                                   (Lib._V__nth
                                     (_LinearScan__nextInterval sd)
                                     (_LinearScan__intervals sd)
                                     (Vector0.to_vfin
                                       (_LinearScan__nextInterval sd) x))))
                               (_LinearScan__inactive sd)}
    in
    let {nextUsePos = go intersectingIntervals nextUsePos'} in
    case _LinearScan__registerWithHighestPos nextUsePos of {
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
              (Interval.firstUseReqReg ( (_LinearScan__curIntDetails sd)))))
          (_LinearScan__assignSpillSlotToCurrent pre);
       Prelude.False ->
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

_LinearScan__checkActiveIntervals :: LinearScan__ScanStateDesc -> Prelude.Int
                                     -> LinearScan__SState ()
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
                               (Lib._V__nth (_LinearScan__nextInterval sd)
                                 (_LinearScan__intervals sd)
                                 (Vector0.to_vfin
                                   (_LinearScan__nextInterval sd) ( x))))))
                           pos of {
                     Prelude.True ->
                      Lib.uncurry_sig (\x0 _ ->
                        _LinearScan__moveActiveToHandled sd x0) x;
                     Prelude.False ->
                      case (Prelude.not)
                             (Interval.intervalCoversPos
                               (
                                 (Lib._V__nth (_LinearScan__nextInterval sd)
                                   (_LinearScan__intervals sd)
                                   (Vector0.to_vfin
                                     (_LinearScan__nextInterval sd) ( x))))
                               pos) of {
                       Prelude.True ->
                        Lib.uncurry_sig (\x0 _ ->
                          _LinearScan__moveActiveToInactive sd x0) x;
                       Prelude.False -> ss}}}
             in
             go sd st1 xs}}
        in go}
  in
  (Prelude.$) (_LinearScan__withScanStatePO pre) (\sd _ ->
    IState.iput
      (unsafeCoerce go sd sd
        (Lib.list_membership
          (Fintype.ordinal_eqType (_LinearScan__nextInterval sd))
          (unsafeCoerce (_LinearScan__active sd)))))

_LinearScan__checkInactiveIntervals :: LinearScan__ScanStateDesc ->
                                       Prelude.Int -> LinearScan__SState 
                                       ()
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
                               (Lib._V__nth (_LinearScan__nextInterval sd)
                                 (_LinearScan__intervals sd)
                                 (Vector0.to_vfin
                                   (_LinearScan__nextInterval sd) ( x))))))
                           pos of {
                     Prelude.True ->
                      Lib.uncurry_sig (\x0 _ ->
                        _LinearScan__moveInactiveToHandled sd x0) x;
                     Prelude.False ->
                      case Interval.intervalCoversPos
                             (
                               (Lib._V__nth (_LinearScan__nextInterval sd)
                                 (_LinearScan__intervals sd)
                                 (Vector0.to_vfin
                                   (_LinearScan__nextInterval sd) ( x)))) pos of {
                       Prelude.True ->
                        Lib.uncurry_sig (\x0 _ ->
                          _LinearScan__moveInactiveToActive sd x0) x;
                       Prelude.False -> ss}}}
             in
             go sd st1 xs}}
        in go}
  in
  (Prelude.$) (_LinearScan__withScanStatePO pre) (\sd _ ->
    IState.iput
      (unsafeCoerce go sd sd
        (Lib.list_membership
          (Fintype.ordinal_eqType (_LinearScan__nextInterval sd))
          (unsafeCoerce (_LinearScan__inactive sd)))))

_LinearScan__handleInterval :: LinearScan__ScanStateDesc ->
                               LinearScan__SState
                               (Prelude.Maybe LinearScan__PhysReg)
_LinearScan__handleInterval pre =
  (Prelude.$) (unsafeCoerce (_LinearScan__withCursor pre)) (\sd _ ->
    let {position = _LinearScan__curPosition sd} in
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

_LinearScan__linearScan_F :: (LinearScan__ScanStateDesc -> () ->
                             LinearScan__ScanStateDesc) ->
                             LinearScan__ScanStateDesc ->
                             LinearScan__ScanStateDesc
_LinearScan__linearScan_F linearScan0 sd =
  case List0.destruct_list (_LinearScan__unhandled sd) of {
   Prelude.Just s ->
    case IState.runIState (_LinearScan__handleInterval sd) sd of {
     (,) x ssinfo' -> linearScan0 (_LinearScan__thisDesc sd ssinfo') __};
   Prelude.Nothing -> sd}

_LinearScan__linearScan_terminate :: LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc
_LinearScan__linearScan_terminate =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__linearScan :: LinearScan__ScanStateDesc ->
                           LinearScan__ScanStateDesc
_LinearScan__linearScan x =
  Prelude.error "AXIOM TO BE REALIZED"

data LinearScan__R_linearScan =
   LinearScan__R_linearScan_0 LinearScan__ScanStateDesc ((,)
                                                        LinearScan__IntervalId
                                                        Prelude.Int) 
 ([] ((,) LinearScan__IntervalId Prelude.Int)) (Prelude.Maybe
                                               LinearScan__PhysReg) LinearScan__SSInfo 
 LinearScan__ScanStateDesc LinearScan__R_linearScan
 | LinearScan__R_linearScan_1 LinearScan__ScanStateDesc

_LinearScan__coq_R_linearScan_rect :: (LinearScan__ScanStateDesc -> () ->
                                      ((,) LinearScan__IntervalId
                                      Prelude.Int) -> ([]
                                      ((,) LinearScan__IntervalId
                                      Prelude.Int)) -> () -> () ->
                                      (Prelude.Maybe LinearScan__PhysReg) ->
                                      LinearScan__SSInfo -> () ->
                                      LinearScan__ScanStateDesc ->
                                      LinearScan__R_linearScan -> a1 -> a1)
                                      -> (LinearScan__ScanStateDesc -> () ->
                                      () -> () -> a1) ->
                                      LinearScan__ScanStateDesc ->
                                      LinearScan__ScanStateDesc ->
                                      LinearScan__R_linearScan -> a1
_LinearScan__coq_R_linearScan_rect f f0 sd s r =
  case r of {
   LinearScan__R_linearScan_0 sd0 x xs x0 x1 x2 x3 ->
    f sd0 __ x xs __ __ x0 x1 __ x2 x3
      (_LinearScan__coq_R_linearScan_rect f f0 (_LinearScan__thisDesc sd0 x1)
        x2 x3);
   LinearScan__R_linearScan_1 sd0 -> f0 sd0 __ __ __}

_LinearScan__coq_R_linearScan_rec :: (LinearScan__ScanStateDesc -> () -> ((,)
                                     LinearScan__IntervalId Prelude.Int) ->
                                     ([]
                                     ((,) LinearScan__IntervalId Prelude.Int))
                                     -> () -> () -> (Prelude.Maybe
                                     LinearScan__PhysReg) ->
                                     LinearScan__SSInfo -> () ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__R_linearScan -> a1 -> a1) ->
                                     (LinearScan__ScanStateDesc -> () -> ()
                                     -> () -> a1) ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__R_linearScan -> a1
_LinearScan__coq_R_linearScan_rec f f0 sd s r =
  _LinearScan__coq_R_linearScan_rect f f0 sd s r

type LinearScan__VirtReg = Prelude.Int

type LinearScan__SomeVar = Vector0.Coq_fin

data LinearScan__Block baseType =
   LinearScan__Build_Block baseType Prelude.Bool Prelude.Bool Prelude.Int 
 (Lib.Vec LinearScan__SomeVar)

_LinearScan__coq_Block_rect :: Prelude.Int -> (a1 -> Prelude.Bool ->
                               Prelude.Bool -> Prelude.Int -> (Lib.Vec
                               LinearScan__SomeVar) -> a2) ->
                               (LinearScan__Block a1) -> a2
_LinearScan__coq_Block_rect maxVirtReg f b =
  case b of {
   LinearScan__Build_Block x x0 x1 x2 x3 -> f x x0 x1 x2 x3}

_LinearScan__coq_Block_rec :: Prelude.Int -> (a1 -> Prelude.Bool ->
                              Prelude.Bool -> Prelude.Int -> (Lib.Vec
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

_LinearScan__references :: Prelude.Int -> (LinearScan__Block a1) -> Lib.Vec
                           LinearScan__SomeVar
_LinearScan__references maxVirtReg b =
  case b of {
   LinearScan__Build_Block original0 loopBound0 regRequired0 refCount0
    references0 -> references0}

type LinearScan__Coq_boundedRange = Specif.Coq_sig2 Range.RangeDesc

type LinearScan__Coq_boundedTriple =
  (,) ((,) (Prelude.Maybe Prelude.Int) (Prelude.Maybe Prelude.Int))
  (Prelude.Maybe LinearScan__Coq_boundedRange)

type LinearScan__Coq_boundedRangeVec = Lib.Vec LinearScan__Coq_boundedTriple

_LinearScan__boundedTransport :: Prelude.Int -> Prelude.Int -> Prelude.Int ->
                                 LinearScan__Coq_boundedRangeVec ->
                                 LinearScan__Coq_boundedRangeVec
_LinearScan__boundedTransport =
  Prelude.error "AXIOM TO BE REALIZED"

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
  Lib._V__const ((,) ((,) Prelude.Nothing Prelude.Nothing) Prelude.Nothing)
    maxVirtReg

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
         (,) mb me -> (,) ((,) (liftOr (Prelude.min) mb pos)
          (liftOr (Prelude.max) me pos)) r}};
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
  let {rest' = Lib._V__map savingBound maxVirtReg rest} in
  case _LinearScan__references maxVirtReg b of {
   Lib.V__Coq_nil ->
    _LinearScan__boundedTransport maxVirtReg pos (Prelude.succ (Prelude.succ
      pos)) rest';
   Lib.V__Coq_cons v n vs ->
    let {
     x = consr (Lib._V__nth maxVirtReg rest' (Vector0.to_vfin maxVirtReg v))}
    in
    Lib._V__replace maxVirtReg
      (_LinearScan__boundedTransport maxVirtReg pos (Prelude.succ
        (Prelude.succ pos)) rest') (Vector0.to_vfin maxVirtReg v) x}

_LinearScan__extractRange :: LinearScan__Coq_boundedTriple -> Prelude.Maybe
                             Range.RangeSig
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
             Range.getRangeDesc (Range.Build_RangeDesc
               ((Prelude.min) b0 (Range.rbeg b))
               ((Prelude.max) e (Range.rend b)) (Range.ups b))};
          Prelude.Nothing -> b});
       Prelude.Nothing -> Prelude.Nothing}}}

_LinearScan__processBlocks :: Prelude.Int -> (NonEmpty0.NonEmpty
                              (LinearScan__Block a1)) -> Lib.Vec
                              (Prelude.Maybe Range.RangeSig)
_LinearScan__processBlocks maxVirtReg blocks =
  let {
   res = _LinearScan__applyList maxVirtReg blocks
           (_LinearScan__emptyBoundedRangeVec maxVirtReg) (\x x0 _ ->
           _LinearScan__handleBlock maxVirtReg x x0)}
  in
  Lib._V__map _LinearScan__extractRange maxVirtReg res

_LinearScan__determineIntervals :: Prelude.Int -> (NonEmpty0.NonEmpty
                                   (LinearScan__Block a1)) ->
                                   LinearScan__ScanStateDesc
_LinearScan__determineIntervals maxVirtReg blocks =
  let {
   mkint = \mx ->
    case mx of {
     Prelude.Just r0 -> Prelude.Just
      (Interval.getIntervalDesc (Interval.Build_IntervalDesc (Range.rbeg r0)
        (Range.rend r0) (NonEmpty0.NE_Sing r0)));
     Prelude.Nothing -> Prelude.Nothing}}
  in
  let {
   go = \ss mx ->
    case mkint mx of {
     Prelude.Just i0 ->
      _LinearScan__getScanStateDesc (LinearScan__Build_ScanStateDesc
        (Prelude.succ (_LinearScan__nextInterval ss)) ((:) ((,)
        (Fintype.ord_max (_LinearScan__nextInterval ss)) (Interval.ibeg i0))
        ((Prelude.map) (\p -> (,)
          (Fintype.lift (Prelude.succ (_LinearScan__nextInterval ss))
            (Fintype.ord0 (_LinearScan__nextInterval ss)) ((Prelude.fst) p))
          ((Prelude.snd) p)) (_LinearScan__unhandled ss)))
        ((Prelude.map)
          (Fintype.lift (Prelude.succ (_LinearScan__nextInterval ss))
            (Fintype.ord0 (_LinearScan__nextInterval ss)))
          (_LinearScan__active ss))
        ((Prelude.map)
          (Fintype.lift (Prelude.succ (_LinearScan__nextInterval ss))
            (Fintype.ord0 (_LinearScan__nextInterval ss)))
          (_LinearScan__inactive ss))
        ((Prelude.map)
          (Fintype.lift (Prelude.succ (_LinearScan__nextInterval ss))
            (Fintype.ord0 (_LinearScan__nextInterval ss)))
          (_LinearScan__handled ss))
        (Lib._V__shiftin (_LinearScan__nextInterval ss) i0
          (_LinearScan__intervals ss))
        (Lib._V__shiftin (_LinearScan__nextInterval ss) Prelude.Nothing
          (_LinearScan__assignments ss)) (_LinearScan__fixedIntervals ss));
     Prelude.Nothing -> ss}}
  in
  let {
   s1 = _LinearScan__getScanStateDesc (LinearScan__Build_ScanStateDesc 0 []
          [] [] [] Lib.V__Coq_nil Lib.V__Coq_nil
          (Lib._V__const Prelude.Nothing _LinearScan__maxReg))}
  in
  let {ranges = _LinearScan__processBlocks maxVirtReg blocks} in
  Lib._V__fold_left go s1 maxVirtReg ranges

_LinearScan__allocateRegisters :: Prelude.Int -> (NonEmpty0.NonEmpty
                                  (LinearScan__Block a1)) ->
                                  LinearScan__ScanStateDesc
_LinearScan__allocateRegisters maxVirtReg blocks =
  
    (Lib.uncurry_sig (\x _ -> _LinearScan__linearScan x)
      (_LinearScan__determineIntervals maxVirtReg blocks))

