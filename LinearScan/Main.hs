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
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Range as Range
import qualified LinearScan.Specif as Specif
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Seq as Seq
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

type Coq_fixedIntervalsType =
  [] (Prelude.Maybe Interval.IntervalDesc)

data ScanStateDesc =
   Build_ScanStateDesc Prelude.Int ([] Interval.IntervalDesc) 
 Coq_fixedIntervalsType ([] ((,) Prelude.Int Prelude.Int)) 
 ([] ((,) Prelude.Int PhysReg)) ([]
                                            ((,) Prelude.Int
                                            PhysReg)) ([]
                                                                  ((,)
                                                                  Prelude.Int
                                                                  PhysReg))

coq_ScanStateDesc_rect :: (Prelude.Int -> ([]
                                       Interval.IntervalDesc) ->
                                       Coq_fixedIntervalsType ->
                                       ([] ((,) Prelude.Int Prelude.Int)) ->
                                       ([]
                                       ((,) Prelude.Int PhysReg))
                                       -> ([]
                                       ((,) Prelude.Int PhysReg))
                                       -> ([]
                                       ((,) Prelude.Int PhysReg))
                                       -> a1) -> ScanStateDesc ->
                                       a1
coq_ScanStateDesc_rect f s =
  case s of {
   Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
    f x x0 x1 x2 x3 x4 x5}

coq_ScanStateDesc_rec :: (Prelude.Int -> ([]
                                      Interval.IntervalDesc) ->
                                      Coq_fixedIntervalsType ->
                                      ([] ((,) Prelude.Int Prelude.Int)) ->
                                      ([]
                                      ((,) Prelude.Int PhysReg))
                                      -> ([]
                                      ((,) Prelude.Int PhysReg))
                                      -> ([]
                                      ((,) Prelude.Int PhysReg))
                                      -> a1) -> ScanStateDesc ->
                                      a1
coq_ScanStateDesc_rec =
  coq_ScanStateDesc_rect

nextInterval :: ScanStateDesc -> Prelude.Int
nextInterval s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
    unhandled0 active0 inactive0 handled0 -> nextInterval0}

type IntervalId = Prelude.Int

intervals :: ScanStateDesc -> []
                          Interval.IntervalDesc
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

unhandledIds :: ScanStateDesc -> []
                             IntervalId
unhandledIds s =
  Prelude.map (\i -> Prelude.fst i) (unhandled s)

activeIds :: ScanStateDesc -> []
                          IntervalId
activeIds s =
  Prelude.map (\i -> Prelude.fst i) (active s)

inactiveIds :: ScanStateDesc -> []
                            IntervalId
inactiveIds s =
  Prelude.map (\i -> Prelude.fst i) (inactive s)

handledIds :: ScanStateDesc -> []
                           IntervalId
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
                                  ((,) IntervalId
                                  PhysReg)) ->
                                  PhysReg -> []
                                  IntervalId
intervals_for_reg sd xs reg =
  Data.List.foldl' (\acc x ->
    case x of {
     (,) xid r ->
      case Eqtype.eq_op (Fintype.ordinal_eqType maxReg)
             (unsafeCoerce r) (unsafeCoerce reg) of {
       Prelude.True -> (:) xid acc;
       Prelude.False -> acc}}) [] xs

registerWithHighestPos :: ([] (Prelude.Maybe Prelude.Int)) ->
                                       (,) Prelude.Int
                                       (Prelude.Maybe Prelude.Int)
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

coq_ScanStateCursor_rect :: ScanStateDesc -> (() ->
                                         () -> a1) -> a1
coq_ScanStateCursor_rect sd f =
  f __ __

coq_ScanStateCursor_rec :: ScanStateDesc -> (() ->
                                        () -> a1) -> a1
coq_ScanStateCursor_rec sd f =
  coq_ScanStateCursor_rect sd f

curId :: ScanStateDesc -> (,) IntervalId
                      Prelude.Int
curId sd =
  Prelude.head (unhandled sd)

curIntDetails :: ScanStateDesc ->
                              Interval.IntervalDesc
curIntDetails sd =
  LinearScan.Utils.nth (nextInterval sd)
    (intervals sd) (Prelude.fst (curId sd))

curPosition :: ScanStateDesc -> Prelude.Int
curPosition sd =
  Interval.intervalStart ( (curIntDetails sd))

coq_SSMorph_rect :: ScanStateDesc ->
                                 ScanStateDesc -> (() -> () -> ()
                                 -> a1) -> a1
coq_SSMorph_rect sd1 sd2 f =
  f __ __ __

coq_SSMorph_rec :: ScanStateDesc ->
                                ScanStateDesc -> (() -> () -> ()
                                -> a1) -> a1
coq_SSMorph_rec sd1 sd2 f =
  coq_SSMorph_rect sd1 sd2 f

coq_SSMorphSt_rect :: ScanStateDesc ->
                                   ScanStateDesc -> (() -> () ->
                                   a1) -> a1
coq_SSMorphSt_rect sd1 sd2 f =
  f __ __

coq_SSMorphSt_rec :: ScanStateDesc ->
                                  ScanStateDesc -> (() -> () ->
                                  a1) -> a1
coq_SSMorphSt_rec sd1 sd2 f =
  coq_SSMorphSt_rect sd1 sd2 f

coq_SSMorphLen_rect :: ScanStateDesc ->
                                    ScanStateDesc -> (() -> () ->
                                    a1) -> a1
coq_SSMorphLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphLen_rec :: ScanStateDesc ->
                                   ScanStateDesc -> (() -> () ->
                                   a1) -> a1
coq_SSMorphLen_rec sd1 sd2 f =
  coq_SSMorphLen_rect sd1 sd2 f

transportation :: ScanStateDesc ->
                               ScanStateDesc ->
                               IntervalId ->
                               IntervalId
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
                                      ScanStateDesc -> (() -> ()
                                      -> a1) -> a1
coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphStLen_rec :: ScanStateDesc ->
                                     ScanStateDesc -> (() -> ()
                                     -> a1) -> a1
coq_SSMorphStLen_rec sd1 sd2 f =
  coq_SSMorphStLen_rect sd1 sd2 f

coq_SSMorphHasLen_rect :: ScanStateDesc ->
                                       ScanStateDesc -> (() -> ()
                                       -> a1) -> a1
coq_SSMorphHasLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphHasLen_rec :: ScanStateDesc ->
                                      ScanStateDesc -> (() -> ()
                                      -> a1) -> a1
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
                                         ScanStateDesc -> (() ->
                                         () -> a1) -> a1
coq_SSMorphStHasLen_rect sd1 sd2 f =
  f __ __

coq_SSMorphStHasLen_rec :: ScanStateDesc ->
                                        ScanStateDesc -> (() ->
                                        () -> a1) -> a1
coq_SSMorphStHasLen_rec sd1 sd2 f =
  coq_SSMorphStHasLen_rect sd1 sd2 f

coq_SSMorphSplit_rect :: ScanStateDesc ->
                                      ScanStateDesc -> (() -> ()
                                      -> a1) -> a1
coq_SSMorphSplit_rect sd1 sd2 f =
  f __ __

coq_SSMorphSplit_rec :: ScanStateDesc ->
                                     ScanStateDesc -> (() -> ()
                                     -> a1) -> a1
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
                                        ScanStateDesc -> (() ->
                                        () -> a1) -> a1
coq_SSMorphStSplit_rect sd1 sd2 f =
  f __ __

coq_SSMorphStSplit_rec :: ScanStateDesc ->
                                       ScanStateDesc -> (() -> ()
                                       -> a1) -> a1
coq_SSMorphStSplit_rec sd1 sd2 f =
  coq_SSMorphStSplit_rect sd1 sd2 f

data SSInfo p =
   Build_SSInfo ScanStateDesc p

coq_SSInfo_rect :: ScanStateDesc ->
                                (ScanStateDesc -> a1 -> () -> a2)
                                -> (SSInfo a1) -> a2
coq_SSInfo_rect startDesc f s =
  case s of {
   Build_SSInfo x x0 -> f x x0 __}

coq_SSInfo_rec :: ScanStateDesc ->
                               (ScanStateDesc -> a1 -> () -> a2)
                               -> (SSInfo a1) -> a2
coq_SSInfo_rec startDesc =
  coq_SSInfo_rect startDesc

thisDesc :: ScanStateDesc -> (SSInfo 
                         a1) -> ScanStateDesc
thisDesc startDesc s =
  case s of {
   Build_SSInfo thisDesc0 thisHolds0 -> thisDesc0}

thisHolds :: ScanStateDesc -> (SSInfo
                          a1) -> a1
thisHolds startDesc s =
  case s of {
   Build_SSInfo thisDesc0 thisHolds0 -> thisHolds0}

data SSError =
   ECurrentIsSingleton
 | ENoIntervalsToSplit
 | EFailedToAllocateRegister
 | ESpillingNotYetImplemented

coq_SSError_rect :: a1 -> a1 -> a1 -> a1 -> SSError
                                 -> a1
coq_SSError_rect f f0 f1 f2 s =
  case s of {
   ECurrentIsSingleton -> f;
   ENoIntervalsToSplit -> f0;
   EFailedToAllocateRegister -> f1;
   ESpillingNotYetImplemented -> f2}

coq_SSError_rec :: a1 -> a1 -> a1 -> a1 -> SSError
                                -> a1
coq_SSError_rec =
  coq_SSError_rect

type SState p q a =
  IState.IState SSError (SSInfo p)
  (SSInfo q) a

withScanState :: ScanStateDesc ->
                              (ScanStateDesc -> () ->
                              SState a2 a3 a1) ->
                              SState a2 a3 a1
withScanState pre f =
  IMonad.ibind (unsafeCoerce IState.coq_IState_IMonad) (\i ->
    f (thisDesc pre i) __) (unsafeCoerce IState.iget)

withScanStatePO :: ScanStateDesc ->
                                (ScanStateDesc -> () ->
                                SState () () a1) ->
                                SState () () a1
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

liftLen :: ScanStateDesc -> (SState 
                        () () a1) -> SState () () a1
liftLen pre x x0 =
  case x0 of {
   Build_SSInfo thisDesc0 _ ->
    let {s = x (Build_SSInfo thisDesc0 __)} in
    case s of {
     Prelude.Left s0 -> Prelude.Left s0;
     Prelude.Right p -> Prelude.Right
      (case p of {
        (,) a0 s0 -> (,) a0 (Build_SSInfo thisDesc0 __)})}}

stbind :: (a4 -> IState.IState SSError a2 a3 
                       a5) -> (IState.IState SSError a1 a2 
                       a4) -> IState.IState SSError a1 a3 
                       a5
stbind f x =
  IMonad.ijoin (unsafeCoerce IState.coq_IState_IMonad)
    (IEndo.imap (unsafeCoerce IState.coq_IState_IFunctor) f (unsafeCoerce x))

return_ :: a2 -> IState.IState SSError a1 a1 a2
return_ =
  IApplicative.ipure (unsafeCoerce IState.coq_IState_IApplicative)

weakenStHasLenToSt :: ScanStateDesc ->
                                   SState () () ()
weakenStHasLenToSt pre hS =
  Prelude.Right ((,) ()
    (case hS of {
      Build_SSInfo thisDesc0 _ -> Build_SSInfo
       thisDesc0 __}))

withCursor :: ScanStateDesc ->
                           (ScanStateDesc -> () ->
                           SState a1 a2 a3) -> SState
                           a1 a2 a3
withCursor pre f x =
  case x of {
   Build_SSInfo thisDesc0 thisHolds0 ->
    f thisDesc0 __ (Build_SSInfo thisDesc0 thisHolds0)}

moveUnhandledToActive :: ScanStateDesc ->
                                      PhysReg ->
                                      SState a1 () ()
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
                                     Specif.Coq_sig2
                                     ScanStateDesc
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
                                     Specif.Coq_sig2
                                     ScanStateDesc
moveInactiveToActive sd x =
  Build_ScanStateDesc (nextInterval sd)
    (intervals sd) (fixedIntervals sd)
    (unhandled sd) ((:) (unsafeCoerce x)
    (active sd))
    (unsafeCoerce
      ((Prelude.const Data.List.delete)
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (nextInterval sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (inactive sd)))) (handled sd)

moveInactiveToHandled :: ScanStateDesc ->
                                      Eqtype.Equality__Coq_sort ->
                                      Specif.Coq_sig2
                                      ScanStateDesc
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

splitCurrentInterval :: ScanStateDesc ->
                                     (Prelude.Maybe Prelude.Int) ->
                                     SState a1 () ()
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
           _evar_0_0 = \_ -> Prelude.Left ECurrentIsSingleton}
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
                                            PhysReg ->
                                            (Prelude.Maybe Prelude.Int) ->
                                            Prelude.Bool ->
                                            SState a1 () 
                                            ()
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
        let {
         _evar_0_ = \_ _ _ -> Prelude.Left ENoIntervalsToSplit}
        in
        let {
         _evar_0_0 = \aid _the_1st_wildcard_ ->
          let {int = LinearScan.Utils.nth ni intervals0 aid} in
          let {
           _evar_0_0 = \_ -> Prelude.Left ECurrentIsSingleton}
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
                                          PhysReg -> Prelude.Int
                                          -> SState a1 () 
                                          ()
splitActiveIntervalForReg pre reg pos =
  splitAssignedIntervalForReg pre reg (Prelude.Just pos)
    Prelude.True

splitAnyInactiveIntervalForReg :: ScanStateDesc ->
                                               PhysReg ->
                                               SState a1 
                                               () ()
splitAnyInactiveIntervalForReg pre reg =
  splitAssignedIntervalForReg pre reg Prelude.Nothing
    Prelude.False

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
                                 Prelude.Bool -> a1) -> VarInfo
                                 -> a1
coq_VarInfo_rect f v =
  case v of {
   Build_VarInfo x x0 x1 -> f x x0 x1}

coq_VarInfo_rec :: (VarId -> VarKind ->
                                Prelude.Bool -> a1) -> VarInfo ->
                                a1
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
 (opType -> Prelude.Maybe ([] MyMachine__PhysReg)) (opType -> []
                                                   VarInfo) 
 (opType -> [] MyMachine__PhysReg)

coq_OpInfo_rect :: ((a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool)
                                -> (a1 -> Prelude.Maybe
                                ([] MyMachine__PhysReg)) -> (a1 -> []
                                VarInfo) -> (a1 -> []
                                MyMachine__PhysReg) -> a2) ->
                                (OpInfo a1) -> a2
coq_OpInfo_rect f o =
  case o of {
   Build_OpInfo x x0 x1 x2 x3 -> f x x0 x1 x2 x3}

coq_OpInfo_rec :: ((a1 -> Prelude.Bool) -> (a1 -> Prelude.Bool)
                               -> (a1 -> Prelude.Maybe
                               ([] MyMachine__PhysReg)) -> (a1 -> []
                               VarInfo) -> (a1 -> []
                               MyMachine__PhysReg) -> a2) ->
                               (OpInfo a1) -> a2
coq_OpInfo_rec =
  coq_OpInfo_rect

isLoopBegin :: (OpInfo a1) -> a1 -> Prelude.Bool
isLoopBegin o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 varRefs0
    regRefs0 -> isLoopBegin0}

isLoopEnd :: (OpInfo a1) -> a1 -> Prelude.Bool
isLoopEnd o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 varRefs0
    regRefs0 -> isLoopEnd0}

isCall :: (OpInfo a1) -> a1 -> Prelude.Maybe
                       ([] MyMachine__PhysReg)
isCall o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 varRefs0
    regRefs0 -> isCall0}

varRefs :: (OpInfo a1) -> a1 -> []
                        VarInfo
varRefs o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 varRefs0
    regRefs0 -> varRefs0}

regRefs :: (OpInfo a1) -> a1 -> []
                        MyMachine__PhysReg
regRefs o =
  case o of {
   Build_OpInfo isLoopBegin0 isLoopEnd0 isCall0 varRefs0
    regRefs0 -> regRefs0}

type OpList opType = [] opType

type SpecialInstr =
  Prelude.Maybe ([] VarId)
  -- singleton inductive, whose constructor was SpillVictims
  
coq_SpecialInstr_rect :: ((Prelude.Maybe ([] VarId))
                                      -> a1) -> SpecialInstr ->
                                      a1
coq_SpecialInstr_rect f s =
  f s

coq_SpecialInstr_rec :: ((Prelude.Maybe ([] VarId))
                                     -> a1) -> SpecialInstr -> a1
coq_SpecialInstr_rec =
  coq_SpecialInstr_rect

data AllocationInfo opType =
   Build_AllocationInfo (Prelude.Either SpecialInstr
                                    opType) (VarId ->
                                            MyMachine__PhysReg)

coq_AllocationInfo_rect :: ((Prelude.Either
                                        SpecialInstr a1) ->
                                        (VarId ->
                                        MyMachine__PhysReg) -> a2) ->
                                        (AllocationInfo a1) -> a2
coq_AllocationInfo_rect f a =
  case a of {
   Build_AllocationInfo x x0 -> f x x0}

coq_AllocationInfo_rec :: ((Prelude.Either
                                       SpecialInstr a1) ->
                                       (VarId ->
                                       MyMachine__PhysReg) -> a2) ->
                                       (AllocationInfo a1) -> a2
coq_AllocationInfo_rec =
  coq_AllocationInfo_rect

operation :: (AllocationInfo a1) -> Prelude.Either
                          SpecialInstr a1
operation a =
  case a of {
   Build_AllocationInfo operation0 allocations0 -> operation0}

allocations :: (AllocationInfo a1) ->
                            VarId -> MyMachine__PhysReg
allocations a =
  case a of {
   Build_AllocationInfo operation0 allocations0 -> allocations0}

type Coq_boundedRange = Specif.Coq_sig2 Range.RangeDesc

type Coq_boundedTriple =
  (,) ((,) (Prelude.Maybe Prelude.Int) (Prelude.Maybe Prelude.Int))
  (Prelude.Maybe Coq_boundedRange)

data Coq_boundedRangeVec =
   Build_boundedRangeVec ([] Coq_boundedTriple) 
 ([] Coq_boundedTriple)

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

transportVecBounds :: Prelude.Int -> Prelude.Int -> Prelude.Int
                                   -> ([] Coq_boundedTriple) ->
                                   [] Coq_boundedTriple
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

applyList :: a1 -> (OpList a1) -> (Prelude.Int ->
                          Coq_boundedRangeVec) -> (a1 ->
                          Prelude.Int -> () ->
                          Coq_boundedRangeVec ->
                          Coq_boundedRangeVec) ->
                          Coq_boundedRangeVec
applyList op ops base f =
  let {
   go i x xs =
     case xs of {
      [] -> f x i __ (base i);
      (:) y ys -> f x i __ (go ((Prelude.succ) ((Prelude.succ) i)) y ys)}}
  in go ((Prelude.succ) 0) op ops

emptyBoundedRangeVec :: Prelude.Int ->
                                     Coq_boundedRangeVec
emptyBoundedRangeVec n =
  Build_boundedRangeVec []
    (Data.List.replicate _MyMachine__maxReg ((,) ((,) Prelude.Nothing
      Prelude.Nothing) Prelude.Nothing))

handleOp :: (OpInfo a1) -> a1 -> Prelude.Int ->
                         Coq_boundedRangeVec ->
                         Coq_boundedRangeVec
handleOp opInfo o pos rest =
  Lib.undefined

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

processOperations :: (OpInfo a1) ->
                                  (OpList a1) -> (,)
                                  ([] (Prelude.Maybe Range.RangeDesc))
                                  ([] (Prelude.Maybe Range.RangeDesc))
processOperations opInfo ops =
  case ops of {
   [] -> (,) [] (Data.List.replicate _MyMachine__maxReg Prelude.Nothing);
   (:) x xs ->
    case applyList x xs emptyBoundedRangeVec
           (\x0 x1 _ -> handleOp opInfo x0 x1) of {
     Build_boundedRangeVec vars' regs' -> (,)
      (Prelude.map extractRange vars')
      (LinearScan.Utils.vmap _MyMachine__maxReg extractRange
        regs')}}

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

assignSpillSlotToCurrent :: ScanStateDesc ->
                                         SState a1 a1 ()
assignSpillSlotToCurrent pre h1 =
  Prelude.Left ESpillingNotYetImplemented

tryAllocateFreeReg :: ScanStateDesc ->
                                   SState a1 a1
                                   (Prelude.Maybe
                                   (SState a1 ()
                                   PhysReg))
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
                          (LinearScan.Utils.nth
                            (nextInterval sd)
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
                          stbind (\x0 ->
                            return_ reg)
                            (moveUnhandledToActive pre reg))
                          (splitCurrentInterval pre
                            (Prelude.Just n))})};
                  Prelude.Nothing -> Prelude.Just success}}
      in
      return_ maction})

allocateBlockedReg :: ScanStateDesc ->
                                   SState a1 ()
                                   (Prelude.Maybe PhysReg)
allocateBlockedReg pre =
  (Prelude.$) (withCursor pre) (\sd _ ->
    let {start = Interval.intervalStart ( (curIntDetails sd))}
    in
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
     nextUsePos' = go
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
    let {nextUsePos = go nextUsePos' intersectingIntervals} in
    case registerWithHighestPos nextUsePos of {
     (,) reg mres ->
      case case mres of {
            Prelude.Just n -> (Prelude.<=) ((Prelude.succ) n) start;
            Prelude.Nothing -> Prelude.False} of {
       Prelude.True ->
        stbind (\x ->
          stbind (\x0 ->
            stbind (\mloc ->
              stbind (\x1 ->
                stbind (\x2 ->
                  return_ Prelude.Nothing)
                  (weakenStHasLenToSt pre))
                (case mloc of {
                  Prelude.Just n ->
                   splitCurrentInterval pre (Prelude.Just n);
                  Prelude.Nothing -> return_ ()}))
              (intersectsWithFixedInterval pre reg))
            (splitCurrentInterval pre
              (Interval.firstUseReqReg ( (curIntDetails sd)))))
          (assignSpillSlotToCurrent pre);
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
                  Prelude.Nothing ->
                   moveUnhandledToActive pre reg}))
              (intersectsWithFixedInterval pre reg))
            (splitAnyInactiveIntervalForReg pre reg))
          (splitActiveIntervalForReg pre reg pos)}})

checkActiveIntervals :: ScanStateDesc -> Prelude.Int
                                     -> SState () () ()
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

checkInactiveIntervals :: ScanStateDesc ->
                                       Prelude.Int -> SState 
                                       () () ()
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
                      moveInactiveToHandled sd
                        ( (unsafeCoerce x));
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

handleInterval :: ScanStateDesc ->
                               SState () ()
                               (Prelude.Maybe PhysReg)
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

linearScan_func :: ((,) ()
                                ((,) ([] ())
                                ((,) ScanStateDesc ()))) ->
                                Prelude.Either SSError
                                ([] (AllocationInfo ()))
linearScan_func x =
  let {ops = Prelude.fst (Specif.projT2 x)} in
  let {sd = Prelude.fst (Specif.projT2 (Specif.projT2 x))} in
  let {
   linearScan0 = \ops0 sd0 ->
    let {y = (,) __ ((,) ops0 ((,) sd0 __))} in
    linearScan_func ( y)}
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
       (,) mreg ssinfo' ->
        case mreg of {
         Prelude.Just wildcard' ->
          let {
           filtered_var1 = linearScan0 ops (thisDesc sd ssinfo')}
          in
          case filtered_var1 of {
           Prelude.Left err -> Prelude.Left err;
           Prelude.Right xs -> Prelude.Right xs};
         Prelude.Nothing -> Prelude.Left
          EFailedToAllocateRegister}}};
   Prelude.Nothing -> Prelude.Right Lib.undefined}

linearScan :: ([] a1) -> ScanStateDesc ->
                           Prelude.Either SSError
                           ([] (AllocationInfo a1))
linearScan ops sd =
  unsafeCoerce
    (linearScan_func ((,) __ ((,) (unsafeCoerce ops) ((,) sd
      __))))

_Blocks__computeBlockOrder :: ([] a1) -> [] a1
_Blocks__computeBlockOrder blocks =
  blocks

determineIntervals :: (OpInfo a1) -> (OpList 
                      a1) -> ScanStateDesc
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
      packScanState (Build_ScanStateDesc
        ((Prelude.succ) (nextInterval sd))
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
   (,) varRanges regRanges ->
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
    Data.List.foldl' handleVar s2 varRanges}

allocateRegisters :: (a1 -> [] a2) -> (OpInfo a2) -> ([] 
                     a1) -> Prelude.Either SSError
                     ([] (AllocationInfo a2))
allocateRegisters blockToOpList opInfo blocks =
  let {
   ops = Seq.flatten
           (Prelude.map blockToOpList (_Blocks__computeBlockOrder blocks))}
  in
  Lib.uncurry_sig (\x _ -> linearScan ops x)
    (determineIntervals opInfo ops)

