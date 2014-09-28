module Data.Data.LinearScan where

import qualified Prelude
import qualified Data.Data.Compare as Compare as Data.Compare as Compare
import qualified Data.Data.Compare_dec as Compare_dec as Data.Compare_dec as Compare_dec
import qualified Data.Data.Datatypes as Datatypes as Data.Datatypes as Datatypes
import qualified Data.Data.EqNat as EqNat as Data.EqNat as EqNat
import qualified Data.Data.Fin0 as Fin0 as Data.Fin0 as Fin0
import qualified Data.Data.Fin as Fin as Data.Fin as Fin
import qualified Data.Data.Interval as Interval as Data.Interval as Interval
import qualified Data.Data.Lib as Lib as Data.Lib as Lib
import qualified Data.Data.List as List as Data.List as List
import qualified Data.Data.Logic as Logic as Data.Logic as Logic
import qualified Data.Data.NPeano as NPeano as Data.NPeano as NPeano
import qualified Data.Data.Peano as Peano as Data.Peano as Peano
import qualified Data.Data.Specif as Specif as Data.Specif as Specif


__ :: any
__ = Prelude.error "Logical or arity value used"

_MyMachine__maxReg :: Datatypes.Coq_nat
_MyMachine__maxReg =
  Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
    (Datatypes.S (Datatypes.S Datatypes.O)))))))))))))))))))))))))))))))

type Allocator__PhysReg = Fin0.Coq_fin

_Allocator__maxReg :: Datatypes.Coq_nat
_Allocator__maxReg =
  _MyMachine__maxReg

data Allocator__ScanStateDesc =
   Allocator__Build_ScanStateDesc Datatypes.Coq_nat (Datatypes.Coq_list
                                                    Fin0.Coq_fin) (Datatypes.Coq_list
                                                                  Fin0.Coq_fin) 
 (Datatypes.Coq_list Fin0.Coq_fin) (Datatypes.Coq_list Fin0.Coq_fin) 
 (Fin0.Coq_fin -> Specif.Coq_sigT Interval.IntervalDesc Interval.Interval) 
 (Fin0.Coq_fin -> Datatypes.Coq_option Allocator__PhysReg) (Allocator__PhysReg
                                                           ->
                                                           Datatypes.Coq_option
                                                           (Specif.Coq_sigT
                                                           Interval.IntervalDesc
                                                           Interval.FixedInterval))

_Allocator__coq_ScanStateDesc_rect :: (Datatypes.Coq_nat ->
                                      (Datatypes.Coq_list Fin0.Coq_fin) ->
                                      (Datatypes.Coq_list Fin0.Coq_fin) ->
                                      (Datatypes.Coq_list Fin0.Coq_fin) ->
                                      (Datatypes.Coq_list Fin0.Coq_fin) ->
                                      (Fin0.Coq_fin -> Specif.Coq_sigT
                                      Interval.IntervalDesc
                                      Interval.Interval) -> (Fin0.Coq_fin ->
                                      Datatypes.Coq_option
                                      Allocator__PhysReg) ->
                                      (Allocator__PhysReg ->
                                      Datatypes.Coq_option
                                      (Specif.Coq_sigT Interval.IntervalDesc
                                      Interval.FixedInterval)) -> () -> a1)
                                      -> Allocator__ScanStateDesc -> a1
_Allocator__coq_ScanStateDesc_rect f s =
  case s of {
   Allocator__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6 __}

_Allocator__coq_ScanStateDesc_rec :: (Datatypes.Coq_nat ->
                                     (Datatypes.Coq_list Fin0.Coq_fin) ->
                                     (Datatypes.Coq_list Fin0.Coq_fin) ->
                                     (Datatypes.Coq_list Fin0.Coq_fin) ->
                                     (Datatypes.Coq_list Fin0.Coq_fin) ->
                                     (Fin0.Coq_fin -> Specif.Coq_sigT
                                     Interval.IntervalDesc Interval.Interval)
                                     -> (Fin0.Coq_fin -> Datatypes.Coq_option
                                     Allocator__PhysReg) ->
                                     (Allocator__PhysReg ->
                                     Datatypes.Coq_option
                                     (Specif.Coq_sigT Interval.IntervalDesc
                                     Interval.FixedInterval)) -> () -> a1) ->
                                     Allocator__ScanStateDesc -> a1
_Allocator__coq_ScanStateDesc_rec =
  _Allocator__coq_ScanStateDesc_rect

_Allocator__nextInterval :: Allocator__ScanStateDesc -> Datatypes.Coq_nat
_Allocator__nextInterval s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> nextInterval0}

type Allocator__IntervalId = Fin0.Coq_fin

_Allocator__unhandled :: Allocator__ScanStateDesc -> Datatypes.Coq_list
                         Allocator__IntervalId
_Allocator__unhandled s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> unhandled0}

_Allocator__active :: Allocator__ScanStateDesc -> Datatypes.Coq_list
                      Allocator__IntervalId
_Allocator__active s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> active0}

_Allocator__inactive :: Allocator__ScanStateDesc -> Datatypes.Coq_list
                        Allocator__IntervalId
_Allocator__inactive s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> inactive0}

_Allocator__handled :: Allocator__ScanStateDesc -> Datatypes.Coq_list
                       Allocator__IntervalId
_Allocator__handled s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> handled0}

_Allocator__getInterval :: Allocator__ScanStateDesc -> Allocator__IntervalId
                           -> Specif.Coq_sigT Interval.IntervalDesc
                           Interval.Interval
_Allocator__getInterval s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getInterval0}

_Allocator__assignments :: Allocator__ScanStateDesc -> Allocator__IntervalId
                           -> Datatypes.Coq_option Allocator__PhysReg
_Allocator__assignments s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> assignments0}

_Allocator__getFixedInterval :: Allocator__ScanStateDesc ->
                                Allocator__PhysReg -> Datatypes.Coq_option
                                (Specif.Coq_sigT Interval.IntervalDesc
                                Interval.FixedInterval)
_Allocator__getFixedInterval s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getFixedInterval0}

_Allocator__all_state_lists :: Allocator__ScanStateDesc -> Datatypes.Coq_list
                               Allocator__IntervalId
_Allocator__all_state_lists s =
  Datatypes.app (_Allocator__unhandled s)
    (Datatypes.app (_Allocator__active s)
      (Datatypes.app (_Allocator__inactive s) (_Allocator__handled s)))

_Allocator__lt_sub :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                      Datatypes.Coq_nat
_Allocator__lt_sub n m =
  Peano.minus m n

_Allocator__transportId :: Allocator__ScanStateDesc ->
                           Allocator__ScanStateDesc -> Allocator__IntervalId
                           -> Allocator__IntervalId
_Allocator__transportId st st' x =
  let {
   h = Compare_dec.le_lt_eq_dec (_Allocator__nextInterval st)
         (_Allocator__nextInterval st')}
  in
  case h of {
   Specif.Coq_left ->
    case st of {
     Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0
      inactive0 handled0 getInterval0 assignments0 getFixedInterval0 ->
      case st' of {
       Allocator__Build_ScanStateDesc nextInterval1 unhandled1 active1
        inactive1 handled1 getInterval1 assignments1 getFixedInterval1 ->
        let {h0 = _Allocator__lt_sub nextInterval0 nextInterval1} in
        Logic.eq_rec (Peano.plus h0 nextInterval0)
          (Fin.coq_R nextInterval0 h0 x) nextInterval1}};
   Specif.Coq_right ->
    Logic.eq_rec (_Allocator__nextInterval st) x
      (_Allocator__nextInterval st')}

data Allocator__ScanState =
   Allocator__ScanState_nil
 | Allocator__ScanState_newUnhandled Datatypes.Coq_nat (Datatypes.Coq_list
                                                       Fin0.Coq_fin) 
 (Datatypes.Coq_list Fin0.Coq_fin) (Datatypes.Coq_list Fin0.Coq_fin) 
 (Datatypes.Coq_list Fin0.Coq_fin) (Fin0.Coq_fin -> Specif.Coq_sigT
                                   Interval.IntervalDesc Interval.Interval) 
 (Fin0.Coq_fin -> Datatypes.Coq_option Allocator__PhysReg) (Allocator__PhysReg
                                                           ->
                                                           Datatypes.Coq_option
                                                           (Specif.Coq_sigT
                                                           Interval.IntervalDesc
                                                           Interval.FixedInterval)) 
 Interval.IntervalDesc Interval.Interval Allocator__ScanState Fin0.Coq_fin
 | Allocator__ScanState_moveUnhandledToActive Datatypes.Coq_nat (Datatypes.Coq_list
                                                                Fin0.Coq_fin) 
 (Datatypes.Coq_list Fin0.Coq_fin) (Datatypes.Coq_list Fin0.Coq_fin) 
 (Datatypes.Coq_list Fin0.Coq_fin) (Fin0.Coq_fin -> Specif.Coq_sigT
                                   Interval.IntervalDesc Interval.Interval) 
 (Fin0.Coq_fin -> Datatypes.Coq_option Allocator__PhysReg) (Allocator__PhysReg
                                                           ->
                                                           Datatypes.Coq_option
                                                           (Specif.Coq_sigT
                                                           Interval.IntervalDesc
                                                           Interval.FixedInterval)) 
 Fin0.Coq_fin Allocator__PhysReg Allocator__ScanState
 | Allocator__ScanState_moveActiveToInactive Allocator__ScanStateDesc 
 Allocator__IntervalId Allocator__ScanState
 | Allocator__ScanState_moveActiveToHandled Allocator__ScanStateDesc 
 Allocator__IntervalId Allocator__ScanState
 | Allocator__ScanState_moveInactiveToActive Allocator__ScanStateDesc 
 Allocator__IntervalId Allocator__ScanState
 | Allocator__ScanState_moveInactiveToHandled Allocator__ScanStateDesc 
 Allocator__IntervalId Allocator__ScanState

_Allocator__coq_ScanState_rect :: a1 -> (Datatypes.Coq_nat ->
                                  (Datatypes.Coq_list Fin0.Coq_fin) ->
                                  (Datatypes.Coq_list Fin0.Coq_fin) ->
                                  (Datatypes.Coq_list Fin0.Coq_fin) ->
                                  (Datatypes.Coq_list Fin0.Coq_fin) ->
                                  (Fin0.Coq_fin -> Specif.Coq_sigT
                                  Interval.IntervalDesc Interval.Interval) ->
                                  (Fin0.Coq_fin -> Datatypes.Coq_option
                                  Allocator__PhysReg) -> (Allocator__PhysReg
                                  -> Datatypes.Coq_option
                                  (Specif.Coq_sigT Interval.IntervalDesc
                                  Interval.FixedInterval)) -> () ->
                                  Interval.IntervalDesc -> Interval.Interval
                                  -> Allocator__ScanState -> a1 ->
                                  Fin0.Coq_fin -> () -> a1) ->
                                  (Datatypes.Coq_nat -> (Datatypes.Coq_list
                                  Fin0.Coq_fin) -> (Datatypes.Coq_list
                                  Fin0.Coq_fin) -> (Datatypes.Coq_list
                                  Fin0.Coq_fin) -> (Datatypes.Coq_list
                                  Fin0.Coq_fin) -> (Fin0.Coq_fin ->
                                  Specif.Coq_sigT Interval.IntervalDesc
                                  Interval.Interval) -> (Fin0.Coq_fin ->
                                  Datatypes.Coq_option Allocator__PhysReg) ->
                                  (Allocator__PhysReg -> Datatypes.Coq_option
                                  (Specif.Coq_sigT Interval.IntervalDesc
                                  Interval.FixedInterval)) -> Fin0.Coq_fin ->
                                  Allocator__PhysReg -> () ->
                                  Allocator__ScanState -> a1 -> a1) ->
                                  (Allocator__ScanStateDesc ->
                                  Allocator__IntervalId ->
                                  Allocator__ScanState -> a1 -> () -> a1) ->
                                  (Allocator__ScanStateDesc ->
                                  Allocator__IntervalId ->
                                  Allocator__ScanState -> a1 -> () -> a1) ->
                                  (Allocator__ScanStateDesc ->
                                  Allocator__IntervalId ->
                                  Allocator__ScanState -> a1 -> () -> a1) ->
                                  (Allocator__ScanStateDesc ->
                                  Allocator__IntervalId ->
                                  Allocator__ScanState -> a1 -> () -> a1) ->
                                  Allocator__ScanStateDesc ->
                                  Allocator__ScanState -> a1
_Allocator__coq_ScanState_rect f f0 f1 f2 f3 f4 f5 s s0 =
  case s0 of {
   Allocator__ScanState_nil -> f;
   Allocator__ScanState_newUnhandled ni unh act inact hnd geti assgn getfixi
    d i s1 newi ->
    f0 ni unh act inact hnd geti assgn getfixi __ d i s1
      (_Allocator__coq_ScanState_rect f f0 f1 f2 f3 f4 f5
        (Allocator__Build_ScanStateDesc ni unh act inact hnd geti assgn
        getfixi) s1) newi __;
   Allocator__ScanState_moveUnhandledToActive ni unh act inact hnd geti assgn
    getfixi x reg s1 ->
    f1 ni unh act inact hnd geti assgn getfixi x reg __ s1
      (_Allocator__coq_ScanState_rect f f0 f1 f2 f3 f4 f5
        (Allocator__Build_ScanStateDesc ni (Datatypes.Coq_cons x unh) act
        inact hnd geti assgn getfixi) s1);
   Allocator__ScanState_moveActiveToInactive sd x s1 ->
    f2 sd x s1 (_Allocator__coq_ScanState_rect f f0 f1 f2 f3 f4 f5 sd s1) __;
   Allocator__ScanState_moveActiveToHandled sd x s1 ->
    f3 sd x s1 (_Allocator__coq_ScanState_rect f f0 f1 f2 f3 f4 f5 sd s1) __;
   Allocator__ScanState_moveInactiveToActive sd x s1 ->
    f4 sd x s1 (_Allocator__coq_ScanState_rect f f0 f1 f2 f3 f4 f5 sd s1) __;
   Allocator__ScanState_moveInactiveToHandled sd x s1 ->
    f5 sd x s1 (_Allocator__coq_ScanState_rect f f0 f1 f2 f3 f4 f5 sd s1) __}

_Allocator__coq_ScanState_rec :: a1 -> (Datatypes.Coq_nat ->
                                 (Datatypes.Coq_list Fin0.Coq_fin) ->
                                 (Datatypes.Coq_list Fin0.Coq_fin) ->
                                 (Datatypes.Coq_list Fin0.Coq_fin) ->
                                 (Datatypes.Coq_list Fin0.Coq_fin) ->
                                 (Fin0.Coq_fin -> Specif.Coq_sigT
                                 Interval.IntervalDesc Interval.Interval) ->
                                 (Fin0.Coq_fin -> Datatypes.Coq_option
                                 Allocator__PhysReg) -> (Allocator__PhysReg
                                 -> Datatypes.Coq_option
                                 (Specif.Coq_sigT Interval.IntervalDesc
                                 Interval.FixedInterval)) -> () ->
                                 Interval.IntervalDesc -> Interval.Interval
                                 -> Allocator__ScanState -> a1 ->
                                 Fin0.Coq_fin -> () -> a1) ->
                                 (Datatypes.Coq_nat -> (Datatypes.Coq_list
                                 Fin0.Coq_fin) -> (Datatypes.Coq_list
                                 Fin0.Coq_fin) -> (Datatypes.Coq_list
                                 Fin0.Coq_fin) -> (Datatypes.Coq_list
                                 Fin0.Coq_fin) -> (Fin0.Coq_fin ->
                                 Specif.Coq_sigT Interval.IntervalDesc
                                 Interval.Interval) -> (Fin0.Coq_fin ->
                                 Datatypes.Coq_option Allocator__PhysReg) ->
                                 (Allocator__PhysReg -> Datatypes.Coq_option
                                 (Specif.Coq_sigT Interval.IntervalDesc
                                 Interval.FixedInterval)) -> Fin0.Coq_fin ->
                                 Allocator__PhysReg -> () ->
                                 Allocator__ScanState -> a1 -> a1) ->
                                 (Allocator__ScanStateDesc ->
                                 Allocator__IntervalId ->
                                 Allocator__ScanState -> a1 -> () -> a1) ->
                                 (Allocator__ScanStateDesc ->
                                 Allocator__IntervalId ->
                                 Allocator__ScanState -> a1 -> () -> a1) ->
                                 (Allocator__ScanStateDesc ->
                                 Allocator__IntervalId ->
                                 Allocator__ScanState -> a1 -> () -> a1) ->
                                 (Allocator__ScanStateDesc ->
                                 Allocator__IntervalId ->
                                 Allocator__ScanState -> a1 -> () -> a1) ->
                                 Allocator__ScanStateDesc ->
                                 Allocator__ScanState -> a1
_Allocator__coq_ScanState_rec =
  _Allocator__coq_ScanState_rect

_Allocator__unhandledExtent :: Allocator__ScanStateDesc -> Datatypes.Coq_nat
_Allocator__unhandledExtent sd =
  case _Allocator__unhandled sd of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons i l ->
    case l of {
     Datatypes.Coq_nil ->
      Interval.intervalExtent (Specif.projT1 (_Allocator__getInterval sd i))
        (Specif.projT2 (_Allocator__getInterval sd i));
     Datatypes.Coq_cons i0 l0 ->
      let {
       f = \n x ->
        Peano.plus n
          (Interval.intervalExtent
            (Specif.projT1 (_Allocator__getInterval sd x))
            (Specif.projT2 (_Allocator__getInterval sd x)))}
      in
      List.fold_left f (Datatypes.Coq_cons i (Datatypes.Coq_cons i0 l0))
        Datatypes.O}}

data Allocator__ScanStateCursor =
   Allocator__Build_ScanStateCursor Allocator__ScanState Interval.IntervalDesc

_Allocator__coq_ScanStateCursor_rect :: Allocator__ScanStateDesc ->
                                        (Allocator__ScanState -> () ->
                                        Interval.IntervalDesc -> a1) ->
                                        Allocator__ScanStateCursor -> a1
_Allocator__coq_ScanStateCursor_rect sd f s =
  case s of {
   Allocator__Build_ScanStateCursor x x0 -> f x __ x0}

_Allocator__coq_ScanStateCursor_rec :: Allocator__ScanStateDesc ->
                                       (Allocator__ScanState -> () ->
                                       Interval.IntervalDesc -> a1) ->
                                       Allocator__ScanStateCursor -> a1
_Allocator__coq_ScanStateCursor_rec sd =
  _Allocator__coq_ScanStateCursor_rect sd

_Allocator__curState :: Allocator__ScanStateDesc ->
                        Allocator__ScanStateCursor -> Allocator__ScanState
_Allocator__curState sd s =
  case s of {
   Allocator__Build_ScanStateCursor curState0 x -> curState0}

_Allocator__curId :: Allocator__ScanStateDesc -> Allocator__ScanStateCursor
                     -> Allocator__IntervalId
_Allocator__curId sd s =
  Lib.safe_hd (_Allocator__unhandled sd)

_Allocator__curIntDesc :: Allocator__ScanStateDesc ->
                          Allocator__ScanStateCursor -> Interval.IntervalDesc
_Allocator__curIntDesc sd s =
  case s of {
   Allocator__Build_ScanStateCursor curState0 x -> x}

_Allocator__curInterval :: Allocator__ScanStateDesc ->
                           Allocator__ScanStateCursor -> Interval.Interval
_Allocator__curInterval sd s =
  Specif.projT2 (_Allocator__getInterval sd (_Allocator__curId sd s))

_Allocator__curPosition :: Allocator__ScanStateDesc ->
                           Allocator__ScanStateCursor -> Datatypes.Coq_nat
_Allocator__curPosition sd s =
  Interval.intervalStart
    (Specif.projT1 (_Allocator__getInterval sd (_Allocator__curId sd s)))
    (_Allocator__curInterval sd s)

data Allocator__NextScanState =
   Allocator__Build_NextScanState Allocator__ScanStateDesc Allocator__ScanState

_Allocator__coq_NextScanState_rect :: (Allocator__ScanStateDesc ->
                                      Allocator__ScanState -> () -> a1) ->
                                      Allocator__NextScanState -> a1
_Allocator__coq_NextScanState_rect f n =
  case n of {
   Allocator__Build_NextScanState x x0 -> f x x0 __}

_Allocator__coq_NextScanState_rec :: (Allocator__ScanStateDesc ->
                                     Allocator__ScanState -> () -> a1) ->
                                     Allocator__NextScanState -> a1
_Allocator__coq_NextScanState_rec =
  _Allocator__coq_NextScanState_rect

_Allocator__nextDesc :: Allocator__NextScanState -> Allocator__ScanStateDesc
_Allocator__nextDesc n =
  case n of {
   Allocator__Build_NextScanState nextDesc0 nextState0 -> nextDesc0}

_Allocator__nextState :: Allocator__NextScanState -> Allocator__ScanState
_Allocator__nextState n =
  case n of {
   Allocator__Build_NextScanState nextDesc0 nextState0 -> nextState0}

type Allocator__NextState = Allocator__NextScanState

type Allocator__NextStateDep q = Specif.Coq_sigT Allocator__NextScanState q

type Allocator__NextStateWith a =
  Datatypes.Coq_prod a Allocator__NextScanState

_Allocator__coq_NextScanState_transitivity :: Allocator__ScanStateDesc ->
                                              Allocator__NextScanState ->
                                              Allocator__NextScanState ->
                                              Allocator__NextScanState
_Allocator__coq_NextScanState_transitivity sd0 n o =
  o

_Allocator__coq_SSMorph_rect :: Allocator__ScanStateDesc ->
                                Allocator__ScanStateDesc -> (() -> () -> ()
                                -> a1) -> a1
_Allocator__coq_SSMorph_rect sd1 sd2 f =
  f __ __ __

_Allocator__coq_SSMorph_rec :: Allocator__ScanStateDesc ->
                               Allocator__ScanStateDesc -> (() -> () -> () ->
                               a1) -> a1
_Allocator__coq_SSMorph_rec sd1 sd2 f =
  _Allocator__coq_SSMorph_rect sd1 sd2 f

_Allocator__coq_SSMorphLen_rect :: Allocator__ScanStateDesc ->
                                   Allocator__ScanStateDesc -> (() -> () ->
                                   a1) -> a1
_Allocator__coq_SSMorphLen_rect sd1 sd2 f =
  f __ __

_Allocator__coq_SSMorphLen_rec :: Allocator__ScanStateDesc ->
                                  Allocator__ScanStateDesc -> (() -> () ->
                                  a1) -> a1
_Allocator__coq_SSMorphLen_rec sd1 sd2 f =
  _Allocator__coq_SSMorphLen_rect sd1 sd2 f

_Allocator__coq_SSMorphSt_rect :: Allocator__ScanStateDesc ->
                                  Allocator__ScanStateDesc -> (() -> () ->
                                  a1) -> a1
_Allocator__coq_SSMorphSt_rect sd1 sd2 f =
  f __ __

_Allocator__coq_SSMorphSt_rec :: Allocator__ScanStateDesc ->
                                 Allocator__ScanStateDesc -> (() -> () -> a1)
                                 -> a1
_Allocator__coq_SSMorphSt_rec sd1 sd2 f =
  _Allocator__coq_SSMorphSt_rect sd1 sd2 f

_Allocator__coq_SSMorphStLen_rect :: Allocator__ScanStateDesc ->
                                     Allocator__ScanStateDesc -> (() -> () ->
                                     a1) -> a1
_Allocator__coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __

_Allocator__coq_SSMorphStLen_rec :: Allocator__ScanStateDesc ->
                                    Allocator__ScanStateDesc -> (() -> () ->
                                    a1) -> a1
_Allocator__coq_SSMorphStLen_rec sd1 sd2 f =
  _Allocator__coq_SSMorphStLen_rect sd1 sd2 f

_Allocator__moveActiveToHandled :: Allocator__ScanStateDesc ->
                                   Allocator__ScanState ->
                                   Allocator__IntervalId ->
                                   Allocator__NextScanState
_Allocator__moveActiveToHandled sd st x =
  let {s = Allocator__ScanState_moveActiveToInactive sd x st} in
  Allocator__Build_NextScanState (Allocator__Build_ScanStateDesc
  (_Allocator__nextInterval sd) (_Allocator__unhandled sd)
  (List.remove
    (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Allocator__nextInterval sd)))
    x (_Allocator__active sd)) (Datatypes.Coq_cons x
  (_Allocator__inactive sd)) (_Allocator__handled sd)
  (_Allocator__getInterval sd) (_Allocator__assignments sd)
  (_Allocator__getFixedInterval sd)) s

_Allocator__moveActiveToInactive :: Allocator__ScanStateDesc ->
                                    Allocator__ScanState ->
                                    Allocator__IntervalId ->
                                    Allocator__NextScanState
_Allocator__moveActiveToInactive sd st x =
  let {s = Allocator__ScanState_moveActiveToInactive sd x st} in
  Allocator__Build_NextScanState (Allocator__Build_ScanStateDesc
  (_Allocator__nextInterval sd) (_Allocator__unhandled sd)
  (List.remove
    (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Allocator__nextInterval sd)))
    x (_Allocator__active sd)) (Datatypes.Coq_cons x
  (_Allocator__inactive sd)) (_Allocator__handled sd)
  (_Allocator__getInterval sd) (_Allocator__assignments sd)
  (_Allocator__getFixedInterval sd)) s

_Allocator__moveInactiveToActive :: Allocator__ScanStateDesc ->
                                    Allocator__ScanState ->
                                    Allocator__IntervalId ->
                                    Allocator__NextScanState
_Allocator__moveInactiveToActive sd st x =
  let {s = Allocator__ScanState_moveInactiveToActive sd x st} in
  Allocator__Build_NextScanState (Allocator__Build_ScanStateDesc
  (_Allocator__nextInterval sd) (_Allocator__unhandled sd)
  (Datatypes.Coq_cons x (_Allocator__active sd))
  (List.remove
    (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Allocator__nextInterval sd)))
    x (_Allocator__inactive sd)) (_Allocator__handled sd)
  (_Allocator__getInterval sd) (_Allocator__assignments sd)
  (_Allocator__getFixedInterval sd)) s

_Allocator__moveInactiveToHandled :: Allocator__ScanStateDesc ->
                                     Allocator__ScanState ->
                                     Allocator__IntervalId ->
                                     Allocator__NextScanState
_Allocator__moveInactiveToHandled sd st x =
  let {s = Allocator__ScanState_moveInactiveToHandled sd x st} in
  Allocator__Build_NextScanState (Allocator__Build_ScanStateDesc
  (_Allocator__nextInterval sd) (_Allocator__unhandled sd)
  (_Allocator__active sd)
  (List.remove
    (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Allocator__nextInterval sd)))
    x (_Allocator__inactive sd)) (Datatypes.Coq_cons x
  (_Allocator__handled sd)) (_Allocator__getInterval sd)
  (_Allocator__assignments sd) (_Allocator__getFixedInterval sd)) s

_Allocator__moveUnhandledToActive :: Allocator__ScanStateDesc ->
                                     Allocator__ScanStateCursor ->
                                     Allocator__PhysReg ->
                                     Allocator__NextState
_Allocator__moveUnhandledToActive sd cur reg =
  case cur of {
   Allocator__Build_ScanStateCursor curState0 x ->
    case sd of {
     Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0
      inactive0 handled0 getInterval0 assignments0 getFixedInterval0 ->
      case unhandled0 of {
       Datatypes.Coq_nil -> Logic.coq_False_rec;
       Datatypes.Coq_cons i unhandled1 ->
        let {
         s = \x0 -> Allocator__ScanState_moveUnhandledToActive nextInterval0
          unhandled1 active0 inactive0 handled0 getInterval0 assignments0
          getFixedInterval0 i reg x0}
        in
        Allocator__Build_NextScanState (Allocator__Build_ScanStateDesc
        nextInterval0 unhandled1 (Datatypes.Coq_cons i active0) inactive0
        handled0 getInterval0 (\i0 ->
        case Compare.cmp_eq_dec (Fin0.fin_CompareSpec nextInterval0) i0 i of {
         Specif.Coq_left -> Datatypes.Some reg;
         Specif.Coq_right -> assignments0 i0}) getFixedInterval0)
        (s curState0)}}}

_Allocator__nextIntersectionWith :: Interval.IntervalDesc ->
                                    Interval.Interval ->
                                    Allocator__ScanStateDesc ->
                                    Allocator__IntervalId ->
                                    Datatypes.Coq_option Datatypes.Coq_nat
_Allocator__nextIntersectionWith d i sd jid =
  Interval.firstIntersectionPoint
    (Specif.projT1 (_Allocator__getInterval sd jid))
    (Specif.projT2 (_Allocator__getInterval sd jid)) d i

_Allocator__getRegisterIndex :: Allocator__ScanStateDesc ->
                                Allocator__ScanState ->
                                (Allocator__IntervalId ->
                                Datatypes.Coq_option Datatypes.Coq_nat) ->
                                (Allocator__PhysReg -> Datatypes.Coq_option
                                Datatypes.Coq_nat) -> (Datatypes.Coq_list
                                Allocator__IntervalId) -> Allocator__PhysReg
                                -> Datatypes.Coq_option Datatypes.Coq_nat
_Allocator__getRegisterIndex sd st intervalIndex registerIndex intervals =
  List.fold_right (\x f r ->
    case _Allocator__assignments sd x of {
     Datatypes.Some a ->
      case Compare.cmp_eq_dec (Fin0.fin_CompareSpec _MyMachine__maxReg) a r of {
       Specif.Coq_left -> intervalIndex x;
       Specif.Coq_right -> f r};
     Datatypes.None -> f r}) registerIndex intervals

_Allocator__findRegister_F :: ((Allocator__PhysReg -> Datatypes.Coq_option
                              Datatypes.Coq_nat) -> Allocator__PhysReg ->
                              Datatypes.Coq_prod Allocator__PhysReg
                              (Datatypes.Coq_option Datatypes.Coq_nat)) ->
                              (Allocator__PhysReg -> Datatypes.Coq_option
                              Datatypes.Coq_nat) -> Allocator__PhysReg ->
                              Datatypes.Coq_prod Allocator__PhysReg
                              (Datatypes.Coq_option Datatypes.Coq_nat)
_Allocator__findRegister_F findRegister0 registerIndex start =
  case registerIndex start of {
   Datatypes.Some pos ->
    case Fin0.pred_fin _MyMachine__maxReg start of {
     Datatypes.Some nreg ->
      case findRegister0 registerIndex nreg of {
       Datatypes.Coq_pair reg o ->
        case o of {
         Datatypes.Some pos' ->
          case NPeano.ltb pos pos' of {
           Datatypes.Coq_true -> Datatypes.Coq_pair reg (Datatypes.Some pos');
           Datatypes.Coq_false -> Datatypes.Coq_pair reg (Datatypes.Some pos)};
         Datatypes.None -> Datatypes.Coq_pair reg Datatypes.None}};
     Datatypes.None -> Datatypes.Coq_pair start (Datatypes.Some pos)};
   Datatypes.None -> Datatypes.Coq_pair start Datatypes.None}

_Allocator__findRegister_terminate :: (Allocator__PhysReg ->
                                      Datatypes.Coq_option Datatypes.Coq_nat)
                                      -> Allocator__PhysReg ->
                                      (Datatypes.Coq_prod Allocator__PhysReg
                                      (Datatypes.Coq_option
                                      Datatypes.Coq_nat))
_Allocator__findRegister_terminate registerIndex start =
  case registerIndex start of {
   Datatypes.Some pos ->
    case Fin0.pred_fin _MyMachine__maxReg start of {
     Datatypes.Some nreg ->
      Specif.sig_rec (\rec_res _ ->
        case rec_res of {
         Datatypes.Coq_pair reg o ->
          case o of {
           Datatypes.Some pos' ->
            case NPeano.ltb pos pos' of {
             Datatypes.Coq_true -> Datatypes.Coq_pair reg (Datatypes.Some
              pos');
             Datatypes.Coq_false -> Datatypes.Coq_pair reg (Datatypes.Some
              pos)};
           Datatypes.None -> Datatypes.Coq_pair reg Datatypes.None}})
        (_Allocator__findRegister_terminate registerIndex nreg);
     Datatypes.None -> Datatypes.Coq_pair start (Datatypes.Some pos)};
   Datatypes.None -> Datatypes.Coq_pair start Datatypes.None}

_Allocator__findRegister :: (Allocator__PhysReg -> Datatypes.Coq_option
                            Datatypes.Coq_nat) -> Allocator__PhysReg ->
                            Datatypes.Coq_prod Allocator__PhysReg
                            (Datatypes.Coq_option Datatypes.Coq_nat)
_Allocator__findRegister registerIndex start =
  case registerIndex start of {
   Datatypes.Some pos ->
    case Fin0.pred_fin _MyMachine__maxReg start of {
     Datatypes.Some nreg ->
      Specif.sig_rec (\rec_res _ ->
        case rec_res of {
         Datatypes.Coq_pair reg o ->
          case o of {
           Datatypes.Some pos' ->
            case NPeano.ltb pos pos' of {
             Datatypes.Coq_true -> Datatypes.Coq_pair reg (Datatypes.Some
              pos');
             Datatypes.Coq_false -> Datatypes.Coq_pair reg (Datatypes.Some
              pos)};
           Datatypes.None -> Datatypes.Coq_pair reg Datatypes.None}})
        (_Allocator__findRegister registerIndex nreg);
     Datatypes.None -> Datatypes.Coq_pair start (Datatypes.Some pos)};
   Datatypes.None -> Datatypes.Coq_pair start Datatypes.None}

data Allocator__R_findRegister =
   Allocator__R_findRegister_0 Allocator__PhysReg
 | Allocator__R_findRegister_1 Allocator__PhysReg Datatypes.Coq_nat
 | Allocator__R_findRegister_2 Allocator__PhysReg Datatypes.Coq_nat Fin0.Coq_fin 
 (Datatypes.Coq_prod Allocator__PhysReg
 (Datatypes.Coq_option Datatypes.Coq_nat)) Allocator__R_findRegister 
 Allocator__PhysReg
 | Allocator__R_findRegister_3 Allocator__PhysReg Datatypes.Coq_nat Fin0.Coq_fin 
 (Datatypes.Coq_prod Allocator__PhysReg
 (Datatypes.Coq_option Datatypes.Coq_nat)) Allocator__R_findRegister 
 Allocator__PhysReg Datatypes.Coq_nat
 | Allocator__R_findRegister_4 Allocator__PhysReg Datatypes.Coq_nat Fin0.Coq_fin 
 (Datatypes.Coq_prod Allocator__PhysReg
 (Datatypes.Coq_option Datatypes.Coq_nat)) Allocator__R_findRegister 
 Allocator__PhysReg Datatypes.Coq_nat

_Allocator__coq_R_findRegister_rect :: (Allocator__PhysReg ->
                                       Datatypes.Coq_option
                                       Datatypes.Coq_nat) ->
                                       (Allocator__PhysReg -> () -> a1) ->
                                       (Allocator__PhysReg ->
                                       Datatypes.Coq_nat -> () -> () -> a1)
                                       -> (Allocator__PhysReg ->
                                       Datatypes.Coq_nat -> () ->
                                       Fin0.Coq_fin -> () ->
                                       (Datatypes.Coq_prod Allocator__PhysReg
                                       (Datatypes.Coq_option
                                       Datatypes.Coq_nat)) ->
                                       Allocator__R_findRegister -> a1 ->
                                       Allocator__PhysReg -> () -> a1) ->
                                       (Allocator__PhysReg ->
                                       Datatypes.Coq_nat -> () ->
                                       Fin0.Coq_fin -> () ->
                                       (Datatypes.Coq_prod Allocator__PhysReg
                                       (Datatypes.Coq_option
                                       Datatypes.Coq_nat)) ->
                                       Allocator__R_findRegister -> a1 ->
                                       Allocator__PhysReg ->
                                       Datatypes.Coq_nat -> () -> () -> a1)
                                       -> (Allocator__PhysReg ->
                                       Datatypes.Coq_nat -> () ->
                                       Fin0.Coq_fin -> () ->
                                       (Datatypes.Coq_prod Allocator__PhysReg
                                       (Datatypes.Coq_option
                                       Datatypes.Coq_nat)) ->
                                       Allocator__R_findRegister -> a1 ->
                                       Allocator__PhysReg ->
                                       Datatypes.Coq_nat -> () -> () -> a1)
                                       -> Allocator__PhysReg ->
                                       (Datatypes.Coq_prod Allocator__PhysReg
                                       (Datatypes.Coq_option
                                       Datatypes.Coq_nat)) ->
                                       Allocator__R_findRegister -> a1
_Allocator__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 start p r =
  case r of {
   Allocator__R_findRegister_0 start0 -> f start0 __;
   Allocator__R_findRegister_1 start0 pos -> f0 start0 pos __ __;
   Allocator__R_findRegister_2 start0 pos nreg res r0 reg ->
    f1 start0 pos __ nreg __ res r0
      (_Allocator__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg
        res r0) reg __;
   Allocator__R_findRegister_3 start0 pos nreg res r0 reg pos' ->
    f2 start0 pos __ nreg __ res r0
      (_Allocator__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg
        res r0) reg pos' __ __;
   Allocator__R_findRegister_4 start0 pos nreg res r0 reg pos' ->
    f3 start0 pos __ nreg __ res r0
      (_Allocator__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg
        res r0) reg pos' __ __}

_Allocator__coq_R_findRegister_rec :: (Allocator__PhysReg ->
                                      Datatypes.Coq_option Datatypes.Coq_nat)
                                      -> (Allocator__PhysReg -> () -> a1) ->
                                      (Allocator__PhysReg ->
                                      Datatypes.Coq_nat -> () -> () -> a1) ->
                                      (Allocator__PhysReg ->
                                      Datatypes.Coq_nat -> () -> Fin0.Coq_fin
                                      -> () -> (Datatypes.Coq_prod
                                      Allocator__PhysReg
                                      (Datatypes.Coq_option
                                      Datatypes.Coq_nat)) ->
                                      Allocator__R_findRegister -> a1 ->
                                      Allocator__PhysReg -> () -> a1) ->
                                      (Allocator__PhysReg ->
                                      Datatypes.Coq_nat -> () -> Fin0.Coq_fin
                                      -> () -> (Datatypes.Coq_prod
                                      Allocator__PhysReg
                                      (Datatypes.Coq_option
                                      Datatypes.Coq_nat)) ->
                                      Allocator__R_findRegister -> a1 ->
                                      Allocator__PhysReg -> Datatypes.Coq_nat
                                      -> () -> () -> a1) ->
                                      (Allocator__PhysReg ->
                                      Datatypes.Coq_nat -> () -> Fin0.Coq_fin
                                      -> () -> (Datatypes.Coq_prod
                                      Allocator__PhysReg
                                      (Datatypes.Coq_option
                                      Datatypes.Coq_nat)) ->
                                      Allocator__R_findRegister -> a1 ->
                                      Allocator__PhysReg -> Datatypes.Coq_nat
                                      -> () -> () -> a1) ->
                                      Allocator__PhysReg ->
                                      (Datatypes.Coq_prod Allocator__PhysReg
                                      (Datatypes.Coq_option
                                      Datatypes.Coq_nat)) ->
                                      Allocator__R_findRegister -> a1
_Allocator__coq_R_findRegister_rec registerIndex =
  _Allocator__coq_R_findRegister_rect registerIndex

_Allocator__findRegister_rect :: (Allocator__PhysReg -> Datatypes.Coq_option
                                 Datatypes.Coq_nat) -> (Allocator__PhysReg ->
                                 () -> a1) -> (Allocator__PhysReg ->
                                 Datatypes.Coq_nat -> () -> () -> a1) ->
                                 (Allocator__PhysReg -> Datatypes.Coq_nat ->
                                 () -> Fin0.Coq_fin -> () -> a1 ->
                                 Allocator__PhysReg -> () -> a1) ->
                                 (Allocator__PhysReg -> Datatypes.Coq_nat ->
                                 () -> Fin0.Coq_fin -> () -> a1 ->
                                 Allocator__PhysReg -> Datatypes.Coq_nat ->
                                 () -> () -> a1) -> (Allocator__PhysReg ->
                                 Datatypes.Coq_nat -> () -> Fin0.Coq_fin ->
                                 () -> a1 -> Allocator__PhysReg ->
                                 Datatypes.Coq_nat -> () -> () -> a1) ->
                                 Allocator__PhysReg -> a1
_Allocator__findRegister_rect registerIndex f f0 f1 f2 f3 start =
  Logic.eq_rect_r
    (case registerIndex start of {
      Datatypes.Some pos ->
       case Fin0.pred_fin _MyMachine__maxReg start of {
        Datatypes.Some nreg ->
         case _Allocator__findRegister registerIndex nreg of {
          Datatypes.Coq_pair reg o ->
           case o of {
            Datatypes.Some pos' ->
             case NPeano.ltb pos pos' of {
              Datatypes.Coq_true -> Datatypes.Coq_pair reg (Datatypes.Some
               pos');
              Datatypes.Coq_false -> Datatypes.Coq_pair reg (Datatypes.Some
               pos)};
            Datatypes.None -> Datatypes.Coq_pair reg Datatypes.None}};
        Datatypes.None -> Datatypes.Coq_pair start (Datatypes.Some pos)};
      Datatypes.None -> Datatypes.Coq_pair start Datatypes.None})
    (let {f4 = f3 start} in
     let {f5 = f2 start} in
     let {f6 = f1 start} in
     let {f7 = f0 start} in
     let {f8 = f start} in
     case registerIndex start of {
      Datatypes.Some n ->
       let {f9 = f7 n __} in
       let {f10 = f6 n __} in
       let {f11 = f5 n __} in
       let {f12 = f4 n __} in
       case Fin0.pred_fin _MyMachine__maxReg start of {
        Datatypes.Some f13 ->
         let {f14 = f12 f13 __} in
         let {f15 = f11 f13 __} in
         let {f16 = f10 f13 __} in
         case _Allocator__findRegister registerIndex f13 of {
          Datatypes.Coq_pair p o ->
           case o of {
            Datatypes.Some n0 ->
             let {f17 = \h -> f14 h p n0 __} in
             let {f18 = \h -> f15 h p n0 __} in
             case NPeano.ltb n n0 of {
              Datatypes.Coq_true ->
               let {f19 = \h -> f18 h __} in
               let {
                hrec = Logic.eq_rect o
                         (Logic.eq_rect
                           (_Allocator__findRegister registerIndex f13)
                           (_Allocator__findRegister_rect registerIndex f f0
                             f1 f2 f3 f13) (Datatypes.Coq_pair p o))
                         (Datatypes.Some n0)}
               in
               f19 hrec;
              Datatypes.Coq_false ->
               let {f19 = \h -> f17 h __} in
               let {
                hrec = Logic.eq_rect o
                         (Logic.eq_rect
                           (_Allocator__findRegister registerIndex f13)
                           (_Allocator__findRegister_rect registerIndex f f0
                             f1 f2 f3 f13) (Datatypes.Coq_pair p o))
                         (Datatypes.Some n0)}
               in
               f19 hrec};
            Datatypes.None ->
             let {f17 = \h -> f16 h p __} in
             let {
              hrec = Logic.eq_rect o
                       (Logic.eq_rect
                         (_Allocator__findRegister registerIndex f13)
                         (_Allocator__findRegister_rect registerIndex f f0 f1
                           f2 f3 f13) (Datatypes.Coq_pair p o))
                       Datatypes.None}
             in
             f17 hrec}};
        Datatypes.None -> f9 __};
      Datatypes.None -> f8 __})
    (_Allocator__findRegister registerIndex start)

_Allocator__findRegister_rec :: (Allocator__PhysReg -> Datatypes.Coq_option
                                Datatypes.Coq_nat) -> (Allocator__PhysReg ->
                                () -> a1) -> (Allocator__PhysReg ->
                                Datatypes.Coq_nat -> () -> () -> a1) ->
                                (Allocator__PhysReg -> Datatypes.Coq_nat ->
                                () -> Fin0.Coq_fin -> () -> a1 ->
                                Allocator__PhysReg -> () -> a1) ->
                                (Allocator__PhysReg -> Datatypes.Coq_nat ->
                                () -> Fin0.Coq_fin -> () -> a1 ->
                                Allocator__PhysReg -> Datatypes.Coq_nat -> ()
                                -> () -> a1) -> (Allocator__PhysReg ->
                                Datatypes.Coq_nat -> () -> Fin0.Coq_fin -> ()
                                -> a1 -> Allocator__PhysReg ->
                                Datatypes.Coq_nat -> () -> () -> a1) ->
                                Allocator__PhysReg -> a1
_Allocator__findRegister_rec registerIndex =
  _Allocator__findRegister_rect registerIndex

_Allocator__coq_R_findRegister_correct :: (Allocator__PhysReg ->
                                          Datatypes.Coq_option
                                          Datatypes.Coq_nat) ->
                                          Allocator__PhysReg ->
                                          (Datatypes.Coq_prod
                                          Allocator__PhysReg
                                          (Datatypes.Coq_option
                                          Datatypes.Coq_nat)) ->
                                          Allocator__R_findRegister
_Allocator__coq_R_findRegister_correct x x0 res =
  _Allocator__findRegister_rect x (\y _ z _ ->
    Logic.eq_rec_r (Datatypes.Coq_pair y Datatypes.None)
      (Allocator__R_findRegister_0 y) z) (\y y0 _ _ z _ ->
    Logic.eq_rec_r (Datatypes.Coq_pair y (Datatypes.Some y0))
      (Allocator__R_findRegister_1 y y0) z) (\y y0 _ y2 _ y4 y5 _ z _ ->
    Logic.eq_rec_r (Datatypes.Coq_pair y5 Datatypes.None)
      (Allocator__R_findRegister_2 y y0 y2 (_Allocator__findRegister x y2)
      (y4 (_Allocator__findRegister x y2) __) y5) z)
    (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r (Datatypes.Coq_pair y5 (Datatypes.Some y6))
      (Allocator__R_findRegister_3 y y0 y2 (_Allocator__findRegister x y2)
      (y4 (_Allocator__findRegister x y2) __) y5 y6) z)
    (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r (Datatypes.Coq_pair y5 (Datatypes.Some y0))
      (Allocator__R_findRegister_4 y y0 y2 (_Allocator__findRegister x y2)
      (y4 (_Allocator__findRegister x y2) __) y5 y6) z) x0 res __

_Allocator__splitInterval :: Allocator__ScanStateDesc ->
                             Allocator__ScanStateCursor ->
                             (Datatypes.Coq_option Datatypes.Coq_nat) ->
                             Allocator__NextState
_Allocator__splitInterval sd cur before =
  Allocator__Build_NextScanState sd (_Allocator__curState sd cur)

_Allocator__cursorFromMorphLen :: Allocator__ScanStateDesc ->
                                  Allocator__ScanStateCursor ->
                                  Allocator__NextState ->
                                  Allocator__ScanStateCursor
_Allocator__cursorFromMorphLen sd cur n =
  case cur of {
   Allocator__Build_ScanStateCursor curState0 x ->
    Allocator__Build_ScanStateCursor
    (case n of {
      Allocator__Build_NextScanState nextDesc0 nextState0 -> nextState0}) x}

_Allocator__cursorFromMorphStLen :: Allocator__ScanStateDesc ->
                                    Allocator__ScanStateCursor ->
                                    Allocator__NextState ->
                                    Allocator__ScanStateCursor
_Allocator__cursorFromMorphStLen sd cur n =
  _Allocator__cursorFromMorphLen sd cur (Allocator__Build_NextScanState
    (_Allocator__nextDesc n) (_Allocator__nextState n))

_Allocator__tryAllocateFreeReg :: Allocator__ScanStateDesc ->
                                  Allocator__ScanStateCursor ->
                                  Datatypes.Coq_option Allocator__NextState
_Allocator__tryAllocateFreeReg sd cur =
  let {st = _Allocator__curState sd cur} in
  let {current = _Allocator__curInterval sd cur} in
  let {
   freeUntilPos' = _Allocator__getRegisterIndex sd st (\x -> Datatypes.Some
                     Datatypes.O) (\x -> Datatypes.None)
                     (_Allocator__active sd)}
  in
  let {
   intersectingIntervals = List.filter (\x ->
                             Interval.anyRangeIntersects
                               (Specif.projT1
                                 (_Allocator__getInterval sd
                                   (_Allocator__curId sd cur))) current
                               (Specif.projT1 (_Allocator__getInterval sd x))
                               (Specif.projT2 (_Allocator__getInterval sd x)))
                             (_Allocator__inactive sd)}
  in
  let {
   freeUntilPos = _Allocator__getRegisterIndex sd st
                    (_Allocator__nextIntersectionWith
                      (Specif.projT1
                        (_Allocator__getInterval sd
                          (_Allocator__curId sd cur))) current sd)
                    freeUntilPos' intersectingIntervals}
  in
  let {lastReg = Fin0.ultimate_from_nat _Allocator__maxReg} in
  case _Allocator__findRegister freeUntilPos lastReg of {
   Datatypes.Coq_pair reg mres ->
    let {default0 = _Allocator__moveUnhandledToActive sd cur reg} in
    case mres of {
     Datatypes.Some n ->
      case EqNat.beq_nat n Datatypes.O of {
       Datatypes.Coq_true -> Datatypes.None;
       Datatypes.Coq_false -> Datatypes.Some
        (case NPeano.ltb
                (Interval.intervalEnd
                  (Specif.projT1
                    (_Allocator__getInterval sd (_Allocator__curId sd cur)))
                  current) n of {
          Datatypes.Coq_true -> default0;
          Datatypes.Coq_false ->
           _Allocator__moveUnhandledToActive
             (_Allocator__nextDesc
               (_Allocator__splitInterval sd cur (Datatypes.Some n)))
             (_Allocator__cursorFromMorphStLen sd cur
               (_Allocator__splitInterval sd cur (Datatypes.Some n))) reg})};
     Datatypes.None -> Datatypes.Some default0}}

_Allocator__nextUseAfter :: Datatypes.Coq_nat -> Allocator__ScanStateDesc ->
                            Allocator__IntervalId -> Datatypes.Coq_option
                            Datatypes.Coq_nat
_Allocator__nextUseAfter =
  Prelude.error "AXIOM TO BE REALIZED"

_Allocator__assignSpillSlotToCurrent :: Allocator__ScanStateDesc ->
                                        Allocator__ScanStateCursor ->
                                        Allocator__NextScanState
_Allocator__assignSpillSlotToCurrent =
  Prelude.error "AXIOM TO BE REALIZED"

_Allocator__allocateBlockedReg :: Allocator__ScanStateDesc ->
                                  Allocator__ScanStateCursor ->
                                  Allocator__NextState
_Allocator__allocateBlockedReg sd cur =
  Lib.undefined

_Allocator__checkActiveIntervals :: Allocator__ScanStateDesc ->
                                    Allocator__ScanState -> Datatypes.Coq_nat
                                    -> Allocator__NextScanState
_Allocator__checkActiveIntervals sd st pos =
  let {
   go sd0 st0 ss is pos0 =
     case is of {
      Datatypes.Coq_nil -> ss;
      Datatypes.Coq_cons x xs ->
       let {
        i = Specif.projT2 (_Allocator__getInterval sd0 (Specif.projT1 x))}
       in
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       (Specif.projT1
                         (_Allocator__getInterval sd0 (Specif.projT1 x))) i)
                     pos0 of {
               Datatypes.Coq_true ->
                _Allocator__moveActiveToHandled sd0 st0 (Specif.projT1 x);
               Datatypes.Coq_false ->
                case Datatypes.negb
                       (Interval.intervalCoversPos
                         (Specif.projT1
                           (_Allocator__getInterval sd0 (Specif.projT1 x))) i
                         pos0) of {
                 Datatypes.Coq_true ->
                  _Allocator__moveActiveToInactive sd0 st0 (Specif.projT1 x);
                 Datatypes.Coq_false -> ss}}}
       in
       go sd0 st0 st1 xs pos0}}
  in go sd st (Allocator__Build_NextScanState sd st)
       (Lib.list_membership (_Allocator__active sd)) pos

_Allocator__checkInactiveIntervals :: Allocator__ScanStateDesc ->
                                      Allocator__ScanState ->
                                      Datatypes.Coq_nat ->
                                      Allocator__NextScanState
_Allocator__checkInactiveIntervals sd st pos =
  let {
   go sd0 st0 ss is pos0 =
     case is of {
      Datatypes.Coq_nil -> ss;
      Datatypes.Coq_cons x xs ->
       let {
        i = Specif.projT2 (_Allocator__getInterval sd0 (Specif.projT1 x))}
       in
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       (Specif.projT1
                         (_Allocator__getInterval sd0 (Specif.projT1 x))) i)
                     pos0 of {
               Datatypes.Coq_true ->
                _Allocator__moveInactiveToHandled sd0 st0 (Specif.projT1 x);
               Datatypes.Coq_false ->
                case Interval.intervalCoversPos
                       (Specif.projT1
                         (_Allocator__getInterval sd0 (Specif.projT1 x))) i
                       pos0 of {
                 Datatypes.Coq_true ->
                  _Allocator__moveInactiveToActive sd0 st0 (Specif.projT1 x);
                 Datatypes.Coq_false -> ss}}}
       in
       go sd0 st0 st1 xs pos0}}
  in go sd st (Allocator__Build_NextScanState sd st)
       (Lib.list_membership (_Allocator__inactive sd)) pos

_Allocator__handleInterval :: Allocator__ScanStateDesc ->
                              Allocator__ScanStateCursor ->
                              Allocator__NextState
_Allocator__handleInterval sd cur =
  let {position = _Allocator__curPosition sd cur} in
  let {
   sp1 = _Allocator__checkActiveIntervals sd (_Allocator__curState sd cur)
           position}
  in
  let {
   sp2 = _Allocator__checkInactiveIntervals (_Allocator__nextDesc sp1)
           (_Allocator__nextState sp1) position}
  in
  let {
   cursor = Allocator__Build_ScanStateCursor (_Allocator__nextState sp2)
    (_Allocator__curIntDesc sd cur)}
  in
  let {
   result = Lib.fromMaybe
              (_Allocator__allocateBlockedReg (_Allocator__nextDesc sp2)
                cursor)
              (_Allocator__tryAllocateFreeReg (_Allocator__nextDesc sp2)
                cursor)}
  in
  Allocator__Build_NextScanState (_Allocator__nextDesc result)
  (_Allocator__nextState result)

_Allocator__linearScan_F :: (Allocator__ScanStateDesc -> Allocator__ScanState
                            -> Specif.Coq_sigT Allocator__ScanStateDesc
                            Allocator__ScanState) -> Allocator__ScanStateDesc
                            -> Allocator__ScanState -> Specif.Coq_sigT
                            Allocator__ScanStateDesc Allocator__ScanState
_Allocator__linearScan_F linearScan0 sd st =
  case List.destruct_list (_Allocator__unhandled sd) of {
   Specif.Coq_inleft s ->
    case s of {
     Specif.Coq_existT x s0 ->
      case _Allocator__handleInterval sd (Allocator__Build_ScanStateCursor st
             (Specif.projT1 (_Allocator__getInterval sd x))) of {
       Allocator__Build_NextScanState sd2 st2 -> linearScan0 sd2 st2}};
   Specif.Coq_inright -> Specif.Coq_existT sd st}

_Allocator__linearScan_terminate :: Allocator__ScanStateDesc ->
                                    Allocator__ScanState ->
                                    (Specif.Coq_sigT Allocator__ScanStateDesc
                                    Allocator__ScanState)
_Allocator__linearScan_terminate sd st =
  case List.destruct_list (_Allocator__unhandled sd) of {
   Specif.Coq_inleft s ->
    case s of {
     Specif.Coq_existT x s0 ->
      case _Allocator__handleInterval sd (Allocator__Build_ScanStateCursor st
             (Specif.projT1 (_Allocator__getInterval sd x))) of {
       Allocator__Build_NextScanState sd2 st2 ->
        Specif.sig_rec (\rec_res _ -> rec_res)
          (_Allocator__linearScan_terminate sd2 st2)}};
   Specif.Coq_inright -> Specif.Coq_existT sd st}

_Allocator__linearScan :: Allocator__ScanStateDesc -> Allocator__ScanState ->
                          Specif.Coq_sigT Allocator__ScanStateDesc
                          Allocator__ScanState
_Allocator__linearScan sd st =
  case List.destruct_list (_Allocator__unhandled sd) of {
   Specif.Coq_inleft s ->
    case s of {
     Specif.Coq_existT x s0 ->
      case _Allocator__handleInterval sd (Allocator__Build_ScanStateCursor st
             (Specif.projT1 (_Allocator__getInterval sd x))) of {
       Allocator__Build_NextScanState sd2 st2 ->
        Specif.sig_rec (\rec_res _ -> rec_res)
          (_Allocator__linearScan sd2 st2)}};
   Specif.Coq_inright -> Specif.Coq_existT sd st}

data Allocator__R_linearScan =
   Allocator__R_linearScan_0 Allocator__ScanStateDesc Allocator__ScanState 
 Allocator__IntervalId (Datatypes.Coq_list Allocator__IntervalId) Allocator__ScanStateDesc 
 Allocator__ScanState (Specif.Coq_sigT Allocator__ScanStateDesc
                      Allocator__ScanState) Allocator__R_linearScan
 | Allocator__R_linearScan_1 Allocator__ScanStateDesc Allocator__ScanState

_Allocator__coq_R_linearScan_rect :: (Allocator__ScanStateDesc ->
                                     Allocator__ScanState ->
                                     Allocator__IntervalId ->
                                     (Datatypes.Coq_list
                                     Allocator__IntervalId) -> () -> () ->
                                     Allocator__ScanStateDesc ->
                                     Allocator__ScanState -> () -> () ->
                                     (Specif.Coq_sigT
                                     Allocator__ScanStateDesc
                                     Allocator__ScanState) ->
                                     Allocator__R_linearScan -> a1 -> a1) ->
                                     (Allocator__ScanStateDesc ->
                                     Allocator__ScanState -> () -> () -> a1)
                                     -> Allocator__ScanStateDesc ->
                                     Allocator__ScanState -> (Specif.Coq_sigT
                                     Allocator__ScanStateDesc
                                     Allocator__ScanState) ->
                                     Allocator__R_linearScan -> a1
_Allocator__coq_R_linearScan_rect f f0 sd st s r =
  case r of {
   Allocator__R_linearScan_0 sd0 st0 x xs x0 x1 x2 x3 ->
    f sd0 st0 x xs __ __ x0 x1 __ __ x2 x3
      (_Allocator__coq_R_linearScan_rect f f0 x0 x1 x2 x3);
   Allocator__R_linearScan_1 sd0 st0 -> f0 sd0 st0 __ __}

_Allocator__coq_R_linearScan_rec :: (Allocator__ScanStateDesc ->
                                    Allocator__ScanState ->
                                    Allocator__IntervalId ->
                                    (Datatypes.Coq_list
                                    Allocator__IntervalId) -> () -> () ->
                                    Allocator__ScanStateDesc ->
                                    Allocator__ScanState -> () -> () ->
                                    (Specif.Coq_sigT Allocator__ScanStateDesc
                                    Allocator__ScanState) ->
                                    Allocator__R_linearScan -> a1 -> a1) ->
                                    (Allocator__ScanStateDesc ->
                                    Allocator__ScanState -> () -> () -> a1)
                                    -> Allocator__ScanStateDesc ->
                                    Allocator__ScanState -> (Specif.Coq_sigT
                                    Allocator__ScanStateDesc
                                    Allocator__ScanState) ->
                                    Allocator__R_linearScan -> a1
_Allocator__coq_R_linearScan_rec =
  _Allocator__coq_R_linearScan_rect

type Allocator__VirtReg = Datatypes.Coq_nat

type Allocator__Graph a =
  a
  -- singleton inductive, whose constructor was Build_Graph
  
_Allocator__coq_Graph_rect :: (a1 -> a2) -> (Allocator__Graph a1) -> a2
_Allocator__coq_Graph_rect f g =
  f g

_Allocator__coq_Graph_rec :: (a1 -> a2) -> (Allocator__Graph a1) -> a2
_Allocator__coq_Graph_rec =
  _Allocator__coq_Graph_rect

_Allocator__postOrderTraversal :: (Allocator__Graph a1) -> a1
_Allocator__postOrderTraversal graph =
  graph

_Allocator__determineIntervals :: (Allocator__Graph Allocator__VirtReg) ->
                                  Specif.Coq_sigT Allocator__ScanStateDesc
                                  Allocator__ScanState
_Allocator__determineIntervals =
  Prelude.error "AXIOM TO BE REALIZED"

_Allocator__allocateRegisters :: (Allocator__Graph Allocator__VirtReg) ->
                                 Specif.Coq_sigT Allocator__ScanStateDesc
                                 Allocator__ScanState
_Allocator__allocateRegisters g =
  case _Allocator__determineIntervals g of {
   Specif.Coq_existT sd st -> _Allocator__linearScan sd st}

