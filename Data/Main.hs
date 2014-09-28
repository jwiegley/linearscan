module Data.Main where

import qualified Prelude
import qualified Data.List
import qualified Data.Compare as Compare
import qualified Data.Compare_dec as Compare_dec
import qualified Data.EqNat as EqNat
import qualified Data.Fin0 as Fin0
import qualified Data.Fin as Fin
import qualified Data.Interval as Interval
import qualified Data.Lib as Lib
import qualified Data.List0 as List0
import qualified Data.Logic as Logic
import qualified Data.NPeano as NPeano
import qualified Data.Peano as Peano
import qualified Data.Specif as Specif


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

type Allocator__PhysReg = Fin0.Coq_fin

_Allocator__maxReg :: Prelude.Int
_Allocator__maxReg =
  _MyMachine__maxReg

data Allocator__ScanStateDesc =
   Allocator__Build_ScanStateDesc Prelude.Int ([] Fin0.Coq_fin) ([]
                                                                Fin0.Coq_fin) 
 ([] Fin0.Coq_fin) ([] Fin0.Coq_fin) (Fin0.Coq_fin -> Interval.IntervalDesc) 
 (Fin0.Coq_fin -> Prelude.Maybe Allocator__PhysReg) (Allocator__PhysReg ->
                                                    Prelude.Maybe
                                                    Interval.IntervalDesc)

_Allocator__coq_ScanStateDesc_rect :: (Prelude.Int -> ([] Fin0.Coq_fin) ->
                                      ([] Fin0.Coq_fin) -> ([] Fin0.Coq_fin)
                                      -> ([] Fin0.Coq_fin) -> (Fin0.Coq_fin
                                      -> Interval.IntervalDesc) ->
                                      (Fin0.Coq_fin -> Prelude.Maybe
                                      Allocator__PhysReg) ->
                                      (Allocator__PhysReg -> Prelude.Maybe
                                      Interval.IntervalDesc) -> () -> a1) ->
                                      Allocator__ScanStateDesc -> a1
_Allocator__coq_ScanStateDesc_rect f s =
  case s of {
   Allocator__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6 __}

_Allocator__coq_ScanStateDesc_rec :: (Prelude.Int -> ([] Fin0.Coq_fin) -> ([]
                                     Fin0.Coq_fin) -> ([] Fin0.Coq_fin) ->
                                     ([] Fin0.Coq_fin) -> (Fin0.Coq_fin ->
                                     Interval.IntervalDesc) -> (Fin0.Coq_fin
                                     -> Prelude.Maybe Allocator__PhysReg) ->
                                     (Allocator__PhysReg -> Prelude.Maybe
                                     Interval.IntervalDesc) -> () -> a1) ->
                                     Allocator__ScanStateDesc -> a1
_Allocator__coq_ScanStateDesc_rec =
  _Allocator__coq_ScanStateDesc_rect

_Allocator__nextInterval :: Allocator__ScanStateDesc -> Prelude.Int
_Allocator__nextInterval s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> nextInterval0}

type Allocator__IntervalId = Fin0.Coq_fin

_Allocator__unhandled :: Allocator__ScanStateDesc -> [] Allocator__IntervalId
_Allocator__unhandled s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> unhandled0}

_Allocator__active :: Allocator__ScanStateDesc -> [] Allocator__IntervalId
_Allocator__active s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> active0}

_Allocator__inactive :: Allocator__ScanStateDesc -> [] Allocator__IntervalId
_Allocator__inactive s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> inactive0}

_Allocator__handled :: Allocator__ScanStateDesc -> [] Allocator__IntervalId
_Allocator__handled s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> handled0}

_Allocator__getInterval :: Allocator__ScanStateDesc -> Allocator__IntervalId
                           -> Interval.IntervalDesc
_Allocator__getInterval s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getInterval0}

_Allocator__assignments :: Allocator__ScanStateDesc -> Allocator__IntervalId
                           -> Prelude.Maybe Allocator__PhysReg
_Allocator__assignments s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> assignments0}

_Allocator__getFixedInterval :: Allocator__ScanStateDesc ->
                                Allocator__PhysReg -> Prelude.Maybe
                                Interval.IntervalDesc
_Allocator__getFixedInterval s =
  case s of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getFixedInterval0}

_Allocator__all_state_lists :: Allocator__ScanStateDesc -> []
                               Allocator__IntervalId
_Allocator__all_state_lists s =
  (Prelude.++) (_Allocator__unhandled s)
    ((Prelude.++) (_Allocator__active s)
      ((Prelude.++) (_Allocator__inactive s) (_Allocator__handled s)))

_Allocator__lt_sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
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
        Logic.eq_rec ((Prelude.+) h0 nextInterval0)
          (Fin.coq_R nextInterval0 h0 x) nextInterval1}};
   Specif.Coq_right ->
    Logic.eq_rec (_Allocator__nextInterval st) x
      (_Allocator__nextInterval st')}

_Allocator__unhandledExtent :: Allocator__ScanStateDesc -> Prelude.Int
_Allocator__unhandledExtent sd =
  case _Allocator__unhandled sd of {
   [] -> 0;
   (:) i l ->
    case l of {
     [] -> Interval.intervalExtent ( (_Allocator__getInterval sd i));
     (:) i0 l0 ->
      let {
       f = \n x ->
        (Prelude.+) n
          (Interval.intervalExtent ( (_Allocator__getInterval sd x)))}
      in
      (\f -> Prelude.flip (Data.List.foldl' f)) f ((:) i ((:) i0 l0)) 0}}

type Allocator__ScanStateCursor =
  Interval.IntervalDesc
  -- singleton inductive, whose constructor was Build_ScanStateCursor
  
_Allocator__coq_ScanStateCursor_rect :: Allocator__ScanStateDesc -> (() -> ()
                                        -> Interval.IntervalDesc -> a1) ->
                                        Allocator__ScanStateCursor -> a1
_Allocator__coq_ScanStateCursor_rect sd f s =
  f __ __ s

_Allocator__coq_ScanStateCursor_rec :: Allocator__ScanStateDesc -> (() -> ()
                                       -> Interval.IntervalDesc -> a1) ->
                                       Allocator__ScanStateCursor -> a1
_Allocator__coq_ScanStateCursor_rec sd =
  _Allocator__coq_ScanStateCursor_rect sd

_Allocator__curId :: Allocator__ScanStateDesc -> Allocator__ScanStateCursor
                     -> Allocator__IntervalId
_Allocator__curId sd s =
  Lib.safe_hd (_Allocator__unhandled sd)

_Allocator__curIntDesc :: Allocator__ScanStateDesc ->
                          Allocator__ScanStateCursor -> Interval.IntervalDesc
_Allocator__curIntDesc sd s =
  s

_Allocator__curPosition :: Allocator__ScanStateDesc ->
                           Allocator__ScanStateCursor -> Prelude.Int
_Allocator__curPosition sd s =
  Interval.intervalStart
    ( (_Allocator__getInterval sd (_Allocator__curId sd s)))

type Allocator__NextScanState =
  Allocator__ScanStateDesc
  -- singleton inductive, whose constructor was Build_NextScanState
  
_Allocator__coq_NextScanState_rect :: (Allocator__ScanStateDesc -> () -> ()
                                      -> a1) -> Allocator__NextScanState ->
                                      a1
_Allocator__coq_NextScanState_rect f n =
  f n __ __

_Allocator__coq_NextScanState_rec :: (Allocator__ScanStateDesc -> () -> () ->
                                     a1) -> Allocator__NextScanState -> a1
_Allocator__coq_NextScanState_rec =
  _Allocator__coq_NextScanState_rect

_Allocator__nextDesc :: Allocator__NextScanState -> Allocator__ScanStateDesc
_Allocator__nextDesc n =
  n

type Allocator__NextState = Allocator__NextScanState

type Allocator__NextStateDep = Allocator__NextScanState

type Allocator__NextStateWith a = (,) a Allocator__NextScanState

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
                                   Allocator__IntervalId ->
                                   Allocator__NextScanState
_Allocator__moveActiveToHandled sd x =
  Allocator__Build_ScanStateDesc (_Allocator__nextInterval sd)
    (_Allocator__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_Allocator__nextInterval sd))) x
      (_Allocator__active sd)) ((:) x (_Allocator__inactive sd))
    (_Allocator__handled sd) (_Allocator__getInterval sd)
    (_Allocator__assignments sd) (_Allocator__getFixedInterval sd)

_Allocator__moveActiveToInactive :: Allocator__ScanStateDesc ->
                                    Allocator__IntervalId ->
                                    Allocator__NextScanState
_Allocator__moveActiveToInactive sd x =
  Allocator__Build_ScanStateDesc (_Allocator__nextInterval sd)
    (_Allocator__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_Allocator__nextInterval sd))) x
      (_Allocator__active sd)) ((:) x (_Allocator__inactive sd))
    (_Allocator__handled sd) (_Allocator__getInterval sd)
    (_Allocator__assignments sd) (_Allocator__getFixedInterval sd)

_Allocator__moveInactiveToActive :: Allocator__ScanStateDesc ->
                                    Allocator__IntervalId ->
                                    Allocator__NextScanState
_Allocator__moveInactiveToActive sd x =
  Allocator__Build_ScanStateDesc (_Allocator__nextInterval sd)
    (_Allocator__unhandled sd) ((:) x (_Allocator__active sd))
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_Allocator__nextInterval sd))) x
      (_Allocator__inactive sd)) (_Allocator__handled sd)
    (_Allocator__getInterval sd) (_Allocator__assignments sd)
    (_Allocator__getFixedInterval sd)

_Allocator__moveInactiveToHandled :: Allocator__ScanStateDesc ->
                                     Allocator__IntervalId ->
                                     Allocator__NextScanState
_Allocator__moveInactiveToHandled sd x =
  Allocator__Build_ScanStateDesc (_Allocator__nextInterval sd)
    (_Allocator__unhandled sd) (_Allocator__active sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_Allocator__nextInterval sd))) x
      (_Allocator__inactive sd)) ((:) x (_Allocator__handled sd))
    (_Allocator__getInterval sd) (_Allocator__assignments sd)
    (_Allocator__getFixedInterval sd)

_Allocator__moveUnhandledToActive :: Allocator__ScanStateDesc ->
                                     Allocator__ScanStateCursor ->
                                     Allocator__PhysReg ->
                                     Allocator__NextState
_Allocator__moveUnhandledToActive sd cur reg =
  case sd of {
   Allocator__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 ->
    case unhandled0 of {
     [] -> Logic.coq_False_rec;
     (:) i unhandled1 -> Allocator__Build_ScanStateDesc nextInterval0
      unhandled1 ((:) i active0) inactive0 handled0 getInterval0 (\i0 ->
      case Compare.cmp_eq_dec (Fin0.fin_CompareSpec nextInterval0) i0 i of {
       Specif.Coq_left -> Prelude.Just reg;
       Specif.Coq_right -> assignments0 i0}) getFixedInterval0}}

_Allocator__nextIntersectionWith :: Interval.IntervalDesc ->
                                    Allocator__ScanStateDesc ->
                                    Allocator__IntervalId -> Prelude.Maybe
                                    Prelude.Int
_Allocator__nextIntersectionWith d sd jid =
  Interval.firstIntersectionPoint ( (_Allocator__getInterval sd jid)) d

_Allocator__getRegisterIndex :: Allocator__ScanStateDesc ->
                                (Allocator__IntervalId -> Prelude.Maybe
                                Prelude.Int) -> (Allocator__PhysReg ->
                                Prelude.Maybe Prelude.Int) -> ([]
                                Allocator__IntervalId) -> Allocator__PhysReg
                                -> Prelude.Maybe Prelude.Int
_Allocator__getRegisterIndex sd intervalIndex registerIndex intervals =
  Prelude.foldr (\x f r ->
    case _Allocator__assignments sd x of {
     Prelude.Just a ->
      case Compare.cmp_eq_dec (Fin0.fin_CompareSpec _MyMachine__maxReg) a r of {
       Specif.Coq_left -> intervalIndex x;
       Specif.Coq_right -> f r};
     Prelude.Nothing -> f r}) registerIndex intervals

_Allocator__findRegister_F :: ((Allocator__PhysReg -> Prelude.Maybe
                              Prelude.Int) -> Allocator__PhysReg -> (,)
                              Allocator__PhysReg (Prelude.Maybe Prelude.Int))
                              -> (Allocator__PhysReg -> Prelude.Maybe
                              Prelude.Int) -> Allocator__PhysReg -> (,)
                              Allocator__PhysReg (Prelude.Maybe Prelude.Int)
_Allocator__findRegister_F findRegister0 registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _MyMachine__maxReg start of {
     Prelude.Just nreg ->
      case findRegister0 registerIndex nreg of {
       (,) reg o ->
        case o of {
         Prelude.Just pos' ->
          case NPeano.ltb pos pos' of {
           Prelude.True -> (,) reg (Prelude.Just pos');
           Prelude.False -> (,) reg (Prelude.Just pos)};
         Prelude.Nothing -> (,) reg Prelude.Nothing}};
     Prelude.Nothing -> (,) start (Prelude.Just pos)};
   Prelude.Nothing -> (,) start Prelude.Nothing}

_Allocator__findRegister_terminate :: (Allocator__PhysReg -> Prelude.Maybe
                                      Prelude.Int) -> Allocator__PhysReg ->
                                      ((,) Allocator__PhysReg
                                      (Prelude.Maybe Prelude.Int))
_Allocator__findRegister_terminate registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _MyMachine__maxReg start of {
     Prelude.Just nreg ->
      Specif.sig_rec (\rec_res _ ->
        case rec_res of {
         (,) reg o ->
          case o of {
           Prelude.Just pos' ->
            case NPeano.ltb pos pos' of {
             Prelude.True -> (,) reg (Prelude.Just pos');
             Prelude.False -> (,) reg (Prelude.Just pos)};
           Prelude.Nothing -> (,) reg Prelude.Nothing}})
        (_Allocator__findRegister_terminate registerIndex nreg);
     Prelude.Nothing -> (,) start (Prelude.Just pos)};
   Prelude.Nothing -> (,) start Prelude.Nothing}

_Allocator__findRegister :: (Allocator__PhysReg -> Prelude.Maybe Prelude.Int)
                            -> Allocator__PhysReg -> (,) Allocator__PhysReg
                            (Prelude.Maybe Prelude.Int)
_Allocator__findRegister registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _MyMachine__maxReg start of {
     Prelude.Just nreg ->
      Specif.sig_rec (\rec_res _ ->
        case rec_res of {
         (,) reg o ->
          case o of {
           Prelude.Just pos' ->
            case NPeano.ltb pos pos' of {
             Prelude.True -> (,) reg (Prelude.Just pos');
             Prelude.False -> (,) reg (Prelude.Just pos)};
           Prelude.Nothing -> (,) reg Prelude.Nothing}})
        (_Allocator__findRegister registerIndex nreg);
     Prelude.Nothing -> (,) start (Prelude.Just pos)};
   Prelude.Nothing -> (,) start Prelude.Nothing}

data Allocator__R_findRegister =
   Allocator__R_findRegister_0 Allocator__PhysReg
 | Allocator__R_findRegister_1 Allocator__PhysReg Prelude.Int
 | Allocator__R_findRegister_2 Allocator__PhysReg Prelude.Int Fin0.Coq_fin 
 ((,) Allocator__PhysReg (Prelude.Maybe Prelude.Int)) Allocator__R_findRegister 
 Allocator__PhysReg
 | Allocator__R_findRegister_3 Allocator__PhysReg Prelude.Int Fin0.Coq_fin 
 ((,) Allocator__PhysReg (Prelude.Maybe Prelude.Int)) Allocator__R_findRegister 
 Allocator__PhysReg Prelude.Int
 | Allocator__R_findRegister_4 Allocator__PhysReg Prelude.Int Fin0.Coq_fin 
 ((,) Allocator__PhysReg (Prelude.Maybe Prelude.Int)) Allocator__R_findRegister 
 Allocator__PhysReg Prelude.Int

_Allocator__coq_R_findRegister_rect :: (Allocator__PhysReg -> Prelude.Maybe
                                       Prelude.Int) -> (Allocator__PhysReg ->
                                       () -> a1) -> (Allocator__PhysReg ->
                                       Prelude.Int -> () -> () -> a1) ->
                                       (Allocator__PhysReg -> Prelude.Int ->
                                       () -> Fin0.Coq_fin -> () -> ((,)
                                       Allocator__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
                                       Allocator__R_findRegister -> a1 ->
                                       Allocator__PhysReg -> () -> a1) ->
                                       (Allocator__PhysReg -> Prelude.Int ->
                                       () -> Fin0.Coq_fin -> () -> ((,)
                                       Allocator__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
                                       Allocator__R_findRegister -> a1 ->
                                       Allocator__PhysReg -> Prelude.Int ->
                                       () -> () -> a1) -> (Allocator__PhysReg
                                       -> Prelude.Int -> () -> Fin0.Coq_fin
                                       -> () -> ((,) Allocator__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
                                       Allocator__R_findRegister -> a1 ->
                                       Allocator__PhysReg -> Prelude.Int ->
                                       () -> () -> a1) -> Allocator__PhysReg
                                       -> ((,) Allocator__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
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

_Allocator__coq_R_findRegister_rec :: (Allocator__PhysReg -> Prelude.Maybe
                                      Prelude.Int) -> (Allocator__PhysReg ->
                                      () -> a1) -> (Allocator__PhysReg ->
                                      Prelude.Int -> () -> () -> a1) ->
                                      (Allocator__PhysReg -> Prelude.Int ->
                                      () -> Fin0.Coq_fin -> () -> ((,)
                                      Allocator__PhysReg
                                      (Prelude.Maybe Prelude.Int)) ->
                                      Allocator__R_findRegister -> a1 ->
                                      Allocator__PhysReg -> () -> a1) ->
                                      (Allocator__PhysReg -> Prelude.Int ->
                                      () -> Fin0.Coq_fin -> () -> ((,)
                                      Allocator__PhysReg
                                      (Prelude.Maybe Prelude.Int)) ->
                                      Allocator__R_findRegister -> a1 ->
                                      Allocator__PhysReg -> Prelude.Int -> ()
                                      -> () -> a1) -> (Allocator__PhysReg ->
                                      Prelude.Int -> () -> Fin0.Coq_fin -> ()
                                      -> ((,) Allocator__PhysReg
                                      (Prelude.Maybe Prelude.Int)) ->
                                      Allocator__R_findRegister -> a1 ->
                                      Allocator__PhysReg -> Prelude.Int -> ()
                                      -> () -> a1) -> Allocator__PhysReg ->
                                      ((,) Allocator__PhysReg
                                      (Prelude.Maybe Prelude.Int)) ->
                                      Allocator__R_findRegister -> a1
_Allocator__coq_R_findRegister_rec registerIndex =
  _Allocator__coq_R_findRegister_rect registerIndex

_Allocator__findRegister_rect :: (Allocator__PhysReg -> Prelude.Maybe
                                 Prelude.Int) -> (Allocator__PhysReg -> () ->
                                 a1) -> (Allocator__PhysReg -> Prelude.Int ->
                                 () -> () -> a1) -> (Allocator__PhysReg ->
                                 Prelude.Int -> () -> Fin0.Coq_fin -> () ->
                                 a1 -> Allocator__PhysReg -> () -> a1) ->
                                 (Allocator__PhysReg -> Prelude.Int -> () ->
                                 Fin0.Coq_fin -> () -> a1 ->
                                 Allocator__PhysReg -> Prelude.Int -> () ->
                                 () -> a1) -> (Allocator__PhysReg ->
                                 Prelude.Int -> () -> Fin0.Coq_fin -> () ->
                                 a1 -> Allocator__PhysReg -> Prelude.Int ->
                                 () -> () -> a1) -> Allocator__PhysReg -> a1
_Allocator__findRegister_rect registerIndex f f0 f1 f2 f3 start =
  Logic.eq_rect_r
    (case registerIndex start of {
      Prelude.Just pos ->
       case Fin0.pred_fin _MyMachine__maxReg start of {
        Prelude.Just nreg ->
         case _Allocator__findRegister registerIndex nreg of {
          (,) reg o ->
           case o of {
            Prelude.Just pos' ->
             case NPeano.ltb pos pos' of {
              Prelude.True -> (,) reg (Prelude.Just pos');
              Prelude.False -> (,) reg (Prelude.Just pos)};
            Prelude.Nothing -> (,) reg Prelude.Nothing}};
        Prelude.Nothing -> (,) start (Prelude.Just pos)};
      Prelude.Nothing -> (,) start Prelude.Nothing})
    (let {f4 = f3 start} in
     let {f5 = f2 start} in
     let {f6 = f1 start} in
     let {f7 = f0 start} in
     let {f8 = f start} in
     case registerIndex start of {
      Prelude.Just n ->
       let {f9 = f7 n __} in
       let {f10 = f6 n __} in
       let {f11 = f5 n __} in
       let {f12 = f4 n __} in
       case Fin0.pred_fin _MyMachine__maxReg start of {
        Prelude.Just f13 ->
         let {f14 = f12 f13 __} in
         let {f15 = f11 f13 __} in
         let {f16 = f10 f13 __} in
         case _Allocator__findRegister registerIndex f13 of {
          (,) p o ->
           case o of {
            Prelude.Just n0 ->
             let {f17 = \h -> f14 h p n0 __} in
             let {f18 = \h -> f15 h p n0 __} in
             case NPeano.ltb n n0 of {
              Prelude.True ->
               let {f19 = \h -> f18 h __} in
               let {
                hrec = Logic.eq_rect o
                         (Logic.eq_rect
                           (_Allocator__findRegister registerIndex f13)
                           (_Allocator__findRegister_rect registerIndex f f0
                             f1 f2 f3 f13) ((,) p o)) (Prelude.Just n0)}
               in
               f19 hrec;
              Prelude.False ->
               let {f19 = \h -> f17 h __} in
               let {
                hrec = Logic.eq_rect o
                         (Logic.eq_rect
                           (_Allocator__findRegister registerIndex f13)
                           (_Allocator__findRegister_rect registerIndex f f0
                             f1 f2 f3 f13) ((,) p o)) (Prelude.Just n0)}
               in
               f19 hrec};
            Prelude.Nothing ->
             let {f17 = \h -> f16 h p __} in
             let {
              hrec = Logic.eq_rect o
                       (Logic.eq_rect
                         (_Allocator__findRegister registerIndex f13)
                         (_Allocator__findRegister_rect registerIndex f f0 f1
                           f2 f3 f13) ((,) p o)) Prelude.Nothing}
             in
             f17 hrec}};
        Prelude.Nothing -> f9 __};
      Prelude.Nothing -> f8 __})
    (_Allocator__findRegister registerIndex start)

_Allocator__findRegister_rec :: (Allocator__PhysReg -> Prelude.Maybe
                                Prelude.Int) -> (Allocator__PhysReg -> () ->
                                a1) -> (Allocator__PhysReg -> Prelude.Int ->
                                () -> () -> a1) -> (Allocator__PhysReg ->
                                Prelude.Int -> () -> Fin0.Coq_fin -> () -> a1
                                -> Allocator__PhysReg -> () -> a1) ->
                                (Allocator__PhysReg -> Prelude.Int -> () ->
                                Fin0.Coq_fin -> () -> a1 ->
                                Allocator__PhysReg -> Prelude.Int -> () -> ()
                                -> a1) -> (Allocator__PhysReg -> Prelude.Int
                                -> () -> Fin0.Coq_fin -> () -> a1 ->
                                Allocator__PhysReg -> Prelude.Int -> () -> ()
                                -> a1) -> Allocator__PhysReg -> a1
_Allocator__findRegister_rec registerIndex =
  _Allocator__findRegister_rect registerIndex

_Allocator__coq_R_findRegister_correct :: (Allocator__PhysReg ->
                                          Prelude.Maybe Prelude.Int) ->
                                          Allocator__PhysReg -> ((,)
                                          Allocator__PhysReg
                                          (Prelude.Maybe Prelude.Int)) ->
                                          Allocator__R_findRegister
_Allocator__coq_R_findRegister_correct x x0 res =
  _Allocator__findRegister_rect x (\y _ z _ ->
    Logic.eq_rec_r ((,) y Prelude.Nothing) (Allocator__R_findRegister_0 y) z)
    (\y y0 _ _ z _ ->
    Logic.eq_rec_r ((,) y (Prelude.Just y0)) (Allocator__R_findRegister_1 y
      y0) z) (\y y0 _ y2 _ y4 y5 _ z _ ->
    Logic.eq_rec_r ((,) y5 Prelude.Nothing) (Allocator__R_findRegister_2 y y0
      y2 (_Allocator__findRegister x y2)
      (y4 (_Allocator__findRegister x y2) __) y5) z)
    (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r ((,) y5 (Prelude.Just y6)) (Allocator__R_findRegister_3 y
      y0 y2 (_Allocator__findRegister x y2)
      (y4 (_Allocator__findRegister x y2) __) y5 y6) z)
    (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r ((,) y5 (Prelude.Just y0)) (Allocator__R_findRegister_4 y
      y0 y2 (_Allocator__findRegister x y2)
      (y4 (_Allocator__findRegister x y2) __) y5 y6) z) x0 res __

_Allocator__splitInterval :: Allocator__ScanStateDesc ->
                             Allocator__ScanStateCursor -> (Prelude.Maybe
                             Prelude.Int) -> Allocator__NextState
_Allocator__splitInterval sd cur before =
  sd

_Allocator__cursorFromMorphLen :: Allocator__ScanStateDesc ->
                                  Allocator__ScanStateCursor ->
                                  Allocator__NextState ->
                                  Allocator__ScanStateCursor
_Allocator__cursorFromMorphLen sd cur n =
  cur

_Allocator__cursorFromMorphStLen :: Allocator__ScanStateDesc ->
                                    Allocator__ScanStateCursor ->
                                    Allocator__NextState ->
                                    Allocator__ScanStateCursor
_Allocator__cursorFromMorphStLen sd cur n =
  _Allocator__cursorFromMorphLen sd cur (_Allocator__nextDesc n)

_Allocator__tryAllocateFreeReg :: Allocator__ScanStateDesc ->
                                  Allocator__ScanStateCursor -> Prelude.Maybe
                                  Allocator__NextState
_Allocator__tryAllocateFreeReg sd cur =
  let {
   freeUntilPos' = _Allocator__getRegisterIndex sd (\x -> Prelude.Just 0)
                     (\x -> Prelude.Nothing) (_Allocator__active sd)}
  in
  let {
   intersectingIntervals = (Prelude.filter) (\x ->
                             Interval.anyRangeIntersects
                               (
                                 (_Allocator__getInterval sd
                                   (_Allocator__curId sd cur)))
                               ( (_Allocator__getInterval sd x)))
                             (_Allocator__inactive sd)}
  in
  let {
   freeUntilPos = _Allocator__getRegisterIndex sd
                    (_Allocator__nextIntersectionWith
                      (
                        (_Allocator__getInterval sd
                          (_Allocator__curId sd cur))) sd) freeUntilPos'
                    intersectingIntervals}
  in
  let {lastReg = Fin0.ultimate_from_nat _Allocator__maxReg} in
  case _Allocator__findRegister freeUntilPos lastReg of {
   (,) reg mres ->
    let {default0 = _Allocator__moveUnhandledToActive sd cur reg} in
    case mres of {
     Prelude.Just n ->
      case EqNat.beq_nat n 0 of {
       Prelude.True -> Prelude.Nothing;
       Prelude.False -> Prelude.Just
        (case NPeano.ltb
                (Interval.intervalEnd
                  ( (_Allocator__getInterval sd (_Allocator__curId sd cur))))
                n of {
          Prelude.True -> default0;
          Prelude.False ->
           _Allocator__moveUnhandledToActive
             (_Allocator__nextDesc
               (_Allocator__splitInterval sd cur (Prelude.Just n)))
             (_Allocator__cursorFromMorphStLen sd cur
               (_Allocator__splitInterval sd cur (Prelude.Just n))) reg})};
     Prelude.Nothing -> Prelude.Just default0}}

_Allocator__nextUseAfter :: Prelude.Int -> Allocator__ScanStateDesc ->
                            Allocator__IntervalId -> Prelude.Maybe
                            Prelude.Int
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

_Allocator__checkActiveIntervals :: Allocator__ScanStateDesc -> Prelude.Int
                                    -> Allocator__NextScanState
_Allocator__checkActiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       ( (_Allocator__getInterval sd0 ( x)))) pos0 of {
               Prelude.True -> _Allocator__moveActiveToHandled sd0 ( x);
               Prelude.False ->
                case (Prelude.not)
                       (Interval.intervalCoversPos
                         ( (_Allocator__getInterval sd0 ( x))) pos0) of {
                 Prelude.True -> _Allocator__moveActiveToInactive sd0 ( x);
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_Allocator__active sd)) pos

_Allocator__checkInactiveIntervals :: Allocator__ScanStateDesc -> Prelude.Int
                                      -> Allocator__NextScanState
_Allocator__checkInactiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       ( (_Allocator__getInterval sd0 ( x)))) pos0 of {
               Prelude.True -> _Allocator__moveInactiveToHandled sd0 ( x);
               Prelude.False ->
                case Interval.intervalCoversPos
                       ( (_Allocator__getInterval sd0 ( x))) pos0 of {
                 Prelude.True -> _Allocator__moveInactiveToActive sd0 ( x);
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_Allocator__inactive sd)) pos

_Allocator__handleInterval :: Allocator__ScanStateDesc ->
                              Allocator__ScanStateCursor ->
                              Allocator__NextState
_Allocator__handleInterval sd cur =
  let {position = _Allocator__curPosition sd cur} in
  let {sp1 = _Allocator__checkActiveIntervals sd position} in
  let {
   sp2 = _Allocator__checkInactiveIntervals (_Allocator__nextDesc sp1)
           position}
  in
  let {cursor = _Allocator__curIntDesc sd cur} in
  let {
   result = Lib.fromMaybe
              (_Allocator__allocateBlockedReg (_Allocator__nextDesc sp2)
                cursor)
              (_Allocator__tryAllocateFreeReg (_Allocator__nextDesc sp2)
                cursor)}
  in
  _Allocator__nextDesc result

_Allocator__linearScan_F :: (Allocator__ScanStateDesc -> () ->
                            Allocator__ScanStateDesc) ->
                            Allocator__ScanStateDesc ->
                            Allocator__ScanStateDesc
_Allocator__linearScan_F linearScan0 sd =
  case List0.destruct_list (_Allocator__unhandled sd) of {
   Specif.Coq_inleft s ->
    case s of {
     Specif.Coq_existT x s0 ->
      linearScan0
        (_Allocator__handleInterval sd ( (_Allocator__getInterval sd x))) __};
   Specif.Coq_inright -> Specif.sig_of_sigT (Specif.Coq_existT sd __)}

_Allocator__linearScan_terminate :: Allocator__ScanStateDesc ->
                                    Allocator__ScanStateDesc
_Allocator__linearScan_terminate sd =
  case List0.destruct_list (_Allocator__unhandled sd) of {
   Specif.Coq_inleft s ->
    case s of {
     Specif.Coq_existT x s0 ->
      Specif.sig_rec (\rec_res _ -> rec_res)
        (_Allocator__linearScan_terminate
          (_Allocator__handleInterval sd ( (_Allocator__getInterval sd x))))};
   Specif.Coq_inright -> Specif.sig_of_sigT (Specif.Coq_existT sd __)}

_Allocator__linearScan :: Allocator__ScanStateDesc ->
                          Allocator__ScanStateDesc
_Allocator__linearScan sd =
  case List0.destruct_list (_Allocator__unhandled sd) of {
   Specif.Coq_inleft s ->
    case s of {
     Specif.Coq_existT x s0 ->
      Specif.sig_rec (\rec_res _ -> rec_res)
        (_Allocator__linearScan
          (_Allocator__handleInterval sd ( (_Allocator__getInterval sd x))))};
   Specif.Coq_inright -> Specif.sig_of_sigT (Specif.Coq_existT sd __)}

data Allocator__R_linearScan =
   Allocator__R_linearScan_0 Allocator__ScanStateDesc Allocator__IntervalId 
 ([] Allocator__IntervalId) Allocator__ScanStateDesc Allocator__ScanStateDesc 
 Allocator__R_linearScan
 | Allocator__R_linearScan_1 Allocator__ScanStateDesc

_Allocator__coq_R_linearScan_rect :: (Allocator__ScanStateDesc -> () ->
                                     Allocator__IntervalId -> ([]
                                     Allocator__IntervalId) -> () -> () ->
                                     Allocator__ScanStateDesc -> () -> () ->
                                     () -> Allocator__ScanStateDesc ->
                                     Allocator__R_linearScan -> a1 -> a1) ->
                                     (Allocator__ScanStateDesc -> () -> () ->
                                     () -> a1) -> Allocator__ScanStateDesc ->
                                     Allocator__ScanStateDesc ->
                                     Allocator__R_linearScan -> a1
_Allocator__coq_R_linearScan_rect f f0 sd s r =
  case r of {
   Allocator__R_linearScan_0 sd0 x xs x0 x1 x2 ->
    f sd0 __ x xs __ __ x0 __ __ __ x1 x2
      (_Allocator__coq_R_linearScan_rect f f0 x0 x1 x2);
   Allocator__R_linearScan_1 sd0 -> f0 sd0 __ __ __}

_Allocator__coq_R_linearScan_rec :: (Allocator__ScanStateDesc -> () ->
                                    Allocator__IntervalId -> ([]
                                    Allocator__IntervalId) -> () -> () ->
                                    Allocator__ScanStateDesc -> () -> () ->
                                    () -> Allocator__ScanStateDesc ->
                                    Allocator__R_linearScan -> a1 -> a1) ->
                                    (Allocator__ScanStateDesc -> () -> () ->
                                    () -> a1) -> Allocator__ScanStateDesc ->
                                    Allocator__ScanStateDesc ->
                                    Allocator__R_linearScan -> a1
_Allocator__coq_R_linearScan_rec f f0 sd s r =
  _Allocator__coq_R_linearScan_rect f f0 sd s r

type Allocator__VirtReg = Prelude.Int

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
                                  Allocator__ScanStateDesc
_Allocator__determineIntervals =
  Prelude.error "AXIOM TO BE REALIZED"

_Allocator__allocateRegisters :: (Allocator__Graph Allocator__VirtReg) ->
                                 Allocator__ScanStateDesc
_Allocator__allocateRegisters g =
   (_Allocator__linearScan (_Allocator__determineIntervals g))

