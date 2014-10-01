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

_LinearScan__maxReg :: Prelude.Int
_LinearScan__maxReg =
  _MyMachine__maxReg

type LinearScan__PhysReg = Fin0.Coq_fin

data LinearScan__ScanStateDesc =
   LinearScan__Build_ScanStateDesc Prelude.Int ([] Fin0.Coq_fin) ([]
                                                                 Fin0.Coq_fin) 
 ([] Fin0.Coq_fin) ([] Fin0.Coq_fin) (Fin0.Coq_fin -> Interval.IntervalDesc) 
 (Fin0.Coq_fin -> Prelude.Maybe LinearScan__PhysReg) (LinearScan__PhysReg ->
                                                     Prelude.Maybe
                                                     Interval.IntervalDesc)

_LinearScan__coq_ScanStateDesc_rect :: (Prelude.Int -> ([] Fin0.Coq_fin) ->
                                       ([] Fin0.Coq_fin) -> ([] Fin0.Coq_fin)
                                       -> ([] Fin0.Coq_fin) -> (Fin0.Coq_fin
                                       -> Interval.IntervalDesc) ->
                                       (Fin0.Coq_fin -> Prelude.Maybe
                                       LinearScan__PhysReg) ->
                                       (LinearScan__PhysReg -> Prelude.Maybe
                                       Interval.IntervalDesc) -> () -> a1) ->
                                       LinearScan__ScanStateDesc -> a1
_LinearScan__coq_ScanStateDesc_rect f s =
  case s of {
   LinearScan__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6 __}

_LinearScan__coq_ScanStateDesc_rec :: (Prelude.Int -> ([] Fin0.Coq_fin) ->
                                      ([] Fin0.Coq_fin) -> ([] Fin0.Coq_fin)
                                      -> ([] Fin0.Coq_fin) -> (Fin0.Coq_fin
                                      -> Interval.IntervalDesc) ->
                                      (Fin0.Coq_fin -> Prelude.Maybe
                                      LinearScan__PhysReg) ->
                                      (LinearScan__PhysReg -> Prelude.Maybe
                                      Interval.IntervalDesc) -> () -> a1) ->
                                      LinearScan__ScanStateDesc -> a1
_LinearScan__coq_ScanStateDesc_rec =
  _LinearScan__coq_ScanStateDesc_rect

_LinearScan__nextInterval :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__nextInterval s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> nextInterval0}

type LinearScan__IntervalId = Fin0.Coq_fin

_LinearScan__unhandled :: LinearScan__ScanStateDesc -> []
                          LinearScan__IntervalId
_LinearScan__unhandled s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> unhandled0}

_LinearScan__active :: LinearScan__ScanStateDesc -> [] LinearScan__IntervalId
_LinearScan__active s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> active0}

_LinearScan__inactive :: LinearScan__ScanStateDesc -> []
                         LinearScan__IntervalId
_LinearScan__inactive s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> inactive0}

_LinearScan__handled :: LinearScan__ScanStateDesc -> []
                        LinearScan__IntervalId
_LinearScan__handled s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> handled0}

_LinearScan__getInterval :: LinearScan__ScanStateDesc ->
                            LinearScan__IntervalId -> Interval.IntervalDesc
_LinearScan__getInterval s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getInterval0}

_LinearScan__assignments :: LinearScan__ScanStateDesc ->
                            LinearScan__IntervalId -> Prelude.Maybe
                            LinearScan__PhysReg
_LinearScan__assignments s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> assignments0}

_LinearScan__getFixedInterval :: LinearScan__ScanStateDesc ->
                                 LinearScan__PhysReg -> Prelude.Maybe
                                 Interval.IntervalDesc
_LinearScan__getFixedInterval s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getFixedInterval0}

_LinearScan__all_state_lists :: LinearScan__ScanStateDesc -> []
                                LinearScan__IntervalId
_LinearScan__all_state_lists s =
  (Prelude.++) (_LinearScan__unhandled s)
    ((Prelude.++) (_LinearScan__active s)
      ((Prelude.++) (_LinearScan__inactive s) (_LinearScan__handled s)))

_LinearScan__transportId :: LinearScan__ScanStateDesc ->
                            LinearScan__ScanStateDesc ->
                            LinearScan__IntervalId -> LinearScan__IntervalId
_LinearScan__transportId sd sd' x =
  let {
   h = Compare_dec.le_lt_eq_dec (_LinearScan__nextInterval sd)
         (_LinearScan__nextInterval sd')}
  in
  case h of {
   Specif.Coq_left ->
    case sd of {
     LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0
      inactive0 handled0 getInterval0 assignments0 getFixedInterval0 ->
      case sd' of {
       LinearScan__Build_ScanStateDesc nextInterval1 unhandled1 active1
        inactive1 handled1 getInterval1 assignments1 getFixedInterval1 ->
        let {h0 = Lib.lt_sub nextInterval0 nextInterval1} in
        Logic.eq_rec ((Prelude.+) h0 nextInterval0)
          (Fin.coq_R nextInterval0 h0 x) nextInterval1}};
   Specif.Coq_right ->
    Logic.eq_rec (_LinearScan__nextInterval sd) x
      (_LinearScan__nextInterval sd')}

_LinearScan__unhandledExtent :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__unhandledExtent sd =
  case _LinearScan__unhandled sd of {
   [] -> 0;
   (:) i l ->
    case l of {
     [] -> Interval.intervalExtent ( (_LinearScan__getInterval sd i));
     (:) i0 l0 ->
      let {
       f = \n x ->
        (Prelude.+) n
          (Interval.intervalExtent ( (_LinearScan__getInterval sd x)))}
      in
      (\f -> Prelude.flip (Data.List.foldl' f)) f ((:) i ((:) i0 l0)) 0}}

data LinearScan__ScanStateCursor =
   LinearScan__Build_ScanStateCursor

_LinearScan__coq_ScanStateCursor_rect :: LinearScan__ScanStateDesc -> (() ->
                                         () -> a1) -> a1
_LinearScan__coq_ScanStateCursor_rect sd f =
  f __ __

_LinearScan__coq_ScanStateCursor_rec :: LinearScan__ScanStateDesc -> (() ->
                                        () -> a1) -> a1
_LinearScan__coq_ScanStateCursor_rec sd f =
  _LinearScan__coq_ScanStateCursor_rect sd f

_LinearScan__curId :: LinearScan__ScanStateDesc -> LinearScan__IntervalId
_LinearScan__curId sd =
  Lib.safe_hd (_LinearScan__unhandled sd)

_LinearScan__curIntDetails :: LinearScan__ScanStateDesc ->
                              Interval.IntervalDesc
_LinearScan__curIntDetails sd =
  _LinearScan__getInterval sd (_LinearScan__curId sd)

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

_LinearScan__coq_NextScanState_transitivity :: LinearScan__ScanStateDesc ->
                                               LinearScan__NextScanState ->
                                               LinearScan__NextScanState ->
                                               LinearScan__NextScanState
_LinearScan__coq_NextScanState_transitivity sd0 n o =
  o

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

_LinearScan__coq_SSMorphStLen_rect :: LinearScan__ScanStateDesc ->
                                      LinearScan__ScanStateDesc -> (() -> ()
                                      -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphStLen_rec :: LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc -> (() -> ()
                                     -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphStLen_rect sd1 sd2 f

_LinearScan__moveUnhandledToActive :: LinearScan__ScanStateDesc ->
                                      LinearScan__PhysReg ->
                                      LinearScan__NextState
_LinearScan__moveUnhandledToActive sd reg =
  case sd of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 ->
    case unhandled0 of {
     [] -> Logic.coq_False_rec;
     (:) i unhandled1 -> LinearScan__Build_ScanStateDesc nextInterval0
      unhandled1 ((:) i active0) inactive0 handled0 getInterval0 (\i0 ->
      case Compare.cmp_eq_dec (Fin0.fin_CompareSpec nextInterval0) i0 i of {
       Specif.Coq_left -> Prelude.Just reg;
       Specif.Coq_right -> assignments0 i0}) getFixedInterval0}}

_LinearScan__moveActiveToHandled :: LinearScan__ScanStateDesc ->
                                    LinearScan__IntervalId ->
                                    LinearScan__NextScanState
_LinearScan__moveActiveToHandled sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__active sd)) ((:) x (_LinearScan__inactive sd))
    (_LinearScan__handled sd) (_LinearScan__getInterval sd)
    (_LinearScan__assignments sd) (_LinearScan__getFixedInterval sd)

_LinearScan__moveActiveToInactive :: LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId ->
                                     LinearScan__NextScanState
_LinearScan__moveActiveToInactive sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__active sd)) ((:) x (_LinearScan__inactive sd))
    (_LinearScan__handled sd) (_LinearScan__getInterval sd)
    (_LinearScan__assignments sd) (_LinearScan__getFixedInterval sd)

_LinearScan__moveInactiveToActive :: LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId ->
                                     LinearScan__NextScanState
_LinearScan__moveInactiveToActive sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd) ((:) x (_LinearScan__active sd))
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__inactive sd)) (_LinearScan__handled sd)
    (_LinearScan__getInterval sd) (_LinearScan__assignments sd)
    (_LinearScan__getFixedInterval sd)

_LinearScan__moveInactiveToHandled :: LinearScan__ScanStateDesc ->
                                      LinearScan__IntervalId ->
                                      LinearScan__NextScanState
_LinearScan__moveInactiveToHandled sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd) (_LinearScan__active sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__inactive sd)) ((:) x (_LinearScan__handled sd))
    (_LinearScan__getInterval sd) (_LinearScan__assignments sd)
    (_LinearScan__getFixedInterval sd)

_LinearScan__nextIntersectionWith :: Interval.IntervalDesc ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId -> Prelude.Maybe
                                     Prelude.Int
_LinearScan__nextIntersectionWith d sd jid =
  Interval.firstIntersectionPoint ( (_LinearScan__getInterval sd jid)) d

_LinearScan__getRegisterIndex :: LinearScan__ScanStateDesc ->
                                 (LinearScan__IntervalId -> Prelude.Maybe
                                 Prelude.Int) -> (LinearScan__PhysReg ->
                                 Prelude.Maybe Prelude.Int) -> ([]
                                 LinearScan__IntervalId) ->
                                 LinearScan__PhysReg -> Prelude.Maybe
                                 Prelude.Int
_LinearScan__getRegisterIndex sd intervalIndex registerIndex intervals =
  Prelude.foldr (\x f r ->
    case _LinearScan__assignments sd x of {
     Prelude.Just a ->
      case Compare.cmp_eq_dec (Fin0.fin_CompareSpec _LinearScan__maxReg) a r of {
       Specif.Coq_left -> intervalIndex x;
       Specif.Coq_right -> f r};
     Prelude.Nothing -> f r}) registerIndex intervals

_LinearScan__findRegister_F :: ((LinearScan__PhysReg -> Prelude.Maybe
                               Prelude.Int) -> LinearScan__PhysReg -> (,)
                               LinearScan__PhysReg
                               (Prelude.Maybe Prelude.Int)) ->
                               (LinearScan__PhysReg -> Prelude.Maybe
                               Prelude.Int) -> LinearScan__PhysReg -> (,)
                               LinearScan__PhysReg
                               (Prelude.Maybe Prelude.Int)
_LinearScan__findRegister_F findRegister0 registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _LinearScan__maxReg start of {
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

_LinearScan__findRegister_terminate :: (LinearScan__PhysReg -> Prelude.Maybe
                                       Prelude.Int) -> LinearScan__PhysReg ->
                                       ((,) LinearScan__PhysReg
                                       (Prelude.Maybe Prelude.Int))
_LinearScan__findRegister_terminate registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _LinearScan__maxReg start of {
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
        (_LinearScan__findRegister_terminate registerIndex nreg);
     Prelude.Nothing -> (,) start (Prelude.Just pos)};
   Prelude.Nothing -> (,) start Prelude.Nothing}

_LinearScan__findRegister :: (LinearScan__PhysReg -> Prelude.Maybe
                             Prelude.Int) -> LinearScan__PhysReg -> (,)
                             LinearScan__PhysReg (Prelude.Maybe Prelude.Int)
_LinearScan__findRegister registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _LinearScan__maxReg start of {
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
        (_LinearScan__findRegister registerIndex nreg);
     Prelude.Nothing -> (,) start (Prelude.Just pos)};
   Prelude.Nothing -> (,) start Prelude.Nothing}

data LinearScan__R_findRegister =
   LinearScan__R_findRegister_0 LinearScan__PhysReg
 | LinearScan__R_findRegister_1 LinearScan__PhysReg Prelude.Int
 | LinearScan__R_findRegister_2 LinearScan__PhysReg Prelude.Int Fin0.Coq_fin 
 ((,) LinearScan__PhysReg (Prelude.Maybe Prelude.Int)) LinearScan__R_findRegister 
 LinearScan__PhysReg
 | LinearScan__R_findRegister_3 LinearScan__PhysReg Prelude.Int Fin0.Coq_fin 
 ((,) LinearScan__PhysReg (Prelude.Maybe Prelude.Int)) LinearScan__R_findRegister 
 LinearScan__PhysReg Prelude.Int
 | LinearScan__R_findRegister_4 LinearScan__PhysReg Prelude.Int Fin0.Coq_fin 
 ((,) LinearScan__PhysReg (Prelude.Maybe Prelude.Int)) LinearScan__R_findRegister 
 LinearScan__PhysReg Prelude.Int

_LinearScan__coq_R_findRegister_rect :: (LinearScan__PhysReg -> Prelude.Maybe
                                        Prelude.Int) -> (LinearScan__PhysReg
                                        -> () -> a1) -> (LinearScan__PhysReg
                                        -> Prelude.Int -> () -> () -> a1) ->
                                        (LinearScan__PhysReg -> Prelude.Int
                                        -> () -> Fin0.Coq_fin -> () -> ((,)
                                        LinearScan__PhysReg
                                        (Prelude.Maybe Prelude.Int)) ->
                                        LinearScan__R_findRegister -> a1 ->
                                        LinearScan__PhysReg -> () -> a1) ->
                                        (LinearScan__PhysReg -> Prelude.Int
                                        -> () -> Fin0.Coq_fin -> () -> ((,)
                                        LinearScan__PhysReg
                                        (Prelude.Maybe Prelude.Int)) ->
                                        LinearScan__R_findRegister -> a1 ->
                                        LinearScan__PhysReg -> Prelude.Int ->
                                        () -> () -> a1) ->
                                        (LinearScan__PhysReg -> Prelude.Int
                                        -> () -> Fin0.Coq_fin -> () -> ((,)
                                        LinearScan__PhysReg
                                        (Prelude.Maybe Prelude.Int)) ->
                                        LinearScan__R_findRegister -> a1 ->
                                        LinearScan__PhysReg -> Prelude.Int ->
                                        () -> () -> a1) ->
                                        LinearScan__PhysReg -> ((,)
                                        LinearScan__PhysReg
                                        (Prelude.Maybe Prelude.Int)) ->
                                        LinearScan__R_findRegister -> a1
_LinearScan__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 start p r =
  case r of {
   LinearScan__R_findRegister_0 start0 -> f start0 __;
   LinearScan__R_findRegister_1 start0 pos -> f0 start0 pos __ __;
   LinearScan__R_findRegister_2 start0 pos nreg res r0 reg ->
    f1 start0 pos __ nreg __ res r0
      (_LinearScan__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg
        res r0) reg __;
   LinearScan__R_findRegister_3 start0 pos nreg res r0 reg pos' ->
    f2 start0 pos __ nreg __ res r0
      (_LinearScan__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg
        res r0) reg pos' __ __;
   LinearScan__R_findRegister_4 start0 pos nreg res r0 reg pos' ->
    f3 start0 pos __ nreg __ res r0
      (_LinearScan__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg
        res r0) reg pos' __ __}

_LinearScan__coq_R_findRegister_rec :: (LinearScan__PhysReg -> Prelude.Maybe
                                       Prelude.Int) -> (LinearScan__PhysReg
                                       -> () -> a1) -> (LinearScan__PhysReg
                                       -> Prelude.Int -> () -> () -> a1) ->
                                       (LinearScan__PhysReg -> Prelude.Int ->
                                       () -> Fin0.Coq_fin -> () -> ((,)
                                       LinearScan__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
                                       LinearScan__R_findRegister -> a1 ->
                                       LinearScan__PhysReg -> () -> a1) ->
                                       (LinearScan__PhysReg -> Prelude.Int ->
                                       () -> Fin0.Coq_fin -> () -> ((,)
                                       LinearScan__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
                                       LinearScan__R_findRegister -> a1 ->
                                       LinearScan__PhysReg -> Prelude.Int ->
                                       () -> () -> a1) ->
                                       (LinearScan__PhysReg -> Prelude.Int ->
                                       () -> Fin0.Coq_fin -> () -> ((,)
                                       LinearScan__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
                                       LinearScan__R_findRegister -> a1 ->
                                       LinearScan__PhysReg -> Prelude.Int ->
                                       () -> () -> a1) -> LinearScan__PhysReg
                                       -> ((,) LinearScan__PhysReg
                                       (Prelude.Maybe Prelude.Int)) ->
                                       LinearScan__R_findRegister -> a1
_LinearScan__coq_R_findRegister_rec registerIndex =
  _LinearScan__coq_R_findRegister_rect registerIndex

_LinearScan__findRegister_rect :: (LinearScan__PhysReg -> Prelude.Maybe
                                  Prelude.Int) -> (LinearScan__PhysReg -> ()
                                  -> a1) -> (LinearScan__PhysReg ->
                                  Prelude.Int -> () -> () -> a1) ->
                                  (LinearScan__PhysReg -> Prelude.Int -> ()
                                  -> Fin0.Coq_fin -> () -> a1 ->
                                  LinearScan__PhysReg -> () -> a1) ->
                                  (LinearScan__PhysReg -> Prelude.Int -> ()
                                  -> Fin0.Coq_fin -> () -> a1 ->
                                  LinearScan__PhysReg -> Prelude.Int -> () ->
                                  () -> a1) -> (LinearScan__PhysReg ->
                                  Prelude.Int -> () -> Fin0.Coq_fin -> () ->
                                  a1 -> LinearScan__PhysReg -> Prelude.Int ->
                                  () -> () -> a1) -> LinearScan__PhysReg ->
                                  a1
_LinearScan__findRegister_rect registerIndex f f0 f1 f2 f3 start =
  Logic.eq_rect_r
    (case registerIndex start of {
      Prelude.Just pos ->
       case Fin0.pred_fin _LinearScan__maxReg start of {
        Prelude.Just nreg ->
         case _LinearScan__findRegister registerIndex nreg of {
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
       case Fin0.pred_fin _LinearScan__maxReg start of {
        Prelude.Just f13 ->
         let {f14 = f12 f13 __} in
         let {f15 = f11 f13 __} in
         let {f16 = f10 f13 __} in
         case _LinearScan__findRegister registerIndex f13 of {
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
                           (_LinearScan__findRegister registerIndex f13)
                           (_LinearScan__findRegister_rect registerIndex f f0
                             f1 f2 f3 f13) ((,) p o)) (Prelude.Just n0)}
               in
               f19 hrec;
              Prelude.False ->
               let {f19 = \h -> f17 h __} in
               let {
                hrec = Logic.eq_rect o
                         (Logic.eq_rect
                           (_LinearScan__findRegister registerIndex f13)
                           (_LinearScan__findRegister_rect registerIndex f f0
                             f1 f2 f3 f13) ((,) p o)) (Prelude.Just n0)}
               in
               f19 hrec};
            Prelude.Nothing ->
             let {f17 = \h -> f16 h p __} in
             let {
              hrec = Logic.eq_rect o
                       (Logic.eq_rect
                         (_LinearScan__findRegister registerIndex f13)
                         (_LinearScan__findRegister_rect registerIndex f f0
                           f1 f2 f3 f13) ((,) p o)) Prelude.Nothing}
             in
             f17 hrec}};
        Prelude.Nothing -> f9 __};
      Prelude.Nothing -> f8 __})
    (_LinearScan__findRegister registerIndex start)

_LinearScan__findRegister_rec :: (LinearScan__PhysReg -> Prelude.Maybe
                                 Prelude.Int) -> (LinearScan__PhysReg -> ()
                                 -> a1) -> (LinearScan__PhysReg ->
                                 Prelude.Int -> () -> () -> a1) ->
                                 (LinearScan__PhysReg -> Prelude.Int -> () ->
                                 Fin0.Coq_fin -> () -> a1 ->
                                 LinearScan__PhysReg -> () -> a1) ->
                                 (LinearScan__PhysReg -> Prelude.Int -> () ->
                                 Fin0.Coq_fin -> () -> a1 ->
                                 LinearScan__PhysReg -> Prelude.Int -> () ->
                                 () -> a1) -> (LinearScan__PhysReg ->
                                 Prelude.Int -> () -> Fin0.Coq_fin -> () ->
                                 a1 -> LinearScan__PhysReg -> Prelude.Int ->
                                 () -> () -> a1) -> LinearScan__PhysReg -> a1
_LinearScan__findRegister_rec registerIndex =
  _LinearScan__findRegister_rect registerIndex

_LinearScan__coq_R_findRegister_correct :: (LinearScan__PhysReg ->
                                           Prelude.Maybe Prelude.Int) ->
                                           LinearScan__PhysReg -> ((,)
                                           LinearScan__PhysReg
                                           (Prelude.Maybe Prelude.Int)) ->
                                           LinearScan__R_findRegister
_LinearScan__coq_R_findRegister_correct x x0 res =
  _LinearScan__findRegister_rect x (\y _ z _ ->
    Logic.eq_rec_r ((,) y Prelude.Nothing) (LinearScan__R_findRegister_0 y) z)
    (\y y0 _ _ z _ ->
    Logic.eq_rec_r ((,) y (Prelude.Just y0)) (LinearScan__R_findRegister_1 y
      y0) z) (\y y0 _ y2 _ y4 y5 _ z _ ->
    Logic.eq_rec_r ((,) y5 Prelude.Nothing) (LinearScan__R_findRegister_2 y
      y0 y2 (_LinearScan__findRegister x y2)
      (y4 (_LinearScan__findRegister x y2) __) y5) z)
    (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r ((,) y5 (Prelude.Just y6)) (LinearScan__R_findRegister_3 y
      y0 y2 (_LinearScan__findRegister x y2)
      (y4 (_LinearScan__findRegister x y2) __) y5 y6) z)
    (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r ((,) y5 (Prelude.Just y0)) (LinearScan__R_findRegister_4 y
      y0 y2 (_LinearScan__findRegister x y2)
      (y4 (_LinearScan__findRegister x y2) __) y5 y6) z) x0 res __

_LinearScan__splitInterval :: LinearScan__ScanStateDesc -> (Prelude.Maybe
                              Prelude.Int) -> LinearScan__NextState
_LinearScan__splitInterval sd before =
  sd

_LinearScan__tryAllocateFreeReg :: LinearScan__ScanStateDesc -> Prelude.Maybe
                                   LinearScan__NextState
_LinearScan__tryAllocateFreeReg sd =
  let {
   freeUntilPos' = _LinearScan__getRegisterIndex sd (\x -> Prelude.Just 0)
                     (\x -> Prelude.Nothing) (_LinearScan__active sd)}
  in
  let {
   intersectingIntervals = (Prelude.filter) (\x ->
                             Interval.anyRangeIntersects
                               ( (_LinearScan__curIntDetails sd))
                               ( (_LinearScan__getInterval sd x)))
                             (_LinearScan__inactive sd)}
  in
  let {
   freeUntilPos = _LinearScan__getRegisterIndex sd
                    (_LinearScan__nextIntersectionWith
                      ( (_LinearScan__curIntDetails sd)) sd) freeUntilPos'
                    intersectingIntervals}
  in
  let {lastReg = Fin0.ultimate_from_nat _LinearScan__maxReg} in
  case _LinearScan__findRegister freeUntilPos lastReg of {
   (,) reg mres ->
    let {default0 = _LinearScan__moveUnhandledToActive sd reg} in
    case mres of {
     Prelude.Just n ->
      case EqNat.beq_nat n 0 of {
       Prelude.True -> Prelude.Nothing;
       Prelude.False -> Prelude.Just
        (case NPeano.ltb
                (Interval.intervalEnd ( (_LinearScan__curIntDetails sd))) n of {
          Prelude.True -> default0;
          Prelude.False ->
           _LinearScan__moveUnhandledToActive
             (_LinearScan__nextDesc
               (_LinearScan__splitInterval sd (Prelude.Just n))) reg})};
     Prelude.Nothing -> Prelude.Just default0}}

_LinearScan__nextUseAfter :: Prelude.Int -> LinearScan__ScanStateDesc ->
                             LinearScan__IntervalId -> Prelude.Maybe
                             Prelude.Int
_LinearScan__nextUseAfter =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__assignSpillSlotToCurrent :: LinearScan__ScanStateDesc ->
                                         LinearScan__NextScanState
_LinearScan__assignSpillSlotToCurrent =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__allocateBlockedReg :: LinearScan__ScanStateDesc ->
                                   LinearScan__NextState
_LinearScan__allocateBlockedReg sd =
  Lib.undefined

_LinearScan__checkActiveIntervals :: LinearScan__ScanStateDesc -> Prelude.Int
                                     -> LinearScan__NextScanState
_LinearScan__checkActiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       ( (_LinearScan__getInterval sd0 ( x)))) pos0 of {
               Prelude.True ->
                Lib.uncurry_sig (\x0 _ ->
                  _LinearScan__moveActiveToHandled sd0 x0) x;
               Prelude.False ->
                case (Prelude.not)
                       (Interval.intervalCoversPos
                         ( (_LinearScan__getInterval sd0 ( x))) pos0) of {
                 Prelude.True ->
                  Lib.uncurry_sig (\x0 _ ->
                    _LinearScan__moveActiveToInactive sd0 x0) x;
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_LinearScan__active sd)) pos

_LinearScan__checkInactiveIntervals :: LinearScan__ScanStateDesc ->
                                       Prelude.Int ->
                                       LinearScan__NextScanState
_LinearScan__checkInactiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       ( (_LinearScan__getInterval sd0 ( x)))) pos0 of {
               Prelude.True ->
                Lib.uncurry_sig (\x0 _ ->
                  _LinearScan__moveInactiveToHandled sd0 x0) x;
               Prelude.False ->
                case Interval.intervalCoversPos
                       ( (_LinearScan__getInterval sd0 ( x))) pos0 of {
                 Prelude.True ->
                  Lib.uncurry_sig (\x0 _ ->
                    _LinearScan__moveInactiveToActive sd0 x0) x;
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_LinearScan__inactive sd)) pos

_LinearScan__handleInterval :: LinearScan__ScanStateDesc ->
                               LinearScan__NextState
_LinearScan__handleInterval sd =
  let {position = _LinearScan__curPosition sd} in
  let {sp1 = _LinearScan__checkActiveIntervals sd position} in
  let {
   sp2 = _LinearScan__checkInactiveIntervals (_LinearScan__nextDesc sp1)
           position}
  in
  let {
   result = Lib.fromMaybe
              (_LinearScan__allocateBlockedReg (_LinearScan__nextDesc sp2))
              (_LinearScan__tryAllocateFreeReg (_LinearScan__nextDesc sp2))}
  in
  _LinearScan__nextDesc result

_LinearScan__linearScan_F :: (LinearScan__ScanStateDesc -> () ->
                             LinearScan__ScanStateDesc) ->
                             LinearScan__ScanStateDesc ->
                             LinearScan__ScanStateDesc
_LinearScan__linearScan_F linearScan0 sd =
  case List0.destruct_list (_LinearScan__unhandled sd) of {
   Specif.Coq_inleft s -> linearScan0 (_LinearScan__handleInterval sd) __;
   Specif.Coq_inright -> sd}

_LinearScan__linearScan_terminate :: LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc
_LinearScan__linearScan_terminate sd =
  case List0.destruct_list (_LinearScan__unhandled sd) of {
   Specif.Coq_inleft s ->
    Specif.sig_rec (\rec_res _ -> rec_res)
      (_LinearScan__linearScan_terminate (_LinearScan__handleInterval sd));
   Specif.Coq_inright -> sd}

_LinearScan__linearScan :: LinearScan__ScanStateDesc ->
                           LinearScan__ScanStateDesc
_LinearScan__linearScan sd =
  case List0.destruct_list (_LinearScan__unhandled sd) of {
   Specif.Coq_inleft s ->
    Specif.sig_rec (\rec_res _ -> rec_res)
      (_LinearScan__linearScan (_LinearScan__handleInterval sd));
   Specif.Coq_inright -> sd}

data LinearScan__R_linearScan =
   LinearScan__R_linearScan_0 LinearScan__ScanStateDesc LinearScan__IntervalId 
 ([] LinearScan__IntervalId) LinearScan__ScanStateDesc LinearScan__ScanStateDesc 
 LinearScan__R_linearScan
 | LinearScan__R_linearScan_1 LinearScan__ScanStateDesc

_LinearScan__coq_R_linearScan_rect :: (LinearScan__ScanStateDesc -> () ->
                                      LinearScan__IntervalId -> ([]
                                      LinearScan__IntervalId) -> () -> () ->
                                      LinearScan__ScanStateDesc -> () -> ()
                                      -> () -> LinearScan__ScanStateDesc ->
                                      LinearScan__R_linearScan -> a1 -> a1)
                                      -> (LinearScan__ScanStateDesc -> () ->
                                      () -> () -> a1) ->
                                      LinearScan__ScanStateDesc ->
                                      LinearScan__ScanStateDesc ->
                                      LinearScan__R_linearScan -> a1
_LinearScan__coq_R_linearScan_rect f f0 sd s r =
  case r of {
   LinearScan__R_linearScan_0 sd0 x xs sd2 res r0 ->
    f sd0 __ x xs __ __ sd2 __ __ __ res r0
      (_LinearScan__coq_R_linearScan_rect f f0 sd2 res r0);
   LinearScan__R_linearScan_1 sd0 -> f0 sd0 __ __ __}

_LinearScan__coq_R_linearScan_rec :: (LinearScan__ScanStateDesc -> () ->
                                     LinearScan__IntervalId -> ([]
                                     LinearScan__IntervalId) -> () -> () ->
                                     LinearScan__ScanStateDesc -> () -> () ->
                                     () -> LinearScan__ScanStateDesc ->
                                     LinearScan__R_linearScan -> a1 -> a1) ->
                                     (LinearScan__ScanStateDesc -> () -> ()
                                     -> () -> a1) ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__R_linearScan -> a1
_LinearScan__coq_R_linearScan_rec f f0 sd s r =
  _LinearScan__coq_R_linearScan_rect f f0 sd s r

type LinearScan__VirtReg = Prelude.Int

type LinearScan__Graph a =
  a
  -- singleton inductive, whose constructor was Build_Graph
  
_LinearScan__coq_Graph_rect :: (a1 -> a2) -> (LinearScan__Graph a1) -> a2
_LinearScan__coq_Graph_rect f g =
  f g

_LinearScan__coq_Graph_rec :: (a1 -> a2) -> (LinearScan__Graph a1) -> a2
_LinearScan__coq_Graph_rec =
  _LinearScan__coq_Graph_rect

_LinearScan__postOrderTraversal :: (LinearScan__Graph a1) -> a1
_LinearScan__postOrderTraversal graph =
  graph

_LinearScan__determineIntervals :: (LinearScan__Graph LinearScan__VirtReg) ->
                                   LinearScan__ScanStateDesc
_LinearScan__determineIntervals =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__allocateRegisters :: (LinearScan__Graph LinearScan__VirtReg) ->
                                  LinearScan__ScanStateDesc
_LinearScan__allocateRegisters g =
  
    (Lib.uncurry_sig (\x _ -> _LinearScan__linearScan x)
      (_LinearScan__determineIntervals g))

