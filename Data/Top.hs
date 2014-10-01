module Data.Data.Top where

import qualified Prelude
import qualified Data.List
import qualified Data.Data.List as Data.List
import qualified Data.Data.Compare as Compare as Data.Compare as Compare
import qualified Data.Data.Compare_dec as Compare_dec as Data.Compare_dec as Compare_dec
import qualified Data.Data.EqNat as EqNat as Data.EqNat as EqNat
import qualified Data.Data.Fin0 as Fin0 as Data.Fin0 as Fin0
import qualified Data.Data.Fin as Fin as Data.Fin as Fin
import qualified Data.Data.Interval as Interval as Data.Interval as Interval
import qualified Data.Data.Lib as Lib as Data.Lib as Lib
import qualified Data.Data.List0 as List0 as Data.List0 as List0
import qualified Data.Data.Logic as Logic as Data.Logic as Logic
import qualified Data.Data.NPeano as NPeano as Data.NPeano as NPeano
import qualified Data.Data.Specif as Specif as Data.Specif as Specif


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

_Graph__maxReg :: Prelude.Int
_Graph__maxReg =
  _MyMachine__maxReg

type Graph__PhysReg = Fin0.Coq_fin

data Graph__ScanStateDesc =
   Graph__Build_ScanStateDesc Prelude.Int ([] Fin0.Coq_fin) ([] Fin0.Coq_fin) 
 ([] Fin0.Coq_fin) ([] Fin0.Coq_fin) (Fin0.Coq_fin -> Interval.IntervalDesc) 
 (Fin0.Coq_fin -> Prelude.Maybe Graph__PhysReg) (Graph__PhysReg ->
                                                Prelude.Maybe
                                                Interval.IntervalDesc)

_Graph__coq_ScanStateDesc_rect :: (Prelude.Int -> ([] Fin0.Coq_fin) -> ([]
                                  Fin0.Coq_fin) -> ([] Fin0.Coq_fin) -> ([]
                                  Fin0.Coq_fin) -> (Fin0.Coq_fin ->
                                  Interval.IntervalDesc) -> (Fin0.Coq_fin ->
                                  Prelude.Maybe Graph__PhysReg) ->
                                  (Graph__PhysReg -> Prelude.Maybe
                                  Interval.IntervalDesc) -> () -> a1) ->
                                  Graph__ScanStateDesc -> a1
_Graph__coq_ScanStateDesc_rect f s =
  case s of {
   Graph__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6 __}

_Graph__coq_ScanStateDesc_rec :: (Prelude.Int -> ([] Fin0.Coq_fin) -> ([]
                                 Fin0.Coq_fin) -> ([] Fin0.Coq_fin) -> ([]
                                 Fin0.Coq_fin) -> (Fin0.Coq_fin ->
                                 Interval.IntervalDesc) -> (Fin0.Coq_fin ->
                                 Prelude.Maybe Graph__PhysReg) ->
                                 (Graph__PhysReg -> Prelude.Maybe
                                 Interval.IntervalDesc) -> () -> a1) ->
                                 Graph__ScanStateDesc -> a1
_Graph__coq_ScanStateDesc_rec =
  _Graph__coq_ScanStateDesc_rect

_Graph__nextInterval :: Graph__ScanStateDesc -> Prelude.Int
_Graph__nextInterval s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> nextInterval0}

type Graph__IntervalId = Fin0.Coq_fin

_Graph__unhandled :: Graph__ScanStateDesc -> [] Graph__IntervalId
_Graph__unhandled s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> unhandled0}

_Graph__active :: Graph__ScanStateDesc -> [] Graph__IntervalId
_Graph__active s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> active0}

_Graph__inactive :: Graph__ScanStateDesc -> [] Graph__IntervalId
_Graph__inactive s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> inactive0}

_Graph__handled :: Graph__ScanStateDesc -> [] Graph__IntervalId
_Graph__handled s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> handled0}

_Graph__getInterval :: Graph__ScanStateDesc -> Graph__IntervalId ->
                       Interval.IntervalDesc
_Graph__getInterval s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getInterval0}

_Graph__assignments :: Graph__ScanStateDesc -> Graph__IntervalId ->
                       Prelude.Maybe Graph__PhysReg
_Graph__assignments s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> assignments0}

_Graph__getFixedInterval :: Graph__ScanStateDesc -> Graph__PhysReg ->
                            Prelude.Maybe Interval.IntervalDesc
_Graph__getFixedInterval s =
  case s of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 -> getFixedInterval0}

_Graph__all_state_lists :: Graph__ScanStateDesc -> [] Graph__IntervalId
_Graph__all_state_lists s =
  (Prelude.++) (_Graph__unhandled s)
    ((Prelude.++) (_Graph__active s)
      ((Prelude.++) (_Graph__inactive s) (_Graph__handled s)))

_Graph__transportId :: Graph__ScanStateDesc -> Graph__ScanStateDesc ->
                       Graph__IntervalId -> Graph__IntervalId
_Graph__transportId sd sd' x =
  let {
   h = Compare_dec.le_lt_eq_dec (_Graph__nextInterval sd)
         (_Graph__nextInterval sd')}
  in
  case h of {
   Specif.Coq_left ->
    case sd of {
     Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
      handled0 getInterval0 assignments0 getFixedInterval0 ->
      case sd' of {
       Graph__Build_ScanStateDesc nextInterval1 unhandled1 active1 inactive1
        handled1 getInterval1 assignments1 getFixedInterval1 ->
        let {h0 = Lib.lt_sub nextInterval0 nextInterval1} in
        Logic.eq_rec ((Prelude.+) h0 nextInterval0)
          (Fin.coq_R nextInterval0 h0 x) nextInterval1}};
   Specif.Coq_right ->
    Logic.eq_rec (_Graph__nextInterval sd) x (_Graph__nextInterval sd')}

_Graph__unhandledExtent :: Graph__ScanStateDesc -> Prelude.Int
_Graph__unhandledExtent sd =
  case _Graph__unhandled sd of {
   [] -> 0;
   (:) i l ->
    case l of {
     [] -> Interval.intervalExtent ( (_Graph__getInterval sd i));
     (:) i0 l0 ->
      let {
       f = \n x ->
        (Prelude.+) n (Interval.intervalExtent ( (_Graph__getInterval sd x)))}
      in
      (\f -> Prelude.flip (Data.List.foldl' f)) f ((:) i ((:) i0 l0)) 0}}

data Graph__ScanStateCursor =
   Graph__Build_ScanStateCursor

_Graph__coq_ScanStateCursor_rect :: Graph__ScanStateDesc -> (() -> () -> a1)
                                    -> a1
_Graph__coq_ScanStateCursor_rect sd f =
  f __ __

_Graph__coq_ScanStateCursor_rec :: Graph__ScanStateDesc -> (() -> () -> a1)
                                   -> a1
_Graph__coq_ScanStateCursor_rec sd f =
  _Graph__coq_ScanStateCursor_rect sd f

_Graph__curId :: Graph__ScanStateDesc -> Graph__IntervalId
_Graph__curId sd =
  Lib.safe_hd (_Graph__unhandled sd)

_Graph__curIntDetails :: Graph__ScanStateDesc -> Interval.IntervalDesc
_Graph__curIntDetails sd =
  _Graph__getInterval sd (_Graph__curId sd)

_Graph__curIntDesc :: Graph__ScanStateDesc -> Interval.IntervalDesc
_Graph__curIntDesc sd =
   (_Graph__curIntDetails sd)

_Graph__curPosition :: Graph__ScanStateDesc -> Prelude.Int
_Graph__curPosition sd =
  Interval.intervalStart ( (_Graph__curIntDetails sd))

type Graph__NextScanState =
  Graph__ScanStateDesc
  -- singleton inductive, whose constructor was Build_NextScanState
  
_Graph__coq_NextScanState_rect :: (Graph__ScanStateDesc -> () -> () -> a1) ->
                                  Graph__NextScanState -> a1
_Graph__coq_NextScanState_rect f n =
  f n __ __

_Graph__coq_NextScanState_rec :: (Graph__ScanStateDesc -> () -> () -> a1) ->
                                 Graph__NextScanState -> a1
_Graph__coq_NextScanState_rec =
  _Graph__coq_NextScanState_rect

_Graph__nextDesc :: Graph__NextScanState -> Graph__ScanStateDesc
_Graph__nextDesc n =
  n

type Graph__NextState = Graph__NextScanState

type Graph__NextStateDep = Graph__NextScanState

type Graph__NextStateWith a = (,) a Graph__NextScanState

_Graph__coq_NextScanState_transitivity :: Graph__ScanStateDesc ->
                                          Graph__NextScanState ->
                                          Graph__NextScanState ->
                                          Graph__NextScanState
_Graph__coq_NextScanState_transitivity sd0 n o =
  o

_Graph__coq_SSMorph_rect :: Graph__ScanStateDesc -> Graph__ScanStateDesc ->
                            (() -> () -> () -> a1) -> a1
_Graph__coq_SSMorph_rect sd1 sd2 f =
  f __ __ __

_Graph__coq_SSMorph_rec :: Graph__ScanStateDesc -> Graph__ScanStateDesc ->
                           (() -> () -> () -> a1) -> a1
_Graph__coq_SSMorph_rec sd1 sd2 f =
  _Graph__coq_SSMorph_rect sd1 sd2 f

_Graph__coq_SSMorphSt_rect :: Graph__ScanStateDesc -> Graph__ScanStateDesc ->
                              (() -> () -> a1) -> a1
_Graph__coq_SSMorphSt_rect sd1 sd2 f =
  f __ __

_Graph__coq_SSMorphSt_rec :: Graph__ScanStateDesc -> Graph__ScanStateDesc ->
                             (() -> () -> a1) -> a1
_Graph__coq_SSMorphSt_rec sd1 sd2 f =
  _Graph__coq_SSMorphSt_rect sd1 sd2 f

_Graph__coq_SSMorphLen_rect :: Graph__ScanStateDesc -> Graph__ScanStateDesc
                               -> (() -> () -> a1) -> a1
_Graph__coq_SSMorphLen_rect sd1 sd2 f =
  f __ __

_Graph__coq_SSMorphLen_rec :: Graph__ScanStateDesc -> Graph__ScanStateDesc ->
                              (() -> () -> a1) -> a1
_Graph__coq_SSMorphLen_rec sd1 sd2 f =
  _Graph__coq_SSMorphLen_rect sd1 sd2 f

_Graph__coq_SSMorphStLen_rect :: Graph__ScanStateDesc -> Graph__ScanStateDesc
                                 -> (() -> () -> a1) -> a1
_Graph__coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __

_Graph__coq_SSMorphStLen_rec :: Graph__ScanStateDesc -> Graph__ScanStateDesc
                                -> (() -> () -> a1) -> a1
_Graph__coq_SSMorphStLen_rec sd1 sd2 f =
  _Graph__coq_SSMorphStLen_rect sd1 sd2 f

_Graph__moveUnhandledToActive :: Graph__ScanStateDesc -> Graph__PhysReg ->
                                 Graph__NextState
_Graph__moveUnhandledToActive sd reg =
  case sd of {
   Graph__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 getInterval0 assignments0 getFixedInterval0 ->
    case unhandled0 of {
     [] -> Logic.coq_False_rec;
     (:) i unhandled1 -> Graph__Build_ScanStateDesc nextInterval0 unhandled1
      ((:) i active0) inactive0 handled0 getInterval0 (\i0 ->
      case Compare.cmp_eq_dec (Fin0.fin_CompareSpec nextInterval0) i0 i of {
       Specif.Coq_left -> Prelude.Just reg;
       Specif.Coq_right -> assignments0 i0}) getFixedInterval0}}

_Graph__moveActiveToHandled :: Graph__ScanStateDesc -> Graph__IntervalId ->
                               Graph__NextScanState
_Graph__moveActiveToHandled sd x =
  Graph__Build_ScanStateDesc (_Graph__nextInterval sd) (_Graph__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Graph__nextInterval sd))) x
      (_Graph__active sd)) ((:) x (_Graph__inactive sd)) (_Graph__handled sd)
    (_Graph__getInterval sd) (_Graph__assignments sd)
    (_Graph__getFixedInterval sd)

_Graph__moveActiveToInactive :: Graph__ScanStateDesc -> Graph__IntervalId ->
                                Graph__NextScanState
_Graph__moveActiveToInactive sd x =
  Graph__Build_ScanStateDesc (_Graph__nextInterval sd) (_Graph__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Graph__nextInterval sd))) x
      (_Graph__active sd)) ((:) x (_Graph__inactive sd)) (_Graph__handled sd)
    (_Graph__getInterval sd) (_Graph__assignments sd)
    (_Graph__getFixedInterval sd)

_Graph__moveInactiveToActive :: Graph__ScanStateDesc -> Graph__IntervalId ->
                                Graph__NextScanState
_Graph__moveInactiveToActive sd x =
  Graph__Build_ScanStateDesc (_Graph__nextInterval sd) (_Graph__unhandled sd)
    ((:) x (_Graph__active sd))
    (List0.remove
      (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Graph__nextInterval sd))) x
      (_Graph__inactive sd)) (_Graph__handled sd) (_Graph__getInterval sd)
    (_Graph__assignments sd) (_Graph__getFixedInterval sd)

_Graph__moveInactiveToHandled :: Graph__ScanStateDesc -> Graph__IntervalId ->
                                 Graph__NextScanState
_Graph__moveInactiveToHandled sd x =
  Graph__Build_ScanStateDesc (_Graph__nextInterval sd) (_Graph__unhandled sd)
    (_Graph__active sd)
    (List0.remove
      (Compare.cmp_eq_dec (Fin0.fin_CompareSpec (_Graph__nextInterval sd))) x
      (_Graph__inactive sd)) ((:) x (_Graph__handled sd))
    (_Graph__getInterval sd) (_Graph__assignments sd)
    (_Graph__getFixedInterval sd)

_Graph__nextIntersectionWith :: Interval.IntervalDesc -> Graph__ScanStateDesc
                                -> Graph__IntervalId -> Prelude.Maybe
                                Prelude.Int
_Graph__nextIntersectionWith d sd jid =
  Interval.firstIntersectionPoint ( (_Graph__getInterval sd jid)) d

_Graph__getRegisterIndex :: Graph__ScanStateDesc -> (Graph__IntervalId ->
                            Prelude.Maybe Prelude.Int) -> (Graph__PhysReg ->
                            Prelude.Maybe Prelude.Int) -> ([]
                            Graph__IntervalId) -> Graph__PhysReg ->
                            Prelude.Maybe Prelude.Int
_Graph__getRegisterIndex sd intervalIndex registerIndex intervals =
  Prelude.foldr (\x f r ->
    case _Graph__assignments sd x of {
     Prelude.Just a ->
      case Compare.cmp_eq_dec (Fin0.fin_CompareSpec _Graph__maxReg) a r of {
       Specif.Coq_left -> intervalIndex x;
       Specif.Coq_right -> f r};
     Prelude.Nothing -> f r}) registerIndex intervals

_Graph__findRegister_F :: ((Graph__PhysReg -> Prelude.Maybe Prelude.Int) ->
                          Graph__PhysReg -> (,) Graph__PhysReg
                          (Prelude.Maybe Prelude.Int)) -> (Graph__PhysReg ->
                          Prelude.Maybe Prelude.Int) -> Graph__PhysReg -> (,)
                          Graph__PhysReg (Prelude.Maybe Prelude.Int)
_Graph__findRegister_F findRegister0 registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _Graph__maxReg start of {
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

_Graph__findRegister_terminate :: (Graph__PhysReg -> Prelude.Maybe
                                  Prelude.Int) -> Graph__PhysReg ->
                                  ((,) Graph__PhysReg
                                  (Prelude.Maybe Prelude.Int))
_Graph__findRegister_terminate registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _Graph__maxReg start of {
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
        (_Graph__findRegister_terminate registerIndex nreg);
     Prelude.Nothing -> (,) start (Prelude.Just pos)};
   Prelude.Nothing -> (,) start Prelude.Nothing}

_Graph__findRegister :: (Graph__PhysReg -> Prelude.Maybe Prelude.Int) ->
                        Graph__PhysReg -> (,) Graph__PhysReg
                        (Prelude.Maybe Prelude.Int)
_Graph__findRegister registerIndex start =
  case registerIndex start of {
   Prelude.Just pos ->
    case Fin0.pred_fin _Graph__maxReg start of {
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
        (_Graph__findRegister registerIndex nreg);
     Prelude.Nothing -> (,) start (Prelude.Just pos)};
   Prelude.Nothing -> (,) start Prelude.Nothing}

data Graph__R_findRegister =
   Graph__R_findRegister_0 Graph__PhysReg
 | Graph__R_findRegister_1 Graph__PhysReg Prelude.Int
 | Graph__R_findRegister_2 Graph__PhysReg Prelude.Int Fin0.Coq_fin ((,)
                                                                   Graph__PhysReg
                                                                   (Prelude.Maybe
                                                                   Prelude.Int)) 
 Graph__R_findRegister Graph__PhysReg
 | Graph__R_findRegister_3 Graph__PhysReg Prelude.Int Fin0.Coq_fin ((,)
                                                                   Graph__PhysReg
                                                                   (Prelude.Maybe
                                                                   Prelude.Int)) 
 Graph__R_findRegister Graph__PhysReg Prelude.Int
 | Graph__R_findRegister_4 Graph__PhysReg Prelude.Int Fin0.Coq_fin ((,)
                                                                   Graph__PhysReg
                                                                   (Prelude.Maybe
                                                                   Prelude.Int)) 
 Graph__R_findRegister Graph__PhysReg Prelude.Int

_Graph__coq_R_findRegister_rect :: (Graph__PhysReg -> Prelude.Maybe
                                   Prelude.Int) -> (Graph__PhysReg -> () ->
                                   a1) -> (Graph__PhysReg -> Prelude.Int ->
                                   () -> () -> a1) -> (Graph__PhysReg ->
                                   Prelude.Int -> () -> Fin0.Coq_fin -> () ->
                                   ((,) Graph__PhysReg
                                   (Prelude.Maybe Prelude.Int)) ->
                                   Graph__R_findRegister -> a1 ->
                                   Graph__PhysReg -> () -> a1) ->
                                   (Graph__PhysReg -> Prelude.Int -> () ->
                                   Fin0.Coq_fin -> () -> ((,) Graph__PhysReg
                                   (Prelude.Maybe Prelude.Int)) ->
                                   Graph__R_findRegister -> a1 ->
                                   Graph__PhysReg -> Prelude.Int -> () -> ()
                                   -> a1) -> (Graph__PhysReg -> Prelude.Int
                                   -> () -> Fin0.Coq_fin -> () -> ((,)
                                   Graph__PhysReg
                                   (Prelude.Maybe Prelude.Int)) ->
                                   Graph__R_findRegister -> a1 ->
                                   Graph__PhysReg -> Prelude.Int -> () -> ()
                                   -> a1) -> Graph__PhysReg -> ((,)
                                   Graph__PhysReg
                                   (Prelude.Maybe Prelude.Int)) ->
                                   Graph__R_findRegister -> a1
_Graph__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 start p r =
  case r of {
   Graph__R_findRegister_0 start0 -> f start0 __;
   Graph__R_findRegister_1 start0 pos -> f0 start0 pos __ __;
   Graph__R_findRegister_2 start0 pos nreg res r0 reg ->
    f1 start0 pos __ nreg __ res r0
      (_Graph__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg res
        r0) reg __;
   Graph__R_findRegister_3 start0 pos nreg res r0 reg pos' ->
    f2 start0 pos __ nreg __ res r0
      (_Graph__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg res
        r0) reg pos' __ __;
   Graph__R_findRegister_4 start0 pos nreg res r0 reg pos' ->
    f3 start0 pos __ nreg __ res r0
      (_Graph__coq_R_findRegister_rect registerIndex f f0 f1 f2 f3 nreg res
        r0) reg pos' __ __}

_Graph__coq_R_findRegister_rec :: (Graph__PhysReg -> Prelude.Maybe
                                  Prelude.Int) -> (Graph__PhysReg -> () ->
                                  a1) -> (Graph__PhysReg -> Prelude.Int -> ()
                                  -> () -> a1) -> (Graph__PhysReg ->
                                  Prelude.Int -> () -> Fin0.Coq_fin -> () ->
                                  ((,) Graph__PhysReg
                                  (Prelude.Maybe Prelude.Int)) ->
                                  Graph__R_findRegister -> a1 ->
                                  Graph__PhysReg -> () -> a1) ->
                                  (Graph__PhysReg -> Prelude.Int -> () ->
                                  Fin0.Coq_fin -> () -> ((,) Graph__PhysReg
                                  (Prelude.Maybe Prelude.Int)) ->
                                  Graph__R_findRegister -> a1 ->
                                  Graph__PhysReg -> Prelude.Int -> () -> ()
                                  -> a1) -> (Graph__PhysReg -> Prelude.Int ->
                                  () -> Fin0.Coq_fin -> () -> ((,)
                                  Graph__PhysReg (Prelude.Maybe Prelude.Int))
                                  -> Graph__R_findRegister -> a1 ->
                                  Graph__PhysReg -> Prelude.Int -> () -> ()
                                  -> a1) -> Graph__PhysReg -> ((,)
                                  Graph__PhysReg (Prelude.Maybe Prelude.Int))
                                  -> Graph__R_findRegister -> a1
_Graph__coq_R_findRegister_rec registerIndex =
  _Graph__coq_R_findRegister_rect registerIndex

_Graph__findRegister_rect :: (Graph__PhysReg -> Prelude.Maybe Prelude.Int) ->
                             (Graph__PhysReg -> () -> a1) -> (Graph__PhysReg
                             -> Prelude.Int -> () -> () -> a1) ->
                             (Graph__PhysReg -> Prelude.Int -> () ->
                             Fin0.Coq_fin -> () -> a1 -> Graph__PhysReg -> ()
                             -> a1) -> (Graph__PhysReg -> Prelude.Int -> ()
                             -> Fin0.Coq_fin -> () -> a1 -> Graph__PhysReg ->
                             Prelude.Int -> () -> () -> a1) ->
                             (Graph__PhysReg -> Prelude.Int -> () ->
                             Fin0.Coq_fin -> () -> a1 -> Graph__PhysReg ->
                             Prelude.Int -> () -> () -> a1) -> Graph__PhysReg
                             -> a1
_Graph__findRegister_rect registerIndex f f0 f1 f2 f3 start =
  Logic.eq_rect_r
    (case registerIndex start of {
      Prelude.Just pos ->
       case Fin0.pred_fin _Graph__maxReg start of {
        Prelude.Just nreg ->
         case _Graph__findRegister registerIndex nreg of {
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
       case Fin0.pred_fin _Graph__maxReg start of {
        Prelude.Just f13 ->
         let {f14 = f12 f13 __} in
         let {f15 = f11 f13 __} in
         let {f16 = f10 f13 __} in
         case _Graph__findRegister registerIndex f13 of {
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
                           (_Graph__findRegister registerIndex f13)
                           (_Graph__findRegister_rect registerIndex f f0 f1
                             f2 f3 f13) ((,) p o)) (Prelude.Just n0)}
               in
               f19 hrec;
              Prelude.False ->
               let {f19 = \h -> f17 h __} in
               let {
                hrec = Logic.eq_rect o
                         (Logic.eq_rect
                           (_Graph__findRegister registerIndex f13)
                           (_Graph__findRegister_rect registerIndex f f0 f1
                             f2 f3 f13) ((,) p o)) (Prelude.Just n0)}
               in
               f19 hrec};
            Prelude.Nothing ->
             let {f17 = \h -> f16 h p __} in
             let {
              hrec = Logic.eq_rect o
                       (Logic.eq_rect
                         (_Graph__findRegister registerIndex f13)
                         (_Graph__findRegister_rect registerIndex f f0 f1 f2
                           f3 f13) ((,) p o)) Prelude.Nothing}
             in
             f17 hrec}};
        Prelude.Nothing -> f9 __};
      Prelude.Nothing -> f8 __}) (_Graph__findRegister registerIndex start)

_Graph__findRegister_rec :: (Graph__PhysReg -> Prelude.Maybe Prelude.Int) ->
                            (Graph__PhysReg -> () -> a1) -> (Graph__PhysReg
                            -> Prelude.Int -> () -> () -> a1) ->
                            (Graph__PhysReg -> Prelude.Int -> () ->
                            Fin0.Coq_fin -> () -> a1 -> Graph__PhysReg -> ()
                            -> a1) -> (Graph__PhysReg -> Prelude.Int -> () ->
                            Fin0.Coq_fin -> () -> a1 -> Graph__PhysReg ->
                            Prelude.Int -> () -> () -> a1) -> (Graph__PhysReg
                            -> Prelude.Int -> () -> Fin0.Coq_fin -> () -> a1
                            -> Graph__PhysReg -> Prelude.Int -> () -> () ->
                            a1) -> Graph__PhysReg -> a1
_Graph__findRegister_rec registerIndex =
  _Graph__findRegister_rect registerIndex

_Graph__coq_R_findRegister_correct :: (Graph__PhysReg -> Prelude.Maybe
                                      Prelude.Int) -> Graph__PhysReg -> ((,)
                                      Graph__PhysReg
                                      (Prelude.Maybe Prelude.Int)) ->
                                      Graph__R_findRegister
_Graph__coq_R_findRegister_correct x x0 res =
  _Graph__findRegister_rect x (\y _ z _ ->
    Logic.eq_rec_r ((,) y Prelude.Nothing) (Graph__R_findRegister_0 y) z)
    (\y y0 _ _ z _ ->
    Logic.eq_rec_r ((,) y (Prelude.Just y0)) (Graph__R_findRegister_1 y y0) z)
    (\y y0 _ y2 _ y4 y5 _ z _ ->
    Logic.eq_rec_r ((,) y5 Prelude.Nothing) (Graph__R_findRegister_2 y y0 y2
      (_Graph__findRegister x y2) (y4 (_Graph__findRegister x y2) __) y5) z)
    (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r ((,) y5 (Prelude.Just y6)) (Graph__R_findRegister_3 y y0
      y2 (_Graph__findRegister x y2) (y4 (_Graph__findRegister x y2) __) y5
      y6) z) (\y y0 _ y2 _ y4 y5 y6 _ _ z _ ->
    Logic.eq_rec_r ((,) y5 (Prelude.Just y0)) (Graph__R_findRegister_4 y y0
      y2 (_Graph__findRegister x y2) (y4 (_Graph__findRegister x y2) __) y5
      y6) z) x0 res __

_Graph__splitInterval :: Graph__ScanStateDesc -> (Prelude.Maybe Prelude.Int)
                         -> Graph__NextState
_Graph__splitInterval sd before =
  sd

_Graph__tryAllocateFreeReg :: Graph__ScanStateDesc -> Prelude.Maybe
                              Graph__NextState
_Graph__tryAllocateFreeReg sd =
  let {
   freeUntilPos' = _Graph__getRegisterIndex sd (\x -> Prelude.Just 0) (\x ->
                     Prelude.Nothing) (_Graph__active sd)}
  in
  let {
   intersectingIntervals = (Prelude.filter) (\x ->
                             Interval.anyRangeIntersects
                               ( (_Graph__curIntDetails sd))
                               ( (_Graph__getInterval sd x)))
                             (_Graph__inactive sd)}
  in
  let {
   freeUntilPos = _Graph__getRegisterIndex sd
                    (_Graph__nextIntersectionWith
                      ( (_Graph__curIntDetails sd)) sd) freeUntilPos'
                    intersectingIntervals}
  in
  let {lastReg = Fin0.ultimate_from_nat _Graph__maxReg} in
  case _Graph__findRegister freeUntilPos lastReg of {
   (,) reg mres ->
    let {default0 = _Graph__moveUnhandledToActive sd reg} in
    case mres of {
     Prelude.Just n ->
      case EqNat.beq_nat n 0 of {
       Prelude.True -> Prelude.Nothing;
       Prelude.False -> Prelude.Just
        (case NPeano.ltb (Interval.intervalEnd ( (_Graph__curIntDetails sd)))
                n of {
          Prelude.True -> default0;
          Prelude.False ->
           _Graph__moveUnhandledToActive
             (_Graph__nextDesc (_Graph__splitInterval sd (Prelude.Just n)))
             reg})};
     Prelude.Nothing -> Prelude.Just default0}}

_Graph__nextUseAfter :: Prelude.Int -> Graph__ScanStateDesc ->
                        Graph__IntervalId -> Prelude.Maybe Prelude.Int
_Graph__nextUseAfter =
  Prelude.error "AXIOM TO BE REALIZED"

_Graph__assignSpillSlotToCurrent :: Graph__ScanStateDesc ->
                                    Graph__NextScanState
_Graph__assignSpillSlotToCurrent =
  Prelude.error "AXIOM TO BE REALIZED"

_Graph__allocateBlockedReg :: Graph__ScanStateDesc -> Graph__NextState
_Graph__allocateBlockedReg sd =
  Lib.undefined

_Graph__checkActiveIntervals :: Graph__ScanStateDesc -> Prelude.Int ->
                                Graph__NextScanState
_Graph__checkActiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd ( (_Graph__getInterval sd0 ( x))))
                     pos0 of {
               Prelude.True ->
                Lib.uncurry_sig (\x0 _ -> _Graph__moveActiveToHandled sd0 x0)
                  x;
               Prelude.False ->
                case (Prelude.not)
                       (Interval.intervalCoversPos
                         ( (_Graph__getInterval sd0 ( x))) pos0) of {
                 Prelude.True ->
                  Lib.uncurry_sig (\x0 _ ->
                    _Graph__moveActiveToInactive sd0 x0) x;
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_Graph__active sd)) pos

_Graph__checkInactiveIntervals :: Graph__ScanStateDesc -> Prelude.Int ->
                                  Graph__NextScanState
_Graph__checkInactiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd ( (_Graph__getInterval sd0 ( x))))
                     pos0 of {
               Prelude.True ->
                Lib.uncurry_sig (\x0 _ ->
                  _Graph__moveInactiveToHandled sd0 x0) x;
               Prelude.False ->
                case Interval.intervalCoversPos
                       ( (_Graph__getInterval sd0 ( x))) pos0 of {
                 Prelude.True ->
                  Lib.uncurry_sig (\x0 _ ->
                    _Graph__moveInactiveToActive sd0 x0) x;
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_Graph__inactive sd)) pos

_Graph__handleInterval :: Graph__ScanStateDesc -> Graph__NextState
_Graph__handleInterval sd =
  let {position = _Graph__curPosition sd} in
  let {sp1 = _Graph__checkActiveIntervals sd position} in
  let {sp2 = _Graph__checkInactiveIntervals (_Graph__nextDesc sp1) position}
  in
  let {
   result = Lib.fromMaybe (_Graph__allocateBlockedReg (_Graph__nextDesc sp2))
              (_Graph__tryAllocateFreeReg (_Graph__nextDesc sp2))}
  in
  _Graph__nextDesc result

_Graph__linearScan_F :: (Graph__ScanStateDesc -> () -> Graph__ScanStateDesc)
                        -> Graph__ScanStateDesc -> Graph__ScanStateDesc
_Graph__linearScan_F linearScan0 sd =
  case List0.destruct_list (_Graph__unhandled sd) of {
   Specif.Coq_inleft s -> linearScan0 (_Graph__handleInterval sd) __;
   Specif.Coq_inright -> sd}

_Graph__linearScan_terminate :: Graph__ScanStateDesc -> Graph__ScanStateDesc
_Graph__linearScan_terminate sd =
  case List0.destruct_list (_Graph__unhandled sd) of {
   Specif.Coq_inleft s ->
    Specif.sig_rec (\rec_res _ -> rec_res)
      (_Graph__linearScan_terminate (_Graph__handleInterval sd));
   Specif.Coq_inright -> sd}

_Graph__linearScan :: Graph__ScanStateDesc -> Graph__ScanStateDesc
_Graph__linearScan sd =
  case List0.destruct_list (_Graph__unhandled sd) of {
   Specif.Coq_inleft s ->
    Specif.sig_rec (\rec_res _ -> rec_res)
      (_Graph__linearScan (_Graph__handleInterval sd));
   Specif.Coq_inright -> sd}

data Graph__R_linearScan =
   Graph__R_linearScan_0 Graph__ScanStateDesc Graph__IntervalId ([]
                                                                Graph__IntervalId) 
 Graph__ScanStateDesc Graph__ScanStateDesc Graph__R_linearScan
 | Graph__R_linearScan_1 Graph__ScanStateDesc

_Graph__coq_R_linearScan_rect :: (Graph__ScanStateDesc -> () ->
                                 Graph__IntervalId -> ([] Graph__IntervalId)
                                 -> () -> () -> Graph__ScanStateDesc -> () ->
                                 () -> () -> Graph__ScanStateDesc ->
                                 Graph__R_linearScan -> a1 -> a1) ->
                                 (Graph__ScanStateDesc -> () -> () -> () ->
                                 a1) -> Graph__ScanStateDesc ->
                                 Graph__ScanStateDesc -> Graph__R_linearScan
                                 -> a1
_Graph__coq_R_linearScan_rect f f0 sd s r =
  case r of {
   Graph__R_linearScan_0 sd0 x xs sd2 res r0 ->
    f sd0 __ x xs __ __ sd2 __ __ __ res r0
      (_Graph__coq_R_linearScan_rect f f0 sd2 res r0);
   Graph__R_linearScan_1 sd0 -> f0 sd0 __ __ __}

_Graph__coq_R_linearScan_rec :: (Graph__ScanStateDesc -> () ->
                                Graph__IntervalId -> ([] Graph__IntervalId)
                                -> () -> () -> Graph__ScanStateDesc -> () ->
                                () -> () -> Graph__ScanStateDesc ->
                                Graph__R_linearScan -> a1 -> a1) ->
                                (Graph__ScanStateDesc -> () -> () -> () ->
                                a1) -> Graph__ScanStateDesc ->
                                Graph__ScanStateDesc -> Graph__R_linearScan
                                -> a1
_Graph__coq_R_linearScan_rec f f0 sd s r =
  _Graph__coq_R_linearScan_rect f f0 sd s r

type Graph__VirtReg = Prelude.Int

type Graph__Graph a =
  a
  -- singleton inductive, whose constructor was Build_Graph
  
_Graph__coq_Graph_rect :: (a1 -> a2) -> (Graph__Graph a1) -> a2
_Graph__coq_Graph_rect f g =
  f g

_Graph__coq_Graph_rec :: (a1 -> a2) -> (Graph__Graph a1) -> a2
_Graph__coq_Graph_rec =
  _Graph__coq_Graph_rect

_Graph__postOrderTraversal :: (Graph__Graph a1) -> a1
_Graph__postOrderTraversal graph =
  graph

_Graph__determineIntervals :: (Graph__Graph Graph__VirtReg) ->
                              Graph__ScanStateDesc
_Graph__determineIntervals =
  Prelude.error "AXIOM TO BE REALIZED"

_Graph__allocateRegisters :: (Graph__Graph Graph__VirtReg) ->
                             Graph__ScanStateDesc
_Graph__allocateRegisters g =
  
    (Lib.uncurry_sig (\x _ -> _Graph__linearScan x)
      (_Graph__determineIntervals g))

