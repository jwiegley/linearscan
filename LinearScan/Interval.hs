module LinearScan.Interval where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Range as Range


__ :: any
__ = Prelude.error "Logical or arity value used"

data IntervalKind =
   Whole
 | LeftMost
 | Middle
 | RightMost

splitKind :: IntervalKind -> (,) IntervalKind IntervalKind
splitKind k =
  case k of {
   Whole -> (,) LeftMost RightMost;
   LeftMost -> (,) LeftMost Middle;
   Middle -> (,) Middle Middle;
   RightMost -> (,) Middle RightMost}

data IntervalDesc =
   Build_IntervalDesc Prelude.Int Prelude.Int Prelude.Int IntervalKind 
 ([] Range.RangeDesc)

ivar :: IntervalDesc -> Prelude.Int
ivar i =
  case i of {
   Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 -> ivar0}

ibeg :: IntervalDesc -> Prelude.Int
ibeg i =
  case i of {
   Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 -> ibeg0}

iend :: IntervalDesc -> Prelude.Int
iend i =
  case i of {
   Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 -> iend0}

iknd :: IntervalDesc -> IntervalKind
iknd i =
  case i of {
   Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 -> iknd0}

rds :: IntervalDesc -> [] Range.RangeDesc
rds i =
  case i of {
   Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 -> rds0}

getIntervalDesc :: IntervalDesc -> IntervalDesc
getIntervalDesc d =
  d

packInterval :: IntervalDesc -> IntervalDesc
packInterval d =
  d

intervalStart :: IntervalDesc -> Prelude.Int
intervalStart i =
  ibeg i

intervalEnd :: IntervalDesc -> Prelude.Int
intervalEnd i =
  iend i

intervalCoversPos :: IntervalDesc -> Prelude.Int -> Prelude.Bool
intervalCoversPos d pos =
  (Prelude.&&) ((Prelude.<=) (intervalStart d) pos)
    ((Prelude.<=) ((Prelude.succ) pos) (intervalEnd d))

intervalsIntersect :: IntervalDesc -> IntervalDesc -> Prelude.Bool
intervalsIntersect i j =
  let {f = \x y -> Range.rangesIntersect ( x) ( y)} in
  Data.List.any (\x -> Data.List.any (f x) ( (rds j))) ( (rds i))

intervalIntersectionPoint :: IntervalDesc -> IntervalDesc -> Prelude.Maybe
                             Prelude.Int
intervalIntersectionPoint i j =
  Data.List.foldl' (\acc rd ->
    case acc of {
     Prelude.Just x -> Prelude.Just x;
     Prelude.Nothing ->
      Data.List.foldl' (\acc' rd' ->
        case acc' of {
         Prelude.Just x -> Prelude.Just x;
         Prelude.Nothing -> Range.rangeIntersectionPoint ( rd) ( rd')})
        Prelude.Nothing (rds j)}) Prelude.Nothing (rds i)

findIntervalUsePos :: IntervalDesc -> (Range.UsePos -> Prelude.Bool) ->
                      Prelude.Maybe ((,) Range.RangeDesc Range.UsePos)
findIntervalUsePos d f =
  let {
   f0 = \r ->
    case Range.findRangeUsePos r f of {
     Prelude.Just pos -> Prelude.Just ((,) r pos);
     Prelude.Nothing -> Prelude.Nothing}}
  in
  let {
   go rs =
     (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
       (\r ->
       f0 r)
       (\r rs' ->
       Lib.option_choose (f0 r) (go rs'))
       rs}
  in go (rds d)

nextUseAfter :: IntervalDesc -> Prelude.Int -> Prelude.Maybe Prelude.Int
nextUseAfter d pos =
  Lib.option_map ((Prelude..) Range.uloc Prelude.snd)
    (findIntervalUsePos d (\u ->
      (Prelude.<=) ((Prelude.succ) pos) (Range.uloc u)))

firstUsePos :: IntervalDesc -> Prelude.Int
firstUsePos d =
  Range.uloc (Prelude.head (Range.ups ( (Prelude.head (rds d)))))

firstUseReqReg :: IntervalDesc -> Prelude.Maybe Prelude.Int
firstUseReqReg d =
  Lib.option_map ((Prelude..) Range.uloc Prelude.snd)
    (findIntervalUsePos d Range.regReq)

type BoundedInterval = IntervalDesc

transportBoundedInterval :: Prelude.Int -> Prelude.Int -> BoundedInterval ->
                            BoundedInterval
transportBoundedInterval base prev x =
  x

data SplitPosition =
   BeforePos Prelude.Int
 | BeforeFirstUsePosReqReg
 | EndOfLifetimeHole

splitPosition :: IntervalDesc -> SplitPosition -> Prelude.Maybe Prelude.Int
splitPosition d pos =
  case pos of {
   BeforePos x -> Prelude.Just x;
   BeforeFirstUsePosReqReg -> firstUseReqReg (getIntervalDesc d);
   EndOfLifetimeHole -> Prelude.Nothing}

intervalSpan :: ([] Range.RangeDesc) -> Prelude.Int -> Prelude.Int ->
                Prelude.Int -> Prelude.Int -> IntervalKind ->
                ((,) (Prelude.Maybe IntervalDesc)
                (Prelude.Maybe IntervalDesc))
intervalSpan rs before iv ib ie knd =
  let {
   _evar_0_ = \lknd rknd ->
    (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
      (\r ->
      let {_top_assumption_ = Range.rangeSpan before ( r)} in
      let {
       _evar_0_ = \_top_assumption_0 ->
        let {
         _evar_0_ = \r0 _top_assumption_1 ->
          let {
           _evar_0_ = \r1 ->
            let {
             _evar_0_ = let {
                         _evar_0_ = \_ _ -> (,) (Prelude.Just
                          (Build_IntervalDesc iv (Range.rbeg ( r0))
                          (Range.rend ( r0)) lknd ((:[]) ( r0))))
                          (Prelude.Just (Build_IntervalDesc iv
                          (Range.rbeg ( r1)) (Range.rend ( r1)) rknd ((:[])
                          ( r1))))}
                        in
                         _evar_0_}
            in
             _evar_0_ __ __}
          in
          let {
           _evar_0_0 = let {
                        _evar_0_0 = let {
                                     _evar_0_0 = \_ -> (,) (Prelude.Just
                                      (Build_IntervalDesc iv
                                      (Range.rbeg ( r0)) (Range.rend ( r0))
                                      knd ((:[]) ( r0)))) Prelude.Nothing}
                                    in
                                     _evar_0_0}
                       in
                        _evar_0_0}
          in
          case _top_assumption_1 of {
           Prelude.Just x -> (\_ -> _evar_0_ x);
           Prelude.Nothing -> _evar_0_0}}
        in
        let {
         _evar_0_0 = \_top_assumption_1 ->
          let {
           _evar_0_0 = \r1 ->
            let {
             _evar_0_0 = let {
                          _evar_0_0 = \_ -> (,) Prelude.Nothing (Prelude.Just
                           (Build_IntervalDesc iv (Range.rbeg ( r1))
                           (Range.rend ( r1)) knd ((:[]) ( r1))))}
                         in
                          _evar_0_0}
            in
             _evar_0_0}
          in
          let {_evar_0_1 = \_ -> Logic.coq_False_rec} in
          case _top_assumption_1 of {
           Prelude.Just x -> _evar_0_0 x;
           Prelude.Nothing -> _evar_0_1}}
        in
        case _top_assumption_0 of {
         Prelude.Just x -> _evar_0_ x;
         Prelude.Nothing -> _evar_0_0}}
      in
      case _top_assumption_ of {
       (,) x x0 -> _evar_0_ x x0 __})
      (\r rs0 ->
      let {_top_assumption_ = Range.rangeSpan before ( r)} in
      let {
       _evar_0_ = \_top_assumption_0 ->
        let {
         _evar_0_ = \r0 _top_assumption_1 ->
          let {
           _evar_0_ = \r1 ->
            let {
             _evar_0_ = \_ ->
              (Prelude.flip (Prelude.$)) __ (\_ ->
                let {
                 _evar_0_ = \_ -> (,) (Prelude.Just (Build_IntervalDesc iv
                  (Range.rbeg ( r0)) (Range.rend ( r0)) lknd ((:[]) ( r0))))
                  (Prelude.Just (Build_IntervalDesc iv (Range.rbeg ( r1))
                  (Range.rend ( (Prelude.last rs0))) knd ((:) r1 rs0)))}
                in
                 _evar_0_ __)}
            in
             _evar_0_ __}
          in
          let {
           _evar_0_0 = \_ ->
            let {
             _evar_0_0 = \_ ->
              let {
               _top_assumption_2 = intervalSpan rs0 before iv
                                     (Range.rbeg ( (Prelude.head rs0)))
                                     (Range.rend ( (Prelude.last rs0))) knd}
              in
              let {
               _evar_0_0 = \_top_assumption_3 ->
                let {
                 _evar_0_0 = \i1_1 _top_assumption_4 ->
                  let {
                   _evar_0_0 = \i1_2 ->
                    case i1_1 of {
                     Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 ->
                      let {
                       _evar_0_0 = let {
                                    _evar_0_0 = \_ ->
                                     let {
                                      _evar_0_0 = \_ ->
                                       let {
                                        _evar_0_0 = \_ ->
                                         (Prelude.flip (Prelude.$)) __ (\_ ->
                                           let {
                                            _evar_0_0 = let {
                                                         _evar_0_0 = \_ _ _ ->
                                                          (,) (Prelude.Just
                                                          (Build_IntervalDesc
                                                          ivar0
                                                          (Range.rbeg ( r))
                                                          iend0 iknd0 ((:) r
                                                          rds0)))
                                                          (Prelude.Just
                                                          i1_2)}
                                                        in
                                                         _evar_0_0 __}
                                           in
                                            _evar_0_0)}
                                       in
                                        _evar_0_0 __}
                                     in
                                      _evar_0_0 __}
                                   in
                                    _evar_0_0}
                      in
                       _evar_0_0 __}}
                  in
                  let {
                   _evar_0_1 = \_ _ _ ->
                    case i1_1 of {
                     Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 ->
                      let {
                       _evar_0_1 = let {
                                    _evar_0_1 = \_ ->
                                     (Prelude.flip (Prelude.$)) __ (\_ ->
                                       (Prelude.flip (Prelude.$)) __ (\_ ->
                                         let {
                                          _evar_0_1 = \_ ->
                                           let {
                                            _evar_0_1 = \_ -> (,)
                                             (Prelude.Just
                                             (Build_IntervalDesc ivar0
                                             (Range.rbeg ( r)) iend0 iknd0
                                             ((:) r rds0))) Prelude.Nothing}
                                           in
                                            _evar_0_1 __}
                                         in
                                          _evar_0_1 __))}
                                   in
                                    _evar_0_1}
                      in
                       _evar_0_1 __}}
                  in
                  case _top_assumption_4 of {
                   Prelude.Just x -> (\_ -> _evar_0_0 x);
                   Prelude.Nothing -> _evar_0_1}}
                in
                let {
                 _evar_0_1 = \_top_assumption_4 ->
                  let {
                   _evar_0_1 = \i1_2 ->
                    case i1_2 of {
                     Build_IntervalDesc ivar0 ibeg0 iend0 iknd0 rds0 ->
                      let {
                       _evar_0_1 = let {
                                    _evar_0_1 = \_ ->
                                     let {
                                      _evar_0_1 = \_ _ ->
                                       let {
                                        _evar_0_1 = \_ ->
                                         let {
                                          _evar_0_1 = \_ ->
                                           let {
                                            _evar_0_1 = \_ ->
                                             (Prelude.flip (Prelude.$)) __
                                               (\_ -> (,) (Prelude.Just
                                               (Build_IntervalDesc iv
                                               (Range.rbeg ( r0))
                                               (Range.rend ( r0)) lknd ((:[])
                                               ( r0)))) (Prelude.Just
                                               (Build_IntervalDesc ivar0
                                               (Range.rbeg
                                                 ( (Prelude.head rds0)))
                                               (Range.rend
                                                 ( (Prelude.last rds0)))
                                               iknd0 rds0)))}
                                           in
                                            _evar_0_1 __}
                                         in
                                          _evar_0_1 __}
                                       in
                                        _evar_0_1 __}
                                     in
                                      _evar_0_1 __ __}
                                   in
                                    _evar_0_1}
                      in
                       _evar_0_1 __}}
                  in
                  let {_evar_0_2 = \_ _ _ -> Logic.coq_False_rec} in
                  case _top_assumption_4 of {
                   Prelude.Just x -> (\_ _ _ -> _evar_0_1 x);
                   Prelude.Nothing -> _evar_0_2}}
                in
                case _top_assumption_3 of {
                 Prelude.Just x -> _evar_0_0 x;
                 Prelude.Nothing -> _evar_0_1}}
              in
              case _top_assumption_2 of {
               (,) x x0 -> _evar_0_0 x x0 __ __ __}}
            in
             _evar_0_0 __}
          in
          case _top_assumption_1 of {
           Prelude.Just x -> (\_ -> _evar_0_ x);
           Prelude.Nothing -> _evar_0_0}}
        in
        let {
         _evar_0_0 = \_top_assumption_1 ->
          let {
           _evar_0_0 = \r1 ->
            let {
             _evar_0_0 = \_ ->
              let {
               _evar_0_0 = \_ ->
                let {
                 _evar_0_0 = \_ -> (,) Prelude.Nothing (Prelude.Just
                  (Build_IntervalDesc iv (Range.rbeg ( r1))
                  (Range.rend ( (Prelude.last rs0))) knd ((:) r1 rs0)))}
                in
                 _evar_0_0 __}
              in
               _evar_0_0 __}
            in
             _evar_0_0 __}
          in
          let {_evar_0_1 = \_ -> Logic.coq_False_rec} in
          case _top_assumption_1 of {
           Prelude.Just x -> (\_ -> _evar_0_0 x);
           Prelude.Nothing -> _evar_0_1}}
        in
        case _top_assumption_0 of {
         Prelude.Just x -> _evar_0_ x;
         Prelude.Nothing -> _evar_0_0}}
      in
      case _top_assumption_ of {
       (,) x x0 -> _evar_0_ x x0 __})
      rs}
  in
  case splitKind knd of {
   (,) x x0 -> _evar_0_ x x0}

