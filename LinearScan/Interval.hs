module LinearScan.Interval where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.NonEmpty0 as NonEmpty0
import qualified LinearScan.Range as Range
import qualified LinearScan.Ssreflect as Ssreflect
import qualified LinearScan.Ssrfun as Ssrfun


__ :: any
__ = Prelude.error "Logical or arity value used"

data IntervalDesc =
   Build_IntervalDesc Prelude.Int Prelude.Int (NonEmpty0.NonEmpty
                                              Range.RangeDesc)

ibeg :: IntervalDesc -> Prelude.Int
ibeg i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> ibeg0}

iend :: IntervalDesc -> Prelude.Int
iend i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> iend0}

rds :: IntervalDesc -> NonEmpty0.NonEmpty Range.RangeDesc
rds i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> rds0}

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
    ((Prelude.<=) (Prelude.succ pos) (intervalEnd d))

intervalExtent :: IntervalDesc -> Prelude.Int
intervalExtent d =
  (Prelude.-) (intervalEnd d) (intervalStart d)

intervalsIntersect :: IntervalDesc -> IntervalDesc -> Prelude.Bool
intervalsIntersect i j =
  let {f = \x y -> Range.rangesIntersect ( x) ( y)} in
  Data.List.any (\x ->
    Data.List.any (f x) (NonEmpty0.coq_NE_to_list (rds j)))
    (NonEmpty0.coq_NE_to_list (rds i))

intervalIntersectionPoint :: IntervalDesc -> IntervalDesc -> Prelude.Maybe
                             Prelude.Int
intervalIntersectionPoint i j =
  NonEmpty0.coq_NE_fold_left (\acc rd ->
    case acc of {
     Prelude.Just x -> Prelude.Just x;
     Prelude.Nothing ->
      NonEmpty0.coq_NE_fold_left (\acc' rd' ->
        case acc' of {
         Prelude.Just x -> Prelude.Just x;
         Prelude.Nothing -> Range.rangeIntersectionPoint ( rd) ( rd')})
        (rds j) Prelude.Nothing}) (rds i) Prelude.Nothing

findIntervalUsePos :: IntervalDesc -> (Range.UsePos -> Prelude.Bool) ->
                      Prelude.Maybe ((,) Range.RangeDesc Range.UsePos)
findIntervalUsePos i f =
  let {
   f0 = \r ->
    case Range.findRangeUsePos r f of {
     Prelude.Just pos -> Prelude.Just ((,) r pos);
     Prelude.Nothing -> Prelude.Nothing}}
  in
  let {
   go rs =
     case rs of {
      NonEmpty0.NE_Sing r -> f0 r;
      NonEmpty0.NE_Cons r rs' -> Lib.option_choose (f0 r) (go rs')}}
  in go (rds i)

nextUseAfter :: IntervalDesc -> Prelude.Int -> Prelude.Maybe Prelude.Int
nextUseAfter d pos =
  Lib.option_map (Ssrfun.funcomp () Range.uloc Prelude.snd)
    (findIntervalUsePos d (\u ->
      (Prelude.<=) (Prelude.succ pos) (Range.uloc u)))

firstUsePos :: IntervalDesc -> Prelude.Int
firstUsePos d =
  Range.uloc
    (NonEmpty0.coq_NE_head (Range.ups ( (NonEmpty0.coq_NE_head (rds d)))))

firstUseReqReg :: IntervalDesc -> Prelude.Maybe Prelude.Int
firstUseReqReg d =
  Lib.option_map (Ssrfun.funcomp () Range.uloc Prelude.snd)
    (findIntervalUsePos d Range.regReq)

lastUsePos :: IntervalDesc -> Prelude.Int
lastUsePos d =
  Range.uloc
    (NonEmpty0.coq_NE_last (Range.ups ( (NonEmpty0.coq_NE_last (rds d)))))

splitPosition :: IntervalDesc -> (Prelude.Maybe Prelude.Int) -> Prelude.Bool
                 -> Prelude.Int
splitPosition d before splitBeforeLifetimeHole =
  let {initial = firstUsePos d} in
  let {final = lastUsePos d} in
  Prelude.max (Prelude.succ initial)
    (Prelude.min final
      (Lib.fromMaybe final (Lib.option_choose before (firstUseReqReg d))))

intervalSpan :: (NonEmpty0.NonEmpty Range.RangeDesc) -> Prelude.Int ->
                Prelude.Int -> Prelude.Int ->
                ((,) (Prelude.Maybe IntervalDesc)
                (Prelude.Maybe IntervalDesc))
intervalSpan rs before ib ie =
  let {f = \u -> (Prelude.<=) (Prelude.succ (Range.uloc u)) before} in
  case rs of {
   NonEmpty0.NE_Sing r ->
    let {_top_assumption_ = Range.rangeSpan f ( r)} in
    let {
     _evar_0_ = \_top_assumption_0 ->
      let {
       _evar_0_ = \r0 _top_assumption_1 ->
        let {
         _evar_0_ = \r1 ->
          let {
           _evar_0_ = let {
                       _evar_0_ = \_ _ -> (,) (Prelude.Just
                        (Build_IntervalDesc (Range.rbeg ( r0))
                        (Range.rend ( r0)) (NonEmpty0.NE_Sing ( r0))))
                        (Prelude.Just (Build_IntervalDesc (Range.rbeg ( r1))
                        (Range.rend ( r1)) (NonEmpty0.NE_Sing ( r1))))}
                      in
                      Logic.eq_rec_r (Range.rend ( r1)) _evar_0_
                        (Range.rend
                          (Range.getRangeDesc
                            (
                              (NonEmpty0.coq_NE_last
                                (rds (Build_IntervalDesc ib ie
                                  (NonEmpty0.NE_Sing r)))))))}
          in
          Logic.eq_rec_r (Range.rbeg ( r0)) _evar_0_
            (Range.rbeg
              (Range.getRangeDesc
                (
                  (NonEmpty0.coq_NE_head
                    (rds (Build_IntervalDesc ib ie (NonEmpty0.NE_Sing r)))))))
            __ __}
        in
        let {
         _evar_0_0 = \_ ->
          let {
           _evar_0_0 = \_ -> (,) (Prelude.Just (Build_IntervalDesc ib ie
            (NonEmpty0.NE_Sing r))) Prelude.Nothing}
          in
          Logic.eq_rec (Range.ups ( r)) _evar_0_0 (Range.ups ( r0)) __}
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
           _evar_0_0 = \_ -> (,) Prelude.Nothing (Prelude.Just
            (Build_IntervalDesc ib ie (NonEmpty0.NE_Sing r)))}
          in
          Logic.eq_rec (Range.ups ( r)) _evar_0_0 (Range.ups ( r1)) __}
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
     (,) x x0 -> _evar_0_ x x0 __};
   NonEmpty0.NE_Cons r rs0 ->
    let {_top_assumption_ = Range.rangeSpan f ( r)} in
    let {
     _evar_0_ = \_top_assumption_0 ->
      let {
       _evar_0_ = \r0 _top_assumption_1 ->
        let {
         _evar_0_ = \r1 ->
          let {
           _evar_0_ = \_ ->
            let {
             _evar_0_ = \_ _ ->
              Ssreflect.ssr_have __ (\_ -> (,) (Prelude.Just
                (Build_IntervalDesc (Range.rbeg ( r0)) (Range.rend ( r0))
                (NonEmpty0.NE_Sing ( r0)))) (Prelude.Just (Build_IntervalDesc
                (Range.rbeg ( r1))
                (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                (NonEmpty0.NE_Cons r1 rs0))))}
            in
            Logic.eq_rec_r (Range.rbeg ( r0)) _evar_0_
              (Range.rbeg
                (Range.getRangeDesc
                  (
                    (NonEmpty0.coq_NE_head
                      (rds (Build_IntervalDesc ib ie (NonEmpty0.NE_Cons r
                        rs0))))))) __ __}
          in
          Logic.eq_rec_r (Range.rend ( (NonEmpty0.coq_NE_last rs0))) _evar_0_
            ie __}
        in
        let {
         _evar_0_0 = \_ ->
          let {
           _evar_0_0 = \_ ->
            let {
             _evar_0_0 = \_ ->
              let {
               _top_assumption_2 = intervalSpan rs0 before
                                     (Range.rbeg
                                       ( (NonEmpty0.coq_NE_head rs0)))
                                     (Range.rend
                                       ( (NonEmpty0.coq_NE_last rs0)))}
              in
              let {
               _evar_0_0 = \_top_assumption_3 ->
                let {
                 _evar_0_0 = \i1_1 _top_assumption_4 ->
                  let {
                   _evar_0_0 = \i1_2 ->
                    case i1_1 of {
                     Build_IntervalDesc ibeg0 iend0 rds0 ->
                      let {
                       _evar_0_0 = let {
                                    _evar_0_0 = \_ _ ->
                                     let {
                                      _evar_0_0 = \_ ->
                                       let {
                                        _evar_0_0 = \_ ->
                                         let {
                                          _evar_0_0 = Ssreflect.ssr_have __
                                                        (\_ ->
                                                        let {
                                                         _evar_0_0 = \_ _ ->
                                                          (,) (Prelude.Just
                                                          (Build_IntervalDesc
                                                          (Range.rbeg ( r))
                                                          iend0
                                                          (NonEmpty0.NE_Cons
                                                          r rds0)))
                                                          (Prelude.Just
                                                          i1_2)}
                                                        in
                                                        Logic.eq_rec iend0
                                                          _evar_0_0
                                                          (Range.rend
                                                            (
                                                              (NonEmpty0.coq_NE_last
                                                                rds0))) __)}
                                         in
                                         Logic.eq_rec_r (iend ( i1_2))
                                           _evar_0_0
                                           (Range.rend
                                             ( (NonEmpty0.coq_NE_last rs0)))}
                                       in
                                       Logic.eq_rec_r
                                         (Range.rbeg
                                           ( (NonEmpty0.coq_NE_head rds0)))
                                         _evar_0_0
                                         (Range.rbeg
                                           ( (NonEmpty0.coq_NE_head rs0))) __}
                                     in
                                     Logic.eq_rec_r
                                       (Range.rbeg
                                         ( (NonEmpty0.coq_NE_head rds0)))
                                       _evar_0_0 ibeg0 __}
                                   in
                                   Logic.eq_rec_r
                                     (Range.rend
                                       ( (NonEmpty0.coq_NE_last rds0)))
                                     _evar_0_0 iend0}
                      in
                      Logic.eq_rec_r
                        (Range.rbeg ( (NonEmpty0.coq_NE_head rds0)))
                        _evar_0_0 ibeg0 __ __}}
                  in
                  let {
                   _evar_0_1 = \_ ->
                    let {
                     _evar_0_1 = \_ _ _ -> (,) (Prelude.Just
                      (Build_IntervalDesc (Range.rbeg ( r))
                      (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                      (NonEmpty0.NE_Cons r rs0))) Prelude.Nothing}
                    in
                    Logic.eq_rec
                      (rds (Build_IntervalDesc
                        (Range.rbeg ( (NonEmpty0.coq_NE_head rs0)))
                        (Range.rend ( (NonEmpty0.coq_NE_last rs0))) rs0))
                      _evar_0_1 (rds ( i1_1)) __}
                  in
                  case _top_assumption_4 of {
                   Prelude.Just x -> (\_ _ -> _evar_0_0 x);
                   Prelude.Nothing -> _evar_0_1}}
                in
                let {
                 _evar_0_1 = \_top_assumption_4 ->
                  let {
                   _evar_0_1 = \i1_2 ->
                    let {
                     _evar_0_1 = \_ _ _ -> (,) (Prelude.Just
                      (Build_IntervalDesc ib (Range.rend ( r))
                      (NonEmpty0.NE_Sing r))) (Prelude.Just
                      (Build_IntervalDesc
                      (Range.rbeg ( (NonEmpty0.coq_NE_head rs0)))
                      (Range.rend ( (NonEmpty0.coq_NE_last rs0))) rs0))}
                    in
                    Logic.eq_rec
                      (rds (Build_IntervalDesc
                        (Range.rbeg ( (NonEmpty0.coq_NE_head rs0)))
                        (Range.rend ( (NonEmpty0.coq_NE_last rs0))) rs0))
                      _evar_0_1 (rds ( i1_2)) __}
                  in
                  let {_evar_0_2 = \_ _ _ -> Logic.coq_False_rec} in
                  case _top_assumption_4 of {
                   Prelude.Just x -> (\_ -> _evar_0_1 x);
                   Prelude.Nothing -> _evar_0_2}}
                in
                case _top_assumption_3 of {
                 Prelude.Just x -> _evar_0_0 x;
                 Prelude.Nothing -> _evar_0_1}}
              in
              case _top_assumption_2 of {
               (,) x x0 -> _evar_0_0 x x0 __ __ __}}
            in
            Logic.eq_rec_r (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
              _evar_0_0 ie __}
          in
          Logic.eq_rec (Range.ups ( r)) _evar_0_0 (Range.ups ( r0)) __}
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
           _evar_0_0 = \_ -> (,) Prelude.Nothing (Prelude.Just
            (Build_IntervalDesc ib ie (NonEmpty0.NE_Cons r rs0)))}
          in
          Logic.eq_rec (Range.ups ( r)) _evar_0_0 (Range.ups ( r1)) __}
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
     (,) x x0 -> _evar_0_ x x0 __}}

splitInterval :: Prelude.Int -> IntervalDesc ->
                 ((,) IntervalDesc IntervalDesc)
splitInterval before d =
  let {
   _evar_0_ = \ib ie rds0 ->
    let {_top_assumption_ = intervalSpan rds0 before ib ie} in
    let {
     _evar_0_ = \_top_assumption_0 ->
      let {
       _evar_0_ = \i0 _top_assumption_1 ->
        let {_evar_0_ = \i1 -> (,) i0 i1} in
        let {
         _evar_0_0 = \_ ->
          let {_evar_0_0 = \_ -> Logic.coq_False_rec} in
          Logic.eq_rec (rds (Build_IntervalDesc ib ie rds0)) _evar_0_0
            (rds ( i0)) __}
        in
        case _top_assumption_1 of {
         Prelude.Just x -> (\_ -> _evar_0_ x);
         Prelude.Nothing -> _evar_0_0}}
      in
      let {
       _evar_0_0 = \_top_assumption_1 ->
        let {
         _evar_0_0 = \i1 ->
          let {_evar_0_0 = \_ -> Logic.coq_False_rec} in
          Logic.eq_rec (rds (Build_IntervalDesc ib ie rds0)) _evar_0_0
            (rds ( i1)) __}
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
     (,) x x0 -> _evar_0_ x x0 __}}
  in
  case d of {
   Build_IntervalDesc x x0 x1 -> _evar_0_ x x0 x1}

