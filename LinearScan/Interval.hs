{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Interval where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Range as Range
import qualified LinearScan.Eqtype as Eqtype
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

data IntervalDesc =
   Build_IntervalDesc Prelude.Int Prelude.Int ([] Range.RangeDesc)

ibeg :: IntervalDesc -> Prelude.Int
ibeg i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> ibeg0}

iend :: IntervalDesc -> Prelude.Int
iend i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> iend0}

rds :: IntervalDesc -> [] Range.RangeDesc
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
    ((Prelude.<=) ((Prelude.succ) pos) (intervalEnd d))

intervalExtent :: IntervalDesc -> Prelude.Int
intervalExtent d =
  (Prelude.-) (intervalEnd d) (intervalStart d)

coq_Interval_is_singleton :: IntervalDesc -> Prelude.Bool
coq_Interval_is_singleton d =
  (Prelude.&&)
    (Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Prelude.length (rds d)))
      (unsafeCoerce ((Prelude.succ) 0)))
    (Eqtype.eq_op Ssrnat.nat_eqType
      (unsafeCoerce (Prelude.length (Range.ups ( (Prelude.head (rds d))))))
      (unsafeCoerce ((Prelude.succ) 0)))

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
findIntervalUsePos i f =
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
  in go (rds i)

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

lastUsePos :: IntervalDesc -> Prelude.Int
lastUsePos d =
  Range.uloc (Prelude.last (Range.ups ( (Prelude.last (rds d)))))

splitPosition :: IntervalDesc -> (Prelude.Maybe Prelude.Int) -> Prelude.Bool
                 -> Prelude.Int
splitPosition d before splitBeforeLifetimeHole =
  let {initial = firstUsePos d} in
  let {final = lastUsePos d} in
  Prelude.max ((Prelude.succ) initial)
    (Prelude.min final
      (Lib.fromMaybe final (Lib.option_choose before (firstUseReqReg d))))

intervalSpan :: ([] Range.RangeDesc) -> Prelude.Int -> Prelude.Int ->
                Prelude.Int ->
                ((,) (Prelude.Maybe IntervalDesc)
                (Prelude.Maybe IntervalDesc))
intervalSpan rs before ib ie =
  let {f = \u -> (Prelude.<=) ((Prelude.succ) (Range.uloc u)) before} in
  (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
    (\r ->
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
                        (Range.rend ( r0)) ((:[]) ( r0)))) (Prelude.Just
                        (Build_IntervalDesc (Range.rbeg ( r1))
                        (Range.rend ( r1)) ((:[]) ( r1))))}
                      in
                       _evar_0_}
          in
           _evar_0_ __ __}
        in
        let {
         _evar_0_0 = \_ ->
          let {
           _evar_0_0 = \_ -> (,) (Prelude.Just (Build_IntervalDesc ib ie
            ((:[]) r))) Prelude.Nothing}
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
           _evar_0_0 = \_ -> (,) Prelude.Nothing (Prelude.Just
            (Build_IntervalDesc ib ie ((:[]) r)))}
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
    (\r rs0 ->
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
              (Prelude.flip (Prelude.$)) __ (\_ -> (,) (Prelude.Just
                (Build_IntervalDesc (Range.rbeg ( r0)) (Range.rend ( r0))
                ((:[]) ( r0)))) (Prelude.Just (Build_IntervalDesc
                (Range.rbeg ( r1)) (Range.rend ( (Prelude.last rs0))) ((:) r1
                rs0))))}
            in
             _evar_0_ __ __}
          in
           _evar_0_ __}
        in
        let {
         _evar_0_0 = \_ ->
          let {
           _evar_0_0 = \_ ->
            let {
             _evar_0_0 = \_ ->
              let {
               _top_assumption_2 = intervalSpan rs0 before
                                     (Range.rbeg ( (Prelude.head rs0)))
                                     (Range.rend ( (Prelude.last rs0)))}
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
                                          _evar_0_0 = (Prelude.flip (Prelude.$))
                                                        __ (\_ ->
                                                        let {
                                                         _evar_0_0 = \_ _ ->
                                                          (,) (Prelude.Just
                                                          (Build_IntervalDesc
                                                          (Range.rbeg ( r))
                                                          iend0 ((:) r
                                                          rds0)))
                                                          (Prelude.Just
                                                          i1_2)}
                                                        in
                                                         _evar_0_0 __)}
                                         in
                                          _evar_0_0}
                                       in
                                        _evar_0_0 __}
                                     in
                                      _evar_0_0 __}
                                   in
                                    _evar_0_0}
                      in
                       _evar_0_0 __ __}}
                  in
                  let {
                   _evar_0_1 = \_ ->
                    let {
                     _evar_0_1 = \_ _ _ -> (,) (Prelude.Just
                      (Build_IntervalDesc (Range.rbeg ( r))
                      (Range.rend ( (Prelude.last rs0))) ((:) r rs0)))
                      Prelude.Nothing}
                    in
                     _evar_0_1 __}
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
                      (Build_IntervalDesc ib (Range.rend ( r)) ((:[]) r)))
                      (Prelude.Just (Build_IntervalDesc
                      (Range.rbeg ( (Prelude.head rs0)))
                      (Range.rend ( (Prelude.last rs0))) rs0))}
                    in
                     _evar_0_1 __}
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
             _evar_0_0 __}
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
           _evar_0_0 = \_ -> (,) Prelude.Nothing (Prelude.Just
            (Build_IntervalDesc ib ie ((:) r rs0)))}
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
    rs

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
          let {_evar_0_0 = \_ -> Logic.coq_False_rec} in  _evar_0_0 __}
        in
        case _top_assumption_1 of {
         Prelude.Just x -> (\_ -> _evar_0_ x);
         Prelude.Nothing -> _evar_0_0}}
      in
      let {
       _evar_0_0 = \_top_assumption_1 ->
        let {
         _evar_0_0 = \i1 ->
          let {_evar_0_0 = \_ -> Logic.coq_False_rec} in  _evar_0_0 __}
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

