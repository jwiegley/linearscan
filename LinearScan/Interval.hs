module LinearScan.Interval where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.NonEmpty0 as NonEmpty0
import qualified LinearScan.Range as Range
import qualified LinearScan.Seq as Seq
import qualified LinearScan.Ssreflect as Ssreflect


__ :: any
__ = Prelude.error "Logical or arity value used"

data IntervalDesc =
   Build_IntervalDesc Prelude.Int Prelude.Int (NonEmpty0.NonEmpty
                                              Range.RangeSig)

ibeg :: IntervalDesc -> Prelude.Int
ibeg i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> ibeg0}

iend :: IntervalDesc -> Prelude.Int
iend i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> iend0}

rds :: IntervalDesc -> NonEmpty0.NonEmpty Range.RangeSig
rds i =
  case i of {
   Build_IntervalDesc ibeg0 iend0 rds0 -> rds0}

getIntervalDesc :: IntervalDesc -> IntervalDesc
getIntervalDesc d =
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
  Seq.has (\x -> Seq.has (f x) (NonEmpty0.coq_NE_to_list (rds j)))
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
                      Prelude.Maybe ((,) Range.RangeSig Range.UsePos)
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
  Lib.option_map ((Prelude..) Range.uloc (Prelude.snd))
    (findIntervalUsePos d (\u ->
      (Prelude.<=) (Prelude.succ pos) (Range.uloc u)))

firstUseReqReg :: IntervalDesc -> Prelude.Maybe Prelude.Int
firstUseReqReg d =
  Lib.option_map ((Prelude..) Range.uloc (Prelude.snd))
    (findIntervalUsePos d Range.regReq)

type IntervalSig = IntervalDesc

intervalSpan :: (NonEmpty0.NonEmpty Range.RangeSig) -> Prelude.Int ->
                Prelude.Int -> Prelude.Int ->
                ((,) (Prelude.Maybe IntervalSig) (Prelude.Maybe IntervalSig))
intervalSpan rs before ib ie =
  let {f = \u -> (Prelude.<=) (Prelude.succ (Range.uloc u)) before} in
  case rs of {
   NonEmpty0.NE_Sing r ->
    let {s = Range.rangeSpan f ( r)} in
    case s of {
     (,) o o0 ->
      case o of {
       Prelude.Just r0 ->
        case o0 of {
         Prelude.Just r1 -> (,) (Prelude.Just (Build_IntervalDesc
          (Range.rbeg ( r0)) (Range.rend ( r0)) (NonEmpty0.NE_Sing ( r0))))
          (Prelude.Just (Build_IntervalDesc (Range.rbeg ( r1))
          (Range.rend ( r1)) (NonEmpty0.NE_Sing ( r1))));
         Prelude.Nothing -> (,) (Prelude.Just (Build_IntervalDesc ib ie
          (NonEmpty0.NE_Sing r))) Prelude.Nothing};
       Prelude.Nothing ->
        case o0 of {
         Prelude.Just r0 -> (,) Prelude.Nothing (Prelude.Just
          (Build_IntervalDesc ib ie (NonEmpty0.NE_Sing r)));
         Prelude.Nothing -> Prelude.error "absurd case"}}};
   NonEmpty0.NE_Cons r rs0 ->
    let {s = Range.rangeSpan f ( r)} in
    case s of {
     (,) o o0 ->
      case o of {
       Prelude.Just r0 ->
        case o0 of {
         Prelude.Just r1 ->
          let {
           _evar_0_ = \_ ->
            Ssreflect.ssr_have __ (\_ -> (,) (Prelude.Just
              (Build_IntervalDesc (Range.rbeg ( r0)) (Range.rend ( r0))
              (NonEmpty0.NE_Sing ( r0)))) (Prelude.Just (Build_IntervalDesc
              (Range.rbeg
                ( (NonEmpty0.coq_NE_head (NonEmpty0.NE_Cons r1 rs0))))
              (Range.rend ( (NonEmpty0.coq_NE_last rs0))) (NonEmpty0.NE_Cons
              (NonEmpty0.coq_NE_head (NonEmpty0.NE_Cons r1 rs0)) rs0))))}
          in
          Logic.eq_rec_r (Range.rend ( (NonEmpty0.coq_NE_last rs0))) _evar_0_
            ie __;
         Prelude.Nothing ->
          let {
           _top_assumption_ = intervalSpan rs0 before
                                (Range.rbeg ( (NonEmpty0.coq_NE_head rs0)))
                                ie}
          in
          let {
           _evar_0_ = \_top_assumption_0 ->
            let {
             _evar_0_ = \o1 _top_assumption_1 ->
              let {
               _evar_0_ = \o2 ->
                let {
                 _evar_0_ = \_ -> (,) (Prelude.Just (Build_IntervalDesc
                  (Range.rbeg ( r))
                  (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                  (NonEmpty0.NE_Cons r rs0))) (Prelude.Just o2)}
                in
                Logic.eq_rec_r (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                  _evar_0_ ie __}
              in
              let {
               _evar_0_0 = \_ ->
                let {
                 _evar_0_0 = \_ -> (,) (Prelude.Just (Build_IntervalDesc
                  (Range.rbeg ( r))
                  (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                  (NonEmpty0.NE_Cons r rs0))) Prelude.Nothing}
                in
                Logic.eq_rec_r (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                  _evar_0_0 ie __}
              in
              case _top_assumption_1 of {
               Prelude.Just x -> (\_ -> _evar_0_ x);
               Prelude.Nothing -> _evar_0_0}}
            in
            let {
             _evar_0_0 = \_top_assumption_1 ->
              let {
               _evar_0_0 = \o1 -> (,) (Prelude.Just (Build_IntervalDesc ib
                (Range.rend ( r)) (NonEmpty0.NE_Sing r))) (Prelude.Just
                (Build_IntervalDesc
                (Range.rbeg ( (NonEmpty0.coq_NE_head rs0))) ie rs0))}
              in
              let {_evar_0_1 = \_ -> (,) Prelude.Nothing Prelude.Nothing} in
              case _top_assumption_1 of {
               Prelude.Just x -> (\_ -> _evar_0_0 x);
               Prelude.Nothing -> _evar_0_1}}
            in
            case _top_assumption_0 of {
             Prelude.Just x -> _evar_0_ x;
             Prelude.Nothing -> _evar_0_0}}
          in
          case _top_assumption_ of {
           (,) x x0 -> _evar_0_ x x0 __}};
       Prelude.Nothing ->
        case o0 of {
         Prelude.Just r0 -> (,) Prelude.Nothing (Prelude.Just
          (Build_IntervalDesc ib ie (NonEmpty0.NE_Cons r rs0)));
         Prelude.Nothing -> Prelude.error "absurd case"}}}}

splitInterval :: Prelude.Int -> IntervalDesc -> ((,) IntervalSig IntervalSig)
splitInterval before d =
  let {
   _evar_0_ = \ibeg0 iend0 rds0 ->
    let {_top_assumption_ = intervalSpan rds0 before ibeg0 iend0} in
    let {
     _evar_0_ = \_top_assumption_0 ->
      let {
       _evar_0_ = \o _top_assumption_1 ->
        let {_evar_0_ = \o0 -> (,) o o0} in
        let {
         _evar_0_0 = \_ ->
          let {_evar_0_0 = \_ _ _ -> Logic.coq_False_rec} in
          Logic.eq_rec (rds (Build_IntervalDesc ibeg0 iend0 rds0)) _evar_0_0
            (rds ( o)) __}
        in
        case _top_assumption_1 of {
         Prelude.Just x -> (\_ _ _ -> _evar_0_ x);
         Prelude.Nothing -> _evar_0_0}}
      in
      let {
       _evar_0_0 = \_top_assumption_1 ->
        let {
         _evar_0_0 = \o0 ->
          let {_evar_0_0 = \_ _ _ -> Logic.coq_False_rec} in
          Logic.eq_rec (rds (Build_IntervalDesc ibeg0 iend0 rds0)) _evar_0_0
            (rds ( o0)) __}
        in
        let {_evar_0_1 = \_ -> Prelude.error "absurd case"} in
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
   Build_IntervalDesc x x0 x1 -> _evar_0_ x x0 x1 __ __}

