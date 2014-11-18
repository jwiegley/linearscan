{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Interval where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.NonEmpty0 as NonEmpty0
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
    ((Prelude.<=) ((Prelude.succ) pos) (intervalEnd d))

intervalExtent :: IntervalDesc -> Prelude.Int
intervalExtent d =
  (Prelude.-) (intervalEnd d) (intervalStart d)

coq_Interval_is_singleton :: IntervalDesc -> Prelude.Bool
coq_Interval_is_singleton d =
  (Prelude.&&)
    (Eqtype.eq_op Ssrnat.nat_eqType
      (unsafeCoerce (NonEmpty0.coq_NE_length (rds d)))
      (unsafeCoerce ((Prelude.succ) 0)))
    (Eqtype.eq_op Ssrnat.nat_eqType
      (unsafeCoerce
        (NonEmpty0.coq_NE_length
          (Range.ups ( (NonEmpty0.coq_NE_head (rds d))))))
      (unsafeCoerce ((Prelude.succ) 0)))

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
  Lib.option_map ((Prelude..) Range.uloc Prelude.snd)
    (findIntervalUsePos d (\u ->
      (Prelude.<=) ((Prelude.succ) pos) (Range.uloc u)))

firstUsePos :: IntervalDesc -> Prelude.Int
firstUsePos d =
  Range.uloc
    (NonEmpty0.coq_NE_head (Range.ups ( (NonEmpty0.coq_NE_head (rds d)))))

firstUseReqReg :: IntervalDesc -> Prelude.Maybe Prelude.Int
firstUseReqReg d =
  Lib.option_map ((Prelude..) Range.uloc Prelude.snd)
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
  Prelude.max ((Prelude.succ) initial)
    (Prelude.min final
      (Lib.fromMaybe final (Lib.option_choose before (firstUseReqReg d))))

intervalSpan_subproof :: (NonEmpty0.NonEmpty Range.RangeDesc) -> Prelude.Int
                         -> Prelude.Int -> Prelude.Int ->
                         ((,) (Prelude.Maybe IntervalDesc)
                         (Prelude.Maybe IntervalDesc))
intervalSpan_subproof rs before ib ie =
  case rs of {
   NonEmpty0.NE_Sing r ->
    case Range.rangeSpan (\u ->
           (Prelude.<=) ((Prelude.succ) (Range.uloc u)) before) ( r) of {
     (,) _top_assumption_ x ->
      case _top_assumption_ of {
       Prelude.Just r0 ->
        case x of {
         Prelude.Just r1 ->
          
            ( (\_ _ -> (,) (Prelude.Just (Build_IntervalDesc
              (Range.rbeg ( r0)) (Range.rend ( r0)) (NonEmpty0.NE_Sing
              ( r0)))) (Prelude.Just (Build_IntervalDesc (Range.rbeg ( r1))
              (Range.rend ( r1)) (NonEmpty0.NE_Sing ( r1)))))) __ __;
         Prelude.Nothing ->
           (\_ -> (,) (Prelude.Just (Build_IntervalDesc ib ie
            (NonEmpty0.NE_Sing r))) Prelude.Nothing) __};
       Prelude.Nothing ->
        case x of {
         Prelude.Just r1 ->
           (\_ -> (,) Prelude.Nothing (Prelude.Just (Build_IntervalDesc ib ie
            (NonEmpty0.NE_Sing r)))) __;
         Prelude.Nothing -> Logic.coq_False_rec}}};
   NonEmpty0.NE_Cons r rs0 ->
    case Range.rangeSpan (\u ->
           (Prelude.<=) ((Prelude.succ) (Range.uloc u)) before) ( r) of {
     (,) _top_assumption_ x ->
      case _top_assumption_ of {
       Prelude.Just r0 ->
        case x of {
         Prelude.Just r1 ->
           (\_ ->
             (\_ _ ->
              (Prelude.flip (Prelude.$)) __ (\_ -> (,) (Prelude.Just
                (Build_IntervalDesc (Range.rbeg ( r0)) (Range.rend ( r0))
                (NonEmpty0.NE_Sing ( r0)))) (Prelude.Just (Build_IntervalDesc
                (Range.rbeg ( r1))
                (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                (NonEmpty0.NE_Cons r1 rs0))))) __ __) __;
         Prelude.Nothing ->
           (\_ ->
             (\_ ->
              case intervalSpan_subproof rs0 before
                     (Range.rbeg ( (NonEmpty0.coq_NE_head rs0)))
                     (Range.rend ( (NonEmpty0.coq_NE_last rs0))) of {
               (,) _top_assumption_0 x0 ->
                case _top_assumption_0 of {
                 Prelude.Just i1_1 ->
                  case x0 of {
                   Prelude.Just i1_2 ->
                    case i1_1 of {
                     Build_IntervalDesc ibeg0 iend0 rds0 ->
                      
                        ( (\_ _ ->
                           (\_ ->
                             (\_ ->
                              
                                ((Prelude.flip (Prelude.$)) __ (\_ ->
                                   (\_ _ -> (,) (Prelude.Just
                                    (Build_IntervalDesc (Range.rbeg ( r))
                                    iend0 (NonEmpty0.NE_Cons r rds0)))
                                    (Prelude.Just i1_2)) __))) __) __)) __ __
                        __};
                   Prelude.Nothing ->
                     (\_ _ _ -> (,) (Prelude.Just (Build_IntervalDesc
                      (Range.rbeg ( r))
                      (Range.rend ( (NonEmpty0.coq_NE_last rs0)))
                      (NonEmpty0.NE_Cons r rs0))) Prelude.Nothing) __ __ __};
                 Prelude.Nothing ->
                  case x0 of {
                   Prelude.Just i1_2 ->
                     (\_ _ _ -> (,) (Prelude.Just (Build_IntervalDesc ib
                      (Range.rend ( r)) (NonEmpty0.NE_Sing r))) (Prelude.Just
                      (Build_IntervalDesc
                      (Range.rbeg ( (NonEmpty0.coq_NE_head rs0)))
                      (Range.rend ( (NonEmpty0.coq_NE_last rs0))) rs0))) __
                      __ __;
                   Prelude.Nothing -> Logic.coq_False_rec}}}) __) __};
       Prelude.Nothing ->
        case x of {
         Prelude.Just r1 ->
           (\_ -> (,) Prelude.Nothing (Prelude.Just (Build_IntervalDesc ib ie
            (NonEmpty0.NE_Cons r rs0)))) __;
         Prelude.Nothing -> Logic.coq_False_rec}}}}

intervalSpan :: (NonEmpty0.NonEmpty Range.RangeDesc) -> Prelude.Int ->
                Prelude.Int -> Prelude.Int ->
                ((,) (Prelude.Maybe IntervalDesc)
                (Prelude.Maybe IntervalDesc))
intervalSpan rs before ib ie =
  intervalSpan_subproof rs before ib ie

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

