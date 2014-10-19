{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Interval where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Alternative as Alternative
import qualified LinearScan.Endo as Endo
import qualified LinearScan.NonEmpty0 as NonEmpty0
import qualified LinearScan.Range as Range



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

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
  Prelude.foldr (\r b ->
    (Prelude.||) b ((Prelude.any) (f r) (NonEmpty0.coq_NE_to_list (rds j))))
    Prelude.False (NonEmpty0.coq_NE_to_list (rds i))

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
      NonEmpty0.NE_Cons r rs' ->
       Alternative.choose (unsafeCoerce Alternative.option_Alternative)
         (f0 r) (go rs')}}
  in go (rds i)

nextUseAfter :: IntervalDesc -> Prelude.Int -> Prelude.Maybe Prelude.Int
nextUseAfter d pos =
  Endo.fmap (unsafeCoerce Endo.option_Functor)
    ((Prelude..) Range.uloc (Prelude.snd))
    (unsafeCoerce
      (findIntervalUsePos d (\u ->
        (Prelude.<=) (Prelude.succ pos) (Range.uloc u))))

firstUseReqReg :: IntervalDesc -> Prelude.Maybe Prelude.Int
firstUseReqReg d =
  Endo.fmap (unsafeCoerce Endo.option_Functor)
    ((Prelude..) Range.uloc (Prelude.snd))
    (unsafeCoerce (findIntervalUsePos d Range.regReq))

