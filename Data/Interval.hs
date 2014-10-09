{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Data.Interval where

import qualified Prelude
import qualified Data.List
import qualified Data.Alternative as Alternative
import qualified Data.Basics as Basics
import qualified Data.Datatypes as Datatypes
import qualified Data.Endo as Endo
import qualified Data.NPeano as NPeano
import qualified Data.NonEmpty0 as NonEmpty0
import qualified Data.Peano as Peano
import qualified Data.Range as Range



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified Data.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

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

intervalStart :: IntervalDesc -> Prelude.Int
intervalStart i =
  ibeg i

intervalEnd :: IntervalDesc -> Prelude.Int
intervalEnd i =
  iend i

intervalCoversPos :: IntervalDesc -> Prelude.Int -> Prelude.Bool
intervalCoversPos d pos =
  (Prelude.&&) (NPeano.leb (intervalStart d) pos)
    (NPeano.ltb pos (intervalEnd d))

intervalExtent :: IntervalDesc -> Prelude.Int
intervalExtent d =
  Peano.minus (intervalEnd d) (intervalStart d)

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
      NonEmpty0.NE_Cons r rs' ->
       Alternative.choose (unsafeCoerce Alternative.option_Alternative)
         (f0 r) (go rs')}}
  in go (rds i)

nextUseAfter :: IntervalDesc -> Prelude.Int -> Prelude.Maybe Prelude.Int
nextUseAfter d pos =
  Endo.fmap (unsafeCoerce Endo.option_Functor)
    (Basics.compose Range.uloc Datatypes.snd)
    (unsafeCoerce
      (findIntervalUsePos d (\u -> NPeano.ltb pos (Range.uloc u))))

firstUseReqReg :: IntervalDesc -> Prelude.Maybe Prelude.Int
firstUseReqReg d =
  Endo.fmap (unsafeCoerce Endo.option_Functor)
    (Basics.compose Range.uloc Datatypes.snd)
    (unsafeCoerce (findIntervalUsePos d Range.regReq))

