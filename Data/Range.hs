{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Data.Range where

import qualified Prelude
import qualified Data.List
import qualified Data.Alternative as Alternative
import qualified Data.Logic as Logic
import qualified Data.NPeano as NPeano
import qualified Data.NonEmpty0 as NonEmpty0
import qualified Data.Peano as Peano



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified Data.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data UsePos =
   Build_UsePos Prelude.Int Prelude.Bool

uloc :: UsePos -> Prelude.Int
uloc u =
  case u of {
   Build_UsePos uloc0 regReq0 -> uloc0}

regReq :: UsePos -> Prelude.Bool
regReq u =
  case u of {
   Build_UsePos uloc0 regReq0 -> regReq0}

type UsePosSublistsOf =
  ((,) (Prelude.Maybe (NonEmpty0.NonEmpty UsePos))
  (Prelude.Maybe (NonEmpty0.NonEmpty UsePos)))

usePosSpan :: (UsePos -> Prelude.Bool) -> (NonEmpty0.NonEmpty UsePos) ->
              UsePosSublistsOf
usePosSpan f l =
  case l of {
   NonEmpty0.NE_Sing x ->
    let {b = f x} in
    case b of {
     Prelude.True -> (,) (Prelude.Just (NonEmpty0.NE_Sing x)) Prelude.Nothing;
     Prelude.False -> (,) Prelude.Nothing (Prelude.Just (NonEmpty0.NE_Sing
      x))};
   NonEmpty0.NE_Cons x xs ->
    let {b = f x} in
    case b of {
     Prelude.True ->
      let {u = usePosSpan f xs} in
      case u of {
       (,) o x0 ->
        case o of {
         Prelude.Just l1 ->
          case x0 of {
           Prelude.Just l2 -> (,) (Prelude.Just (NonEmpty0.NE_Cons x l1))
            (Prelude.Just l2);
           Prelude.Nothing -> (,) (Prelude.Just (NonEmpty0.NE_Cons x l1))
            Prelude.Nothing};
         Prelude.Nothing ->
          case x0 of {
           Prelude.Just l2 -> (,) (Prelude.Just (NonEmpty0.NE_Sing x))
            (Prelude.Just l2);
           Prelude.Nothing -> Prelude.error "absurd case"}}};
     Prelude.False -> (,) Prelude.Nothing (Prelude.Just (NonEmpty0.NE_Cons x
      xs))}}

data RangeDesc =
   Build_RangeDesc Prelude.Int Prelude.Int (NonEmpty0.NonEmpty UsePos)

rbeg :: RangeDesc -> Prelude.Int
rbeg r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups0 -> rbeg0}

rend :: RangeDesc -> Prelude.Int
rend r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups0 -> rend0}

ups :: RangeDesc -> NonEmpty0.NonEmpty UsePos
ups r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups0 -> ups0}

type RangeSig = RangeDesc

rangesIntersect :: RangeDesc -> RangeDesc -> Prelude.Bool
rangesIntersect x y =
  case NPeano.ltb (rbeg x) (rbeg y) of {
   Prelude.True -> NPeano.ltb (rbeg y) (rend x);
   Prelude.False -> NPeano.ltb (rbeg x) (rend y)}

rangeIntersectionPoint :: RangeDesc -> RangeDesc -> Prelude.Maybe Prelude.Int
rangeIntersectionPoint x y =
  case rangesIntersect x y of {
   Prelude.True -> Prelude.Just (Peano.min (rbeg x) (rbeg y));
   Prelude.False -> Prelude.Nothing}

findRangeUsePos :: RangeDesc -> (UsePos -> Prelude.Bool) -> Prelude.Maybe
                   UsePos
findRangeUsePos r f =
  let {
   check = \u ->
    case f u of {
     Prelude.True -> Prelude.Just u;
     Prelude.False -> Prelude.Nothing}}
  in
  let {
   go us =
     case us of {
      NonEmpty0.NE_Sing u -> check u;
      NonEmpty0.NE_Cons u us' ->
       Alternative.choose (unsafeCoerce Alternative.option_Alternative)
         (check u) (go us')}}
  in go (ups r)

rangeSpan :: (UsePos -> Prelude.Bool) -> RangeDesc ->
             ((,) (Prelude.Maybe RangeSig) (Prelude.Maybe RangeSig))
rangeSpan f rd =
  case rd of {
   Build_RangeDesc rbeg0 rend0 ups0 ->
    let {u = usePosSpan f ups0} in
    case u of {
     (,) o x ->
      case o of {
       Prelude.Just l1 ->
        case x of {
         Prelude.Just l2 ->
          let {rd0 = Build_RangeDesc rbeg0 rend0 ups0} in
          Logic.eq_rec_r (NonEmpty0.coq_NE_append l1 l2) (\_ _ ->
            Logic.eq_rec_r (Build_RangeDesc rbeg0 rend0
              (NonEmpty0.coq_NE_append l1 l2)) (\_ ->
              Logic.and_rec (\_ _ ->
                Logic.and_rec (\_ _ ->
                  Logic.and_rec (\_ _ -> (,) (Prelude.Just (Build_RangeDesc
                    rbeg0 (Prelude.succ (uloc (NonEmpty0.coq_NE_last l1)))
                    l1)) (Prelude.Just (Build_RangeDesc
                    (uloc (NonEmpty0.coq_NE_head l2)) rend0 l2)))))) rd0 __)
            ups0 __ __;
         Prelude.Nothing ->
          let {rd0 = Build_RangeDesc rbeg0 rend0 ups0} in
          (,) (Prelude.Just rd0) Prelude.Nothing};
       Prelude.Nothing ->
        case x of {
         Prelude.Just l2 ->
          let {rd0 = Build_RangeDesc rbeg0 rend0 ups0} in
          (,) Prelude.Nothing (Prelude.Just rd0);
         Prelude.Nothing -> Logic.coq_False_rec}}}}

type DefiniteSubRangesOf = ((,) RangeSig RangeSig)

splitRange :: (UsePos -> Prelude.Bool) -> RangeDesc -> DefiniteSubRangesOf
splitRange f rd =
  let {s = rangeSpan f rd} in
  case s of {
   (,) o o0 ->
    case o of {
     Prelude.Just o1 ->
      case o0 of {
       Prelude.Just o2 -> (,) o1 o2;
       Prelude.Nothing -> Logic.coq_False_rec};
     Prelude.Nothing -> Logic.coq_False_rec}}

