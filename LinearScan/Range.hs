module LinearScan.Range where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Logic as Logic
import qualified LinearScan.NonEmpty0 as NonEmpty0
import qualified LinearScan.Specif as Specif


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

getRangeDesc :: RangeDesc -> RangeDesc
getRangeDesc d =
  d

packRange :: RangeDesc -> RangeDesc
packRange d =
  d

rangesIntersect :: RangeDesc -> RangeDesc -> Prelude.Bool
rangesIntersect x y =
  case (Prelude.<=) (Prelude.succ (rbeg x)) (rbeg y) of {
   Prelude.True -> (Prelude.<=) (Prelude.succ (rbeg y)) (rend x);
   Prelude.False -> (Prelude.<=) (Prelude.succ (rbeg x)) (rend y)}

rangeIntersectionPoint :: RangeDesc -> RangeDesc -> Prelude.Maybe Prelude.Int
rangeIntersectionPoint x y =
  case rangesIntersect x y of {
   Prelude.True -> Prelude.Just (Prelude.min (rbeg x) (rbeg y));
   Prelude.False -> Prelude.Nothing}

findRangeUsePos :: RangeDesc -> (UsePos -> Prelude.Bool) -> Prelude.Maybe
                   UsePos
findRangeUsePos r f =
  let {n = ups r} in
  NonEmpty0.coq_NonEmpty_rec (\u ->
    let {b = f u} in
    case b of {
     Prelude.True -> Prelude.Just u;
     Prelude.False -> Prelude.Nothing}) (\u us iHus ->
    let {b = f u} in
    case b of {
     Prelude.True -> Prelude.Just u;
     Prelude.False -> iHus}) n

makeDividedRange :: (UsePos -> Prelude.Bool) -> RangeDesc ->
                    (NonEmpty0.NonEmpty UsePos) -> (NonEmpty0.NonEmpty
                    UsePos) ->
                    ((,) (Prelude.Maybe RangeDesc) (Prelude.Maybe RangeDesc))
makeDividedRange f rd l1 l2 =
  case rd of {
   Build_RangeDesc rbeg0 rend0 ups0 ->
    Logic.eq_rec_r (NonEmpty0.coq_NE_append l1 l2) (\_ -> (,) (Prelude.Just
      (Build_RangeDesc rbeg0 (Prelude.succ (uloc (NonEmpty0.coq_NE_last l1)))
      l1)) (Prelude.Just (Build_RangeDesc (uloc (NonEmpty0.coq_NE_head l2))
      rend0 l2))) ups0 __}

rangeSpan :: (UsePos -> Prelude.Bool) -> RangeDesc ->
             ((,) (Prelude.Maybe RangeDesc) (Prelude.Maybe RangeDesc))
rangeSpan f rd =
  case usePosSpan f (ups rd) of {
   (,) o o0 ->
    case o of {
     Prelude.Just l1 ->
      case o0 of {
       Prelude.Just l2 -> makeDividedRange f rd l1 l2;
       Prelude.Nothing -> (,) (Prelude.Just rd) Prelude.Nothing};
     Prelude.Nothing ->
      case o0 of {
       Prelude.Just n -> (,) Prelude.Nothing (Prelude.Just rd);
       Prelude.Nothing -> Lib.ex_falso_quodlibet}}}

type DefiniteSubRangesOf = ((,) RangeDesc RangeDesc)

splitRange :: (UsePos -> Prelude.Bool) -> RangeDesc -> (Specif.Coq_sig2
              UsePos) -> DefiniteSubRangesOf
splitRange f rd hl =
  let {s = rangeSpan f rd} in
  case s of {
   (,) o o0 ->
    case o of {
     Prelude.Just o1 ->
      case o0 of {
       Prelude.Just o2 -> (,) o1 o2;
       Prelude.Nothing -> Logic.coq_False_rec};
     Prelude.Nothing -> Logic.coq_False_rec}}

