module LinearScan.Range where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Lib as Lib


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
  ((,) (Prelude.Maybe ([] UsePos)) (Prelude.Maybe ([] UsePos)))

usePosSpan :: (UsePos -> Prelude.Bool) -> ([] UsePos) -> UsePosSublistsOf
usePosSpan f l =
  (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
    (\x ->
    let {b = f x} in
    case b of {
     Prelude.True -> (,) (Prelude.Just ((:[]) x)) Prelude.Nothing;
     Prelude.False -> (,) Prelude.Nothing (Prelude.Just ((:[]) x))})
    (\x xs ->
    let {b = f x} in
    case b of {
     Prelude.True ->
      let {u = usePosSpan f xs} in
      case u of {
       (,) o x0 ->
        case o of {
         Prelude.Just l1 ->
          case x0 of {
           Prelude.Just l2 -> (,) (Prelude.Just ((:) x l1)) (Prelude.Just l2);
           Prelude.Nothing -> (,) (Prelude.Just ((:) x l1)) Prelude.Nothing};
         Prelude.Nothing ->
          case x0 of {
           Prelude.Just l2 -> (,) (Prelude.Just ((:[]) x)) (Prelude.Just l2);
           Prelude.Nothing -> Prelude.error "absurd case"}}};
     Prelude.False -> (,) Prelude.Nothing (Prelude.Just ((:) x xs))})
    l

data RangeDesc =
   Build_RangeDesc Prelude.Int Prelude.Int ([] UsePos)

rbeg :: RangeDesc -> Prelude.Int
rbeg r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups0 -> rbeg0}

rend :: RangeDesc -> Prelude.Int
rend r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups0 -> rend0}

ups :: RangeDesc -> [] UsePos
ups r =
  case r of {
   Build_RangeDesc rbeg0 rend0 ups0 -> ups0}

rangesIntersect :: RangeDesc -> RangeDesc -> Prelude.Bool
rangesIntersect x y =
  case (Prelude.<=) ((Prelude.succ) (rbeg x)) (rbeg y) of {
   Prelude.True -> (Prelude.<=) ((Prelude.succ) (rbeg y)) (rend x);
   Prelude.False -> (Prelude.<=) ((Prelude.succ) (rbeg x)) (rend y)}

rangeIntersectionPoint :: RangeDesc -> RangeDesc -> Prelude.Maybe Prelude.Int
rangeIntersectionPoint x y =
  case rangesIntersect x y of {
   Prelude.True -> Prelude.Just (Prelude.min (rbeg x) (rbeg y));
   Prelude.False -> Prelude.Nothing}

findRangeUsePos :: RangeDesc -> (UsePos -> Prelude.Bool) -> Prelude.Maybe
                   UsePos
findRangeUsePos r f =
  let {
   go xs =
     (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
       (\x ->
       case f x of {
        Prelude.True -> Prelude.Just x;
        Prelude.False -> Prelude.Nothing})
       (\x xs0 ->
       case f x of {
        Prelude.True -> Prelude.Just x;
        Prelude.False -> go xs0})
       xs}
  in go (ups r)

makeDividedRange :: (UsePos -> Prelude.Bool) -> RangeDesc -> ([] UsePos) ->
                    ([] UsePos) ->
                    ((,) (Prelude.Maybe RangeDesc) (Prelude.Maybe RangeDesc))
makeDividedRange f rd l1 l2 =
  case rd of {
   Build_RangeDesc rbeg0 rend0 ups0 ->
     (\_ -> (,) (Prelude.Just (Build_RangeDesc rbeg0 ((Prelude.succ)
      (uloc (Prelude.last l1))) l1)) (Prelude.Just (Build_RangeDesc
      (uloc (Prelude.head l2)) rend0 l2))) __}

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

