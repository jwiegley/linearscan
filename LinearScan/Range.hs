module LinearScan.Range where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


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

usePosSpan :: Prelude.Int -> ([] UsePos) -> UsePosSublistsOf
usePosSpan before l =
  (\ns nc l -> case l of [x] -> ns x; (x:xs) -> nc x xs)
    (\x ->
    let {b = (Prelude.<=) ((Prelude.succ) (uloc x)) before} in
    case b of {
     Prelude.True -> (,) (Prelude.Just ((:[]) x)) Prelude.Nothing;
     Prelude.False -> (,) Prelude.Nothing (Prelude.Just ((:[]) x))})
    (\x xs ->
    let {b = (Prelude.<=) ((Prelude.succ) (uloc x)) before} in
    case b of {
     Prelude.True ->
      let {u = \_ -> usePosSpan before xs} in
      case u __ of {
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

type BoundedRange = RangeDesc

transportBoundedRange :: Prelude.Int -> Prelude.Int -> BoundedRange ->
                         BoundedRange
transportBoundedRange base prev x =
  x

type SortedBoundedRanges = ([] BoundedRange)

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

makeDividedRange :: RangeDesc -> Prelude.Int -> ([] UsePos) -> ([] UsePos) ->
                    ((,) (Prelude.Maybe RangeDesc) (Prelude.Maybe RangeDesc))
makeDividedRange rd before l1 l2 =
  case rd of {
   Build_RangeDesc rbeg0 rend0 ups0 ->
     (\_ -> (,) (Prelude.Just (Build_RangeDesc rbeg0 before l1))
      (Prelude.Just (Build_RangeDesc (uloc (Prelude.head l2)) rend0 l2))) __}

rangeSpan :: Prelude.Int -> RangeDesc ->
             ((,) (Prelude.Maybe RangeDesc) (Prelude.Maybe RangeDesc))
rangeSpan before rd =
  let {_top_assumption_ = usePosSpan before (ups rd)} in
  let {
   _evar_0_ = \_top_assumption_0 ->
    let {
     _evar_0_ = \o1 _top_assumption_1 ->
      let {_evar_0_ = \o2 -> makeDividedRange rd before o1 o2} in
      let {
       _evar_0_0 = \_ ->
        let {
         rd' = Build_RangeDesc (rbeg rd) (Prelude.min before (rend rd))
          (ups rd)}
        in
        (,) (Prelude.Just rd') Prelude.Nothing}
      in
      case _top_assumption_1 of {
       Prelude.Just x -> (\_ -> _evar_0_ x);
       Prelude.Nothing -> _evar_0_0}}
    in
    let {
     _evar_0_0 = \_top_assumption_1 ->
      let {
       _evar_0_0 = \o2 ->
        let {
         rd' = Build_RangeDesc (Prelude.max before (rbeg rd)) (rend rd)
          (ups rd)}
        in
        (,) Prelude.Nothing (Prelude.Just rd')}
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
   (,) x x0 -> _evar_0_ x x0 __}

