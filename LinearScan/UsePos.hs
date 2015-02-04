module LinearScan.UsePos where


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

