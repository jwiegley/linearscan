module LinearScan.Lib where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Logic as Logic


__ :: any
__ = Prelude.error "Logical or arity value used"

ex_falso_quodlibet :: a1
ex_falso_quodlibet =
  Logic.coq_False_rect

fromMaybe :: a1 -> (Prelude.Maybe a1) -> a1
fromMaybe d mx =
  case mx of {
   Prelude.Just x -> x;
   Prelude.Nothing -> d}

option_map :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
option_map f x =
  case x of {
   Prelude.Just x0 -> Prelude.Just (f x0);
   Prelude.Nothing -> Prelude.Nothing}

option_choose :: (Prelude.Maybe a1) -> (Prelude.Maybe a1) -> Prelude.Maybe a1
option_choose x y =
  case x of {
   Prelude.Just a -> x;
   Prelude.Nothing -> y}

foldl_with_index :: (Prelude.Int -> a2 -> a1 -> a2) -> a2 -> ([] a1) -> a2
foldl_with_index f b v =
  let {
   go n xs z =
     case xs of {
      [] -> z;
      (:) y ys -> go ((Prelude.succ) n) ys (f n z y)}}
  in go 0 v b

