module LinearScan.List0 where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Datatypes as Datatypes


destruct_list :: ([] a1) -> Prelude.Maybe ((,) a1 ([] a1))
destruct_list l =
  Datatypes.list_rect Prelude.Nothing (\a tail iHtail -> Prelude.Just ((,) a
    tail)) l

fold_left :: (a1 -> a2 -> a1) -> ([] a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   [] -> a0;
   (:) b t -> fold_left f t (f a0 b)}

filter :: (a1 -> Prelude.Bool) -> ([] a1) -> [] a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

