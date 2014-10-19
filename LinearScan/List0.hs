module LinearScan.List0 where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Datatypes as Datatypes


destruct_list :: ([] a1) -> Prelude.Maybe ((,) a1 ([] a1))
destruct_list l =
  Datatypes.list_rect Prelude.Nothing (\a tail iHtail -> Prelude.Just ((,) a
    tail)) l

remove :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] a1) -> [] a1
remove eq_dec x l =
  case l of {
   [] -> [];
   (:) y tl ->
    case eq_dec x y of {
     Prelude.True -> remove eq_dec x tl;
     Prelude.False -> (:) y (remove eq_dec x tl)}}

