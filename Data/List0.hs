module Data.List0 where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.Specif as Specif


destruct_list :: ([] a1) -> Specif.Coq_sumor (Specif.Coq_sigT a1 ([] a1))
destruct_list l =
  Datatypes.list_rect Specif.Coq_inright (\a tail iHtail -> Specif.Coq_inleft
    (Specif.Coq_existT a tail)) l

remove :: (a1 -> a1 -> Prelude.Either) -> a1 -> ([] a1) -> [] a1
remove eq_dec x l =
  case l of {
   [] -> [];
   (:) y tl ->
    case eq_dec x y of {
     Prelude.Left -> remove eq_dec x tl;
     Prelude.Right -> (:) y (remove eq_dec x tl)}}

