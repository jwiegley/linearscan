module LinearScan.List0 where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Specif as Specif


destruct_list :: ([] a1) -> Specif.Coq_sumor (Specif.Coq_sigT a1 ([] a1))
destruct_list l =
  Datatypes.list_rect Specif.Coq_inright (\a tail iHtail -> Specif.Coq_inleft
    (Specif.Coq_existT a tail)) l

remove :: (a1 -> a1 -> Specif.Coq_sumbool) -> a1 -> ([] a1) -> [] a1
remove eq_dec x l =
  case l of {
   [] -> [];
   (:) y tl ->
    case eq_dec x y of {
     Specif.Coq_left -> remove eq_dec x tl;
     Specif.Coq_right -> (:) y (remove eq_dec x tl)}}

