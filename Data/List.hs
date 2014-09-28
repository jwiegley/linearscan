module Data.List where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.Specif as Specif


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

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> ([] a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   [] -> a0;
   (:) b t -> fold_left f t (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> ([] a2) -> a1
fold_right f a0 l =
  case l of {
   [] -> a0;
   (:) b t -> f b (fold_right f a0 t)}

existsb :: (a1 -> Prelude.Bool) -> ([] a1) -> Prelude.Bool
existsb f l =
  case l of {
   [] -> Prelude.False;
   (:) a l0 -> (Prelude.||) (f a) (existsb f l0)}

filter :: (a1 -> Prelude.Bool) -> ([] a1) -> [] a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

