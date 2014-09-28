module Data.List where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.Specif as Specif


destruct_list :: (Datatypes.Coq_list a1) -> Specif.Coq_sumor
                 (Specif.Coq_sigT a1 (Datatypes.Coq_list a1))
destruct_list l =
  Datatypes.list_rect Specif.Coq_inright (\a tail iHtail -> Specif.Coq_inleft
    (Specif.Coq_existT a tail)) l

remove :: (a1 -> a1 -> Specif.Coq_sumbool) -> a1 -> (Datatypes.Coq_list 
          a1) -> Datatypes.Coq_list a1
remove eq_dec x l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons y tl ->
    case eq_dec x y of {
     Specif.Coq_left -> remove eq_dec x tl;
     Specif.Coq_right -> Datatypes.Coq_cons y (remove eq_dec x tl)}}

map :: (a1 -> a2) -> (Datatypes.Coq_list a1) -> Datatypes.Coq_list a2
map f l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons a t -> Datatypes.Coq_cons (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (Datatypes.Coq_list a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   Datatypes.Coq_nil -> a0;
   Datatypes.Coq_cons b t -> fold_left f t (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (Datatypes.Coq_list a2) -> a1
fold_right f a0 l =
  case l of {
   Datatypes.Coq_nil -> a0;
   Datatypes.Coq_cons b t -> f b (fold_right f a0 t)}

existsb :: (a1 -> Datatypes.Coq_bool) -> (Datatypes.Coq_list a1) ->
           Datatypes.Coq_bool
existsb f l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons a l0 -> Datatypes.orb (f a) (existsb f l0)}

filter :: (a1 -> Datatypes.Coq_bool) -> (Datatypes.Coq_list a1) ->
          Datatypes.Coq_list a1
filter f l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons x l0 ->
    case f x of {
     Datatypes.Coq_true -> Datatypes.Coq_cons x (filter f l0);
     Datatypes.Coq_false -> filter f l0}}

