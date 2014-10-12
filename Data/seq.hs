module Data.Seq where

import qualified Prelude
import qualified Data.List
import qualified Data.Ssrbool as Ssrbool


cat :: ([] a1) -> ([] a1) -> [] a1
cat s1 s2 =
  case s1 of {
   [] -> s2;
   (:) x s1' -> (:) x (cat s1' s2)}

filter :: (Ssrbool.Coq_pred a1) -> ([] a1) -> [] a1
filter a s =
  case s of {
   [] -> [];
   (:) x s' ->
    case a x of {
     Prelude.True -> (:) x (filter a s');
     Prelude.False -> filter a s'}}

map :: (a1 -> a2) -> ([] a1) -> [] a2
map f s =
  case s of {
   [] -> [];
   (:) x s' -> (:) (f x) (map f s')}

