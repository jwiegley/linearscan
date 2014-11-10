module LinearScan.Lib where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype


__ :: any
__ = Prelude.error "Logical or arity value used"

ex_falso_quodlibet :: a1
ex_falso_quodlibet =
  Logic.coq_False_rect

uncurry_sig :: (a1 -> () -> a2) -> a1 -> a2
uncurry_sig f p =
  f p __

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

exist_in_cons :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort ->
                 ([] Eqtype.Equality__Coq_sort) -> Eqtype.Equality__Coq_sort
                 -> Eqtype.Equality__Coq_sort
exist_in_cons a a0 l _top_assumption_ =
  _top_assumption_

list_membership :: Eqtype.Equality__Coq_type -> ([]
                   Eqtype.Equality__Coq_sort) -> [] Eqtype.Equality__Coq_sort
list_membership a l =
  case l of {
   [] -> [];
   (:) x xs -> (:) x
    ((Prelude.map) (exist_in_cons a x xs) (list_membership a xs))}

sumlist :: ([] Prelude.Int) -> Prelude.Int
sumlist =
  Data.List.foldl' (Prelude.+) 0

widen_id :: Prelude.Int -> (Prelude.Int) -> (Prelude.Int)
widen_id n =
  Fintype.widen_ord n (Prelude.succ n)

widen_fst :: Prelude.Int -> ((,) (Prelude.Int) a1) -> (,) (Prelude.Int) a1
widen_fst n p =
  (,) (widen_id n ((Prelude.fst) p)) ((Prelude.snd) p)

insert :: (a1 -> Prelude.Bool) -> a1 -> ([] a1) -> [] a1
insert p z l =
  case l of {
   [] -> (:) z [];
   (:) x xs ->
    case p x of {
     Prelude.True -> (:) x (insert p z xs);
     Prelude.False -> (:) z ((:) x xs)}}

lebf :: (a1 -> Prelude.Int) -> a1 -> a1 -> Prelude.Bool
lebf f n m =
  (Prelude.<=) (f n) (f m)

