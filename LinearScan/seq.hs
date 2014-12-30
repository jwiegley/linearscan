module LinearScan.Seq where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Ssrnat as Ssrnat


ncons :: Prelude.Int -> a1 -> ([] a1) -> [] a1
ncons n x =
  Ssrnat.iter n (\x0 -> (:) x x0)

nth :: a1 -> ([] a1) -> Prelude.Int -> a1
nth x0 s n =
  case s of {
   [] -> x0;
   (:) x s' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      x)
      (\n' ->
      nth x0 s' n')
      n}

set_nth :: a1 -> ([] a1) -> Prelude.Int -> a1 -> [] a1
set_nth x0 s n y =
  case s of {
   [] -> ncons n x0 ((:) y []);
   (:) x s' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> (:) y
      s')
      (\n' -> (:) x
      (set_nth x0 s' n' y))
      n}

catrev :: ([] a1) -> ([] a1) -> [] a1
catrev s1 s2 =
  case s1 of {
   [] -> s2;
   (:) x s1' -> catrev s1' ((:) x s2)}

rev :: ([] a1) -> [] a1
rev s =
  catrev s []

rem :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort -> ([]
       Eqtype.Equality__Coq_sort) -> [] Eqtype.Equality__Coq_sort
rem t x s =
  case s of {
   [] -> s;
   (:) y t0 ->
    case Eqtype.eq_op t y x of {
     Prelude.True -> t0;
     Prelude.False -> (:) y (rem t x t0)}}

flatten :: ([] ([] a1)) -> [] a1
flatten =
  Prelude.foldr (Prelude.++) []

