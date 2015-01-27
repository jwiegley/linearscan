{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Seq where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Ssrbool as Ssrbool
import qualified LinearScan.Ssrnat as Ssrnat



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

ncons :: Prelude.Int -> a1 -> ([] a1) -> [] a1
ncons n x =
  Ssrnat.iter n (\x0 -> (:) x x0)

nseq :: Prelude.Int -> a1 -> [] a1
nseq n x =
  ncons n x []

last :: a1 -> ([] a1) -> a1
last x s =
  case s of {
   [] -> x;
   (:) x' s' -> last x' s'}

belast :: a1 -> ([] a1) -> [] a1
belast x s =
  case s of {
   [] -> [];
   (:) x' s' -> (:) x (belast x' s')}

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

count :: (Ssrbool.Coq_pred a1) -> ([] a1) -> Prelude.Int
count a s =
  case s of {
   [] -> 0;
   (:) x s' -> (Prelude.+) (Ssrnat.nat_of_bool (a x)) (count a s')}

catrev :: ([] a1) -> ([] a1) -> [] a1
catrev s1 s2 =
  case s1 of {
   [] -> s2;
   (:) x s1' -> catrev s1' ((:) x s2)}

rev :: ([] a1) -> [] a1
rev s =
  catrev s []

mem_seq :: Eqtype.Equality__Coq_type -> ([] Eqtype.Equality__Coq_sort) ->
           Eqtype.Equality__Coq_sort -> Prelude.Bool
mem_seq t s =
  case s of {
   [] -> (\x -> Prelude.False);
   (:) y s' ->
    let {p = mem_seq t s'} in (\x -> (Prelude.||) (Eqtype.eq_op t x y) (p x))}

type Coq_eqseq_class = [] Eqtype.Equality__Coq_sort

pred_of_eq_seq :: Eqtype.Equality__Coq_type -> Coq_eqseq_class ->
                  Ssrbool.Coq_pred_sort Eqtype.Equality__Coq_sort
pred_of_eq_seq t s =
  unsafeCoerce (\x -> mem_seq t s x)

seq_predType :: Eqtype.Equality__Coq_type -> Ssrbool.Coq_predType
                Eqtype.Equality__Coq_sort
seq_predType t =
  Ssrbool.mkPredType (unsafeCoerce (pred_of_eq_seq t))

undup :: Eqtype.Equality__Coq_type -> ([] Eqtype.Equality__Coq_sort) -> []
         Eqtype.Equality__Coq_sort
undup t s =
  case s of {
   [] -> [];
   (:) x s' ->
    case Ssrbool.in_mem x (Ssrbool.mem (seq_predType t) (unsafeCoerce s')) of {
     Prelude.True -> undup t s';
     Prelude.False -> (:) x (undup t s')}}

rem :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort -> ([]
       Eqtype.Equality__Coq_sort) -> [] Eqtype.Equality__Coq_sort
rem t x s =
  case s of {
   [] -> s;
   (:) y t0 ->
    case Eqtype.eq_op t y x of {
     Prelude.True -> t0;
     Prelude.False -> (:) y (rem t x t0)}}

