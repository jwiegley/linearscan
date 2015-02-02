{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Seq where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Ssrbool as Ssrbool
import qualified LinearScan.Ssrfun as Ssrfun
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

nilp :: ([] a1) -> Prelude.Bool
nilp s =
  Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Data.List.length s))
    (unsafeCoerce 0)

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

rem :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort -> ([]
       Eqtype.Equality__Coq_sort) -> [] Eqtype.Equality__Coq_sort
rem t x s =
  case s of {
   [] -> s;
   (:) y t0 ->
    case Eqtype.eq_op t y x of {
     Prelude.True -> t0;
     Prelude.False -> (:) y (rem t x t0)}}

pmap :: (a1 -> Prelude.Maybe a2) -> ([] a1) -> [] a2
pmap f s =
  case s of {
   [] -> [];
   (:) x s' ->
    let {r = pmap f s'} in Ssrfun._Option__apply (\x0 -> (:) x0 r) r (f x)}

iota :: Prelude.Int -> Prelude.Int -> [] Prelude.Int
iota m n =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    [])
    (\n' -> (:) m
    (iota ((Prelude.succ) m) n'))
    n

