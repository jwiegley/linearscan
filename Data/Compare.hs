module Data.Compare where

import qualified Prelude
import qualified Data.List
import qualified Data.Specif as Specif


mk_cmp_eq_dec :: a1 -> a1 -> (a1 -> a1 -> Prelude.Ordering) ->
                 Specif.Coq_sumbool
mk_cmp_eq_dec x y cmp0 =
  let {c = cmp0 x y} in
  case c of {
   Prelude.LT -> Specif.Coq_left;
   _ -> Specif.Coq_right}

type CompareSpec a =
  a -> a -> Prelude.Ordering
  -- singleton inductive, whose constructor was Build_CompareSpec
  
cmp :: (CompareSpec a1) -> a1 -> a1 -> Prelude.Ordering
cmp compareSpec =
  compareSpec

cmp_eq_dec :: (CompareSpec a1) -> a1 -> a1 -> Specif.Coq_sumbool
cmp_eq_dec compareSpec x y =
  mk_cmp_eq_dec x y (cmp compareSpec)

