module LinearScan.Compare where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils

mk_cmp_eq_dec :: a1 -> a1 -> (a1 -> a1 -> Prelude.Ordering) -> Prelude.Bool
mk_cmp_eq_dec x y cmp0 =
  let {c = cmp0 x y} in
  case c of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

type CompareSpec a =
  a -> a -> Prelude.Ordering
  -- singleton inductive, whose constructor was Build_CompareSpec
  
cmp :: (CompareSpec a1) -> a1 -> a1 -> Prelude.Ordering
cmp compareSpec =
  compareSpec

cmp_eq_dec :: (CompareSpec a1) -> a1 -> a1 -> Prelude.Bool
cmp_eq_dec compareSpec x y =
  mk_cmp_eq_dec x y (cmp compareSpec)

