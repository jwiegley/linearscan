module Data.Compare_dec where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.Logic as Logic
import qualified Data.Specif as Specif


lt_eq_lt_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Specif.Coq_sumor
                Specif.Coq_sumbool
lt_eq_lt_dec n m =
  Datatypes.nat_rec (\m0 ->
    case m0 of {
     Datatypes.O -> Specif.Coq_inleft Specif.Coq_right;
     Datatypes.S m1 -> Specif.Coq_inleft Specif.Coq_left}) (\n0 iHn m0 ->
    case m0 of {
     Datatypes.O -> Specif.Coq_inright;
     Datatypes.S m1 -> iHn m1}) n m

le_lt_eq_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Specif.Coq_sumbool
le_lt_eq_dec n m =
  let {s = lt_eq_lt_dec n m} in
  case s of {
   Specif.Coq_inleft s0 -> s0;
   Specif.Coq_inright -> Logic.coq_False_rec}

nat_compare :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
               Datatypes.Coq_comparison
nat_compare n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Eq;
     Datatypes.S n0 -> Datatypes.Lt};
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Gt;
     Datatypes.S m' -> nat_compare n' m'}}

