module LinearScan.Compare_dec where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Logic as Logic


lt_eq_lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Maybe Prelude.Bool
lt_eq_lt_dec n m =
  Datatypes.nat_rec (\m0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.Just
      Prelude.False)
      (\m1 -> Prelude.Just
      Prelude.True)
      m0) (\n0 iHn m0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.Nothing)
      (\m1 ->
      iHn m1)
      m0) n m

le_lt_eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
le_lt_eq_dec n m =
  let {s = lt_eq_lt_dec n m} in
  case s of {
   Prelude.Just s0 -> s0;
   Prelude.Nothing -> Logic.coq_False_rec}

nat_compare :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
nat_compare n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.LT)
      (\n0 ->
      Prelude.EQ)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.GT)
      (\m' ->
      nat_compare n' m')
      m)
    n

