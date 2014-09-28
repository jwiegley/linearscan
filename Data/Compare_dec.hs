module Data.Compare_dec where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.Logic as Logic
import qualified Data.Specif as Specif


lt_eq_lt_dec :: Prelude.Int -> Prelude.Int -> Specif.Coq_sumor Prelude.Either
lt_eq_lt_dec n m =
  Datatypes.nat_rec (\m0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Specif.Coq_inleft
      Prelude.Right)
      (\m1 -> Specif.Coq_inleft
      Prelude.Left)
      m0) (\n0 iHn m0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Specif.Coq_inright)
      (\m1 ->
      iHn m1)
      m0) n m

le_lt_eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Either
le_lt_eq_dec n m =
  let {s = lt_eq_lt_dec n m} in
  case s of {
   Specif.Coq_inleft s0 -> s0;
   Specif.Coq_inright -> Logic.coq_False_rec}

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

