module Data.EqNat where

import qualified Prelude

beq_nat :: Prelude.Int -> Prelude.Int -> Prelude.Bool
beq_nat n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.True)
      (\n0 ->
      Prelude.False)
      m)
    (\n1 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.False)
      (\m1 ->
      beq_nat n1 m1)
      m)
    n

