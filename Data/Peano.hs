module Data.Peano where

import qualified Prelude

pred :: Prelude.Int -> Prelude.Int
pred n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    n)
    (\u ->
    u)
    n

minus :: Prelude.Int -> Prelude.Int -> Prelude.Int
minus n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    n)
    (\k ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      n)
      (\l ->
      minus k l)
      m)
    n

min :: Prelude.Int -> Prelude.Int -> Prelude.Int
min n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    0)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      0)
      (\m' -> Prelude.succ
      (min n' m'))
      m)
    n

