module LinearScan.Peano where

import qualified Prelude
import qualified Data.List

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

