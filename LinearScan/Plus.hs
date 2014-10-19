module LinearScan.Plus where

import qualified Prelude
import qualified Data.List

tail_plus :: Prelude.Int -> Prelude.Int -> Prelude.Int
tail_plus n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    m)
    (\n0 ->
    tail_plus n0 (Prelude.succ m))
    n

