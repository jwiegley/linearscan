module LinearScan.Datatypes where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils

nat_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    f)
    (\n0 ->
    f0 n0 (nat_rect f f0 n0))
    n

