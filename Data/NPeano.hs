module Data.Data.Data.Data.NPeano where

import qualified Prelude
import qualified Data.List
import qualified Data.Data.List as Data.List
import qualified Data.Data.Data.List as Data.List as Data.Data.List as Data.List
import qualified Data.Data.Data.Data.List as Data.List as Data.Data.List as Data.List as Data.Data.Data.List as Data.List as Data.Data.List as Data.List

leb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
leb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    Prelude.True)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.False)
      (\m' ->
      leb n' m')
      m)
    n

ltb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
ltb n m =
  leb (Prelude.succ n) m

