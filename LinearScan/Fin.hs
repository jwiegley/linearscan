module LinearScan.Fin where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Logic as Logic


data Coq_t =
   F1 Prelude.Int
 | FS Prelude.Int Coq_t

of_nat_lt :: Prelude.Int -> Prelude.Int -> Coq_t
of_nat_lt p n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    Logic.coq_False_rect)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> F1
      n')
      (\p' -> FS n'
      (of_nat_lt p' n'))
      p)
    n

