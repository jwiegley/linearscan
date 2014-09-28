module Data.Fin where

import qualified Prelude
import qualified Data.List
import qualified Data.Logic as Logic


data Coq_t =
   F1 Prelude.Int
 | FS Prelude.Int Coq_t

to_nat :: Prelude.Int -> Coq_t -> Prelude.Int
to_nat m n =
  case n of {
   F1 j -> 0;
   FS n0 p -> Prelude.succ (to_nat n0 p)}

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

coq_R :: Prelude.Int -> Prelude.Int -> Coq_t -> Coq_t
coq_R m n p =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    p)
    (\n' -> FS ((Prelude.+) n' m)
    (coq_R m n' p))
    n

