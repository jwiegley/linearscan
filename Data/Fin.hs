module Data.Fin where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.Logic as Logic
import qualified Data.Peano as Peano


data Coq_t =
   F1 Datatypes.Coq_nat
 | FS Datatypes.Coq_nat Coq_t

to_nat :: Datatypes.Coq_nat -> Coq_t -> Datatypes.Coq_nat
to_nat m n =
  case n of {
   F1 j -> Datatypes.O;
   FS n0 p -> Datatypes.S (to_nat n0 p)}

of_nat_lt :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Coq_t
of_nat_lt p n =
  case n of {
   Datatypes.O -> Logic.coq_False_rect;
   Datatypes.S n' ->
    case p of {
     Datatypes.O -> F1 n';
     Datatypes.S p' -> FS n' (of_nat_lt p' n')}}

coq_R :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Coq_t -> Coq_t
coq_R m n p =
  case n of {
   Datatypes.O -> p;
   Datatypes.S n' -> FS (Peano.plus n' m) (coq_R m n' p)}

