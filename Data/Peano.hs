module Data.Peano where

import qualified Prelude
import qualified Data.Datatypes as Datatypes


pred :: Datatypes.Coq_nat -> Datatypes.Coq_nat
pred n =
  case n of {
   Datatypes.O -> n;
   Datatypes.S u -> u}

plus :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
plus n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S p -> Datatypes.S (plus p m)}

minus :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
minus n m =
  case n of {
   Datatypes.O -> n;
   Datatypes.S k ->
    case m of {
     Datatypes.O -> n;
     Datatypes.S l -> minus k l}}

min :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
min n m =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.O;
     Datatypes.S m' -> Datatypes.S (min n' m')}}

