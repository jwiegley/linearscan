module Data.EqNat where

import qualified Prelude
import qualified Data.Datatypes as Datatypes


beq_nat :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
beq_nat n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Coq_true;
     Datatypes.S n0 -> Datatypes.Coq_false};
   Datatypes.S n1 ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m1 -> beq_nat n1 m1}}

