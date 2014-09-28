module Data.NPeano where

import qualified Prelude
import qualified Data.Datatypes as Datatypes


leb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
leb n m =
  case n of {
   Datatypes.O -> Datatypes.Coq_true;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m' -> leb n' m'}}

ltb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
ltb n m =
  leb (Datatypes.S n) m

