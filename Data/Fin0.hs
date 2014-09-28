module Data.Fin0 where

import qualified Prelude
import qualified Data.Compare as Compare
import qualified Data.Compare_dec as Compare_dec
import qualified Data.Datatypes as Datatypes
import qualified Data.Fin as Fin
import qualified Data.Peano as Peano
import qualified Data.Specif as Specif


type Coq_fin = Fin.Coq_t

from_nat :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Coq_fin
from_nat m n =
  Fin.of_nat_lt n m

fin_to_nat :: Datatypes.Coq_nat -> Coq_fin -> Datatypes.Coq_nat
fin_to_nat n f =
  Specif.proj1_sig (Fin.to_nat n f)

ultimate_from_nat :: Datatypes.Coq_nat -> Coq_fin
ultimate_from_nat n =
  from_nat n (Peano.pred n)

pred_fin :: Datatypes.Coq_nat -> Coq_fin -> Datatypes.Coq_option Coq_fin
pred_fin n f =
  let {f0 = Fin.to_nat n f} in
  case f0 of {
   Datatypes.O -> Datatypes.None;
   Datatypes.S x -> Datatypes.Some (from_nat n x)}

fin_compare :: Datatypes.Coq_nat -> Coq_fin -> Coq_fin ->
               Datatypes.Coq_comparison
fin_compare n x y =
  Compare_dec.nat_compare (fin_to_nat n x) (fin_to_nat n y)

fin_CompareSpec :: Datatypes.Coq_nat -> Compare.CompareSpec Coq_fin
fin_CompareSpec n =
  fin_compare n

