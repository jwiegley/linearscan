module Data.Fin0 where

import qualified Prelude
import qualified Data.List
import qualified Data.Compare as Compare
import qualified Data.Compare_dec as Compare_dec
import qualified Data.Fin as Fin
import qualified Data.Peano as Peano


type Coq_fin = Fin.Coq_t

from_nat :: Prelude.Int -> Prelude.Int -> Coq_fin
from_nat m n =
  Fin.of_nat_lt n m

fin_to_nat :: Prelude.Int -> Coq_fin -> Prelude.Int
fin_to_nat n f =
   (Fin.to_nat n f)

ultimate_from_nat :: Prelude.Int -> Coq_fin
ultimate_from_nat n =
  from_nat n (Peano.pred n)

pred_fin :: Prelude.Int -> Coq_fin -> Prelude.Maybe Coq_fin
pred_fin n f =
  let {f0 = Fin.to_nat n f} in
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    Prelude.Nothing)
    (\x -> Prelude.Just
    (from_nat n x))
    f0

fin_compare :: Prelude.Int -> Coq_fin -> Coq_fin -> Prelude.Ordering
fin_compare n x y =
  Compare_dec.nat_compare (fin_to_nat n x) (fin_to_nat n y)

fin_CompareSpec :: Prelude.Int -> Compare.CompareSpec Coq_fin
fin_CompareSpec n =
  fin_compare n

