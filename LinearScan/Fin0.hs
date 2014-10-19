module LinearScan.Fin0 where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Compare as Compare
import qualified LinearScan.Compare_dec as Compare_dec
import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Fin as Fin
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Peano as Peano
import qualified LinearScan.Specif as Specif


type Coq_fin = Fin.Coq_t

from_nat :: Prelude.Int -> Prelude.Int -> Coq_fin
from_nat m n =
  Fin.of_nat_lt n m

fin_to_nat :: Prelude.Int -> Coq_fin -> Prelude.Int
fin_to_nat n f =
   (Fin.to_nat n f)

fin_Sn_inv :: Prelude.Int -> a1 -> (Coq_fin -> a1) -> Coq_fin -> a1
fin_Sn_inv n pO pS x =
  case x of {
   Fin.F1 n0 -> pO;
   Fin.FS n0 y -> pS y}

fin_compare :: Prelude.Int -> Coq_fin -> Coq_fin -> Prelude.Ordering
fin_compare n x y =
  Compare_dec.nat_compare (fin_to_nat n x) (fin_to_nat n y)

fin_CompareSpec :: Prelude.Int -> Compare.CompareSpec Coq_fin
fin_CompareSpec n =
  fin_compare n

fin_expand :: Prelude.Int -> Fin.Coq_t -> Fin.Coq_t
fin_expand n p =
  Datatypes.nat_rec (\p0 ->
    case p0 of {
     Fin.F1 n0 -> Logic.coq_False_rec;
     Fin.FS n0 h -> Logic.coq_False_rec h}) (\n0 iHn p0 ->
    fin_Sn_inv n0 (Fin.F1 (Prelude.succ n0)) (\y -> Fin.FS (Prelude.succ n0)
      (iHn y)) p0) n p

lt_sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
lt_sub n m =
  Peano.minus m n

fin_transport :: Prelude.Int -> Prelude.Int -> Coq_fin -> Coq_fin
fin_transport n m =
  let {h = Compare_dec.le_lt_eq_dec n m} in
  case h of {
   Specif.Coq_left ->
    let {l = lt_sub n m} in
    Logic.eq_rec ((Prelude.+) n l) (\f ->
      Logic.eq_rec_r ((Prelude.+) l n) (Fin.coq_R n l f) ((Prelude.+) n l)) m;
   Specif.Coq_right -> Logic.eq_rec_r m (\h0 -> h0) n}

