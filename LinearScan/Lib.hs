module LinearScan.Lib where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Logic as Logic


__ :: any
__ = Prelude.error "Logical or arity value used"

ex_falso_quodlibet :: a1
ex_falso_quodlibet =
  Logic.coq_False_rect

uncurry_sig :: (a1 -> () -> a2) -> a1 -> a2
uncurry_sig f p =
  f p __

exist_in_cons :: a1 -> ([] a1) -> a1 -> a1
exist_in_cons a l x =
  case l of {
   [] -> Prelude.error "absurd case";
   (:) a0 l0 -> x}

list_membership :: ([] a1) -> [] a1
list_membership l =
  case l of {
   [] -> [];
   (:) x xs -> (:) x
    ((Prelude.map) (exist_in_cons x xs) (list_membership xs))}

