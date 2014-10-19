module LinearScan.Lib where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Seq as Seq


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
   (:) x xs -> (:) x (Seq.map (exist_in_cons x xs) (list_membership xs))}

safe_hd :: ([] a1) -> a1
safe_hd xs =
  let {_evar_0_ = \_ -> Logic.coq_False_rect} in
  let {_evar_0_0 = \a0 l x -> a0} in
  Datatypes.list_rect _evar_0_ (\a0 l x _ -> _evar_0_0 a0 l x) xs __

