module LinearScan.Seq where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Ssrbool as Ssrbool


has :: (Ssrbool.Coq_pred a1) -> ([] a1) -> Prelude.Bool
has a s =
  case s of {
   [] -> Prelude.False;
   (:) x s' -> (Prelude.||) (a x) (has a s')}

rem :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort -> ([]
       Eqtype.Equality__Coq_sort) -> [] Eqtype.Equality__Coq_sort
rem t x s =
  case s of {
   [] -> s;
   (:) y t0 ->
    case Eqtype.eq_op t y x of {
     Prelude.True -> t0;
     Prelude.False -> (:) y (rem t x t0)}}

