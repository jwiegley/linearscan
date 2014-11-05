module LinearScan.Ssrfun where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

newtype Coq_simpl_fun aT rT =
   SimplFun (aT -> rT)

fun_of_simpl :: (Coq_simpl_fun a1 a2) -> a1 -> a2
fun_of_simpl f x =
  case f of {
   SimplFun lam -> lam x}

funcomp :: () -> (a2 -> a1) -> (a3 -> a2) -> a3 -> a1
funcomp u f g x =
  f (g x)

