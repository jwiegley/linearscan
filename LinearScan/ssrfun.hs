module LinearScan.Ssrfun where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

_Option__apply :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
_Option__apply f x u =
  case u of {
   Prelude.Just y -> f y;
   Prelude.Nothing -> x}

_Option__coq_default :: a1 -> (Prelude.Maybe a1) -> a1
_Option__coq_default =
  _Option__apply (\x -> x)

_Option__bind :: (a1 -> Prelude.Maybe a2) -> (Prelude.Maybe a1) ->
                 Prelude.Maybe a2
_Option__bind f =
  _Option__apply f Prelude.Nothing

_Option__map :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
_Option__map f =
  _Option__bind (\x -> Prelude.Just (f x))

newtype Coq_simpl_fun aT rT =
   SimplFun (aT -> rT)

fun_of_simpl :: (Coq_simpl_fun a1 a2) -> a1 -> a2
fun_of_simpl f x =
  case f of {
   SimplFun lam -> lam x}

funcomp :: () -> (a2 -> a1) -> (a3 -> a2) -> a3 -> a1
funcomp u f g x =
  f (g x)

