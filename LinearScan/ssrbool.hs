module LinearScan.Ssrbool where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Ssrfun as Ssrfun


__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_reflect =
   ReflectT
 | ReflectF

iffP :: Prelude.Bool -> Coq_reflect -> Coq_reflect
iffP b pb =
  let {_evar_0_ = \_ _ _ -> ReflectT} in
  let {_evar_0_0 = \_ _ _ -> ReflectF} in
  case pb of {
   ReflectT -> _evar_0_ __ __ __;
   ReflectF -> _evar_0_0 __ __ __}

idP :: Prelude.Bool -> Coq_reflect
idP b1 =
  case b1 of {
   Prelude.True -> ReflectT;
   Prelude.False -> ReflectF}

andP :: Prelude.Bool -> Prelude.Bool -> Coq_reflect
andP b1 b2 =
  case b1 of {
   Prelude.True ->
    case b2 of {
     Prelude.True -> ReflectT;
     Prelude.False -> ReflectF};
   Prelude.False -> ReflectF}

type Coq_pred t = t -> Prelude.Bool

type Coq_rel t = t -> Coq_pred t

type Coq_simpl_rel t = Ssrfun.Coq_simpl_fun t (Coq_pred t)

coq_SimplRel :: (Coq_rel a1) -> Coq_simpl_rel a1
coq_SimplRel r =
  Ssrfun.SimplFun (\x -> r x)

rel_of_simpl_rel :: (Coq_simpl_rel a1) -> Coq_rel a1
rel_of_simpl_rel r x y =
  Ssrfun.fun_of_simpl r x y

