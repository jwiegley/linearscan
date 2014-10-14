module Data.Ssrbool where

import qualified Prelude
import qualified Data.List

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

type Coq_pred t = t -> Prelude.Bool

type Coq_rel t = t -> Coq_pred t

