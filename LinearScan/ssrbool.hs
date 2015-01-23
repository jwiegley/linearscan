{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Ssrbool where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

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

type Coq_simpl_rel t = (->) t (Coq_pred t)

rel_of_simpl_rel :: (Coq_simpl_rel a1) -> Coq_rel a1
rel_of_simpl_rel r x y =
  (Prelude.$) r x y

data Coq_mem_pred t =
   Mem (Coq_pred t)

data Coq_predType t =
   PredType (() -> Coq_pred t) (() -> Coq_mem_pred t)

type Coq_pred_sort t = ()

mkPredType :: (a2 -> a1 -> Prelude.Bool) -> Coq_predType a1
mkPredType toP =
  PredType (unsafeCoerce toP) (\p -> Mem (\x -> unsafeCoerce toP p x))

pred_of_mem :: (Coq_mem_pred a1) -> Coq_pred_sort a1
pred_of_mem mp =
  case mp of {
   Mem p -> unsafeCoerce (\x -> p x)}

mem :: (Coq_predType a1) -> (Coq_pred_sort a1) -> Coq_mem_pred a1
mem pT =
  case pT of {
   PredType topred s -> s}

in_mem :: a1 -> (Coq_mem_pred a1) -> Prelude.Bool
in_mem x mp =
  unsafeCoerce (\_ -> pred_of_mem) __ mp x

