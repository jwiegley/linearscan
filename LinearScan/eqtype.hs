{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Eqtype where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Ssrbool as Ssrbool
import qualified LinearScan.Ssrfun as Ssrfun



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

type Equality__Coq_axiom t = t -> t -> Ssrbool.Coq_reflect

data Equality__Coq_mixin_of t =
   Equality__Mixin (Ssrbool.Coq_rel t) (Equality__Coq_axiom t)

_Equality__mixin_of_rect :: ((Ssrbool.Coq_rel a1) -> (Equality__Coq_axiom 
                            a1) -> a2) -> (Equality__Coq_mixin_of a1) -> a2
_Equality__mixin_of_rect f m =
  case m of {
   Equality__Mixin x x0 -> f x x0}

_Equality__mixin_of_rec :: ((Ssrbool.Coq_rel a1) -> (Equality__Coq_axiom 
                           a1) -> a2) -> (Equality__Coq_mixin_of a1) -> a2
_Equality__mixin_of_rec =
  _Equality__mixin_of_rect

_Equality__op :: (Equality__Coq_mixin_of a1) -> Ssrbool.Coq_rel a1
_Equality__op m =
  case m of {
   Equality__Mixin op0 x -> op0}

type Equality__Coq_type =
  Equality__Coq_mixin_of ()
  -- singleton inductive, whose constructor was Pack
  
_Equality__type_rect :: (() -> (Equality__Coq_mixin_of ()) -> () -> a1) ->
                        Equality__Coq_type -> a1
_Equality__type_rect f t =
  f __ t __

_Equality__type_rec :: (() -> (Equality__Coq_mixin_of ()) -> () -> a1) ->
                       Equality__Coq_type -> a1
_Equality__type_rec =
  _Equality__type_rect

type Equality__Coq_sort = ()

_Equality__coq_class :: Equality__Coq_type -> Equality__Coq_mixin_of
                        Equality__Coq_sort
_Equality__coq_class cT =
  cT

_Equality__pack :: (Equality__Coq_mixin_of a1) -> Equality__Coq_type
_Equality__pack c =
  unsafeCoerce c

_Equality__clone :: Equality__Coq_type -> (Equality__Coq_mixin_of a1) ->
                    (Equality__Coq_sort -> a1) -> Equality__Coq_type
_Equality__clone cT c x =
  _Equality__pack c

eq_op :: Equality__Coq_type -> Ssrbool.Coq_rel Equality__Coq_sort
eq_op t =
  _Equality__op (_Equality__coq_class t)

eqP :: Equality__Coq_type -> Equality__Coq_axiom Equality__Coq_sort
eqP t =
  let {_evar_0_ = \op0 a -> a} in
  case t of {
   Equality__Mixin x x0 -> _evar_0_ x x0}

data Coq_subType t =
   SubType (() -> t) (t -> () -> ()) (() -> (t -> () -> ()) -> () -> ())

type Coq_sub_sort t = ()

val :: (Ssrbool.Coq_pred a1) -> (Coq_subType a1) -> (Coq_sub_sort a1) -> a1
val p s =
  case s of {
   SubType val0 sub x -> val0}

inj_eqAxiom :: Equality__Coq_type -> (a1 -> Equality__Coq_sort) ->
               Equality__Coq_axiom a1
inj_eqAxiom eT f x y =
  Ssrbool.iffP (eq_op eT (f x) (f y)) (eqP eT (f x) (f y))

val_eqP :: Equality__Coq_type -> (Ssrbool.Coq_pred Equality__Coq_sort) ->
           (Coq_subType Equality__Coq_sort) -> Equality__Coq_axiom
           (Coq_sub_sort Equality__Coq_sort)
val_eqP t p sT =
  inj_eqAxiom t (val p sT)

pair_eq :: Equality__Coq_type -> Equality__Coq_type -> Ssrbool.Coq_simpl_rel
           ((,) Equality__Coq_sort Equality__Coq_sort)
pair_eq t1 t2 =
   (\u v ->
    (Prelude.&&) (eq_op t1 (Prelude.fst u) (Prelude.fst v))
      (eq_op t2 (Prelude.snd u) (Prelude.snd v)))

pair_eqP :: Equality__Coq_type -> Equality__Coq_type -> Equality__Coq_axiom
            ((,) Equality__Coq_sort Equality__Coq_sort)
pair_eqP t1 t2 _top_assumption_ =
  let {
   _evar_0_ = \x1 x2 _top_assumption_0 ->
    let {
     _evar_0_ = \y1 y2 ->
      Ssrbool.iffP ((Prelude.&&) (eq_op t1 x1 y1) (eq_op t2 x2 y2))
        (Ssrbool.andP (eq_op t1 x1 y1) (eq_op t2 x2 y2))}
    in
    case _top_assumption_0 of {
     (,) x x0 -> _evar_0_ x x0}}
  in
  case _top_assumption_ of {
   (,) x x0 -> _evar_0_ x x0}

prod_eqMixin :: Equality__Coq_type -> Equality__Coq_type ->
                Equality__Coq_mixin_of
                ((,) Equality__Coq_sort Equality__Coq_sort)
prod_eqMixin t1 t2 =
  Equality__Mixin (Ssrbool.rel_of_simpl_rel (pair_eq t1 t2)) (pair_eqP t1 t2)

prod_eqType :: Equality__Coq_type -> Equality__Coq_type -> Equality__Coq_type
prod_eqType t1 t2 =
  unsafeCoerce (prod_eqMixin t1 t2)

opt_eq :: Equality__Coq_type -> (Prelude.Maybe Equality__Coq_sort) ->
          (Prelude.Maybe Equality__Coq_sort) -> Prelude.Bool
opt_eq t u v =
  Ssrfun._Option__apply (\x ->
    Ssrfun._Option__apply (eq_op t x) Prelude.False v)
    (Prelude.not (Ssrbool.isSome v)) u

opt_eqP :: Equality__Coq_type -> Equality__Coq_axiom
           (Prelude.Maybe Equality__Coq_sort)
opt_eqP t _top_assumption_ =
  let {
   _evar_0_ = \x _top_assumption_0 ->
    let {_evar_0_ = \y -> Ssrbool.iffP (eq_op t x y) (eqP t x y)} in
    let {_evar_0_0 = Ssrbool.ReflectF} in
    case _top_assumption_0 of {
     Prelude.Just x0 -> _evar_0_ x0;
     Prelude.Nothing -> _evar_0_0}}
  in
  let {
   _evar_0_0 = \_top_assumption_0 ->
    let {_evar_0_0 = \y -> Ssrbool.ReflectF} in
    let {_evar_0_1 = Ssrbool.ReflectT} in
    case _top_assumption_0 of {
     Prelude.Just x -> _evar_0_0 x;
     Prelude.Nothing -> _evar_0_1}}
  in
  case _top_assumption_ of {
   Prelude.Just x -> _evar_0_ x;
   Prelude.Nothing -> _evar_0_0}

option_eqMixin :: Equality__Coq_type -> Equality__Coq_mixin_of
                  (Prelude.Maybe Equality__Coq_sort)
option_eqMixin t =
  Equality__Mixin (opt_eq t) (opt_eqP t)

option_eqType :: Equality__Coq_type -> Equality__Coq_type
option_eqType t =
  unsafeCoerce (option_eqMixin t)

