{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Choice where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Logic as Logic
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Ssrbool as Ssrbool
import qualified LinearScan.Ssrfun as Ssrfun
import qualified LinearScan.Ssrnat as Ssrnat



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

type Choice__Coq_mixin_of t =
  (Ssrbool.Coq_pred t) -> Prelude.Int -> Prelude.Maybe t
  -- singleton inductive, whose constructor was Mixin
  
_Choice__mixin_of_rect :: (((Ssrbool.Coq_pred a1) -> Prelude.Int ->
                          Prelude.Maybe a1) -> () -> () -> () -> a2) ->
                          (Choice__Coq_mixin_of a1) -> a2
_Choice__mixin_of_rect f m =
  f m __ __ __

_Choice__mixin_of_rec :: (((Ssrbool.Coq_pred a1) -> Prelude.Int ->
                         Prelude.Maybe a1) -> () -> () -> () -> a2) ->
                         (Choice__Coq_mixin_of a1) -> a2
_Choice__mixin_of_rec =
  _Choice__mixin_of_rect

_Choice__find :: (Choice__Coq_mixin_of a1) -> (Ssrbool.Coq_pred a1) ->
                 Prelude.Int -> Prelude.Maybe a1
_Choice__find m =
  m

data Choice__Coq_class_of t =
   Choice__Class (Eqtype.Equality__Coq_mixin_of t) (Choice__Coq_mixin_of t)

_Choice__class_of_rect :: ((Eqtype.Equality__Coq_mixin_of a1) ->
                          (Choice__Coq_mixin_of a1) -> a2) ->
                          (Choice__Coq_class_of a1) -> a2
_Choice__class_of_rect f c =
  case c of {
   Choice__Class x x0 -> f x x0}

_Choice__class_of_rec :: ((Eqtype.Equality__Coq_mixin_of a1) ->
                         (Choice__Coq_mixin_of a1) -> a2) ->
                         (Choice__Coq_class_of a1) -> a2
_Choice__class_of_rec =
  _Choice__class_of_rect

_Choice__base :: (Choice__Coq_class_of a1) -> Eqtype.Equality__Coq_mixin_of
                 a1
_Choice__base c =
  case c of {
   Choice__Class base0 mixin0 -> base0}

_Choice__mixin :: (Choice__Coq_class_of a1) -> Choice__Coq_mixin_of a1
_Choice__mixin c =
  case c of {
   Choice__Class base0 mixin0 -> mixin0}

type Choice__Coq_type =
  Choice__Coq_class_of ()
  -- singleton inductive, whose constructor was Pack
  
_Choice__type_rect :: (() -> (Choice__Coq_class_of ()) -> () -> a1) ->
                      Choice__Coq_type -> a1
_Choice__type_rect f t =
  f __ t __

_Choice__type_rec :: (() -> (Choice__Coq_class_of ()) -> () -> a1) ->
                     Choice__Coq_type -> a1
_Choice__type_rec =
  _Choice__type_rect

type Choice__Coq_sort = ()

_Choice__coq_class :: Choice__Coq_type -> Choice__Coq_class_of
                      Choice__Coq_sort
_Choice__coq_class cT =
  cT

_Choice__clone :: Choice__Coq_type -> (Choice__Coq_class_of a1) ->
                  Choice__Coq_type
_Choice__clone cT c =
  unsafeCoerce c

_Choice__pack :: (Choice__Coq_mixin_of a1) -> (Eqtype.Equality__Coq_mixin_of
                 a1) -> Eqtype.Equality__Coq_type -> Choice__Coq_type
_Choice__pack m b bT =
  Choice__Class (unsafeCoerce b) (unsafeCoerce m)

_Choice__eqType :: Choice__Coq_type -> Eqtype.Equality__Coq_type
_Choice__eqType cT =
  _Choice__base (_Choice__coq_class cT)

_Choice__InternalTheory__find :: Choice__Coq_type -> (Ssrbool.Coq_pred
                                 Choice__Coq_sort) -> Prelude.Int ->
                                 Prelude.Maybe Choice__Coq_sort
_Choice__InternalTheory__find t =
  _Choice__find (_Choice__mixin (_Choice__coq_class t))

_Choice__InternalTheory__xchoose_subproof :: Choice__Coq_type ->
                                             (Ssrbool.Coq_pred
                                             Choice__Coq_sort) ->
                                             Choice__Coq_sort
_Choice__InternalTheory__xchoose_subproof t p =
  let {
   n = Ssrnat.ex_minnP (\n ->
         Ssrbool.isSome (_Choice__InternalTheory__find t p n))}
  in
  let {_evar_0_ = \x -> x} in
  let {_evar_0_0 = \_ _ -> Logic.coq_False_rect} in
  case _Choice__InternalTheory__find t p n of {
   Prelude.Just x -> _evar_0_ x;
   Prelude.Nothing -> _evar_0_0 __ __}

coq_PcanChoiceMixin :: Choice__Coq_type -> (a1 -> Choice__Coq_sort) ->
                       (Choice__Coq_sort -> Prelude.Maybe a1) ->
                       Choice__Coq_mixin_of a1
coq_PcanChoiceMixin t f f' =
  let {
   liftP = \sP ->
    Ssrbool.coq_SimplPred (\x ->
      Ssrfun._Option__apply sP Prelude.False (f' x))}
  in
  let {
   sf = \sP ->  (\n ->
    Ssrfun._Option__bind f'
      (_Choice__InternalTheory__find t (Ssrbool.pred_of_simpl (liftP sP)) n))}
  in
  (\sP -> (Prelude.$) (sf sP))

sub_choiceMixin :: Choice__Coq_type -> (Ssrbool.Coq_pred Choice__Coq_sort) ->
                   (Eqtype.Coq_subType Choice__Coq_sort) ->
                   Choice__Coq_mixin_of
                   (Eqtype.Coq_sub_sort Choice__Coq_sort)
sub_choiceMixin t p sT =
  coq_PcanChoiceMixin t (Eqtype.val p sT) (Eqtype.insub p sT)

nat_choiceMixin :: Choice__Coq_mixin_of Prelude.Int
nat_choiceMixin =
  let {
   f = \p ->  (\n ->
    case p n of {
     Prelude.True -> Prelude.Just n;
     Prelude.False -> Prelude.Nothing})}
  in
  (\p -> (Prelude.$) (f p))

nat_choiceType :: Choice__Coq_type
nat_choiceType =
  Choice__Class (Eqtype._Equality__coq_class Ssrnat.nat_eqType)
    (unsafeCoerce nat_choiceMixin)

data Countable__Coq_mixin_of t =
   Countable__Mixin (t -> Prelude.Int) (Prelude.Int -> Prelude.Maybe t)

_Countable__mixin_of_rect :: ((a1 -> Prelude.Int) -> (Prelude.Int ->
                             Prelude.Maybe a1) -> () -> a2) ->
                             (Countable__Coq_mixin_of a1) -> a2
_Countable__mixin_of_rect f m =
  case m of {
   Countable__Mixin x x0 -> f x x0 __}

_Countable__mixin_of_rec :: ((a1 -> Prelude.Int) -> (Prelude.Int ->
                            Prelude.Maybe a1) -> () -> a2) ->
                            (Countable__Coq_mixin_of a1) -> a2
_Countable__mixin_of_rec =
  _Countable__mixin_of_rect

_Countable__pickle :: (Countable__Coq_mixin_of a1) -> a1 -> Prelude.Int
_Countable__pickle m =
  case m of {
   Countable__Mixin pickle0 unpickle0 -> pickle0}

_Countable__unpickle :: (Countable__Coq_mixin_of a1) -> Prelude.Int ->
                        Prelude.Maybe a1
_Countable__unpickle m =
  case m of {
   Countable__Mixin pickle0 unpickle0 -> unpickle0}

_Countable__coq_EqMixin :: (Countable__Coq_mixin_of a1) ->
                           Eqtype.Equality__Coq_mixin_of a1
_Countable__coq_EqMixin m =
  Eqtype.coq_PcanEqMixin Ssrnat.nat_eqType
    (unsafeCoerce (_Countable__pickle m))
    (unsafeCoerce (_Countable__unpickle m))

_Countable__coq_ChoiceMixin :: (Countable__Coq_mixin_of a1) ->
                               Choice__Coq_mixin_of a1
_Countable__coq_ChoiceMixin m =
  coq_PcanChoiceMixin nat_choiceType (unsafeCoerce (_Countable__pickle m))
    (unsafeCoerce (_Countable__unpickle m))

data Countable__Coq_class_of t =
   Countable__Class (Choice__Coq_class_of t) (Countable__Coq_mixin_of t)

_Countable__class_of_rect :: ((Choice__Coq_class_of a1) ->
                             (Countable__Coq_mixin_of a1) -> a2) ->
                             (Countable__Coq_class_of a1) -> a2
_Countable__class_of_rect f c =
  case c of {
   Countable__Class x x0 -> f x x0}

_Countable__class_of_rec :: ((Choice__Coq_class_of a1) ->
                            (Countable__Coq_mixin_of a1) -> a2) ->
                            (Countable__Coq_class_of a1) -> a2
_Countable__class_of_rec =
  _Countable__class_of_rect

_Countable__base :: (Countable__Coq_class_of a1) -> Choice__Coq_class_of a1
_Countable__base c =
  case c of {
   Countable__Class base0 mixin0 -> base0}

_Countable__mixin :: (Countable__Coq_class_of a1) -> Countable__Coq_mixin_of
                     a1
_Countable__mixin c =
  case c of {
   Countable__Class base0 mixin0 -> mixin0}

type Countable__Coq_type =
  Countable__Coq_class_of ()
  -- singleton inductive, whose constructor was Pack
  
_Countable__type_rect :: (() -> (Countable__Coq_class_of ()) -> () -> a1) ->
                         Countable__Coq_type -> a1
_Countable__type_rect f t =
  f __ t __

_Countable__type_rec :: (() -> (Countable__Coq_class_of ()) -> () -> a1) ->
                        Countable__Coq_type -> a1
_Countable__type_rec =
  _Countable__type_rect

type Countable__Coq_sort = ()

_Countable__coq_class :: Countable__Coq_type -> Countable__Coq_class_of
                         Countable__Coq_sort
_Countable__coq_class cT =
  cT

_Countable__clone :: Countable__Coq_type -> (Countable__Coq_class_of 
                     a1) -> Countable__Coq_type
_Countable__clone cT c =
  unsafeCoerce c

_Countable__pack :: (Countable__Coq_mixin_of a1) -> Choice__Coq_type ->
                    (Choice__Coq_class_of a1) -> Countable__Coq_type
_Countable__pack m bT b =
  Countable__Class (unsafeCoerce b) (unsafeCoerce m)

_Countable__eqType :: Countable__Coq_type -> Eqtype.Equality__Coq_type
_Countable__eqType cT =
  _Choice__base (_Countable__base (_Countable__coq_class cT))

_Countable__choiceType :: Countable__Coq_type -> Choice__Coq_type
_Countable__choiceType cT =
  _Countable__base (_Countable__coq_class cT)

unpickle :: Countable__Coq_type -> Prelude.Int -> Prelude.Maybe
            Countable__Coq_sort
unpickle t =
  _Countable__unpickle (_Countable__mixin (_Countable__coq_class t))

pickle :: Countable__Coq_type -> Countable__Coq_sort -> Prelude.Int
pickle t =
  _Countable__pickle (_Countable__mixin (_Countable__coq_class t))

pickle_inv :: Countable__Coq_type -> Eqtype.Equality__Coq_sort ->
              Prelude.Maybe Countable__Coq_sort
pickle_inv t n =
  Ssrfun._Option__bind (\x ->
    case Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (pickle t x)) n of {
     Prelude.True -> Prelude.Just x;
     Prelude.False -> Prelude.Nothing}) (unpickle t (unsafeCoerce n))

coq_PcanCountMixin :: Countable__Coq_type -> (a1 -> Countable__Coq_sort) ->
                      (Countable__Coq_sort -> Prelude.Maybe a1) ->
                      Countable__Coq_mixin_of a1
coq_PcanCountMixin t f f' =
  Countable__Mixin ((Prelude..) (pickle t) f) (Ssrfun.pcomp f' (unpickle t))

sub_countMixin :: Countable__Coq_type -> (Ssrbool.Coq_pred
                  Countable__Coq_sort) -> (Eqtype.Coq_subType
                  Countable__Coq_sort) -> Countable__Coq_mixin_of
                  (Eqtype.Coq_sub_sort Countable__Coq_sort)
sub_countMixin t p sT =
  coq_PcanCountMixin t (Eqtype.val p sT) (Eqtype.insub p sT)

nat_countMixin :: Countable__Coq_mixin_of Prelude.Int
nat_countMixin =
  Countable__Mixin (\x -> x) (\x -> Prelude.Just x)

nat_countType :: Countable__Coq_type
nat_countType =
  Countable__Class (_Choice__coq_class nat_choiceType)
    (unsafeCoerce nat_countMixin)

