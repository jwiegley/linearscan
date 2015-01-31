{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Fintype where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Choice as Choice
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Seq as Seq
import qualified LinearScan.Ssrbool as Ssrbool
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

data Finite__Coq_mixin_of =
   Finite__Mixin (Choice.Countable__Coq_mixin_of Eqtype.Equality__Coq_sort) 
 ([] Eqtype.Equality__Coq_sort)

_Finite__mixin_of_rect :: Eqtype.Equality__Coq_type ->
                          ((Choice.Countable__Coq_mixin_of
                          Eqtype.Equality__Coq_sort) -> ([]
                          Eqtype.Equality__Coq_sort) -> () -> a1) ->
                          Finite__Coq_mixin_of -> a1
_Finite__mixin_of_rect t f m =
  case m of {
   Finite__Mixin x x0 -> f x x0 __}

_Finite__mixin_of_rec :: Eqtype.Equality__Coq_type ->
                         ((Choice.Countable__Coq_mixin_of
                         Eqtype.Equality__Coq_sort) -> ([]
                         Eqtype.Equality__Coq_sort) -> () -> a1) ->
                         Finite__Coq_mixin_of -> a1
_Finite__mixin_of_rec t =
  _Finite__mixin_of_rect t

_Finite__mixin_base :: Eqtype.Equality__Coq_type -> Finite__Coq_mixin_of ->
                       Choice.Countable__Coq_mixin_of
                       Eqtype.Equality__Coq_sort
_Finite__mixin_base t m =
  case m of {
   Finite__Mixin mixin_base0 mixin_enum0 -> mixin_base0}

_Finite__mixin_enum :: Eqtype.Equality__Coq_type -> Finite__Coq_mixin_of ->
                       [] Eqtype.Equality__Coq_sort
_Finite__mixin_enum t m =
  case m of {
   Finite__Mixin mixin_base0 mixin_enum0 -> mixin_enum0}

_Finite__coq_EnumMixin :: Choice.Countable__Coq_type -> ([]
                          Choice.Countable__Coq_sort) -> Finite__Coq_mixin_of
_Finite__coq_EnumMixin t e =
  case t of {
   Choice.Countable__Class base0 m -> Finite__Mixin m e}

_Finite__coq_UniqMixin :: Choice.Countable__Coq_type -> ([]
                          Choice.Countable__Coq_sort) -> Finite__Coq_mixin_of
_Finite__coq_UniqMixin t e =
  _Finite__coq_EnumMixin t e

_Finite__count_enum :: Choice.Countable__Coq_type -> Prelude.Int -> []
                       Choice.Countable__Coq_sort
_Finite__count_enum t n =
  Seq.pmap (unsafeCoerce (Choice.pickle_inv t)) (Seq.iota 0 n)

_Finite__coq_CountMixin :: Choice.Countable__Coq_type -> Prelude.Int ->
                           Finite__Coq_mixin_of
_Finite__coq_CountMixin t n =
  _Finite__coq_EnumMixin t (_Finite__count_enum t n)

data Finite__Coq_class_of t =
   Finite__Class (Choice.Choice__Coq_class_of t) Finite__Coq_mixin_of

_Finite__class_of_rect :: ((Choice.Choice__Coq_class_of a1) ->
                          Finite__Coq_mixin_of -> a2) ->
                          (Finite__Coq_class_of a1) -> a2
_Finite__class_of_rect f c =
  case c of {
   Finite__Class x x0 -> f x x0}

_Finite__class_of_rec :: ((Choice.Choice__Coq_class_of a1) ->
                         Finite__Coq_mixin_of -> a2) -> (Finite__Coq_class_of
                         a1) -> a2
_Finite__class_of_rec =
  _Finite__class_of_rect

_Finite__base :: (Finite__Coq_class_of a1) -> Choice.Choice__Coq_class_of a1
_Finite__base c =
  case c of {
   Finite__Class base0 mixin0 -> base0}

_Finite__mixin :: (Finite__Coq_class_of a1) -> Finite__Coq_mixin_of
_Finite__mixin c =
  case c of {
   Finite__Class base0 mixin0 -> mixin0}

_Finite__base2 :: (Finite__Coq_class_of a1) -> Choice.Countable__Coq_class_of
                  a1
_Finite__base2 c =
  Choice.Countable__Class (_Finite__base c)
    (unsafeCoerce
      (_Finite__mixin_base
        (Choice._Choice__base (_Finite__base (unsafeCoerce c)))
        (_Finite__mixin c)))

type Finite__Coq_type =
  Finite__Coq_class_of ()
  -- singleton inductive, whose constructor was Pack
  
_Finite__type_rect :: (() -> (Finite__Coq_class_of ()) -> () -> a1) ->
                      Finite__Coq_type -> a1
_Finite__type_rect f t =
  f __ t __

_Finite__type_rec :: (() -> (Finite__Coq_class_of ()) -> () -> a1) ->
                     Finite__Coq_type -> a1
_Finite__type_rec =
  _Finite__type_rect

type Finite__Coq_sort = ()

_Finite__coq_class :: Finite__Coq_type -> Finite__Coq_class_of
                      Finite__Coq_sort
_Finite__coq_class cT =
  cT

_Finite__clone :: Finite__Coq_type -> (Finite__Coq_class_of a1) ->
                  Finite__Coq_type
_Finite__clone cT c =
  unsafeCoerce c

_Finite__pack :: (Eqtype.Equality__Coq_mixin_of a1) -> Finite__Coq_mixin_of
                 -> Choice.Choice__Coq_type -> (Choice.Choice__Coq_class_of
                 a1) -> Finite__Coq_mixin_of -> Finite__Coq_type
_Finite__pack b0 m0 bT b m =
  Finite__Class (unsafeCoerce b) m

_Finite__eqType :: Finite__Coq_type -> Eqtype.Equality__Coq_type
_Finite__eqType cT =
  Choice._Choice__base (_Finite__base (_Finite__coq_class cT))

_Finite__choiceType :: Finite__Coq_type -> Choice.Choice__Coq_type
_Finite__choiceType cT =
  _Finite__base (_Finite__coq_class cT)

_Finite__countType :: Finite__Coq_type -> Choice.Countable__Coq_type
_Finite__countType cT =
  _Finite__base2 (_Finite__coq_class cT)

_Finite__EnumDef__enum :: Finite__Coq_type -> [] Finite__Coq_sort
_Finite__EnumDef__enum cT =
  _Finite__mixin_enum
    (Choice._Choice__base (_Finite__base (_Finite__coq_class cT)))
    (_Finite__mixin (_Finite__coq_class cT))

enum_mem :: Finite__Coq_type -> (Ssrbool.Coq_mem_pred Finite__Coq_sort) -> []
            Finite__Coq_sort
enum_mem t mA =
  Prelude.filter (Ssrbool.pred_of_simpl (Ssrbool.pred_of_mem_pred mA))
    (_Finite__EnumDef__enum t)

ordinal_subType :: Prelude.Int -> Eqtype.Coq_subType Prelude.Int
ordinal_subType n =
  Eqtype.SubType (unsafeCoerce ) (unsafeCoerce (\x _ ->  x)) (\_ k_S u ->
    case unsafeCoerce u of {
      x -> k_S x __})

ordinal_eqMixin :: Prelude.Int -> Eqtype.Equality__Coq_mixin_of Prelude.Int
ordinal_eqMixin n =
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce ( x)) (unsafeCoerce ( y)))
    (unsafeCoerce
      (Eqtype.val_eqP Ssrnat.nat_eqType (\x ->
        (Prelude.<=) ((Prelude.succ) (unsafeCoerce x)) n)
        (unsafeCoerce (ordinal_subType n))))

ordinal_eqType :: Prelude.Int -> Eqtype.Equality__Coq_type
ordinal_eqType n =
  unsafeCoerce (ordinal_eqMixin n)

ordinal_choiceMixin :: Prelude.Int -> Choice.Choice__Coq_mixin_of Prelude.Int
ordinal_choiceMixin n =
  unsafeCoerce
    (Choice.sub_choiceMixin Choice.nat_choiceType (\x ->
      (Prelude.<=) ((Prelude.succ) (unsafeCoerce x)) n)
      (unsafeCoerce (ordinal_subType n)))

ordinal_choiceType :: Prelude.Int -> Choice.Choice__Coq_type
ordinal_choiceType n =
  Choice.Choice__Class (Eqtype._Equality__coq_class (ordinal_eqType n))
    (unsafeCoerce (ordinal_choiceMixin n))

ordinal_countMixin :: Prelude.Int -> Choice.Countable__Coq_mixin_of
                      Prelude.Int
ordinal_countMixin n =
  unsafeCoerce
    (Choice.sub_countMixin Choice.nat_countType (\x ->
      (Prelude.<=) ((Prelude.succ) (unsafeCoerce x)) n)
      (unsafeCoerce (ordinal_subType n)))

ord_enum :: Prelude.Int -> [] Prelude.Int
ord_enum n =
  Seq.pmap
    (unsafeCoerce
      (Eqtype.insub (\x -> (Prelude.<=) ((Prelude.succ) x) n)
        (ordinal_subType n))) (Seq.iota 0 n)

ordinal_finMixin :: Prelude.Int -> Finite__Coq_mixin_of
ordinal_finMixin n =
  Finite__Mixin (unsafeCoerce (ordinal_countMixin n))
    (unsafeCoerce (ord_enum n))

ordinal_finType :: Prelude.Int -> Finite__Coq_type
ordinal_finType n =
  Finite__Class (Choice._Choice__coq_class (ordinal_choiceType n))
    (ordinal_finMixin n)

