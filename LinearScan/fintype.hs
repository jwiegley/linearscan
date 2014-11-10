{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Fintype where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.Eqtype as Eqtype
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

nat_of_ord :: Prelude.Int -> (Prelude.Int) -> Prelude.Int
nat_of_ord n i =
  case i of {
    m -> m}

ordinal_subType :: Prelude.Int -> Eqtype.Coq_subType Prelude.Int
ordinal_subType n =
  Eqtype.SubType (unsafeCoerce (nat_of_ord n)) (unsafeCoerce (\x _ ->  x))
    (\_ k_S u ->
    case unsafeCoerce u of {
      x -> k_S x __})

ordinal_eqMixin :: Prelude.Int -> Eqtype.Equality__Coq_mixin_of (Prelude.Int)
ordinal_eqMixin n =
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (nat_of_ord n x))
      (unsafeCoerce (nat_of_ord n y)))
    (unsafeCoerce
      (Eqtype.val_eqP Ssrnat.nat_eqType (\x ->
        (Prelude.<=) (Prelude.succ (unsafeCoerce x)) n)
        (unsafeCoerce (ordinal_subType n))))

ordinal_eqType :: Prelude.Int -> Eqtype.Equality__Coq_type
ordinal_eqType n =
  unsafeCoerce (ordinal_eqMixin n)

widen_ord :: Prelude.Int -> Prelude.Int -> (Prelude.Int) -> (Prelude.Int)
widen_ord n m i =
   (nat_of_ord n i)

ord_max :: Prelude.Int -> (Prelude.Int)
ord_max n' =
   n'

