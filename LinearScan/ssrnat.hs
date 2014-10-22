{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Ssrnat where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Eqtype as Eqtype



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

eqnP :: Eqtype.Equality__Coq_axiom Prelude.Int
eqnP =
  Prelude.error "AXIOM TO BE REALIZED"

nat_eqMixin :: Eqtype.Equality__Coq_mixin_of Prelude.Int
nat_eqMixin =
  Eqtype.Equality__Mixin (Prelude.==) eqnP

nat_eqType :: Eqtype.Equality__Coq_type
nat_eqType =
  unsafeCoerce nat_eqMixin

nat_of_bool :: Prelude.Bool -> Prelude.Int
nat_of_bool b =
  case b of {
   Prelude.True -> Prelude.succ 0;
   Prelude.False -> 0}

