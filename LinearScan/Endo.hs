{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Endo where

import qualified Prelude
import qualified Data.List


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

type Functor f =
  () -> () -> (() -> ()) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor
  
fmap :: (Functor a1) -> (a2 -> a3) -> a1 -> a1
fmap functor x x0 =
  unsafeCoerce functor __ __ x x0

option_Functor :: Functor (Prelude.Maybe ())
option_Functor _ _ f x =
  case x of {
   Prelude.Just x0 -> Prelude.Just (f x0);
   Prelude.Nothing -> Prelude.Nothing}

