{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Data.Applicative where

import qualified Prelude
import qualified Data.List
import qualified Data.Endo as Endo



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified Data.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Applicative f =
   Build_Applicative (Endo.Functor f) (() -> () -> f) (() -> () -> f -> f ->
                                                      f)

option_Applicative :: Applicative (Prelude.Maybe ())
option_Applicative =
  Build_Applicative Endo.option_Functor
    (unsafeCoerce (\_ x -> Prelude.Just x)) (\_ _ f x ->
    case f of {
     Prelude.Just f' ->
      unsafeCoerce (\f'0 _ ->
        case x of {
         Prelude.Just x' -> Prelude.Just (f'0 x');
         Prelude.Nothing -> Prelude.Nothing}) f' __;
     Prelude.Nothing -> Prelude.Nothing})

