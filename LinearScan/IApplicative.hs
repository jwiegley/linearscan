{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.IApplicative where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.IEndo as IEndo



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

data IApplicative f =
   Build_IApplicative (IEndo.IFunctor f) (() -> () -> () -> f) (() -> () ->
                                                               () -> () -> ()
                                                               -> f -> f ->
                                                               f)

is_ifunctor :: (IApplicative a1) -> IEndo.IFunctor a1
is_ifunctor iApplicative =
  case iApplicative of {
   Build_IApplicative is_ifunctor0 ipure0 iap -> is_ifunctor0}

ipure :: (IApplicative a1) -> a3 -> a1
ipure iApplicative x =
  case iApplicative of {
   Build_IApplicative is_ifunctor0 ipure0 iap -> unsafeCoerce ipure0 __ __ x}

