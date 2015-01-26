{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.IApplicative where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

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
   Build_IApplicative is_ifunctor0 ipure0 iap0 -> is_ifunctor0}

ipure :: (IApplicative a1) -> a3 -> a1
ipure iApplicative x =
  case iApplicative of {
   Build_IApplicative is_ifunctor0 ipure0 iap0 -> unsafeCoerce ipure0 __ __ x}

iap :: (IApplicative a1) -> a1 -> a1 -> a1
iap iApplicative x x0 =
  case iApplicative of {
   Build_IApplicative is_ifunctor0 ipure0 iap0 -> iap0 __ __ __ __ __ x x0}

liftIA2 :: (IApplicative a1) -> (a5 -> a6 -> a7) -> a1 -> a1 -> a1
liftIA2 h f x y =
  iap h (IEndo.imap (is_ifunctor h) f x) y

