module LinearScan.IMonad where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.IApplicative as IApplicative
import qualified LinearScan.IEndo as IEndo


__ :: any
__ = Prelude.error "Logical or arity value used"

data IMonad m =
   Build_IMonad (IApplicative.IApplicative m) (() -> () -> () -> () -> m ->
                                              m)

is_iapplicative :: (IMonad a1) -> IApplicative.IApplicative a1
is_iapplicative iMonad =
  case iMonad of {
   Build_IMonad is_iapplicative0 ijoin0 -> is_iapplicative0}

ijoin :: (IMonad a1) -> a1 -> a1
ijoin iMonad x =
  case iMonad of {
   Build_IMonad is_iapplicative0 ijoin0 -> ijoin0 __ __ __ __ x}

ibind :: (IMonad a1) -> (a5 -> a1) -> a1 -> a1
ibind h f x =
  ijoin h (IEndo.imap (IApplicative.is_ifunctor (is_iapplicative h)) f x)

