module LinearScan.IMonad where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.IApplicative as IApplicative


__ :: any
__ = Prelude.error "Logical or arity value used"

data IMonad m =
   Build_IMonad (IApplicative.IApplicative m) (() -> () -> () -> () -> m ->
                                              m)

ijoin :: (IMonad a1) -> a1 -> a1
ijoin iMonad x =
  case iMonad of {
   Build_IMonad is_iapplicative ijoin0 -> ijoin0 __ __ __ __ x}

