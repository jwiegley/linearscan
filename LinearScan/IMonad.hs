module LinearScan.IMonad where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
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

mapM :: (IMonad a1) -> (a3 -> a1) -> ([] a3) -> a1
mapM h f l =
  case l of {
   [] -> IApplicative.ipure (is_iapplicative h) [];
   (:) x xs ->
    IApplicative.liftIA2 (is_iapplicative h) (\x0 x1 -> (:) x0 x1) (f x)
      (mapM h f xs)}

concat :: ([] ([] a1)) -> [] a1
concat l =
  case l of {
   [] -> [];
   (:) x xs -> (Prelude.++) x (concat xs)}

concatMapM :: (IMonad a1) -> (a3 -> a1) -> ([] a3) -> a1
concatMapM h f l =
  IEndo.imap (IApplicative.is_ifunctor (is_iapplicative h)) concat
    (mapM h f l)

