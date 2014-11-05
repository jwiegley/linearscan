{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.IState where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
import qualified LinearScan.IApplicative as IApplicative
import qualified LinearScan.IEndo as IEndo
import qualified LinearScan.IMonad as IMonad



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

type IState i o a =
  i -> (,) a o
  -- singleton inductive, whose constructor was mkIState
  
runIState :: (IState a1 a2 a3) -> a1 -> (,) a3 a2
runIState x =
  x

coq_IState_IFunctor :: IEndo.IFunctor (IState () () ())
coq_IState_IFunctor _ _ _ _ f x st =
  case runIState x st of {
   (,) a st' -> (,) (f a) st'}

iget :: IState a1 a1 a1
iget i =
  (,) i i

iput :: a2 -> IState a1 a2 ()
iput x s =
  (,) () x

coq_IState_IApplicative :: IApplicative.IApplicative (IState () () ())
coq_IState_IApplicative =
  IApplicative.Build_IApplicative coq_IState_IFunctor (\_ _ x st -> (,) x st)
    (\_ _ _ _ _ f x st ->
    case runIState f st of {
     (,) f' st' ->
      case runIState x st' of {
       (,) x' st'' -> (,) (unsafeCoerce f' x') st''}})

coq_IState_IMonad :: IMonad.IMonad (IState () () ())
coq_IState_IMonad =
  IMonad.Build_IMonad coq_IState_IApplicative (\_ _ _ _ x st ->
    case runIState x st of {
     (,) y st' ->
      case runIState (unsafeCoerce y) st' of {
       (,) a st'' -> (,) a st''}})

