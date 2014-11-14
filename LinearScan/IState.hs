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

__ :: any
__ = Prelude.error "Logical or arity value used"

type IState errType i o a =
  i -> Prelude.Either errType ((,) a o)
  -- singleton inductive, whose constructor was mkIState
  
runIState :: (IState a1 a2 a3 a4) -> a2 -> Prelude.Either a1 ((,) a4 a3)
runIState x =
  x

coq_IState_IFunctor :: IEndo.IFunctor (IState a1 () () ())
coq_IState_IFunctor _ _ _ _ f x st =
  let {filtered_var = runIState x st} in
  case filtered_var of {
   Prelude.Left err -> Prelude.Left err;
   Prelude.Right p ->
    case p of {
     (,) a st' -> Prelude.Right ((,) (f a) st')}}

iget :: IState a1 a2 a2 a2
iget i =
  Prelude.Right ((,) i i)

iput :: a3 -> IState a1 a2 a3 ()
iput x s =
  Prelude.Right ((,) () x)

coq_IState_IApplicative :: IApplicative.IApplicative (IState a1 () () ())
coq_IState_IApplicative =
  IApplicative.Build_IApplicative coq_IState_IFunctor (\_ _ x st ->
    Prelude.Right ((,) x st)) (\_ _ _ _ _ f x st ->
    let {filtered_var = runIState f st} in
    case filtered_var of {
     Prelude.Left err -> Prelude.Left err;
     Prelude.Right p ->
      case p of {
       (,) f' st' ->
        unsafeCoerce (\f'0 st'0 _ ->
          let {filtered_var0 = runIState x st'0} in
          case filtered_var0 of {
           Prelude.Left err -> Prelude.Left err;
           Prelude.Right p0 ->
            case p0 of {
             (,) x' st'' -> Prelude.Right ((,) (f'0 x') st'')}}) f' st' __}})

coq_IState_IMonad :: IMonad.IMonad (IState a1 () () ())
coq_IState_IMonad =
  IMonad.Build_IMonad coq_IState_IApplicative (\_ _ _ _ x st ->
    let {filtered_var = runIState x st} in
    case filtered_var of {
     Prelude.Left err -> Prelude.Left err;
     Prelude.Right p ->
      case p of {
       (,) y st' ->
        unsafeCoerce (\y0 st'0 _ ->
          let {filtered_var0 = runIState y0 st'0} in
          case filtered_var0 of {
           Prelude.Left err -> Prelude.Left err;
           Prelude.Right p0 ->
            case p0 of {
             (,) a st'' -> Prelude.Right ((,) a st'')}}) y st' __}})

