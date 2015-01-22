{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Ssrnat where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Ssrbool as Ssrbool



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
eqnP n m =
  Ssrbool.iffP ((Prelude.==) n m) (Ssrbool.idP ((Prelude.==) n m))

nat_eqMixin :: Eqtype.Equality__Coq_mixin_of Prelude.Int
nat_eqMixin =
  Eqtype.Equality__Mixin (Prelude.==) eqnP

nat_eqType :: Eqtype.Equality__Coq_type
nat_eqType =
  unsafeCoerce nat_eqMixin

iter :: Prelude.Int -> (a1 -> a1) -> a1 -> a1
iter n f x =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    x)
    (\i ->
    f (iter i f x))
    n

nat_of_bool :: Prelude.Bool -> Prelude.Int
nat_of_bool b =
  case b of {
   Prelude.True -> (Prelude.succ) 0;
   Prelude.False -> 0}

double_rec :: Prelude.Int -> Prelude.Int
double_rec n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    0)
    (\n' -> (Prelude.succ) ((Prelude.succ)
    (double_rec n')))
    n

double :: Prelude.Int -> Prelude.Int
double =
  double_rec

