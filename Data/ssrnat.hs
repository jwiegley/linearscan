{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Data.Ssrnat where

import qualified Prelude
import qualified Data.List
import qualified Data.Peano as Peano
import qualified Data.Eqtype as Eqtype
import qualified Data.Ssrbool as Ssrbool



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified Data.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

eqn :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqn m n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.True)
      (\n0 ->
      Prelude.False)
      n)
    (\m' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      Prelude.False)
      (\n' ->
      eqn m' n')
      n)
    m

eqnP :: Eqtype.Equality__Coq_axiom Prelude.Int
eqnP n m =
  Ssrbool.iffP (eqn n m) (Ssrbool.idP (eqn n m))

nat_eqMixin :: Eqtype.Equality__Coq_mixin_of Prelude.Int
nat_eqMixin =
  Eqtype.Equality__Mixin eqn eqnP

nat_eqType :: Eqtype.Equality__Coq_type
nat_eqType =
  unsafeCoerce nat_eqMixin

addn_rec :: Prelude.Int -> Prelude.Int -> Prelude.Int
addn_rec =
  (Prelude.+)

addn :: Prelude.Int -> Prelude.Int -> Prelude.Int
addn =
  addn_rec

subn_rec :: Prelude.Int -> Prelude.Int -> Prelude.Int
subn_rec =
  Peano.minus

subn :: Prelude.Int -> Prelude.Int -> Prelude.Int
subn =
  subn_rec

leq :: Prelude.Int -> Prelude.Int -> Prelude.Bool
leq m n =
  Eqtype.eq_op nat_eqType (unsafeCoerce (subn m n)) (unsafeCoerce 0)

leP :: Prelude.Int -> Prelude.Int -> Ssrbool.Coq_reflect
leP m n =
  Ssrbool.iffP (leq m n) (Ssrbool.idP (leq m n))

maxn :: Prelude.Int -> Prelude.Int -> Prelude.Int
maxn m n =
  case leq (Prelude.succ m) n of {
   Prelude.True -> n;
   Prelude.False -> m}

minn :: Prelude.Int -> Prelude.Int -> Prelude.Int
minn m n =
  case leq (Prelude.succ m) n of {
   Prelude.True -> m;
   Prelude.False -> n}

