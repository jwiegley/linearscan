{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Ssrnat where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Specif as Specif
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

__ :: any
__ = Prelude.error "Logical or arity value used"

eqnP :: Eqtype.Equality__Coq_axiom Prelude.Int
eqnP n m =
  Ssrbool.iffP ((Prelude.==) n m) (Ssrbool.idP ((Prelude.==) n m))

nat_eqMixin :: Eqtype.Equality__Coq_mixin_of Prelude.Int
nat_eqMixin =
  Eqtype.Equality__Mixin (Prelude.==) eqnP

nat_eqType :: Eqtype.Equality__Coq_type
nat_eqType =
  unsafeCoerce nat_eqMixin

find_ex_minn :: (Ssrbool.Coq_pred Prelude.Int) -> Specif.Coq_sig2 Prelude.Int
find_ex_minn p =
  (Prelude.flip (Prelude.$)) __
    ((Prelude.flip (Prelude.$)) __ (\_ _ ->
      let {
       find_ex_minn0 m =
         let {_evar_0_ = \_ -> m} in
         let {_evar_0_0 = \_ -> find_ex_minn0 ((Prelude.succ) m)} in
         case p m of {
          Prelude.True -> _evar_0_ __;
          Prelude.False -> _evar_0_0 __}}
      in find_ex_minn0 0))

type Coq_ex_minn_spec =
  Prelude.Int
  -- singleton inductive, whose constructor was ExMinnSpec
  
ex_minnP :: (Ssrbool.Coq_pred Prelude.Int) -> Coq_ex_minn_spec
ex_minnP p =
  let {x = find_ex_minn p} in Eqtype.s2val x

iter :: Prelude.Int -> (a1 -> a1) -> a1 -> a1
iter n f x =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
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

