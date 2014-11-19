{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.IEndo where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils



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

type IFunctor f =
  () -> () -> () -> () -> (() -> ()) -> f -> f
  -- singleton inductive, whose constructor was Build_IFunctor
  
imap :: (IFunctor a1) -> (a4 -> a5) -> a1 -> a1
imap iFunctor x x0 =
  unsafeCoerce iFunctor __ __ __ __ x x0

