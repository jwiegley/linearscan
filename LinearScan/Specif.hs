module LinearScan.Specif where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_sig a =
  a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

type Coq_sig2 a =
  a
  -- singleton inductive, whose constructor was exist2
  
