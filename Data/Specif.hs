module Data.Specif where

import qualified Prelude
import qualified Data.List

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

data Coq_sigT a p =
   Coq_existT a p

data Coq_sumbool =
   Coq_left
 | Coq_right

data Coq_sumor a =
   Coq_inleft a
 | Coq_inright

