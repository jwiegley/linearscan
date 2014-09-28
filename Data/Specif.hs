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

proj1_sig :: a1 -> a1
proj1_sig e =
  e

projT1 :: (Coq_sigT a1 a2) -> a1
projT1 x =
  case x of {
   Coq_existT a p -> a}

projT2 :: (Coq_sigT a1 a2) -> a2
projT2 x =
  case x of {
   Coq_existT x0 h -> h}

data Coq_sumbool =
   Coq_left
 | Coq_right

data Coq_sumor a =
   Coq_inleft a
 | Coq_inright

