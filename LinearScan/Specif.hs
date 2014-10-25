module LinearScan.Specif where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils

type Coq_sig a =
  a
  -- singleton inductive, whose constructor was exist
  
type Coq_sig2 a =
  a
  -- singleton inductive, whose constructor was exist2
  
projT1 :: ((,) a1 a2) -> a1
projT1 x =
  case x of {
   (,) a p -> a}

