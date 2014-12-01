module LinearScan.Specif where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


type Coq_sig a =
  a
  -- singleton inductive, whose constructor was exist
  
type Coq_sig2 a =
  a
  -- singleton inductive, whose constructor was exist2
  
