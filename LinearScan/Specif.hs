module LinearScan.Specif where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


type Coq_sig a =
  a
  -- singleton inductive, whose constructor was exist
  
