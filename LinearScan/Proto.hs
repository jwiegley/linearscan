module LinearScan.Proto where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Range as Range


data ProtoRange =
   Build_ProtoRange Prelude.Int Prelude.Int ([] Range.UsePos)

type SortedProtoRanges = ([] ProtoRange)

