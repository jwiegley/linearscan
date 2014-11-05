module LinearScan.List0 where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Datatypes as Datatypes


destruct_list :: ([] a1) -> Prelude.Maybe ((,) a1 ([] a1))
destruct_list l =
  Datatypes.list_rect Prelude.Nothing (\a tail iHtail -> Prelude.Just ((,) a
    tail)) l

