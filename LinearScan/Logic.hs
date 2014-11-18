module LinearScan.Logic where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

coq_False_rect :: a1
coq_False_rect =
  Prelude.error "absurd case"

coq_False_rec :: a1
coq_False_rec =
  coq_False_rect

