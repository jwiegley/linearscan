module LinearScan.Ssrbool where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils

data Coq_reflect =
   ReflectT
 | ReflectF

type Coq_pred t = t -> Prelude.Bool

type Coq_rel t = t -> Coq_pred t

