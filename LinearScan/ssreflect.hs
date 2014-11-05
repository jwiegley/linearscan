module LinearScan.Ssreflect where

import qualified Prelude
import qualified Data.List
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

