module Data.Basics where

import qualified Prelude
import qualified Data.List

apply :: (a1 -> a2) -> a1 -> a2
apply f x =
  f x

