module Data.Basics where

import qualified Prelude
import qualified Data.List

compose :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
compose g f x =
  g (f x)

apply :: (a1 -> a2) -> a1 -> a2
apply f x =
  f x

