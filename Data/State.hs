module Data.Data.State where

import qualified Prelude
import qualified Data.List
import qualified Data.Data.List as Data.List

type State s a =
  a -> (,) s a
  -- singleton inductive, whose constructor was mkState
  
