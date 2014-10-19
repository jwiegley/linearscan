module LinearScan.Alternative where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Applicative as Applicative


__ :: any
__ = Prelude.error "Logical or arity value used"

data Alternative f =
   Build_Alternative (Applicative.Applicative f) (() -> f) (() -> f -> f ->
                                                           f)

choose :: (Alternative a1) -> a1 -> a1 -> a1
choose alternative x x0 =
  case alternative of {
   Build_Alternative alt_is_applicative empty choose0 -> choose0 __ x x0}

option_Alternative :: Alternative (Prelude.Maybe ())
option_Alternative =
  Build_Alternative Applicative.option_Applicative (\_ -> Prelude.Nothing)
    (\_ x y ->
    case x of {
     Prelude.Just wildcard' -> x;
     Prelude.Nothing -> y})

