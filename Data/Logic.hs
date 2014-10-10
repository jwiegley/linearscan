module Data.Logic where

import qualified Prelude
import qualified Data.List

__ :: any
__ = Prelude.error "Logical or arity value used"

coq_False_rect :: a1
coq_False_rect =
  Prelude.error "absurd case"

coq_False_rec :: a1
coq_False_rec =
  coq_False_rect

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r x h y =
  eq_rect x h y

