module Data.Datatypes where

import qualified Prelude
import qualified Data.List

nat_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    f)
    (\n0 ->
    f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rec =
  nat_rect

list_rect :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

