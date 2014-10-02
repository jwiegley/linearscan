module Data.Lib where

import qualified Prelude
import qualified Data.List
import qualified Data.Peano as Peano


__ :: any
__ = Prelude.error "Logical or arity value used"

uncurry_sig :: (a1 -> () -> a2) -> a1 -> a2
uncurry_sig f p =
  f p __

fromMaybe :: a1 -> (Prelude.Maybe a1) -> a1
fromMaybe d mx =
  case mx of {
   Prelude.Just x -> x;
   Prelude.Nothing -> d}

exist_in_cons :: a1 -> ([] a1) -> a1 -> a1
exist_in_cons a l x =
  case l of {
   [] -> Prelude.error "absurd case";
   (:) a0 l0 -> x}

list_membership :: ([] a1) -> [] a1
list_membership l =
  case l of {
   [] -> [];
   (:) x xs -> (:) x
    ((Prelude.map) (exist_in_cons x xs) (list_membership xs))}

lt_sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
lt_sub n m =
  Peano.minus m n

safe_hd :: ([] a1) -> a1
safe_hd xs =
  case xs of {
   [] -> Prelude.error "absurd case";
   (:) a0 xs0 -> a0}

