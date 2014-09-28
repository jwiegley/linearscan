module Data.Lib where

import qualified Prelude
import qualified Data.List
import qualified Data.Specif as Specif


__ :: any
__ = Prelude.error "Logical or arity value used"

undefined :: a1
undefined =
  Prelude.error "AXIOM TO BE REALIZED"

fromMaybe :: a1 -> (Prelude.Maybe a1) -> a1
fromMaybe d mx =
  case mx of {
   Prelude.Just x -> x;
   Prelude.Nothing -> d}

existT_in_cons :: a1 -> ([] a1) -> (Specif.Coq_sigT a1 ()) -> Specif.Coq_sigT
                  a1 ()
existT_in_cons a l x =
  case l of {
   [] -> Prelude.error "absurd case";
   (:) a0 l0 ->
    case x of {
     Specif.Coq_existT x0 _ -> Specif.Coq_existT x0 __}}

list_membership :: ([] a1) -> [] (Specif.Coq_sigT a1 ())
list_membership l =
  case l of {
   [] -> [];
   (:) x xs -> (:) (Specif.Coq_existT x __)
    ((Prelude.map) (existT_in_cons x xs) (list_membership xs))}

safe_hd :: ([] a1) -> a1
safe_hd xs =
  case xs of {
   [] -> Prelude.error "absurd case";
   (:) a0 xs0 -> a0}

