module Data.Lib where

import qualified Prelude
import qualified Data.Datatypes as Datatypes
import qualified Data.List as List
import qualified Data.Specif as Specif


__ :: any
__ = Prelude.error "Logical or arity value used"

undefined :: a1
undefined =
  Prelude.error "AXIOM TO BE REALIZED"

fromMaybe :: a1 -> (Datatypes.Coq_option a1) -> a1
fromMaybe d mx =
  case mx of {
   Datatypes.Some x -> x;
   Datatypes.None -> d}

existT_in_cons :: a1 -> (Datatypes.Coq_list a1) -> (Specif.Coq_sigT a1 
                  ()) -> Specif.Coq_sigT a1 ()
existT_in_cons a l x =
  case l of {
   Datatypes.Coq_nil -> Prelude.error "absurd case";
   Datatypes.Coq_cons a0 l0 ->
    case x of {
     Specif.Coq_existT x0 _ -> Specif.Coq_existT x0 __}}

list_membership :: (Datatypes.Coq_list a1) -> Datatypes.Coq_list
                   (Specif.Coq_sigT a1 ())
list_membership l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons x xs -> Datatypes.Coq_cons (Specif.Coq_existT x __)
    (List.map (existT_in_cons x xs) (list_membership xs))}

safe_hd :: (Datatypes.Coq_list a1) -> a1
safe_hd xs =
  case xs of {
   Datatypes.Coq_nil -> Prelude.error "absurd case";
   Datatypes.Coq_cons a0 xs0 -> a0}

