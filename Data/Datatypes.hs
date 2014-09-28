module Data.Datatypes where

import qualified Prelude

data Coq_bool =
   Coq_true
 | Coq_false

andb :: Coq_bool -> Coq_bool -> Coq_bool
andb b1 b2 =
  case b1 of {
   Coq_true -> b2;
   Coq_false -> Coq_false}

orb :: Coq_bool -> Coq_bool -> Coq_bool
orb b1 b2 =
  case b1 of {
   Coq_true -> Coq_true;
   Coq_false -> b2}

negb :: Coq_bool -> Coq_bool
negb b =
  case b of {
   Coq_true -> Coq_false;
   Coq_false -> Coq_true}

data Coq_nat =
   O
 | S Coq_nat

nat_rect :: a1 -> (Coq_nat -> a1 -> a1) -> Coq_nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Coq_nat -> a1 -> a1) -> Coq_nat -> a1
nat_rec =
  nat_rect

data Coq_option a =
   Some a
 | None

data Coq_prod a b =
   Coq_pair a b

data Coq_list a =
   Coq_nil
 | Coq_cons a (Coq_list a)

list_rect :: a2 -> (a1 -> (Coq_list a1) -> a2 -> a2) -> (Coq_list a1) -> a2
list_rect f f0 l =
  case l of {
   Coq_nil -> f;
   Coq_cons y l0 -> f0 y l0 (list_rect f f0 l0)}

app :: (Coq_list a1) -> (Coq_list a1) -> Coq_list a1
app l m =
  case l of {
   Coq_nil -> m;
   Coq_cons a l1 -> Coq_cons a (app l1 m)}

data Coq_comparison =
   Eq
 | Lt
 | Gt

