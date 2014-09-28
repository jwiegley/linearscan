module Data.NonEmpty where

import qualified Prelude
import qualified Data.Datatypes as Datatypes


data NonEmpty a =
   NE_Sing a
 | NE_Cons a (NonEmpty a)

coq_NE_to_list :: (NonEmpty a1) -> Datatypes.Coq_list a1
coq_NE_to_list ne =
  case ne of {
   NE_Sing x -> Datatypes.Coq_cons x Datatypes.Coq_nil;
   NE_Cons x xs -> Datatypes.Coq_cons x (coq_NE_to_list xs)}

coq_NE_fold_left :: (a1 -> a2 -> a1) -> (NonEmpty a2) -> a1 -> a1
coq_NE_fold_left f ne z =
  case ne of {
   NE_Sing x -> f z x;
   NE_Cons x xs -> coq_NE_fold_left f xs (f z x)}

