module LinearScan.NonEmpty0 where

import qualified Prelude
import qualified Data.List

data NonEmpty a =
   NE_Sing a
 | NE_Cons a (NonEmpty a)

coq_NE_to_list :: (NonEmpty a1) -> [] a1
coq_NE_to_list ne =
  case ne of {
   NE_Sing x -> (:) x [];
   NE_Cons x xs -> (:) x (coq_NE_to_list xs)}

coq_NE_head :: (NonEmpty a1) -> a1
coq_NE_head ne =
  case ne of {
   NE_Sing x -> x;
   NE_Cons x n -> x}

coq_NE_last :: (NonEmpty a1) -> a1
coq_NE_last ne =
  case ne of {
   NE_Sing x -> x;
   NE_Cons x xs -> coq_NE_last xs}

coq_NE_fold_left :: (a1 -> a2 -> a1) -> (NonEmpty a2) -> a1 -> a1
coq_NE_fold_left f ne z =
  case ne of {
   NE_Sing x -> f z x;
   NE_Cons x xs -> coq_NE_fold_left f xs (f z x)}

coq_NE_append :: (NonEmpty a1) -> (NonEmpty a1) -> NonEmpty a1
coq_NE_append l1 l2 =
  case l1 of {
   NE_Sing x -> NE_Cons x l2;
   NE_Cons x xs -> NE_Cons x (coq_NE_append xs l2)}

