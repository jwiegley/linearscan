module LinearScan.Lib where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Logic as Logic
import qualified LinearScan.Specif as Specif
import qualified LinearScan.Eqtype as Eqtype


__ :: any
__ = Prelude.error "Logical or arity value used"

ex_falso_quodlibet :: a1
ex_falso_quodlibet =
  Logic.coq_False_rect

fromMaybe :: a1 -> (Prelude.Maybe a1) -> a1
fromMaybe d mx =
  case mx of {
   Prelude.Just x -> x;
   Prelude.Nothing -> d}

option_map :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
option_map f x =
  case x of {
   Prelude.Just x0 -> Prelude.Just (f x0);
   Prelude.Nothing -> Prelude.Nothing}

option_choose :: (Prelude.Maybe a1) -> (Prelude.Maybe a1) -> Prelude.Maybe a1
option_choose x y =
  case x of {
   Prelude.Just a -> x;
   Prelude.Nothing -> y}

foldl_with_index :: (Prelude.Int -> a2 -> a1 -> a2) -> a2 -> ([] a1) -> a2
foldl_with_index f b v =
  let {
   go n xs z =
     case xs of {
      [] -> z;
      (:) y ys -> go ((Prelude.succ) n) ys (f n z y)}}
  in go 0 v b

dep_foldl_inv :: (a1 -> Eqtype.Equality__Coq_type) -> a1 -> ([]
                 Eqtype.Equality__Coq_sort) -> Prelude.Int -> (a1 -> []
                 Eqtype.Equality__Coq_sort) -> (a1 -> a1 -> () ->
                 Eqtype.Equality__Coq_sort -> Eqtype.Equality__Coq_sort) ->
                 (a1 -> () -> Eqtype.Equality__Coq_sort -> ([]
                 Eqtype.Equality__Coq_sort) -> () -> Specif.Coq_sig2 
                 a1) -> a1
dep_foldl_inv e b v n q f f0 =
  let {filtered_var = (,) v n} in
  case filtered_var of {
   (,) l n0 ->
    case l of {
     [] -> b;
     (:) y ys ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ ->
        b)
        (\n' ->
        let {filtered_var0 = f0 b __ y ys __} in
        let {ys' = Prelude.map (f b filtered_var0 __) ys} in
        dep_foldl_inv e filtered_var0 ys' n' q f f0)
        n0}}

