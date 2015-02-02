module LinearScan.Lib where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Specif as Specif
import qualified LinearScan.Eqtype as Eqtype


__ :: any
__ = Prelude.error "Logical or arity value used"

undefined :: a1
undefined =
  Prelude.error "AXIOM TO BE REALIZED"

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

forFold :: a2 -> ([] a1) -> (a2 -> a1 -> a2) -> a2
forFold b v f =
  Data.List.foldl' f b v

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
      (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
        (\_ ->
        b)
        (\n' ->
        let {filtered_var0 = f0 b __ y ys __} in
        let {ys' = Prelude.map (f b filtered_var0 __) ys} in
        dep_foldl_inv e filtered_var0 ys' n' q f f0)
        n0}}

dep_foldl_invE :: (a2 -> Eqtype.Equality__Coq_type) -> a2 -> ([]
                  Eqtype.Equality__Coq_sort) -> Prelude.Int -> (a2 -> []
                  Eqtype.Equality__Coq_sort) -> (a2 -> a2 -> () ->
                  Eqtype.Equality__Coq_sort -> Eqtype.Equality__Coq_sort) ->
                  (a2 -> () -> Eqtype.Equality__Coq_sort -> ([]
                  Eqtype.Equality__Coq_sort) -> () -> Prelude.Either 
                  a1 (Specif.Coq_sig2 a2)) -> Prelude.Either a1 a2
dep_foldl_invE e b v n q f f0 =
  let {filtered_var = (,) v n} in
  case filtered_var of {
   (,) l n0 ->
    case l of {
     [] -> Prelude.Right b;
     (:) y ys ->
      (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
        (\_ -> Prelude.Right
        b)
        (\n' ->
        let {filtered_var0 = f0 b __ y ys __} in
        case filtered_var0 of {
         Prelude.Left err -> Prelude.Left err;
         Prelude.Right s ->
          let {ys' = Prelude.map (f b s __) ys} in
          dep_foldl_invE e s ys' n' q f f0})
        n0}}

