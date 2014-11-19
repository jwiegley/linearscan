{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Seq where


import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Ssrbool as Ssrbool
import qualified LinearScan.Ssrnat as Ssrnat



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

ncons :: Prelude.Int -> a1 -> ([] a1) -> [] a1
ncons n x =
  Ssrnat.iter n (\x0 -> (:) x x0)

nth :: a1 -> ([] a1) -> Prelude.Int -> a1
nth x0 s n =
  case s of {
   [] -> x0;
   (:) x s' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      x)
      (\n' ->
      nth x0 s' n')
      n}

set_nth :: a1 -> ([] a1) -> Prelude.Int -> a1 -> [] a1
set_nth x0 s n y =
  case s of {
   [] -> ncons n x0 ((:) y []);
   (:) x s' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> (:) y
      s')
      (\n' -> (:) x
      (set_nth x0 s' n' y))
      n}

eqseq :: Eqtype.Equality__Coq_type -> ([] Eqtype.Equality__Coq_sort) -> ([]
         Eqtype.Equality__Coq_sort) -> Prelude.Bool
eqseq t s1 s2 =
  case s1 of {
   [] ->
    case s2 of {
     [] -> Prelude.True;
     (:) s l -> Prelude.False};
   (:) x1 s1' ->
    case s2 of {
     [] -> Prelude.False;
     (:) x2 s2' -> (Prelude.&&) (Eqtype.eq_op t x1 x2) (eqseq t s1' s2')}}

eqseqP :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_axiom
          ([] Eqtype.Equality__Coq_sort)
eqseqP t _top_assumption_ =
  let {
   _evar_0_ = \_top_assumption_0 ->
    let {_evar_0_ = Ssrbool.ReflectT} in
    let {_evar_0_0 = \x2 s2 -> Ssrbool.ReflectF} in
    case _top_assumption_0 of {
     [] -> _evar_0_;
     (:) x x0 -> _evar_0_0 x x0}}
  in
  let {
   _evar_0_0 = \x1 s1 iHs _top_assumption_0 ->
    let {_evar_0_0 = Ssrbool.ReflectF} in
    let {
     _evar_0_1 = \x2 s2 ->
      let {
       _evar_0_1 = \_ ->
        let {_evar_0_1 = Ssrbool.iffP (eqseq t s1 s2) (iHs s2)} in  _evar_0_1}
      in
      let {_evar_0_2 = \_ -> Ssrbool.ReflectF} in
      case Eqtype.eqP t x1 x2 of {
       Ssrbool.ReflectT -> _evar_0_1 __;
       Ssrbool.ReflectF -> _evar_0_2 __}}
    in
    case _top_assumption_0 of {
     [] -> _evar_0_0;
     (:) x x0 -> _evar_0_1 x x0}}
  in
  Datatypes.list_rect _evar_0_ _evar_0_0 _top_assumption_

seq_eqMixin :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_mixin_of
               ([] Eqtype.Equality__Coq_sort)
seq_eqMixin t =
  Eqtype.Equality__Mixin (eqseq t) (eqseqP t)

seq_eqType :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_type
seq_eqType t =
  unsafeCoerce (seq_eqMixin t)

mem_seq :: Eqtype.Equality__Coq_type -> ([] Eqtype.Equality__Coq_sort) ->
           Eqtype.Equality__Coq_sort -> Prelude.Bool
mem_seq t s =
  case s of {
   [] -> (\x -> Prelude.False);
   (:) y s' ->
    let {p = mem_seq t s'} in (\x -> (Prelude.||) (Eqtype.eq_op t x y) (p x))}

type Coq_eqseq_class = [] Eqtype.Equality__Coq_sort

pred_of_eq_seq :: Eqtype.Equality__Coq_type -> Coq_eqseq_class ->
                  Ssrbool.Coq_pred_sort Eqtype.Equality__Coq_sort
pred_of_eq_seq t s =
  unsafeCoerce (\x -> mem_seq t s x)

seq_predType :: Eqtype.Equality__Coq_type -> Ssrbool.Coq_predType
                Eqtype.Equality__Coq_sort
seq_predType t =
  Ssrbool.mkPredType (unsafeCoerce (pred_of_eq_seq t))

