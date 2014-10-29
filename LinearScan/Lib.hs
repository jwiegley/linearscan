{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Lib where

import qualified Prelude
import qualified Data.List
import qualified LinearScan.Utils
import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Fin as Fin
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Eqtype as Eqtype



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

data V__Coq_t a =
   V__Coq_nil
 | V__Coq_cons a Prelude.Int (V__Coq_t a)

_V__t_rect :: a2 -> (a1 -> Prelude.Int -> (V__Coq_t a1) -> a2 -> a2) ->
              Prelude.Int -> (V__Coq_t a1) -> a2
_V__t_rect f f0 n t =
  case t of {
   V__Coq_nil -> f;
   V__Coq_cons h n0 t0 -> f0 h n0 t0 (_V__t_rect f f0 n0 t0)}

_V__t_rec :: a2 -> (a1 -> Prelude.Int -> (V__Coq_t a1) -> a2 -> a2) ->
             Prelude.Int -> (V__Coq_t a1) -> a2
_V__t_rec =
  _V__t_rect

_V__rectS :: (a1 -> a2) -> (a1 -> Prelude.Int -> (V__Coq_t a1) -> a2 -> a2)
             -> Prelude.Int -> (V__Coq_t a1) -> a2
_V__rectS bas rect n v =
  case v of {
   V__Coq_nil -> unsafeCoerce (\_ -> Logic.coq_False_rect);
   V__Coq_cons a n0 v0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case v0 of {
       V__Coq_nil -> bas a;
       V__Coq_cons h n1 t -> unsafeCoerce (\_ -> Logic.coq_False_rect)})
      (\nn' ->
      rect a nn' v0 (_V__rectS bas rect nn' v0))
      n0}

_V__rect2 :: a3 -> (Prelude.Int -> (V__Coq_t a1) -> (V__Coq_t a2) -> a3 -> a1
             -> a2 -> a3) -> Prelude.Int -> (V__Coq_t a1) -> (V__Coq_t 
             a2) -> a3
_V__rect2 bas rect n v1 v2 =
  case v1 of {
   V__Coq_nil ->
    case v2 of {
     V__Coq_nil -> bas;
     V__Coq_cons h n0 t -> unsafeCoerce (\_ -> Logic.coq_False_rect)};
   V__Coq_cons h1 n0 t1 ->
    case v2 of {
     V__Coq_nil -> Logic.coq_False_rect;
     V__Coq_cons h2 n1 t2 ->
      rect n1 t1 t2 (_V__rect2 bas rect n1 t1 t2) h1 h2}}

_V__case0 :: a2 -> (V__Coq_t a1) -> a2
_V__case0 h v =
  case v of {
   V__Coq_nil -> h;
   V__Coq_cons h0 n t -> unsafeCoerce (\_ -> Datatypes.id)}

_V__caseS :: (a1 -> Prelude.Int -> (V__Coq_t a1) -> a2) -> Prelude.Int ->
             (V__Coq_t a1) -> a2
_V__caseS h n v =
  case v of {
   V__Coq_nil -> __;
   V__Coq_cons h0 n0 t -> h h0 n0 t}

_V__hd :: Prelude.Int -> (V__Coq_t a1) -> a1
_V__hd n v =
  case v of {
   V__Coq_nil -> __;
   V__Coq_cons h n0 t -> h}

_V__last :: Prelude.Int -> (V__Coq_t a1) -> a1
_V__last n v =
  let {bas = \a -> a} in
  let {rect = \a n0 v0 h -> h} in
  let {
   rectS_fix n0 v0 =
     case v0 of {
      V__Coq_nil -> unsafeCoerce (\_ -> Prelude.error "absurd case");
      V__Coq_cons a n1 v1 ->
       (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
         (\_ ->
         case v1 of {
          V__Coq_nil -> bas a;
          V__Coq_cons h n2 t ->
           unsafeCoerce (\_ -> Prelude.error "absurd case")})
         (\nn' ->
         rect a nn' v1 (rectS_fix nn' v1))
         n1}}
  in rectS_fix n v

_V__const :: a1 -> Prelude.Int -> V__Coq_t a1
_V__const a n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    V__Coq_nil)
    (\n0 -> V__Coq_cons a n0
    (_V__const a n0))
    n

_V__nth :: Prelude.Int -> (V__Coq_t a1) -> Fin.Coq_t -> a1
_V__nth m v' p =
  case p of {
   Fin.F1 q -> _V__caseS (\h n t -> h) q v';
   Fin.FS q p' -> _V__caseS (\h n t p0 -> _V__nth n t p0) q v' p'}

_V__nth_order :: Prelude.Int -> (V__Coq_t a1) -> Prelude.Int -> a1
_V__nth_order n v p =
  _V__nth n v (Fin.of_nat_lt p n)

_V__replace :: Prelude.Int -> (V__Coq_t a1) -> Fin.Coq_t -> a1 -> V__Coq_t a1
_V__replace n v p a =
  case p of {
   Fin.F1 k -> _V__caseS (\h n0 t -> V__Coq_cons a n0 t) k v;
   Fin.FS k p' ->
    _V__caseS (\h n0 t p2 -> V__Coq_cons h n0 (_V__replace n0 t p2 a)) k v p'}

_V__replace_order :: Prelude.Int -> (V__Coq_t a1) -> Prelude.Int -> a1 ->
                     V__Coq_t a1
_V__replace_order n v p =
  _V__replace n v (Fin.of_nat_lt p n)

_V__tl :: Prelude.Int -> (V__Coq_t a1) -> V__Coq_t a1
_V__tl n v =
  case v of {
   V__Coq_nil -> __;
   V__Coq_cons h n0 t -> t}

_V__shiftout :: Prelude.Int -> (V__Coq_t a1) -> V__Coq_t a1
_V__shiftout n v =
  case v of {
   V__Coq_nil -> unsafeCoerce (\_ -> Prelude.error "absurd case");
   V__Coq_cons a n0 v0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case v0 of {
       V__Coq_nil -> V__Coq_nil;
       V__Coq_cons h n1 t -> unsafeCoerce (\_ -> Prelude.error "absurd case")})
      (\nn' -> V__Coq_cons a nn'
      (_V__shiftout nn' v0))
      n0}

_V__shiftin :: Prelude.Int -> a1 -> (V__Coq_t a1) -> V__Coq_t a1
_V__shiftin n a v =
  case v of {
   V__Coq_nil -> V__Coq_cons a 0 V__Coq_nil;
   V__Coq_cons h n0 t -> V__Coq_cons h (Prelude.succ n0) (_V__shiftin n0 a t)}

_V__shiftrepeat :: Prelude.Int -> (V__Coq_t a1) -> V__Coq_t a1
_V__shiftrepeat n v =
  case v of {
   V__Coq_nil -> unsafeCoerce (\_ -> Prelude.error "absurd case");
   V__Coq_cons a n0 v0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case v0 of {
       V__Coq_nil -> V__Coq_cons a (Prelude.succ 0) (V__Coq_cons a 0
        V__Coq_nil);
       V__Coq_cons h n1 t -> unsafeCoerce (\_ -> Prelude.error "absurd case")})
      (\nn' -> V__Coq_cons a (Prelude.succ (Prelude.succ nn'))
      (_V__shiftrepeat nn' v0))
      n0}

_V__trunc :: Prelude.Int -> Prelude.Int -> (V__Coq_t a1) -> V__Coq_t a1
_V__trunc n p x =
  Datatypes.nat_rect (\_ v -> Logic.eq_rect n v ((Prelude.-) n 0))
    (\p0 f _ v ->
    _V__shiftout ((Prelude.-) n (Prelude.succ p0))
      (Logic.eq_rect_r ((Prelude.-) (Prelude.succ n) (Prelude.succ p0))
        (f __ v) (Prelude.succ ((Prelude.-) n (Prelude.succ p0))))) p __ x

_V__append :: Prelude.Int -> Prelude.Int -> (V__Coq_t a1) -> (V__Coq_t 
              a1) -> V__Coq_t a1
_V__append n p v w =
  case v of {
   V__Coq_nil -> w;
   V__Coq_cons a n0 v' -> V__Coq_cons a ((Prelude.+) n0 p)
    (_V__append n0 p v' w)}

_V__rev_append_tail :: Prelude.Int -> Prelude.Int -> (V__Coq_t a1) ->
                       (V__Coq_t a1) -> V__Coq_t a1
_V__rev_append_tail n p v w =
  case v of {
   V__Coq_nil -> w;
   V__Coq_cons a n0 v' ->
    _V__rev_append_tail n0 (Prelude.succ p) v' (V__Coq_cons a p w)}

_V__rev_append :: Prelude.Int -> Prelude.Int -> (V__Coq_t a1) -> (V__Coq_t
                  a1) -> V__Coq_t a1
_V__rev_append n p v w =
  Logic.eq_rect_r ((Prelude.+) n p) (_V__rev_append_tail n p v w)
    ((Prelude.+) n p)

_V__rev :: Prelude.Int -> (V__Coq_t a1) -> V__Coq_t a1
_V__rev n v =
  Logic.eq_rect_r ((Prelude.+) n 0) (_V__rev_append n 0 v V__Coq_nil) n

_V__map :: (a1 -> a2) -> Prelude.Int -> (V__Coq_t a1) -> V__Coq_t a2
_V__map f n v =
  case v of {
   V__Coq_nil -> V__Coq_nil;
   V__Coq_cons a n0 v' -> V__Coq_cons (f a) n0 (_V__map f n0 v')}

_V__map2 :: (a1 -> a2 -> a3) -> Prelude.Int -> (V__Coq_t a1) -> (V__Coq_t 
            a2) -> V__Coq_t a3
_V__map2 g n v1 v2 =
  case v1 of {
   V__Coq_nil ->
    case v2 of {
     V__Coq_nil -> V__Coq_nil;
     V__Coq_cons h n0 t -> unsafeCoerce (\_ -> Prelude.error "absurd case")};
   V__Coq_cons h1 n0 t1 ->
    case v2 of {
     V__Coq_nil -> Prelude.error "absurd case";
     V__Coq_cons h2 n1 t2 -> V__Coq_cons (g h1 h2) n1 (_V__map2 g n1 t1 t2)}}

_V__fold_left :: (a2 -> a1 -> a2) -> a2 -> Prelude.Int -> (V__Coq_t a1) -> a2
_V__fold_left f b n v =
  case v of {
   V__Coq_nil -> b;
   V__Coq_cons a n0 w -> _V__fold_left f (f b a) n0 w}

_V__fold_right :: (a1 -> a2 -> a2) -> Prelude.Int -> (V__Coq_t a1) -> a2 ->
                  a2
_V__fold_right f n v b =
  case v of {
   V__Coq_nil -> b;
   V__Coq_cons a n0 w -> f a (_V__fold_right f n0 w b)}

_V__fold_right2 :: (a1 -> a2 -> a3 -> a3) -> Prelude.Int -> (V__Coq_t 
                   a1) -> (V__Coq_t a2) -> a3 -> a3
_V__fold_right2 g n v w c =
  case v of {
   V__Coq_nil ->
    case w of {
     V__Coq_nil -> c;
     V__Coq_cons h n0 t -> unsafeCoerce (\_ -> Prelude.error "absurd case")};
   V__Coq_cons h1 n0 t1 ->
    case w of {
     V__Coq_nil -> Prelude.error "absurd case";
     V__Coq_cons h2 n1 t2 -> g h1 h2 (_V__fold_right2 g n1 t1 t2 c)}}

_V__fold_left2 :: (a1 -> a2 -> a3 -> a1) -> a1 -> Prelude.Int -> (V__Coq_t
                  a2) -> (V__Coq_t a3) -> a1
_V__fold_left2 f a n v w =
  case v of {
   V__Coq_nil ->
    case w of {
     V__Coq_nil -> a;
     V__Coq_cons h n0 t -> unsafeCoerce (\_ -> Datatypes.id)};
   V__Coq_cons vh vn vt ->
    case w of {
     V__Coq_nil -> unsafeCoerce (\_ -> Datatypes.id) vt;
     V__Coq_cons wh n0 wt -> _V__fold_left2 f (f a vh wh) n0 vt wt}}

_V__of_list :: ([] a1) -> V__Coq_t a1
_V__of_list l =
  case l of {
   [] -> V__Coq_nil;
   (:) h tail -> V__Coq_cons h ((Data.List.length) tail) (_V__of_list tail)}

_V__to_list :: Prelude.Int -> (V__Coq_t a1) -> [] a1
_V__to_list n v =
  let {
   fold_right_fix n0 v0 b =
     case v0 of {
      V__Coq_nil -> b;
      V__Coq_cons a n1 w -> (:) a (fold_right_fix n1 w b)}}
  in fold_right_fix n v []

type Vec a = V__Coq_t a

ex_falso_quodlibet :: a1
ex_falso_quodlibet =
  Logic.coq_False_rect

uncurry_sig :: (a1 -> () -> a2) -> a1 -> a2
uncurry_sig f p =
  f p __

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

exist_in_cons :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort ->
                 ([] Eqtype.Equality__Coq_sort) -> Eqtype.Equality__Coq_sort
                 -> Eqtype.Equality__Coq_sort
exist_in_cons a a0 l _top_assumption_ =
  _top_assumption_

list_membership :: Eqtype.Equality__Coq_type -> ([]
                   Eqtype.Equality__Coq_sort) -> [] Eqtype.Equality__Coq_sort
list_membership a l =
  case l of {
   [] -> [];
   (:) x xs -> (:) x
    ((Prelude.map) (exist_in_cons a x xs) (list_membership a xs))}

insert :: (a1 -> Prelude.Bool) -> a1 -> ([] a1) -> [] a1
insert p z l =
  case l of {
   [] -> (:) z [];
   (:) x xs ->
    case p x of {
     Prelude.True -> (:) x (insert p z xs);
     Prelude.False -> (:) z ((:) x xs)}}

lebf :: (a1 -> Prelude.Int) -> a1 -> a1 -> Prelude.Bool
lebf f n m =
  (Prelude.<=) (f n) (f m)

