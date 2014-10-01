{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Data.Main where

import qualified Prelude
import qualified Data.List
import qualified Data.Compare as Compare
import qualified Data.Compare_dec as Compare_dec
import qualified Data.Datatypes as Datatypes
import qualified Data.EqNat as EqNat
import qualified Data.Fin0 as Fin0
import qualified Data.Fin as Fin
import qualified Data.Interval as Interval
import qualified Data.Lib as Lib
import qualified Data.List0 as List0
import qualified Data.Logic as Logic
import qualified Data.NPeano as NPeano
import qualified Data.Peano as Peano
import qualified Data.Plus as Plus
import qualified Data.Specif as Specif
import qualified Data.Vector1 as Vector1
import qualified Data.Vector0 as Vector0



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified Data.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

_MyMachine__maxReg :: Prelude.Int
_MyMachine__maxReg =
  Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ 0)))))))))))))))))))))))))))))))

_LinearScan__maxReg :: Prelude.Int
_LinearScan__maxReg =
  _MyMachine__maxReg

type LinearScan__PhysReg = Fin0.Coq_fin

data LinearScan__V__Coq_t a =
   LinearScan__V__Coq_nil
 | LinearScan__V__Coq_cons a Prelude.Int (LinearScan__V__Coq_t a)

_LinearScan__V__t_rect :: a2 -> (a1 -> Prelude.Int -> (LinearScan__V__Coq_t
                          a1) -> a2 -> a2) -> Prelude.Int ->
                          (LinearScan__V__Coq_t a1) -> a2
_LinearScan__V__t_rect f f0 n t =
  case t of {
   LinearScan__V__Coq_nil -> f;
   LinearScan__V__Coq_cons h n0 t0 ->
    f0 h n0 t0 (_LinearScan__V__t_rect f f0 n0 t0)}

_LinearScan__V__t_rec :: a2 -> (a1 -> Prelude.Int -> (LinearScan__V__Coq_t
                         a1) -> a2 -> a2) -> Prelude.Int ->
                         (LinearScan__V__Coq_t a1) -> a2
_LinearScan__V__t_rec =
  _LinearScan__V__t_rect

_LinearScan__V__rectS :: (a1 -> a2) -> (a1 -> Prelude.Int ->
                         (LinearScan__V__Coq_t a1) -> a2 -> a2) ->
                         Prelude.Int -> (LinearScan__V__Coq_t a1) -> a2
_LinearScan__V__rectS bas rect n v =
  case v of {
   LinearScan__V__Coq_nil -> unsafeCoerce (\_ -> Logic.coq_False_rect);
   LinearScan__V__Coq_cons a n0 v0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case v0 of {
       LinearScan__V__Coq_nil -> bas a;
       LinearScan__V__Coq_cons h n1 t ->
        unsafeCoerce (\_ -> Logic.coq_False_rect)})
      (\nn' ->
      rect a nn' v0 (_LinearScan__V__rectS bas rect nn' v0))
      n0}

_LinearScan__V__rect2 :: a3 -> (Prelude.Int -> (LinearScan__V__Coq_t 
                         a1) -> (LinearScan__V__Coq_t a2) -> a3 -> a1 -> a2
                         -> a3) -> Prelude.Int -> (LinearScan__V__Coq_t 
                         a1) -> (LinearScan__V__Coq_t a2) -> a3
_LinearScan__V__rect2 bas rect n v1 v2 =
  case v1 of {
   LinearScan__V__Coq_nil ->
    case v2 of {
     LinearScan__V__Coq_nil -> bas;
     LinearScan__V__Coq_cons h n0 t ->
      unsafeCoerce (\_ -> Logic.coq_False_rect)};
   LinearScan__V__Coq_cons h1 n0 t1 ->
    case v2 of {
     LinearScan__V__Coq_nil -> Logic.coq_False_rect;
     LinearScan__V__Coq_cons h2 n1 t2 ->
      rect n1 t1 t2 (_LinearScan__V__rect2 bas rect n1 t1 t2) h1 h2}}

_LinearScan__V__case0 :: a2 -> (LinearScan__V__Coq_t a1) -> a2
_LinearScan__V__case0 h v =
  case v of {
   LinearScan__V__Coq_nil -> h;
   LinearScan__V__Coq_cons h0 n t -> unsafeCoerce (\_ -> Datatypes.id)}

_LinearScan__V__caseS :: (a1 -> Prelude.Int -> (LinearScan__V__Coq_t 
                         a1) -> a2) -> Prelude.Int -> (LinearScan__V__Coq_t
                         a1) -> a2
_LinearScan__V__caseS h n v =
  case v of {
   LinearScan__V__Coq_nil -> __;
   LinearScan__V__Coq_cons h0 n0 t -> h h0 n0 t}

_LinearScan__V__hd :: Prelude.Int -> (LinearScan__V__Coq_t a1) -> a1
_LinearScan__V__hd n v =
  case v of {
   LinearScan__V__Coq_nil -> __;
   LinearScan__V__Coq_cons h n0 t -> h}

_LinearScan__V__last :: Prelude.Int -> (LinearScan__V__Coq_t a1) -> a1
_LinearScan__V__last n v =
  let {bas = \a -> a} in
  let {rect = \a n0 v0 h -> h} in
  let {
   rectS_fix n0 v0 =
     case v0 of {
      LinearScan__V__Coq_nil ->
       unsafeCoerce (\_ -> Prelude.error "absurd case");
      LinearScan__V__Coq_cons a n1 v1 ->
       (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
         (\_ ->
         case v1 of {
          LinearScan__V__Coq_nil -> bas a;
          LinearScan__V__Coq_cons h n2 t ->
           unsafeCoerce (\_ -> Prelude.error "absurd case")})
         (\nn' ->
         rect a nn' v1 (rectS_fix nn' v1))
         n1}}
  in rectS_fix n v

_LinearScan__V__const :: a1 -> Prelude.Int -> LinearScan__V__Coq_t a1
_LinearScan__V__const a n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    LinearScan__V__Coq_nil)
    (\n0 -> LinearScan__V__Coq_cons a n0
    (_LinearScan__V__const a n0))
    n

_LinearScan__V__nth :: Prelude.Int -> (LinearScan__V__Coq_t a1) -> Fin.Coq_t
                       -> a1
_LinearScan__V__nth m v' p =
  case p of {
   Fin.F1 q -> _LinearScan__V__caseS (\h n t -> h) q v';
   Fin.FS q p' ->
    _LinearScan__V__caseS (\h n t p0 -> _LinearScan__V__nth n t p0) q v' p'}

_LinearScan__V__nth_order :: Prelude.Int -> (LinearScan__V__Coq_t a1) ->
                             Prelude.Int -> a1
_LinearScan__V__nth_order n v p =
  _LinearScan__V__nth n v (Fin.of_nat_lt p n)

_LinearScan__V__replace :: Prelude.Int -> (LinearScan__V__Coq_t a1) ->
                           Fin.Coq_t -> a1 -> LinearScan__V__Coq_t a1
_LinearScan__V__replace n v p a =
  case p of {
   Fin.F1 k ->
    _LinearScan__V__caseS (\h n0 t -> LinearScan__V__Coq_cons a n0 t) k v;
   Fin.FS k p' ->
    _LinearScan__V__caseS (\h n0 t p2 -> LinearScan__V__Coq_cons h n0
      (_LinearScan__V__replace n0 t p2 a)) k v p'}

_LinearScan__V__replace_order :: Prelude.Int -> (LinearScan__V__Coq_t 
                                 a1) -> Prelude.Int -> a1 ->
                                 LinearScan__V__Coq_t a1
_LinearScan__V__replace_order n v p =
  _LinearScan__V__replace n v (Fin.of_nat_lt p n)

_LinearScan__V__tl :: Prelude.Int -> (LinearScan__V__Coq_t a1) ->
                      LinearScan__V__Coq_t a1
_LinearScan__V__tl n v =
  case v of {
   LinearScan__V__Coq_nil -> __;
   LinearScan__V__Coq_cons h n0 t -> t}

_LinearScan__V__shiftout :: Prelude.Int -> (LinearScan__V__Coq_t a1) ->
                            LinearScan__V__Coq_t a1
_LinearScan__V__shiftout n v =
  case v of {
   LinearScan__V__Coq_nil -> unsafeCoerce (\_ -> Prelude.error "absurd case");
   LinearScan__V__Coq_cons a n0 v0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case v0 of {
       LinearScan__V__Coq_nil -> LinearScan__V__Coq_nil;
       LinearScan__V__Coq_cons h n1 t ->
        unsafeCoerce (\_ -> Prelude.error "absurd case")})
      (\nn' -> LinearScan__V__Coq_cons a nn'
      (_LinearScan__V__shiftout nn' v0))
      n0}

_LinearScan__V__shiftin :: Prelude.Int -> a1 -> (LinearScan__V__Coq_t 
                           a1) -> LinearScan__V__Coq_t a1
_LinearScan__V__shiftin n a v =
  case v of {
   LinearScan__V__Coq_nil -> LinearScan__V__Coq_cons a 0
    LinearScan__V__Coq_nil;
   LinearScan__V__Coq_cons h n0 t -> LinearScan__V__Coq_cons h (Prelude.succ
    n0) (_LinearScan__V__shiftin n0 a t)}

_LinearScan__V__shiftrepeat :: Prelude.Int -> (LinearScan__V__Coq_t a1) ->
                               LinearScan__V__Coq_t a1
_LinearScan__V__shiftrepeat n v =
  case v of {
   LinearScan__V__Coq_nil -> unsafeCoerce (\_ -> Prelude.error "absurd case");
   LinearScan__V__Coq_cons a n0 v0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      case v0 of {
       LinearScan__V__Coq_nil -> LinearScan__V__Coq_cons a (Prelude.succ 0)
        (LinearScan__V__Coq_cons a 0 LinearScan__V__Coq_nil);
       LinearScan__V__Coq_cons h n1 t ->
        unsafeCoerce (\_ -> Prelude.error "absurd case")})
      (\nn' -> LinearScan__V__Coq_cons a (Prelude.succ (Prelude.succ nn'))
      (_LinearScan__V__shiftrepeat nn' v0))
      n0}

_LinearScan__V__trunc :: Prelude.Int -> Prelude.Int -> (LinearScan__V__Coq_t
                         a1) -> LinearScan__V__Coq_t a1
_LinearScan__V__trunc n p x =
  Datatypes.nat_rect (\_ v -> Logic.eq_rect n v (Peano.minus n 0))
    (\p0 f _ v ->
    _LinearScan__V__shiftout (Peano.minus n (Prelude.succ p0))
      (Logic.eq_rect_r (Peano.minus (Prelude.succ n) (Prelude.succ p0))
        (f __ v) (Prelude.succ (Peano.minus n (Prelude.succ p0))))) p __ x

_LinearScan__V__append :: Prelude.Int -> Prelude.Int -> (LinearScan__V__Coq_t
                          a1) -> (LinearScan__V__Coq_t a1) ->
                          LinearScan__V__Coq_t a1
_LinearScan__V__append n p v w =
  case v of {
   LinearScan__V__Coq_nil -> w;
   LinearScan__V__Coq_cons a n0 v' -> LinearScan__V__Coq_cons a
    ((Prelude.+) n0 p) (_LinearScan__V__append n0 p v' w)}

_LinearScan__V__rev_append_tail :: Prelude.Int -> Prelude.Int ->
                                   (LinearScan__V__Coq_t a1) ->
                                   (LinearScan__V__Coq_t a1) ->
                                   LinearScan__V__Coq_t a1
_LinearScan__V__rev_append_tail n p v w =
  case v of {
   LinearScan__V__Coq_nil -> w;
   LinearScan__V__Coq_cons a n0 v' ->
    _LinearScan__V__rev_append_tail n0 (Prelude.succ p) v'
      (LinearScan__V__Coq_cons a p w)}

_LinearScan__V__rev_append :: Prelude.Int -> Prelude.Int ->
                              (LinearScan__V__Coq_t a1) ->
                              (LinearScan__V__Coq_t a1) ->
                              LinearScan__V__Coq_t a1
_LinearScan__V__rev_append n p v w =
  Logic.eq_rect_r (Plus.tail_plus n p)
    (_LinearScan__V__rev_append_tail n p v w) ((Prelude.+) n p)

_LinearScan__V__rev :: Prelude.Int -> (LinearScan__V__Coq_t a1) ->
                       LinearScan__V__Coq_t a1
_LinearScan__V__rev n v =
  Logic.eq_rect_r ((Prelude.+) n 0)
    (_LinearScan__V__rev_append n 0 v LinearScan__V__Coq_nil) n

_LinearScan__V__map :: (a1 -> a2) -> Prelude.Int -> (LinearScan__V__Coq_t 
                       a1) -> LinearScan__V__Coq_t a2
_LinearScan__V__map f n v =
  case v of {
   LinearScan__V__Coq_nil -> LinearScan__V__Coq_nil;
   LinearScan__V__Coq_cons a n0 v' -> LinearScan__V__Coq_cons (f a) n0
    (_LinearScan__V__map f n0 v')}

_LinearScan__V__map2 :: (a1 -> a2 -> a3) -> Prelude.Int ->
                        (LinearScan__V__Coq_t a1) -> (LinearScan__V__Coq_t
                        a2) -> LinearScan__V__Coq_t a3
_LinearScan__V__map2 g n v1 v2 =
  case v1 of {
   LinearScan__V__Coq_nil ->
    case v2 of {
     LinearScan__V__Coq_nil -> LinearScan__V__Coq_nil;
     LinearScan__V__Coq_cons h n0 t ->
      unsafeCoerce (\_ -> Prelude.error "absurd case")};
   LinearScan__V__Coq_cons h1 n0 t1 ->
    case v2 of {
     LinearScan__V__Coq_nil -> Prelude.error "absurd case";
     LinearScan__V__Coq_cons h2 n1 t2 -> LinearScan__V__Coq_cons (g h1 h2) n1
      (_LinearScan__V__map2 g n1 t1 t2)}}

_LinearScan__V__fold_left :: (a2 -> a1 -> a2) -> a2 -> Prelude.Int ->
                             (LinearScan__V__Coq_t a1) -> a2
_LinearScan__V__fold_left f b n v =
  case v of {
   LinearScan__V__Coq_nil -> b;
   LinearScan__V__Coq_cons a n0 w -> _LinearScan__V__fold_left f (f b a) n0 w}

_LinearScan__V__fold_right :: (a1 -> a2 -> a2) -> Prelude.Int ->
                              (LinearScan__V__Coq_t a1) -> a2 -> a2
_LinearScan__V__fold_right f n v b =
  case v of {
   LinearScan__V__Coq_nil -> b;
   LinearScan__V__Coq_cons a n0 w ->
    f a (_LinearScan__V__fold_right f n0 w b)}

_LinearScan__V__fold_right2 :: (a1 -> a2 -> a3 -> a3) -> Prelude.Int ->
                               (LinearScan__V__Coq_t a1) ->
                               (LinearScan__V__Coq_t a2) -> a3 -> a3
_LinearScan__V__fold_right2 g n v w c =
  case v of {
   LinearScan__V__Coq_nil ->
    case w of {
     LinearScan__V__Coq_nil -> c;
     LinearScan__V__Coq_cons h n0 t ->
      unsafeCoerce (\_ -> Prelude.error "absurd case")};
   LinearScan__V__Coq_cons h1 n0 t1 ->
    case w of {
     LinearScan__V__Coq_nil -> Prelude.error "absurd case";
     LinearScan__V__Coq_cons h2 n1 t2 ->
      g h1 h2 (_LinearScan__V__fold_right2 g n1 t1 t2 c)}}

_LinearScan__V__fold_left2 :: (a1 -> a2 -> a3 -> a1) -> a1 -> Prelude.Int ->
                              (LinearScan__V__Coq_t a2) ->
                              (LinearScan__V__Coq_t a3) -> a1
_LinearScan__V__fold_left2 f a n v w =
  case v of {
   LinearScan__V__Coq_nil ->
    case w of {
     LinearScan__V__Coq_nil -> a;
     LinearScan__V__Coq_cons h n0 t -> unsafeCoerce (\_ -> Datatypes.id)};
   LinearScan__V__Coq_cons vh vn vt ->
    case w of {
     LinearScan__V__Coq_nil -> unsafeCoerce (\_ -> Datatypes.id) vt;
     LinearScan__V__Coq_cons wh n0 wt ->
      _LinearScan__V__fold_left2 f (f a vh wh) n0 vt wt}}

_LinearScan__V__of_list :: ([] a1) -> LinearScan__V__Coq_t a1
_LinearScan__V__of_list l =
  case l of {
   [] -> LinearScan__V__Coq_nil;
   (:) h tail -> LinearScan__V__Coq_cons h (Datatypes.length tail)
    (_LinearScan__V__of_list tail)}

_LinearScan__V__to_list :: Prelude.Int -> (LinearScan__V__Coq_t a1) -> [] a1
_LinearScan__V__to_list n v =
  let {
   fold_right_fix n0 v0 b =
     case v0 of {
      LinearScan__V__Coq_nil -> b;
      LinearScan__V__Coq_cons a n1 w -> (:) a (fold_right_fix n1 w b)}}
  in fold_right_fix n v []

type LinearScan__Vec a = LinearScan__V__Coq_t a

data LinearScan__ScanStateDesc =
   LinearScan__Build_ScanStateDesc Prelude.Int ([] Fin0.Coq_fin) ([]
                                                                 Fin0.Coq_fin) 
 ([] Fin0.Coq_fin) ([] Fin0.Coq_fin) (LinearScan__Vec Interval.IntervalDesc) 
 (LinearScan__Vec (Prelude.Maybe LinearScan__PhysReg)) (LinearScan__Vec
                                                       (Prelude.Maybe
                                                       Interval.IntervalDesc))

_LinearScan__coq_ScanStateDesc_rect :: (Prelude.Int -> ([] Fin0.Coq_fin) ->
                                       ([] Fin0.Coq_fin) -> ([] Fin0.Coq_fin)
                                       -> ([] Fin0.Coq_fin) ->
                                       (LinearScan__Vec
                                       Interval.IntervalDesc) ->
                                       (LinearScan__Vec
                                       (Prelude.Maybe LinearScan__PhysReg))
                                       -> (LinearScan__Vec
                                       (Prelude.Maybe Interval.IntervalDesc))
                                       -> () -> a1) ->
                                       LinearScan__ScanStateDesc -> a1
_LinearScan__coq_ScanStateDesc_rect f s =
  case s of {
   LinearScan__Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 x6 ->
    f x x0 x1 x2 x3 x4 x5 x6 __}

_LinearScan__coq_ScanStateDesc_rec :: (Prelude.Int -> ([] Fin0.Coq_fin) ->
                                      ([] Fin0.Coq_fin) -> ([] Fin0.Coq_fin)
                                      -> ([] Fin0.Coq_fin) ->
                                      (LinearScan__Vec Interval.IntervalDesc)
                                      -> (LinearScan__Vec
                                      (Prelude.Maybe LinearScan__PhysReg)) ->
                                      (LinearScan__Vec
                                      (Prelude.Maybe Interval.IntervalDesc))
                                      -> () -> a1) ->
                                      LinearScan__ScanStateDesc -> a1
_LinearScan__coq_ScanStateDesc_rec =
  _LinearScan__coq_ScanStateDesc_rect

_LinearScan__nextInterval :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__nextInterval s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> nextInterval0}

type LinearScan__IntervalId = Fin0.Coq_fin

_LinearScan__unhandled :: LinearScan__ScanStateDesc -> []
                          LinearScan__IntervalId
_LinearScan__unhandled s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> unhandled0}

_LinearScan__active :: LinearScan__ScanStateDesc -> [] LinearScan__IntervalId
_LinearScan__active s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> active0}

_LinearScan__inactive :: LinearScan__ScanStateDesc -> []
                         LinearScan__IntervalId
_LinearScan__inactive s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> inactive0}

_LinearScan__handled :: LinearScan__ScanStateDesc -> []
                        LinearScan__IntervalId
_LinearScan__handled s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> handled0}

_LinearScan__intervals :: LinearScan__ScanStateDesc -> LinearScan__Vec
                          Interval.IntervalDesc
_LinearScan__intervals s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> intervals0}

_LinearScan__assignments :: LinearScan__ScanStateDesc -> LinearScan__Vec
                            (Prelude.Maybe LinearScan__PhysReg)
_LinearScan__assignments s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> assignments0}

_LinearScan__fixedIntervals :: LinearScan__ScanStateDesc -> LinearScan__Vec
                               (Prelude.Maybe Interval.IntervalDesc)
_LinearScan__fixedIntervals s =
  case s of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 -> fixedIntervals0}

_LinearScan__all_state_lists :: LinearScan__ScanStateDesc -> []
                                LinearScan__IntervalId
_LinearScan__all_state_lists s =
  (Prelude.++) (_LinearScan__unhandled s)
    ((Prelude.++) (_LinearScan__active s)
      ((Prelude.++) (_LinearScan__inactive s) (_LinearScan__handled s)))

_LinearScan__transportId :: LinearScan__ScanStateDesc ->
                            LinearScan__ScanStateDesc ->
                            LinearScan__IntervalId -> LinearScan__IntervalId
_LinearScan__transportId sd sd' x =
  let {
   h = Compare_dec.le_lt_eq_dec (_LinearScan__nextInterval sd)
         (_LinearScan__nextInterval sd')}
  in
  case h of {
   Specif.Coq_left ->
    case sd of {
     LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0
      inactive0 handled0 intervals0 assignments0 fixedIntervals0 ->
      case sd' of {
       LinearScan__Build_ScanStateDesc nextInterval1 unhandled1 active1
        inactive1 handled1 intervals1 assignments1 fixedIntervals1 ->
        let {h0 = Lib.lt_sub nextInterval0 nextInterval1} in
        Logic.eq_rec ((Prelude.+) h0 nextInterval0)
          (Fin.coq_R nextInterval0 h0 x) nextInterval1}};
   Specif.Coq_right ->
    Logic.eq_rec (_LinearScan__nextInterval sd) x
      (_LinearScan__nextInterval sd')}

_LinearScan__unhandledExtent :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__unhandledExtent sd =
  case _LinearScan__unhandled sd of {
   [] -> 0;
   (:) i l ->
    case l of {
     [] ->
      Interval.intervalExtent
        (
          (_LinearScan__V__nth (_LinearScan__nextInterval sd)
            (_LinearScan__intervals sd) i));
     (:) i0 l0 ->
      let {
       f = \n x ->
        (Prelude.+) n
          (Interval.intervalExtent
            (
              (_LinearScan__V__nth (_LinearScan__nextInterval sd)
                (_LinearScan__intervals sd) x)))}
      in
      (\f -> Prelude.flip (Data.List.foldl' f)) f ((:) i ((:) i0 l0)) 0}}

data LinearScan__ScanStateCursor =
   LinearScan__Build_ScanStateCursor

_LinearScan__coq_ScanStateCursor_rect :: LinearScan__ScanStateDesc -> (() ->
                                         () -> a1) -> a1
_LinearScan__coq_ScanStateCursor_rect sd f =
  f __ __

_LinearScan__coq_ScanStateCursor_rec :: LinearScan__ScanStateDesc -> (() ->
                                        () -> a1) -> a1
_LinearScan__coq_ScanStateCursor_rec sd f =
  _LinearScan__coq_ScanStateCursor_rect sd f

_LinearScan__curId :: LinearScan__ScanStateDesc -> LinearScan__IntervalId
_LinearScan__curId sd =
  Lib.safe_hd (_LinearScan__unhandled sd)

_LinearScan__curIntDetails :: LinearScan__ScanStateDesc ->
                              Interval.IntervalDesc
_LinearScan__curIntDetails sd =
  _LinearScan__V__nth (_LinearScan__nextInterval sd)
    (_LinearScan__intervals sd) (_LinearScan__curId sd)

_LinearScan__curIntDesc :: LinearScan__ScanStateDesc -> Interval.IntervalDesc
_LinearScan__curIntDesc sd =
   (_LinearScan__curIntDetails sd)

_LinearScan__curPosition :: LinearScan__ScanStateDesc -> Prelude.Int
_LinearScan__curPosition sd =
  Interval.intervalStart ( (_LinearScan__curIntDetails sd))

type LinearScan__NextScanState =
  LinearScan__ScanStateDesc
  -- singleton inductive, whose constructor was Build_NextScanState
  
_LinearScan__coq_NextScanState_rect :: (LinearScan__ScanStateDesc -> () -> ()
                                       -> a1) -> LinearScan__NextScanState ->
                                       a1
_LinearScan__coq_NextScanState_rect f n =
  f n __ __

_LinearScan__coq_NextScanState_rec :: (LinearScan__ScanStateDesc -> () -> ()
                                      -> a1) -> LinearScan__NextScanState ->
                                      a1
_LinearScan__coq_NextScanState_rec =
  _LinearScan__coq_NextScanState_rect

_LinearScan__nextDesc :: LinearScan__NextScanState ->
                         LinearScan__ScanStateDesc
_LinearScan__nextDesc n =
  n

type LinearScan__NextState = LinearScan__NextScanState

type LinearScan__NextStateDep = LinearScan__NextScanState

type LinearScan__NextStateWith a = (,) a LinearScan__NextScanState

_LinearScan__coq_NextScanState_transitivity :: LinearScan__ScanStateDesc ->
                                               LinearScan__NextScanState ->
                                               LinearScan__NextScanState ->
                                               LinearScan__NextScanState
_LinearScan__coq_NextScanState_transitivity sd0 n o =
  o

_LinearScan__coq_SSMorph_rect :: LinearScan__ScanStateDesc ->
                                 LinearScan__ScanStateDesc -> (() -> () -> ()
                                 -> a1) -> a1
_LinearScan__coq_SSMorph_rect sd1 sd2 f =
  f __ __ __

_LinearScan__coq_SSMorph_rec :: LinearScan__ScanStateDesc ->
                                LinearScan__ScanStateDesc -> (() -> () -> ()
                                -> a1) -> a1
_LinearScan__coq_SSMorph_rec sd1 sd2 f =
  _LinearScan__coq_SSMorph_rect sd1 sd2 f

_LinearScan__coq_SSMorphSt_rect :: LinearScan__ScanStateDesc ->
                                   LinearScan__ScanStateDesc -> (() -> () ->
                                   a1) -> a1
_LinearScan__coq_SSMorphSt_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphSt_rec :: LinearScan__ScanStateDesc ->
                                  LinearScan__ScanStateDesc -> (() -> () ->
                                  a1) -> a1
_LinearScan__coq_SSMorphSt_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphSt_rect sd1 sd2 f

_LinearScan__coq_SSMorphLen_rect :: LinearScan__ScanStateDesc ->
                                    LinearScan__ScanStateDesc -> (() -> () ->
                                    a1) -> a1
_LinearScan__coq_SSMorphLen_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphLen_rec :: LinearScan__ScanStateDesc ->
                                   LinearScan__ScanStateDesc -> (() -> () ->
                                   a1) -> a1
_LinearScan__coq_SSMorphLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphLen_rect sd1 sd2 f

_LinearScan__coq_SSMorphStLen_rect :: LinearScan__ScanStateDesc ->
                                      LinearScan__ScanStateDesc -> (() -> ()
                                      -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rect sd1 sd2 f =
  f __ __

_LinearScan__coq_SSMorphStLen_rec :: LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc -> (() -> ()
                                     -> a1) -> a1
_LinearScan__coq_SSMorphStLen_rec sd1 sd2 f =
  _LinearScan__coq_SSMorphStLen_rect sd1 sd2 f

_LinearScan__moveUnhandledToActive :: LinearScan__ScanStateDesc ->
                                      LinearScan__PhysReg ->
                                      LinearScan__NextState
_LinearScan__moveUnhandledToActive sd reg =
  case sd of {
   LinearScan__Build_ScanStateDesc nextInterval0 unhandled0 active0 inactive0
    handled0 intervals0 assignments0 fixedIntervals0 ->
    case unhandled0 of {
     [] -> Logic.coq_False_rec;
     (:) i unhandled1 -> LinearScan__Build_ScanStateDesc nextInterval0
      unhandled1 ((:) i active0) inactive0 handled0 intervals0
      (_LinearScan__V__replace nextInterval0 assignments0 i (Prelude.Just
        reg)) fixedIntervals0}}

_LinearScan__moveActiveToHandled :: LinearScan__ScanStateDesc ->
                                    LinearScan__IntervalId ->
                                    LinearScan__NextScanState
_LinearScan__moveActiveToHandled sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__active sd)) ((:) x (_LinearScan__inactive sd))
    (_LinearScan__handled sd) (_LinearScan__intervals sd)
    (_LinearScan__assignments sd) (_LinearScan__fixedIntervals sd)

_LinearScan__moveActiveToInactive :: LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId ->
                                     LinearScan__NextScanState
_LinearScan__moveActiveToInactive sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__active sd)) ((:) x (_LinearScan__inactive sd))
    (_LinearScan__handled sd) (_LinearScan__intervals sd)
    (_LinearScan__assignments sd) (_LinearScan__fixedIntervals sd)

_LinearScan__moveInactiveToActive :: LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId ->
                                     LinearScan__NextScanState
_LinearScan__moveInactiveToActive sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd) ((:) x (_LinearScan__active sd))
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__inactive sd)) (_LinearScan__handled sd)
    (_LinearScan__intervals sd) (_LinearScan__assignments sd)
    (_LinearScan__fixedIntervals sd)

_LinearScan__moveInactiveToHandled :: LinearScan__ScanStateDesc ->
                                      LinearScan__IntervalId ->
                                      LinearScan__NextScanState
_LinearScan__moveInactiveToHandled sd x =
  LinearScan__Build_ScanStateDesc (_LinearScan__nextInterval sd)
    (_LinearScan__unhandled sd) (_LinearScan__active sd)
    (List0.remove
      (Compare.cmp_eq_dec
        (Fin0.fin_CompareSpec (_LinearScan__nextInterval sd))) x
      (_LinearScan__inactive sd)) ((:) x (_LinearScan__handled sd))
    (_LinearScan__intervals sd) (_LinearScan__assignments sd)
    (_LinearScan__fixedIntervals sd)

_LinearScan__splitInterval :: LinearScan__ScanStateDesc -> (Prelude.Maybe
                              Prelude.Int) -> LinearScan__NextState
_LinearScan__splitInterval sd before =
  sd

_LinearScan__atRegister :: LinearScan__ScanStateDesc ->
                           (LinearScan__IntervalId -> a1) -> (LinearScan__Vec
                           a1) -> LinearScan__IntervalId -> Vector0.Coq_t 
                           a1
_LinearScan__atRegister sd x v i =
  case _LinearScan__V__nth (_LinearScan__nextInterval sd)
         (_LinearScan__assignments sd) i of {
   Prelude.Just r ->
    Vector0.replace _LinearScan__maxReg (unsafeCoerce v) r (x i);
   Prelude.Nothing -> unsafeCoerce v}

_LinearScan__registerWithHighestPos :: (Vector1.Vec
                                       (Prelude.Maybe Prelude.Int)) -> (,)
                                       Fin0.Coq_fin
                                       (Prelude.Maybe Prelude.Int)
_LinearScan__registerWithHighestPos =
  Vector1.fold_left_with_index _LinearScan__maxReg (\reg res x ->
    case res of {
     (,) r o ->
      case o of {
       Prelude.Just n ->
        case x of {
         Prelude.Just m ->
          case NPeano.ltb n m of {
           Prelude.True -> (,) reg (Prelude.Just m);
           Prelude.False -> (,) r (Prelude.Just n)};
         Prelude.Nothing -> (,) reg Prelude.Nothing};
       Prelude.Nothing -> (,) r Prelude.Nothing}}) ((,)
    (Fin0.from_nat _MyMachine__maxReg 0) (Prelude.Just 0))

_LinearScan__nextIntersectionWith :: Interval.IntervalDesc ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__IntervalId -> Prelude.Maybe
                                     Prelude.Int
_LinearScan__nextIntersectionWith d sd jid =
  Interval.firstIntersectionPoint
    (
      (_LinearScan__V__nth (_LinearScan__nextInterval sd)
        (_LinearScan__intervals sd) jid)) d

_LinearScan__tryAllocateFreeReg :: LinearScan__ScanStateDesc -> Prelude.Maybe
                                   LinearScan__NextState
_LinearScan__tryAllocateFreeReg sd =
  let {freeUntilPos'' = Vector0.const Prelude.Nothing _LinearScan__maxReg} in
  let {
   freeUntilPos' = (\f -> Prelude.flip (Data.List.foldl' f))
                     (unsafeCoerce
                       (_LinearScan__atRegister sd (\x -> Prelude.Just 0)))
                     (_LinearScan__active sd) freeUntilPos''}
  in
  let {
   intersectingIntervals = (Prelude.filter) (\x ->
                             Interval.anyRangeIntersects
                               ( (_LinearScan__curIntDetails sd))
                               (
                                 (_LinearScan__V__nth
                                   (_LinearScan__nextInterval sd)
                                   (_LinearScan__intervals sd) x)))
                             (_LinearScan__inactive sd)}
  in
  let {
   freeUntilPos = (\f -> Prelude.flip (Data.List.foldl' f))
                    (unsafeCoerce
                      (_LinearScan__atRegister sd
                        (_LinearScan__nextIntersectionWith
                          ( (_LinearScan__curIntDetails sd)) sd)))
                    intersectingIntervals freeUntilPos'}
  in
  case _LinearScan__registerWithHighestPos (unsafeCoerce freeUntilPos) of {
   (,) reg mres ->
    let {default0 = _LinearScan__moveUnhandledToActive sd reg} in
    case mres of {
     Prelude.Just n ->
      case EqNat.beq_nat n 0 of {
       Prelude.True -> Prelude.Nothing;
       Prelude.False -> Prelude.Just
        (case NPeano.ltb
                (Interval.intervalEnd ( (_LinearScan__curIntDetails sd))) n of {
          Prelude.True -> default0;
          Prelude.False ->
           _LinearScan__moveUnhandledToActive
             (_LinearScan__nextDesc
               (_LinearScan__splitInterval sd (Prelude.Just n))) reg})};
     Prelude.Nothing -> Prelude.Just default0}}

_LinearScan__nextUseAfter :: Prelude.Int -> LinearScan__ScanStateDesc ->
                             LinearScan__IntervalId -> Prelude.Maybe
                             Prelude.Int
_LinearScan__nextUseAfter =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__assignSpillSlotToCurrent :: LinearScan__ScanStateDesc ->
                                         LinearScan__NextScanState
_LinearScan__assignSpillSlotToCurrent =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__allocateBlockedReg :: LinearScan__ScanStateDesc ->
                                   LinearScan__NextState
_LinearScan__allocateBlockedReg sd =
  Lib.undefined

_LinearScan__checkActiveIntervals :: LinearScan__ScanStateDesc -> Prelude.Int
                                     -> LinearScan__NextScanState
_LinearScan__checkActiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       (
                         (_LinearScan__V__nth (_LinearScan__nextInterval sd0)
                           (_LinearScan__intervals sd0) ( x)))) pos0 of {
               Prelude.True ->
                Lib.uncurry_sig (\x0 _ ->
                  _LinearScan__moveActiveToHandled sd0 x0) x;
               Prelude.False ->
                case (Prelude.not)
                       (Interval.intervalCoversPos
                         (
                           (_LinearScan__V__nth
                             (_LinearScan__nextInterval sd0)
                             (_LinearScan__intervals sd0) ( x))) pos0) of {
                 Prelude.True ->
                  Lib.uncurry_sig (\x0 _ ->
                    _LinearScan__moveActiveToInactive sd0 x0) x;
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_LinearScan__active sd)) pos

_LinearScan__checkInactiveIntervals :: LinearScan__ScanStateDesc ->
                                       Prelude.Int ->
                                       LinearScan__NextScanState
_LinearScan__checkInactiveIntervals sd pos =
  let {
   go sd0 ss is pos0 =
     case is of {
      [] -> ss;
      (:) x xs ->
       let {
        st1 = case NPeano.ltb
                     (Interval.intervalEnd
                       (
                         (_LinearScan__V__nth (_LinearScan__nextInterval sd0)
                           (_LinearScan__intervals sd0) ( x)))) pos0 of {
               Prelude.True ->
                Lib.uncurry_sig (\x0 _ ->
                  _LinearScan__moveInactiveToHandled sd0 x0) x;
               Prelude.False ->
                case Interval.intervalCoversPos
                       (
                         (_LinearScan__V__nth (_LinearScan__nextInterval sd0)
                           (_LinearScan__intervals sd0) ( x))) pos0 of {
                 Prelude.True ->
                  Lib.uncurry_sig (\x0 _ ->
                    _LinearScan__moveInactiveToActive sd0 x0) x;
                 Prelude.False -> ss}}}
       in
       go sd0 st1 xs pos0}}
  in go sd sd (Lib.list_membership (_LinearScan__inactive sd)) pos

_LinearScan__handleInterval :: LinearScan__ScanStateDesc ->
                               LinearScan__NextState
_LinearScan__handleInterval sd =
  let {position = _LinearScan__curPosition sd} in
  let {sp1 = _LinearScan__checkActiveIntervals sd position} in
  let {
   sp2 = _LinearScan__checkInactiveIntervals (_LinearScan__nextDesc sp1)
           position}
  in
  let {
   result = Lib.fromMaybe
              (_LinearScan__allocateBlockedReg (_LinearScan__nextDesc sp2))
              (_LinearScan__tryAllocateFreeReg (_LinearScan__nextDesc sp2))}
  in
  _LinearScan__nextDesc result

_LinearScan__linearScan_F :: (LinearScan__ScanStateDesc -> () ->
                             LinearScan__ScanStateDesc) ->
                             LinearScan__ScanStateDesc ->
                             LinearScan__ScanStateDesc
_LinearScan__linearScan_F linearScan0 sd =
  case List0.destruct_list (_LinearScan__unhandled sd) of {
   Specif.Coq_inleft s -> linearScan0 (_LinearScan__handleInterval sd) __;
   Specif.Coq_inright -> sd}

_LinearScan__linearScan_terminate :: LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc
_LinearScan__linearScan_terminate sd =
  case List0.destruct_list (_LinearScan__unhandled sd) of {
   Specif.Coq_inleft s ->
    Specif.sig_rec (\rec_res _ -> rec_res)
      (_LinearScan__linearScan_terminate (_LinearScan__handleInterval sd));
   Specif.Coq_inright -> sd}

_LinearScan__linearScan :: LinearScan__ScanStateDesc ->
                           LinearScan__ScanStateDesc
_LinearScan__linearScan sd =
  case List0.destruct_list (_LinearScan__unhandled sd) of {
   Specif.Coq_inleft s ->
    Specif.sig_rec (\rec_res _ -> rec_res)
      (_LinearScan__linearScan (_LinearScan__handleInterval sd));
   Specif.Coq_inright -> sd}

data LinearScan__R_linearScan =
   LinearScan__R_linearScan_0 LinearScan__ScanStateDesc LinearScan__IntervalId 
 ([] LinearScan__IntervalId) LinearScan__ScanStateDesc LinearScan__ScanStateDesc 
 LinearScan__R_linearScan
 | LinearScan__R_linearScan_1 LinearScan__ScanStateDesc

_LinearScan__coq_R_linearScan_rect :: (LinearScan__ScanStateDesc -> () ->
                                      LinearScan__IntervalId -> ([]
                                      LinearScan__IntervalId) -> () -> () ->
                                      LinearScan__ScanStateDesc -> () -> ()
                                      -> () -> LinearScan__ScanStateDesc ->
                                      LinearScan__R_linearScan -> a1 -> a1)
                                      -> (LinearScan__ScanStateDesc -> () ->
                                      () -> () -> a1) ->
                                      LinearScan__ScanStateDesc ->
                                      LinearScan__ScanStateDesc ->
                                      LinearScan__R_linearScan -> a1
_LinearScan__coq_R_linearScan_rect f f0 sd s r =
  case r of {
   LinearScan__R_linearScan_0 sd0 x xs sd2 res r0 ->
    f sd0 __ x xs __ __ sd2 __ __ __ res r0
      (_LinearScan__coq_R_linearScan_rect f f0 sd2 res r0);
   LinearScan__R_linearScan_1 sd0 -> f0 sd0 __ __ __}

_LinearScan__coq_R_linearScan_rec :: (LinearScan__ScanStateDesc -> () ->
                                     LinearScan__IntervalId -> ([]
                                     LinearScan__IntervalId) -> () -> () ->
                                     LinearScan__ScanStateDesc -> () -> () ->
                                     () -> LinearScan__ScanStateDesc ->
                                     LinearScan__R_linearScan -> a1 -> a1) ->
                                     (LinearScan__ScanStateDesc -> () -> ()
                                     -> () -> a1) ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__ScanStateDesc ->
                                     LinearScan__R_linearScan -> a1
_LinearScan__coq_R_linearScan_rec f f0 sd s r =
  _LinearScan__coq_R_linearScan_rect f f0 sd s r

type LinearScan__VirtReg = Prelude.Int

type LinearScan__Graph a =
  a
  -- singleton inductive, whose constructor was Build_Graph
  
_LinearScan__coq_Graph_rect :: (a1 -> a2) -> (LinearScan__Graph a1) -> a2
_LinearScan__coq_Graph_rect f g =
  f g

_LinearScan__coq_Graph_rec :: (a1 -> a2) -> (LinearScan__Graph a1) -> a2
_LinearScan__coq_Graph_rec =
  _LinearScan__coq_Graph_rect

_LinearScan__postOrderTraversal :: (LinearScan__Graph a1) -> a1
_LinearScan__postOrderTraversal graph =
  graph

_LinearScan__determineIntervals :: (LinearScan__Graph LinearScan__VirtReg) ->
                                   LinearScan__ScanStateDesc
_LinearScan__determineIntervals =
  Prelude.error "AXIOM TO BE REALIZED"

_LinearScan__allocateRegisters :: (LinearScan__Graph LinearScan__VirtReg) ->
                                  LinearScan__ScanStateDesc
_LinearScan__allocateRegisters g =
  
    (Lib.uncurry_sig (\x _ -> _LinearScan__linearScan x)
      (_LinearScan__determineIntervals g))

