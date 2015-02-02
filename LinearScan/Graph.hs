{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Graph where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Seq as Seq
import qualified LinearScan.Ssrbool as Ssrbool



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

data Graph =
   Build_Graph ([] (Prelude.Maybe Eqtype.Equality__Coq_sort)) ([]
                                                              ((,)
                                                              (Prelude.Maybe
                                                              Eqtype.Equality__Coq_sort)
                                                              (Prelude.Maybe
                                                              Eqtype.Equality__Coq_sort)))

vertices :: Eqtype.Equality__Coq_type -> Graph -> []
            (Prelude.Maybe Eqtype.Equality__Coq_sort)
vertices a g =
  case g of {
   Build_Graph vertices0 edges0 -> vertices0}

edges :: Eqtype.Equality__Coq_type -> Graph -> []
         ((,) (Prelude.Maybe Eqtype.Equality__Coq_sort)
         (Prelude.Maybe Eqtype.Equality__Coq_sort))
edges a g =
  case g of {
   Build_Graph vertices0 edges0 -> edges0}

emptyGraph :: Eqtype.Equality__Coq_type -> Graph
emptyGraph a =
  Build_Graph [] []

addVertex :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort -> Graph
             -> Graph
addVertex a v g =
  let {vg = vertices a g} in
  Build_Graph
  (case Ssrbool.in_mem v
          (Ssrbool.mem (Seq.seq_predType (Eqtype.option_eqType a))
            (unsafeCoerce vg)) of {
    Prelude.True -> vg;
    Prelude.False -> (:) (unsafeCoerce v) vg}) (edges a g)

addEdge :: Eqtype.Equality__Coq_type -> Eqtype.Equality__Coq_sort -> Graph ->
           Graph
addEdge a e g =
  let {
   g' = let {eg = edges a g} in
        Build_Graph (vertices a g)
        (case Ssrbool.in_mem e
                (Ssrbool.mem
                  (Seq.seq_predType
                    (Eqtype.prod_eqType (Eqtype.option_eqType a)
                      (Eqtype.option_eqType a))) (unsafeCoerce eg)) of {
          Prelude.True -> eg;
          Prelude.False -> (:) (unsafeCoerce e) eg})}
  in
  addVertex a (Prelude.fst (unsafeCoerce e))
    (addVertex a (Prelude.snd (unsafeCoerce e)) g')

removeEdge :: Eqtype.Equality__Coq_type -> ((,)
              (Prelude.Maybe Eqtype.Equality__Coq_sort)
              (Prelude.Maybe Eqtype.Equality__Coq_sort)) -> Graph -> Graph
removeEdge a x g =
  Build_Graph (vertices a g)
    (Prelude.filter (\y ->
      Prelude.not
        (Eqtype.eq_op
          (Eqtype.prod_eqType (Eqtype.option_eqType a)
            (Eqtype.option_eqType a)) (unsafeCoerce y) (unsafeCoerce x)))
      (edges a g))

connections :: Eqtype.Equality__Coq_type -> (((,)
               (Prelude.Maybe Eqtype.Equality__Coq_sort)
               (Prelude.Maybe Eqtype.Equality__Coq_sort)) -> Prelude.Maybe
               Eqtype.Equality__Coq_sort) -> (Prelude.Maybe
               Eqtype.Equality__Coq_sort) -> Graph -> []
               ((,) (Prelude.Maybe Eqtype.Equality__Coq_sort)
               (Prelude.Maybe Eqtype.Equality__Coq_sort))
connections a f x g =
  Prelude.filter
    ((Prelude..) (\y ->
      Eqtype.eq_op (Eqtype.option_eqType a) (unsafeCoerce y) (unsafeCoerce x))
      f) (edges a g)

outbound :: Eqtype.Equality__Coq_type -> (Prelude.Maybe
            Eqtype.Equality__Coq_sort) -> Graph -> []
            ((,) (Prelude.Maybe Eqtype.Equality__Coq_sort)
            (Prelude.Maybe Eqtype.Equality__Coq_sort))
outbound a =
  connections a Prelude.fst

inbound :: Eqtype.Equality__Coq_type -> (Prelude.Maybe
           Eqtype.Equality__Coq_sort) -> Graph -> []
           ((,) (Prelude.Maybe Eqtype.Equality__Coq_sort)
           (Prelude.Maybe Eqtype.Equality__Coq_sort))
inbound a =
  connections a Prelude.snd

tsort' :: Eqtype.Equality__Coq_type -> Prelude.Int -> ([]
          ((,) (Prelude.Maybe Eqtype.Equality__Coq_sort)
          (Prelude.Maybe Eqtype.Equality__Coq_sort))) -> ([]
          (Prelude.Maybe Eqtype.Equality__Coq_sort)) -> Graph -> []
          ((,) (Prelude.Maybe Eqtype.Equality__Coq_sort)
          (Prelude.Maybe Eqtype.Equality__Coq_sort))
tsort' a fuel l roots g =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    Seq.rev l)
    (\fuel0 ->
    case edges a g of {
     [] -> Seq.rev l;
     (:) p es ->
      case p of {
       (,) se de ->
        case roots of {
         [] ->
          let {l0 = (:) de []} in
          let {
           g' = addEdge a (unsafeCoerce ((,) se Prelude.Nothing))
                  (removeEdge a ((,) se de) g)}
          in
          case l0 of {
           [] -> [];
           (:) n s ->
            let {outEdges = outbound a n g'} in
            case Data.List.foldl' (\acc e ->
                   case acc of {
                    (,) res g'' -> (,) ((:) e res) (removeEdge a e g'')})
                   ((,) [] g') outEdges of {
             (,) res g'' ->
              let {outNodes = Prelude.map Prelude.snd outEdges} in
              let {
               s' = (Prelude.++) s
                      (Prelude.filter
                        ((Prelude..) Seq.nilp (\x -> inbound a x g''))
                        outNodes)}
              in
              tsort' a fuel0 ((Prelude.++) l res) s' g''}};
         (:) n s ->
          let {l0 = (:) n s} in
          case l0 of {
           [] -> [];
           (:) n0 s0 ->
            let {outEdges = outbound a n0 g} in
            case Data.List.foldl' (\acc e ->
                   case acc of {
                    (,) res g'' -> (,) ((:) e res) (removeEdge a e g'')})
                   ((,) [] g) outEdges of {
             (,) res g'' ->
              let {outNodes = Prelude.map Prelude.snd outEdges} in
              let {
               s' = (Prelude.++) s0
                      (Prelude.filter
                        ((Prelude..) Seq.nilp (\x -> inbound a x g''))
                        outNodes)}
              in
              tsort' a fuel0 ((Prelude.++) l res) s' g''}}}}})
    fuel

topsort :: Eqtype.Equality__Coq_type -> Graph -> []
           ((,) (Prelude.Maybe Eqtype.Equality__Coq_sort)
           (Prelude.Maybe Eqtype.Equality__Coq_sort))
topsort a g =
  let {
   noInbound = let {xs = Prelude.map Prelude.snd (edges a g)} in
               Prelude.filter (\x ->
                 Prelude.not
                   (Ssrbool.in_mem (unsafeCoerce x)
                     (Ssrbool.mem (Seq.seq_predType (Eqtype.option_eqType a))
                       (unsafeCoerce xs)))) (vertices a g)}
  in
  tsort' a ((Prelude.succ) (Data.List.length (vertices a g))) [] noInbound g

