{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Loops where


import Debug.Trace (trace, traceShow)
import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Blocks as Blocks
import qualified LinearScan.IntMap as IntMap
import qualified LinearScan.Lib as Lib
import qualified LinearScan.State as State
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Seq as Seq
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

data LoopState =
   Build_LoopState IntMap.IntSet IntMap.IntSet ([] Blocks.BlockId) IntMap.IntSet 
 (IntMap.IntMap IntMap.IntSet) (IntMap.IntMap IntMap.IntSet)

activeBlocks :: LoopState -> IntMap.IntSet
activeBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 -> activeBlocks0}

visitedBlocks :: LoopState -> IntMap.IntSet
visitedBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 -> visitedBlocks0}

loopHeaderBlocks :: LoopState -> [] Blocks.BlockId
loopHeaderBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 -> loopHeaderBlocks0}

loopEndBlocks :: LoopState -> IntMap.IntSet
loopEndBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 -> loopEndBlocks0}

forwardBranches :: LoopState -> IntMap.IntMap IntMap.IntSet
forwardBranches l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 -> forwardBranches0}

backwardBranches :: LoopState -> IntMap.IntMap IntMap.IntSet
backwardBranches l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 -> backwardBranches0}

emptyLoopState :: LoopState
emptyLoopState =
  Build_LoopState IntMap.emptyIntSet IntMap.emptyIntSet [] IntMap.emptyIntSet
    IntMap.emptyIntMap IntMap.emptyIntMap

modifyActiveBlocks :: (IntMap.IntSet -> IntMap.IntSet) -> State.State
                      LoopState ()
modifyActiveBlocks f =
  State.modify (\st -> Build_LoopState (f (activeBlocks st))
    (visitedBlocks st) (loopHeaderBlocks st) (loopEndBlocks st)
    (forwardBranches st) (backwardBranches st))

modifyVisitedBlocks :: (IntMap.IntSet -> IntMap.IntSet) -> State.State
                       LoopState ()
modifyVisitedBlocks f =
  State.modify (\st -> Build_LoopState (activeBlocks st)
    (f (visitedBlocks st)) (loopHeaderBlocks st) (loopEndBlocks st)
    (forwardBranches st) (backwardBranches st))

modifyLoopHeaderBlocks :: (([] Blocks.BlockId) -> [] Blocks.BlockId) ->
                          State.State LoopState ()
modifyLoopHeaderBlocks f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (f (loopHeaderBlocks st)) (loopEndBlocks st) (forwardBranches st)
    (backwardBranches st))

modifyLoopEndBlocks :: (IntMap.IntSet -> IntMap.IntSet) -> State.State
                       LoopState ()
modifyLoopEndBlocks f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (loopHeaderBlocks st) (f (loopEndBlocks st)) (forwardBranches st)
    (backwardBranches st))

modifyForwardBranches :: ((IntMap.IntMap IntMap.IntSet) -> IntMap.IntMap
                         IntMap.IntSet) -> State.State LoopState ()
modifyForwardBranches f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (loopHeaderBlocks st) (loopEndBlocks st) (f (forwardBranches st))
    (backwardBranches st))

modifyBackwardBranches :: ((IntMap.IntMap IntMap.IntSet) -> IntMap.IntMap
                          IntMap.IntSet) -> State.State LoopState ()
modifyBackwardBranches f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (loopHeaderBlocks st) (loopEndBlocks st) (forwardBranches st)
    (f (backwardBranches st)))

addReference :: Prelude.Int -> Prelude.Int -> (IntMap.IntMap IntMap.IntSet)
                -> IntMap.IntMap IntMap.IntSet
addReference i x =
  IntMap.coq_IntMap_alter (\macc ->
    case macc of {
     Prelude.Just acc -> Prelude.Just (IntMap.coq_IntSet_insert x acc);
     Prelude.Nothing -> Prelude.Just (IntMap.coq_IntSet_singleton x)}) i

findLoopEnds :: (Blocks.BlockInfo a1 a2 a3 a4) -> (IntMap.IntMap a1) ->
                State.State LoopState ()
findLoopEnds binfo bs =
  let {
   go = let {
         go n b =
           (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
             (\_ ->
             State.pure ())
             (\n0 ->
             let {bid = Blocks.blockId binfo b} in
             State.bind (\x ->
               State.bind (\x0 ->
                 State.bind (\x1 ->
                   modifyActiveBlocks (IntMap.coq_IntSet_delete bid))
                   (State.forM_ (Blocks.blockSuccessors binfo b) (\sux ->
                     State.bind (\active ->
                       State.bind (\x1 ->
                         State.bind (\visited ->
                           case IntMap.coq_IntSet_member sux visited of {
                            Prelude.True -> State.pure ();
                            Prelude.False ->
                             case IntMap.coq_IntMap_lookup sux bs of {
                              Prelude.Just x2 -> go n0 x2;
                              Prelude.Nothing -> State.pure ()}})
                           (State.gets visitedBlocks))
                         (case IntMap.coq_IntSet_member sux active of {
                           Prelude.True ->
                            State.bind (\x1 ->
                              State.bind (\x2 ->
                                modifyBackwardBranches (addReference sux bid))
                                (modifyLoopEndBlocks
                                  (IntMap.coq_IntSet_insert bid)))
                              (modifyLoopHeaderBlocks (\x1 -> (:) sux x1));
                           Prelude.False ->
                            modifyForwardBranches (addReference sux bid)}))
                       (State.gets activeBlocks))))
                 (modifyActiveBlocks (IntMap.coq_IntSet_insert bid)))
               (modifyVisitedBlocks (IntMap.coq_IntSet_insert bid)))
             n}
        in go}
  in
  case IntMap.coq_IntMap_toList bs of {
   [] -> State.pure ();
   (:) p l ->
    case p of {
     (,) n b -> go (IntMap.coq_IntMap_size bs) b}}

pathToLoopHeader :: Blocks.BlockId -> LoopState -> (,)
                    (Prelude.Maybe Prelude.Int) IntMap.IntSet
pathToLoopHeader b st =
  let {
   go = let {
         go fuel b0 =
           (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
             (\_ -> (,) Prelude.Nothing
             IntMap.emptyIntSet)
             (\n ->
             let {
              idx = Seq.find (\x ->
                      Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce x) b0)
                      (loopHeaderBlocks st)}
             in
             case Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce idx)
                    (unsafeCoerce (Data.List.length (loopHeaderBlocks st))) of {
              Prelude.True ->
               let {
                preds = case IntMap.coq_IntMap_lookup (unsafeCoerce b0)
                               (forwardBranches st) of {
                         Prelude.Just predecessors -> predecessors;
                         Prelude.Nothing -> IntMap.emptyIntSet}}
               in
               Lib.forFold ((,) Prelude.Nothing
                 (IntMap.coq_IntSet_singleton (unsafeCoerce b0)))
                 (unsafeCoerce (IntMap.coq_IntSet_toList preds)) (\z pred ->
                 case z of {
                  (,) mx xs ->
                   case go n pred of {
                    (,) my ys -> (,) (Lib.option_choose mx my)
                     (IntMap.coq_IntSet_union xs ys)}});
              Prelude.False -> (,) (Prelude.Just idx)
               (IntMap.coq_IntSet_singleton (unsafeCoerce b0))})
             fuel}
        in go}
  in
  unsafeCoerce go (IntMap.coq_IntSet_size (visitedBlocks st)) b

computeLoopDepths :: LoopState -> IntMap.IntMap ((,) Prelude.Int Prelude.Int)
computeLoopDepths st =
  Lib.forFold IntMap.emptyIntMap
    (IntMap.coq_IntSet_toList (loopEndBlocks st)) (\m endBlock ->
    case pathToLoopHeader endBlock st of {
     (,) mloopIndex path ->
      case mloopIndex of {
       Prelude.Just loopIndex ->
        Lib.forFold m (IntMap.coq_IntSet_toList path) (\m' blk ->
          let {
           f = \mx ->
            case mx of {
             Prelude.Just y ->
              case y of {
               (,) idx depth -> Prelude.Just ((,) (Prelude.min idx loopIndex)
                ((Prelude.succ) depth))};
             Prelude.Nothing -> Prelude.Just ((,) loopIndex ((Prelude.succ)
              0))}}
          in
          IntMap.coq_IntMap_alter f blk m');
       Prelude.Nothing -> m}})

computeBlockOrder :: (Blocks.BlockInfo a1 a2 a3 a4) -> ([] a1) -> (,)
                     LoopState ([] a1)
computeBlockOrder binfo blocks =
  case blocks of {
   [] -> (,) emptyLoopState [];
   (:) b bs ->
    let {
     blockMap = IntMap.coq_IntMap_fromList
                  (Prelude.map (\x -> (,) (Blocks.blockId binfo x) x) blocks)}
    in
    case findLoopEnds binfo blockMap emptyLoopState of {
     (,) u st ->
      let {depths = computeLoopDepths st} in
      let {
       lighter = \x y ->
        let {x_id = Blocks.blockId binfo x} in
        let {y_id = Blocks.blockId binfo y} in
        let {
         x_depth = case IntMap.coq_IntMap_lookup x_id depths of {
                    Prelude.Just p ->
                     case p of {
                      (,) idx depth -> depth};
                    Prelude.Nothing -> 0}}
        in
        let {
         y_depth = case IntMap.coq_IntMap_lookup y_id depths of {
                    Prelude.Just p ->
                     case p of {
                      (,) idx depth -> depth};
                    Prelude.Nothing -> 0}}
        in
        (Prelude.<=) ((Prelude.succ) x_depth) y_depth}
      in
      let {
       go = let {
             go n branches blocks' work_list =
               (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
                 (\_ ->
                 blocks')
                 (\n0 ->
                 case work_list of {
                  [] -> blocks';
                  (:) w ws ->
                   case let {bid = Blocks.blockId binfo w} in
                        let {suxs = Blocks.blockSuccessors binfo w} in
                        Lib.forFold ((,) branches ws) suxs (\acc sux ->
                          case acc of {
                           (,) branches' ws' ->
                            let {
                             insertion = case IntMap.coq_IntMap_lookup sux
                                                blockMap of {
                                          Prelude.Just s ->
                                           Lib.insert lighter s ws';
                                          Prelude.Nothing -> ws'}}
                            in
                            case IntMap.coq_IntMap_lookup sux branches' of {
                             Prelude.Just incs -> (,)
                              (IntMap.coq_IntMap_insert sux
                                (IntMap.coq_IntSet_delete bid incs)
                                branches')
                              (case Eqtype.eq_op Ssrnat.nat_eqType
                                      (unsafeCoerce
                                        (IntMap.coq_IntSet_size incs))
                                      (unsafeCoerce ((Prelude.succ) 0)) of {
                                Prelude.True -> insertion;
                                Prelude.False -> ws'});
                             Prelude.Nothing -> (,) branches' insertion}}) of {
                    (,) branches' ws' -> go n0 branches' ((:) w blocks') ws'}})
                 n}
            in go}
      in
      (,) st
      (go (Data.List.length blocks) (forwardBranches st) [] ((:) b []))}}

