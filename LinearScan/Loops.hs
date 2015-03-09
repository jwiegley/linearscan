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

data LoopState =
   Build_LoopState IntMap.IntSet IntMap.IntSet ([] Blocks.BlockId) IntMap.IntSet 
 (IntMap.IntMap IntMap.IntSet) (IntMap.IntMap IntMap.IntSet) (IntMap.IntMap
                                                             ((,) Prelude.Int
                                                             Prelude.Int))

activeBlocks :: LoopState -> IntMap.IntSet
activeBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 loopDepths0 ->
    activeBlocks0}

visitedBlocks :: LoopState -> IntMap.IntSet
visitedBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 loopDepths0 ->
    visitedBlocks0}

loopHeaderBlocks :: LoopState -> [] Blocks.BlockId
loopHeaderBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 loopDepths0 ->
    loopHeaderBlocks0}

loopEndBlocks :: LoopState -> IntMap.IntSet
loopEndBlocks l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 loopDepths0 ->
    loopEndBlocks0}

forwardBranches :: LoopState -> IntMap.IntMap IntMap.IntSet
forwardBranches l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 loopDepths0 ->
    forwardBranches0}

backwardBranches :: LoopState -> IntMap.IntMap IntMap.IntSet
backwardBranches l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 loopDepths0 ->
    backwardBranches0}

loopDepths :: LoopState -> IntMap.IntMap ((,) Prelude.Int Prelude.Int)
loopDepths l =
  case l of {
   Build_LoopState activeBlocks0 visitedBlocks0 loopHeaderBlocks0
    loopEndBlocks0 forwardBranches0 backwardBranches0 loopDepths0 ->
    loopDepths0}

emptyLoopState :: LoopState
emptyLoopState =
  Build_LoopState IntMap.emptyIntSet IntMap.emptyIntSet [] IntMap.emptyIntSet
    IntMap.emptyIntMap IntMap.emptyIntMap IntMap.emptyIntMap

modifyActiveBlocks :: (IntMap.IntSet -> IntMap.IntSet) -> State.State
                      LoopState ()
modifyActiveBlocks f =
  State.modify (\st -> Build_LoopState (f (activeBlocks st))
    (visitedBlocks st) (loopHeaderBlocks st) (loopEndBlocks st)
    (forwardBranches st) (backwardBranches st) (loopDepths st))

modifyVisitedBlocks :: (IntMap.IntSet -> IntMap.IntSet) -> State.State
                       LoopState ()
modifyVisitedBlocks f =
  State.modify (\st -> Build_LoopState (activeBlocks st)
    (f (visitedBlocks st)) (loopHeaderBlocks st) (loopEndBlocks st)
    (forwardBranches st) (backwardBranches st) (loopDepths st))

modifyLoopHeaderBlocks :: (([] Blocks.BlockId) -> [] Blocks.BlockId) ->
                          State.State LoopState ()
modifyLoopHeaderBlocks f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (f (loopHeaderBlocks st)) (loopEndBlocks st) (forwardBranches st)
    (backwardBranches st) (loopDepths st))

modifyLoopEndBlocks :: (IntMap.IntSet -> IntMap.IntSet) -> State.State
                       LoopState ()
modifyLoopEndBlocks f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (loopHeaderBlocks st) (f (loopEndBlocks st)) (forwardBranches st)
    (backwardBranches st) (loopDepths st))

modifyForwardBranches :: ((IntMap.IntMap IntMap.IntSet) -> IntMap.IntMap
                         IntMap.IntSet) -> State.State LoopState ()
modifyForwardBranches f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (loopHeaderBlocks st) (loopEndBlocks st) (f (forwardBranches st))
    (backwardBranches st) (loopDepths st))

modifyBackwardBranches :: ((IntMap.IntMap IntMap.IntSet) -> IntMap.IntMap
                          IntMap.IntSet) -> State.State LoopState ()
modifyBackwardBranches f =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (loopHeaderBlocks st) (loopEndBlocks st) (forwardBranches st)
    (f (backwardBranches st)) (loopDepths st))

setLoopDepths :: (IntMap.IntMap ((,) Prelude.Int Prelude.Int)) -> State.State
                 LoopState ()
setLoopDepths depths =
  State.modify (\st -> Build_LoopState (activeBlocks st) (visitedBlocks st)
    (loopHeaderBlocks st) (loopEndBlocks st) (forwardBranches st)
    (backwardBranches st) depths)

addReference :: Prelude.Int -> Prelude.Int -> (IntMap.IntMap IntMap.IntSet)
                -> IntMap.IntMap IntMap.IntSet
addReference i x =
  IntMap.coq_IntMap_alter (\macc ->
    case macc of {
     Prelude.Just acc -> Prelude.Just (IntMap.coq_IntSet_insert x acc);
     Prelude.Nothing -> Prelude.Just (IntMap.coq_IntSet_singleton x)}) i

pathToLoopHeader :: Blocks.BlockId -> Prelude.Int -> LoopState ->
                    Prelude.Maybe IntMap.IntSet
pathToLoopHeader b header st =
  let {
   go fuel visited b0 =
     (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
       (\_ ->
       Prelude.Nothing)
       (\n ->
       let {visited' = IntMap.coq_IntSet_insert b0 visited} in
       let {
        forwardPreds = case IntMap.coq_IntMap_lookup b0 (forwardBranches st) of {
                        Prelude.Just preds -> IntMap.coq_IntSet_toList preds;
                        Prelude.Nothing -> []}}
       in
       let {
        backwardPreds = case IntMap.coq_IntMap_lookup b0
                               (backwardBranches st) of {
                         Prelude.Just preds -> IntMap.coq_IntSet_toList preds;
                         Prelude.Nothing -> []}}
       in
       let {preds = (Prelude.++) forwardPreds backwardPreds} in
       Lib.forFold (Prelude.Just (IntMap.coq_IntSet_singleton b0))
         (unsafeCoerce preds) (\mxs pred ->
         case mxs of {
          Prelude.Just xs ->
           case Eqtype.eq_op Ssrnat.nat_eqType pred (unsafeCoerce header) of {
            Prelude.True -> Prelude.Just
             (IntMap.coq_IntSet_union xs
               (IntMap.coq_IntSet_singleton (unsafeCoerce pred)));
            Prelude.False ->
             case IntMap.coq_IntSet_member (unsafeCoerce pred) visited' of {
              Prelude.True -> Prelude.Just xs;
              Prelude.False ->
               case unsafeCoerce go n visited' pred of {
                Prelude.Just ys -> Prelude.Just
                 (IntMap.coq_IntSet_union xs ys);
                Prelude.Nothing -> Prelude.Nothing}}};
          Prelude.Nothing -> Prelude.Nothing}))
       fuel}
  in go (IntMap.coq_IntSet_size (visitedBlocks st)) IntMap.emptyIntSet b

computeLoopDepths :: (Blocks.BlockInfo a1 a2 a3 a4) -> (IntMap.IntMap 
                     a1) -> LoopState -> IntMap.IntMap
                     ((,) Prelude.Int Prelude.Int)
computeLoopDepths binfo bs st =
  let {
   m = Lib.forFold IntMap.emptyIntMap
         (IntMap.coq_IntSet_toList (loopEndBlocks st)) (\m endBlock ->
         case IntMap.coq_IntMap_lookup endBlock bs of {
          Prelude.Just b ->
           Lib.forFold m (unsafeCoerce (Blocks.blockSuccessors binfo b))
             (\m' sux ->
             let {
              loopIndex = Seq.find (\x ->
                            Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce x)
                              sux) (loopHeaderBlocks st)}
             in
             case Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce loopIndex)
                    (unsafeCoerce (Data.List.length (loopHeaderBlocks st))) of {
              Prelude.True -> m';
              Prelude.False ->
               let {mres = pathToLoopHeader endBlock (unsafeCoerce sux) st}
               in
               case mres of {
                Prelude.Just path ->
                 Lib.forFold m' (IntMap.coq_IntSet_toList path) (\m'' blk ->
                   addReference loopIndex blk m'');
                Prelude.Nothing -> m'}});
          Prelude.Nothing -> m})}
  in
  let {
   f = \acc loopIndex refs ->
    IntMap.coq_IntSet_forFold acc refs (\m' blk ->
      let {
       f = \mx ->
        case mx of {
         Prelude.Just y ->
          case y of {
           (,) idx depth -> Prelude.Just ((,) (Prelude.min idx loopIndex)
            ((Prelude.succ) depth))};
         Prelude.Nothing -> Prelude.Just ((,) loopIndex ((Prelude.succ) 0))}}
      in
      IntMap.coq_IntMap_alter f blk m')}
  in
  IntMap.coq_IntMap_foldlWithKey f IntMap.emptyIntMap m

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
                              (modifyLoopHeaderBlocks (\l ->
                                case Prelude.not
                                       (Ssrbool.in_mem (unsafeCoerce sux)
                                         (Ssrbool.mem
                                           (Seq.seq_predType
                                             Ssrnat.nat_eqType)
                                           (unsafeCoerce l))) of {
                                 Prelude.True -> (:) sux l;
                                 Prelude.False -> l}));
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
     (,) n b ->
      State.bind (\x ->
        State.bind (\st -> setLoopDepths (computeLoopDepths binfo bs st))
          State.get) (go (IntMap.coq_IntMap_size bs) b)}}

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
      let {
       isHeavier = \x y ->
        let {x_id = Blocks.blockId binfo x} in
        let {y_id = Blocks.blockId binfo y} in
        let {
         x_depth = case IntMap.coq_IntMap_lookup x_id (loopDepths st) of {
                    Prelude.Just p ->
                     case p of {
                      (,) idx depth -> depth};
                    Prelude.Nothing -> 0}}
        in
        let {
         y_depth = case IntMap.coq_IntMap_lookup y_id (loopDepths st) of {
                    Prelude.Just p ->
                     case p of {
                      (,) idx depth -> depth};
                    Prelude.Nothing -> 0}}
        in
        (Prelude.<=) ((Prelude.succ) y_depth) x_depth}
      in
      let {
       go = let {
             go n branches work_list =
               (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
                 (\_ ->
                 [])
                 (\n0 ->
                 case work_list of {
                  [] -> [];
                  (:) w ws ->
                   case let {bid = Blocks.blockId binfo w} in
                        let {suxs = Blocks.blockSuccessors binfo w} in
                        Lib.forFoldr ((,) branches ws) suxs (\sux acc ->
                          case acc of {
                           (,) branches' ws' ->
                            let {
                             insertion = case IntMap.coq_IntMap_lookup sux
                                                blockMap of {
                                          Prelude.Just s ->
                                           Lib.insert isHeavier s ws';
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
                    (,) branches' ws' -> (:) w (go n0 branches' ws')}})
                 n}
            in go}
      in
      (,) st (go (Data.List.length blocks) (forwardBranches st) ((:) b []))}}

