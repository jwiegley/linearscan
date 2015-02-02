module LinearScan.LiveSets where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Blocks as Blocks
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Seq as Seq


data BlockLiveSets =
   Build_BlockLiveSets Data.IntSet.IntSet Data.IntSet.IntSet Data.IntSet.IntSet 
 Data.IntSet.IntSet Blocks.OpId Blocks.OpId

blockLiveGen :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveGen b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveGen0}

blockLiveKill :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveKill b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveKill0}

blockLiveIn :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveIn b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveIn0}

blockLiveOut :: BlockLiveSets -> Data.IntSet.IntSet
blockLiveOut b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLiveOut0}

blockFirstOpId :: BlockLiveSets -> Blocks.OpId
blockFirstOpId b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockFirstOpId0}

blockLastOpId :: BlockLiveSets -> Blocks.OpId
blockLastOpId b =
  case b of {
   Build_BlockLiveSets blockLiveGen0 blockLiveKill0 blockLiveIn0
    blockLiveOut0 blockFirstOpId0 blockLastOpId0 -> blockLastOpId0}

computeLocalLiveSets :: Prelude.Int -> (Blocks.BlockInfo a1 a2 a3 a4) ->
                        (Blocks.OpInfo a6 a3 a4 a5) -> (Blocks.VarInfo 
                        a5) -> ([] a1) -> Data.IntMap.IntMap BlockLiveSets
computeLocalLiveSets maxReg binfo oinfo vinfo blocks =
  Prelude.snd
    (Lib.forFold ((,) ((Prelude.succ) 0) Data.IntMap.empty) blocks (\acc b ->
      case acc of {
       (,) idx m ->
        let {
         liveSet = Build_BlockLiveSets Data.IntSet.empty Data.IntSet.empty
          Data.IntSet.empty Data.IntSet.empty idx idx}
        in
        case Lib.forFold ((,) idx liveSet) (Blocks.blockOps binfo b)
               (\acc0 o ->
               case acc0 of {
                (,) lastIdx liveSet1 -> (,) ((Prelude.succ) ((Prelude.succ)
                 lastIdx))
                 (Lib.forFold liveSet1
                   (Prelude.fst (Blocks.opRefs maxReg oinfo o))
                   (\liveSet2 v ->
                   let {vid = Blocks.varId vinfo v} in
                   case Blocks.varKind vinfo v of {
                    Blocks.Input ->
                     case Prelude.not
                            (Data.IntSet.member vid (blockLiveKill liveSet2)) of {
                      Prelude.True -> Build_BlockLiveSets
                       (Data.IntSet.insert vid (blockLiveGen liveSet2))
                       (blockLiveKill liveSet2) (blockLiveIn liveSet2)
                       (blockLiveOut liveSet2) (blockFirstOpId liveSet2)
                       lastIdx;
                      Prelude.False -> liveSet2};
                    _ -> Build_BlockLiveSets (blockLiveGen liveSet2)
                     (Data.IntSet.insert vid (blockLiveKill liveSet2))
                     (blockLiveIn liveSet2) (blockLiveOut liveSet2)
                     (blockFirstOpId liveSet2) lastIdx}))}) of {
         (,) lastIdx' liveSet3 -> (,) lastIdx'
          (Data.IntMap.insert (Blocks.blockId binfo b) liveSet3 m)}}))

computeGlobalLiveSets :: (Blocks.BlockInfo a1 a2 a3 a4) -> ([] a1) ->
                         (Data.IntMap.IntMap BlockLiveSets) ->
                         Data.IntMap.IntMap BlockLiveSets
computeGlobalLiveSets binfo blocks liveSets =
  Lib.forFold liveSets (Seq.rev blocks) (\liveSets1 b ->
    let {bid = Blocks.blockId binfo b} in
    case Data.IntMap.lookup bid liveSets1 of {
     Prelude.Just liveSet ->
      let {
       liveSet2 = Lib.forFold liveSet (Blocks.blockSuccessors binfo b)
                    (\liveSet1 s_bid ->
                    case Data.IntMap.lookup s_bid liveSets1 of {
                     Prelude.Just sux -> Build_BlockLiveSets
                      (blockLiveGen liveSet1) (blockLiveKill liveSet1)
                      (blockLiveIn liveSet1)
                      (Data.IntSet.union (blockLiveOut liveSet1)
                        (blockLiveIn sux)) (blockFirstOpId liveSet1)
                      (blockLastOpId liveSet1);
                     Prelude.Nothing -> liveSet1})}
      in
      Data.IntMap.insert bid (Build_BlockLiveSets (blockLiveGen liveSet2)
        (blockLiveKill liveSet2)
        (Data.IntSet.union
          (Data.IntSet.difference (blockLiveOut liveSet2)
            (blockLiveKill liveSet2)) (blockLiveGen liveSet2))
        (blockLiveOut liveSet2) (blockFirstOpId liveSet2)
        (blockLastOpId liveSet2)) liveSets1;
     Prelude.Nothing -> liveSets1})

