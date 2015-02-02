module LinearScan.Blocks where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils


type PhysReg = Prelude.Int

data VarKind =
   Input
 | Temp
 | Output

type VarId = Prelude.Int

data VarInfo varType =
   Build_VarInfo (varType -> VarId) (varType -> VarKind) (varType ->
                                                         Prelude.Bool)

varId :: (VarInfo a1) -> a1 -> VarId
varId v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired -> varId0}

varKind :: (VarInfo a1) -> a1 -> VarKind
varKind v =
  case v of {
   Build_VarInfo varId0 varKind0 regRequired -> varKind0}

data OpKind =
   IsNormal
 | IsCall
 | IsBranch
 | IsLoopBegin
 | IsLoopEnd

data OpInfo accType opType1 opType2 varType =
   Build_OpInfo (opType1 -> OpKind) (opType1 -> (,) ([] varType)
                                    ([] PhysReg)) (PhysReg -> PhysReg ->
                                                  accType -> (,) ([] opType2)
                                                  accType) (PhysReg ->
                                                           PhysReg -> accType
                                                           -> (,)
                                                           ([] opType2)
                                                           accType) (PhysReg
                                                                    ->
                                                                    (Prelude.Maybe
                                                                    VarId) ->
                                                                    accType
                                                                    -> (,)
                                                                    ([]
                                                                    opType2)
                                                                    accType) 
 ((Prelude.Maybe VarId) -> PhysReg -> accType -> (,) ([] opType2) accType) 
 (opType1 -> ([] ((,) VarId PhysReg)) -> [] opType2)

opKind :: Prelude.Int -> (OpInfo a1 a2 a3 a4) -> a2 -> OpKind
opKind maxReg o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp saveOp0 restoreOp0
    applyAllocs0 -> opKind0}

opRefs :: Prelude.Int -> (OpInfo a1 a2 a3 a4) -> a2 -> (,) ([] a4)
          ([] PhysReg)
opRefs maxReg o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp saveOp0 restoreOp0
    applyAllocs0 -> opRefs0}

moveOp :: Prelude.Int -> (OpInfo a1 a2 a3 a4) -> PhysReg -> PhysReg -> a1 ->
          (,) ([] a3) a1
moveOp maxReg o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp saveOp0 restoreOp0
    applyAllocs0 -> moveOp0}

saveOp :: Prelude.Int -> (OpInfo a1 a2 a3 a4) -> PhysReg -> (Prelude.Maybe
          VarId) -> a1 -> (,) ([] a3) a1
saveOp maxReg o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp saveOp0 restoreOp0
    applyAllocs0 -> saveOp0}

restoreOp :: Prelude.Int -> (OpInfo a1 a2 a3 a4) -> (Prelude.Maybe VarId) ->
             PhysReg -> a1 -> (,) ([] a3) a1
restoreOp maxReg o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp saveOp0 restoreOp0
    applyAllocs0 -> restoreOp0}

applyAllocs :: Prelude.Int -> (OpInfo a1 a2 a3 a4) -> a2 -> ([]
               ((,) VarId PhysReg)) -> [] a3
applyAllocs maxReg o =
  case o of {
   Build_OpInfo opKind0 opRefs0 moveOp0 swapOp saveOp0 restoreOp0
    applyAllocs0 -> applyAllocs0}

type BlockId = Prelude.Int

data BlockInfo blockType1 blockType2 opType1 opType2 =
   Build_BlockInfo (blockType1 -> BlockId) (blockType1 -> [] BlockId) 
 (blockType1 -> [] opType1) (blockType1 -> ([] opType2) -> blockType2)

blockId :: (BlockInfo a1 a2 a3 a4) -> a1 -> BlockId
blockId b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0 setBlockOps0 ->
    blockId0}

blockSuccessors :: (BlockInfo a1 a2 a3 a4) -> a1 -> [] BlockId
blockSuccessors b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0 setBlockOps0 ->
    blockSuccessors0}

blockOps :: (BlockInfo a1 a2 a3 a4) -> a1 -> [] a3
blockOps b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0 setBlockOps0 ->
    blockOps0}

setBlockOps :: (BlockInfo a1 a2 a3 a4) -> a1 -> ([] a4) -> a2
setBlockOps b =
  case b of {
   Build_BlockInfo blockId0 blockSuccessors0 blockOps0 setBlockOps0 ->
    setBlockOps0}

type OpId = Prelude.Int

foldOps :: (BlockInfo a1 a2 a3 a4) -> (a5 -> a3 -> a5) -> a5 -> ([] a1) -> a5
foldOps binfo f z =
  Data.List.foldl' (\bacc blk ->
    Data.List.foldl' f bacc (blockOps binfo blk)) z

countOps :: (BlockInfo a1 a2 a3 a4) -> ([] a1) -> Prelude.Int
countOps binfo =
  foldOps binfo (\acc x -> (Prelude.succ) acc) 0

