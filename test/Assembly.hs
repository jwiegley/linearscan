{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Assembly where

import           Compiler.Hoopl as Hoopl hiding ((<*>))
import           Control.Applicative
import           Control.Monad.Trans.State
import           Data.Foldable
import           Data.Traversable
import qualified Data.List
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Monoid
import           Lens.Family hiding (Constant)
import           LinearScan
import           DSL
import           Hoopl

default (Int)

-- | The basic instructions that have nothing to do with control flow.
data Instruction reg = Add reg reg reg
                     | Nop
    deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Tests used for branching (correspond to branching instructions)
data Test = Zero                -- ^ beq
          | NonZero             -- ^ bne
          | Positive            -- ^ bgt
          | Negative            -- ^ blt
          deriving (Eq, Show)

data CConv = InlineC
           | CConvC { ccArgs     :: [PhysReg]
                    , ccResults  :: [PhysReg]
                    , ccIsBrack  :: Bool
                    }
    deriving (Eq, Show)

type Src a      = a -- ^ Type synonym for indicating source operands
type Dst a      = a -- ^ Type synonym for indicating destination operands
type Success a  = a -- ^ Type synonym for indicating success or true branch
type Failure a  = a -- ^ Type synonym for indicating failure or false branch

data Node v e x where
    Label :: Label -> Node v C O

    Alloc     :: Maybe (Src v) -> Dst v -> Node v O O
    Reclaim   :: Src v -> Node v O O
    Instr     :: Instruction v -> Node v O O
    Call      :: CConv -> Instruction v -> Node v O O
    LoadConst :: Int -> Dst v -> Node v O O
    Move      :: Src v -> Dst v -> Node v O O
    Copy      :: Src v -> Dst v -> Node v O O
    Save      :: Src v -> Dst Int -> Node v O O
    Restore   :: Src Int -> Dst v -> Node v O O

    Jump        :: Label -> Node v O C
    Branch      :: Test -> v -> Success Label -> Failure Label -> Node v O C
    ReturnInstr :: [PhysReg] -> Instruction v -> Node v O C

deriving instance Eq v => Eq (Node v e x)

instance Show v => Show (Node v e x) where
    show (Label l)         = show l ++ ":"
    show (Alloc x1 x2)     = "\t@alloc " ++
                             (case x1 of Just v -> " " ++ show v ; _ -> " _")
                             ++ " " ++ show x2
    show (Reclaim v)       = "\t@reclaim " ++ show v
    show (Instr i)         = "\t" ++ show i
    show (Call c i)        = "\t@call " ++ show c ++ " " ++ show i
    show (LoadConst c v)   = "\t@lc " ++ show v ++ " " ++ show c
    show (Move x1 x2)      = "\t@mvrr " ++ show x1 ++ " " ++ show x2
    show (Copy x1 x2)      = "\t@cprr " ++ show x1 ++ " " ++ show x2
    show (Save src dst)    = "\t@save " ++ " " ++ show src ++ " " ++ show dst
    show (Restore src dst) = "\t@restore " ++ " " ++ show src ++ " " ++ show dst
    show (Jump l)          = "\t@jmp " ++ show l
    show (Branch c v t f)  = "\t@b" ++ show c ++ " " ++ show v
                          ++ " " ++ show t ++ "; @jmp " ++ show f
    show (ReturnInstr regs i) = "\t@return " ++ show regs ++ " " ++ show i

instance NonLocal (Node v) where
  entryLabel (Label l) = l

  successors (Jump l)          = [l]
  successors (Branch _ _ t f)  = [t, f]
  successors (ReturnInstr _ _) = []

instance HooplNode (Node v) where
    mkBranchNode = Jump
    mkLabelNode  = Label

variables :: Applicative f => LensLike f (Node v1 e x) (Node v2 e x) v1 v2
variables f = go
  where
    go (Alloc msrc dst)           = Alloc <$> traverse f msrc <*> f dst
    go (Reclaim src)              = Reclaim <$> f src
    go (Instr i)                  = Instr <$> traverse f i
    go (LoadConst c dst)          = LoadConst c <$> f dst
    go (Move src dst)             = Move <$> f src <*> f dst
    go (Copy src dst)             = Copy <$> f src <*> f dst
    go (Save src x)               = Save <$> f src <*> pure x
    go (Restore x src)            = Restore x <$> f src
    go (Branch x1 cond x2 x3)     = Branch x1 <$> f cond <*> pure x2 <*> pure x3
    go (Call cc i)                = Call cc <$> traverse f i
    go (ReturnInstr liveInRegs i) = ReturnInstr liveInRegs <$> traverse f i
    go (Label x)                  = pure $ Label x
    go (Jump x)                   = pure $ Jump x

add :: v -> v -> v -> BodyNode (Node v)
add x0 x1 x2 = bodyNode $ Instr (Add x0 x1 x2)

nop :: BodyNode (Node v)
nop = bodyNode $ Instr Nop

move :: v -> v -> BodyNode (Node v)
move x0 x1 = bodyNode $ Move x0 x1

lc :: v -> BodyNode (Node v)
lc x0 = bodyNode $ LoadConst 0 x0

save :: PhysReg -> Dst PhysReg -> BodyNode (Node PhysReg)
save r dst = bodyNode $ Save r dst

restore :: Src PhysReg -> PhysReg -> BodyNode (Node PhysReg)
restore src r = bodyNode $ Restore src r

branch :: Test -> v -> String -> String -> EndNode (Node v)
branch tst v good bad =
    endNode $ Branch tst v <$> getLabel good <*> getLabel bad

return_ :: EndNode (Node v)
return_ = endNode $ return $ ReturnInstr [] Nop

data StackInfo = StackInfo
    { stackPtr   :: Int
    , stackSlots :: M.Map (Maybe Int) Int
    }
    deriving (Eq, Show)

newSpillStack :: Int -> StackInfo
newSpillStack offset = StackInfo
    { stackPtr   = offset
    , stackSlots = mempty
    }

getStackSlot :: Maybe VarId -> State StackInfo Int
getStackSlot vid = do
    stack <- get
    case M.lookup vid (stackSlots stack) of
        Just off -> return off
        Nothing -> do
            let off = stackPtr stack
            put StackInfo
                 { stackPtr   = off + 8
                 , stackSlots =
                     M.insert vid off (stackSlots stack)
                 }
            return off

data IRVar = PhysicalIV PhysReg | VirtualIV Int deriving Eq

instance Show IRVar where
    show (PhysicalIV r) = "r" ++ show r
    show (VirtualIV n)  = "v" ++ show n

instance NodeAlloc StackInfo (Node IRVar) (Node PhysReg) where
    isCall (Call {}) = True
    isCall _ = False

    isBranch (Jump {})   = True
    isBranch (Branch {}) = True
    isBranch _ = False

    getReferences = go
      where
        go :: Node IRVar e x -> [VarInfo]
        go (Label _)         = mempty
        go (Instr i)         = fromInstr i
        go (Jump _)          = mempty
        go (Move src dst)    = mkv Input src <> mkv Output dst
        go (LoadConst _ v)   = mkv Output v
        go (Branch _ v _ _)  = mkv Input v
        go (ReturnInstr _ i) = fromInstr i
        go n = error $ "getReferences: unhandled node: " ++ show n

        fromInstr :: Instruction IRVar -> [VarInfo]
        fromInstr Nop = mempty
        fromInstr (Add s1 s2 d1) =
            mkv Input s1 <> mkv Input s2 <> mkv Output d1

        mkv :: VarKind -> IRVar -> [VarInfo]
        mkv k (PhysicalIV n) = [vinfo k (Left n)]
        mkv k (VirtualIV n)  = [vinfo k (Right n)]

        vinfo k en = VarInfo
            { varId       = en
            , varKind     = k
            , regRequired = True
            }

    setRegisters = over variables . go
      where
        go :: [(Int, PhysReg)] -> IRVar -> PhysReg
        go _ (PhysicalIV r) = r
        go m (VirtualIV n)  =
            fromMaybe (error $ "Allocation failed for variable " ++ show n)
                      (Data.List.lookup n m)

    mkMoveOps src dst = return [Move src dst]
    mkSwapOps src dst = liftA2 (++) (mkRestoreOps Nothing dst)
                                    (mkSaveOps src Nothing)

    mkSaveOps    src dst = do off <- getStackSlot dst
                              return [Save src off]
    mkRestoreOps src dst = do off <- getStackSlot src
                              return [Restore off dst]

var :: Int -> IRVar
var = VirtualIV

v0  = var 0
v1  = var 1
v2  = var 2
v3  = var 3
v4  = var 4
v5  = var 5
v6  = var 6
v7  = var 7
v8  = var 8
v9  = var 9
v10 = var 10
v11 = var 11
v12 = var 12
v13 = var 13
v14 = var 14
v15 = var 15
v16 = var 16
v17 = var 17
v18 = var 18
v19 = var 19
v20 = var 20
v21 = var 21
v22 = var 22
v23 = var 23
v24 = var 24
v25 = var 25
v26 = var 26
v27 = var 27
v28 = var 28
v29 = var 29
v30 = var 30
v31 = var 31
v32 = var 32
v33 = var 33
v34 = var 34
v35 = var 35
v36 = var 36
v37 = var 37
v38 = var 38
v39 = var 39
v40 = var 40

reg :: PhysReg -> PhysReg
reg r = r

r0  = reg 0
r1  = reg 1
r2  = reg 2
r3  = reg 3
r4  = reg 4
r5  = reg 5
r6  = reg 6
r7  = reg 7
r8  = reg 8
r9  = reg 9
r10 = reg 10
r11 = reg 11
r12 = reg 12
r13 = reg 13
r14 = reg 14
r15 = reg 15
r16 = reg 16
r17 = reg 17
r18 = reg 18
r19 = reg 19
r20 = reg 20
r21 = reg 21
r22 = reg 22
r23 = reg 23
r24 = reg 24
r25 = reg 25
r26 = reg 26
r27 = reg 27
r28 = reg 28
r29 = reg 29
r30 = reg 30
r31 = reg 31
r32 = reg 32
