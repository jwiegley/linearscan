{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Tempest where

import           Compiler.Hoopl as Hoopl hiding ((<*>))
import           Control.Applicative
import           Control.Exception
import           Control.Lens
import           Control.Monad.Free
import           Control.Monad.State.Class
import           Control.Monad.Trans.Class
import qualified Control.Monad.Trans.Free as TF
import           Control.Monad.Trans.Free hiding (FreeF(..), Free)
import           Control.Monad.Trans.State (StateT, evalStateT, evalState)
import           Data.Foldable
import qualified Data.List
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Monoid
-- import           Debug.Trace
import           LinearScan
import           Test.Hspec

------------------------------------------------------------------------------
-- The input from the Tempest compiler has the following shape: 'Procedure a
-- IRVar', which means that instructions ultimately refer to either physical
-- registers, or virtual variables (by index).
--
-- The output from the register allocator should be as close to the input as
-- possible, with the difference that it has type 'Procedure a Reg', meaning
-- that only physical registers are referenced.
--
-- So the main allocation algorithm roughly has this type at present:
--
--     regAlloc :: Procedure a IRVar -> Procedure a Reg
------------------------------------------------------------------------------

data AtomicGroup = AtomicGroup deriving (Eq, Show)
type Name = String

newtype Linearity = Linearity { isLinear :: Bool }
  deriving (Eq, Show)

-- | Tests used for branching (correspond to branching instructions)
data Test
  -- | beq
  = Zero
  -- | bne
  | NonZero
  -- | bgt
  | Positive
  -- | blt
  | Negative
  deriving (Eq, Show)

data CConv
  = CConvC {
      ccArgs     :: [Reg],
      ccResults  :: [Reg],
      ccIsBrack  :: Bool
    }
  | InlineC
  deriving (Eq, Show)

data Constant = Constant deriving (Eq, Show)

type Src a      = a

-- | Type synonym for indicating destination operands
type Dst a      = a

-- | Type synonym for indicating success or true branch
type Success a  = a

-- | Type synonym for indicating failure or false branch
type Failure a  = a

-- | Type synonym for indicating an external name
type Imported a = a

type Reg = Int

data Instruction reg
  = Add          reg reg reg
  | Nop
  deriving (Eq, Show, Functor, Foldable, Traversable)

data IRInstr v e x where
  Label         :: Label -> IRInstr v C O
  Alloc         :: AtomicGroup -> Maybe (Src v) -> Dst v -> IRInstr v O O
  Reclaim       :: Src v -> IRInstr v O O
  Instr         :: Instruction v -> IRInstr v O O
  Call          :: CConv -> Instruction v -> IRInstr v O O
  LoadConst     :: Constant -> Dst v -> IRInstr v O O
  Move          :: Src v -> Dst v -> IRInstr v O O
  Copy          :: Src v -> Dst v -> IRInstr v O O
  Save          :: Linearity -> Src v -> Dst Int -> IRInstr v O O
  Restore       :: Linearity -> Src Int -> Dst v -> IRInstr v O O
  SaveOffset    :: Linearity -> Int -> Src v -> Dst Int -> IRInstr v O O
  RestoreOffset :: Linearity -> Int -> Src Int -> Dst v -> IRInstr v O O
  Jump          :: Label -> IRInstr v O C
  Branch        :: Test -> v -> Success Label -> Failure Label
                -> IRInstr v O C
  Stwb          :: Linearity -> Src v -> Dst v
                -> Success Label -> Failure Label -> IRInstr v O C
  Strb          :: Src v -> Dst v -> Success Label -> Failure Label
                -> IRInstr v O C
  ReturnInstr   :: [Reg] -> Instruction v -> IRInstr v O C

deriving instance Eq v => Eq (IRInstr v e x)

instance Show v => Show (IRInstr v e x) where
  show (Label l)        = show l ++ ":"
  show (Alloc g x1 x2)  = "\t@alloc " ++ show g ++
                          (case x1 of Just v -> " " ++ show v ; _ -> " _")
                          ++ " " ++ show x2
  show (Reclaim v)      = "\t@reclaim " ++ show v
  show (Instr i)        = "\t" ++ show i
  show (Call c i)       = "\t@call " ++ show c ++ " " ++ show i
  show (LoadConst c v)  = "\t@lc " ++ show v ++ " " ++ show c
  show (Move x1 x2)     = "\t@mvrr " ++ show x1 ++ " " ++ show x2
  show (Copy x1 x2)     = "\t@cprr " ++ show x1 ++ " " ++ show x2
  show (Save (Linearity l) src dst)
                        = "\t@save " ++ show l ++ " " ++ show src ++ " " ++ show dst
  show (Restore (Linearity l) src dst)
                        = "\t@restore " ++ show l ++ " " ++ show src ++ " " ++ show dst
  show (SaveOffset (Linearity l) off src dst)
                        = unwords ["\t@saveoff", show l, show off, show src, show dst]
  show (RestoreOffset (Linearity l) off src dst)
                        = unwords ["\t@restoreoff", show l, show off, show src, show dst]
  show (Jump l)         = "\t@jmp " ++ show l
  show (Branch tst v t f)
                        = "\t@b" ++ show tst ++ " " ++ show v
                            ++ " " ++ show t
                            ++ "; @jmp " ++ show f
  show (Stwb lin x1 x2 t f)
                        = (if isLinear lin then "\t@stwlb " else "\t@stwb ")
                            ++ show x1 ++ " " ++ show x2
                            ++ " " ++ show f ++ "; @jmp " ++ show t
  show (Strb x1 x2 t f) = "\t@strb " ++ show x1 ++ " " ++ show x2
                            ++ " " ++ show f ++ "; @jmp " ++ show t
  show (ReturnInstr liveRegs i)   = "\t@return " ++ show liveRegs ++ " " ++ show i

data Node a v e x = Node
  { _nodeIRInstr :: IRInstr v e x
  , _nodeMeta    :: a
  } deriving Eq

instance Show v => Show (Node a v e x) where
    show (Node i _) = show i

instance NonLocal (Node a v) where
  entryLabel (Node (Label l)         _) = l
  successors (Node (Jump l)          _) = [l]
  successors (Node (Branch _ _ t f)  _) = [t, f]
  successors (Node (Stwb _ _ _ s f)  _) = [s, f]
  successors (Node (Strb _ _ s f)    _) = [s, f]
  successors (Node (ReturnInstr _ _) _) = []

data AtomKind = Atom deriving (Eq, Show)
data Var = Var deriving (Eq, Show)

data IRVar' = PhysicalIV !PhysReg
            | VirtualIV !Int !AtomKind
            deriving Eq

instance Show IRVar' where
    show (PhysicalIV r)  = "r" ++ show r
    show (VirtualIV n _) = "v" ++ show n

-- | Virtual IR variable together with an optional AST variable
data IRVar =
  IRVar
  { _ivVar :: !IRVar' -- ^ The virtual or physical register
  , _ivSrc :: !(Maybe Var) -- ^ An optional corresponding AST variable for
                       -- informational purposes.
  }
  deriving Eq

instance Show IRVar where
    show (IRVar x _) = show x

type Engine m = (UniqueMonad m, MonadState Labels m)

instance UniqueMonad (StateT Labels SimpleUniqueMonad) where
    freshUnique = lift freshUnique

asmTest :: (Engine m, m ~ StateT Labels SimpleUniqueMonad)
        => Int -> Program IRVar m () -> Program Reg m ()
        -> Expectation
asmTest regs (compile -> (prog, entry)) (compile -> (result, _)) =
    go $ M.fromList $ zip (Prelude.map entryLabel blocks) [(1 :: Int)..]
  where
    GMany NothingO body NothingO = prog
    blocks = postorder_dfs_from body entry

    go blockIds =
        case evalState
                 (allocate regs (blockInfo getBlockId) opInfo blocks)
                 (newSpillStack 0) of
            Left e -> error $ "Allocation failed: " ++ e
            Right blks -> do
                let graph' = newGraph blks
                catch
                    (showGraph show graph' `shouldBe` showGraph show result)
                    (\e -> do
                          putStrLn "---- Expecting ----"
                          putStr $ showGraph show result
                          putStrLn "---- Compiled  ----"
                          putStr $ showGraph show graph'
                          putStrLn "-------------------"
                          throwIO (e :: SomeException))
      where
        newBody = Data.Foldable.foldl' (flip addBlock) emptyBody
        newGraph xs = GMany NothingO (newBody xs) NothingO

        getBlockId :: Hoopl.Label -> Int
        getBlockId lbl =
            fromMaybe (error "The impossible happened")
                      (M.lookup lbl blockIds)

variables :: Traversal (IRInstr v1 e x) (IRInstr v2 e x) v1 v2
variables f = go
  where
    go (Alloc ag msrc dst)           = Alloc ag <$> traverse f msrc <*> f dst
    go (Reclaim src)                 = Reclaim <$> f src
    go (Instr i)                     = Instr <$> traverse f i
    go (LoadConst c dst)             = LoadConst c <$> f dst
    go (Move src dst)                = Move <$> f src <*> f dst
    go (Copy src dst)                = Copy <$> f src <*> f dst
    go (Save lin src x)              = Save lin <$> f src <*> pure x
    go (Restore x1 x2 dst)           = Restore x1 x2 <$> f dst
    go (SaveOffset lin off src x)    = SaveOffset lin off <$> f src <*> pure x
    go (RestoreOffset lin off x dst) = RestoreOffset lin off x <$> f dst
    go (Branch x1 cond x2 x3)        = Branch x1 <$> f cond
                                                 <*> pure x2 <*> pure x3
    go (Stwb x1 src dst x2 x3)       = Stwb x1 <$> f src <*> f dst
                                               <*> pure x2 <*> pure x3
    go (Strb src dst x2 x3)          = Strb <$> f src <*> f dst
                                            <*> pure x2 <*> pure x3
    go (Call cc i)                   = Call cc <$> traverse f i
    go (ReturnInstr liveInRegs i)    = ReturnInstr liveInRegs <$> traverse f i
    go (Label x)                     = pure $ Label x
    go (Jump x)                      = pure $ Jump x

metadata :: Lens (Node a1 v e x) (Node a2 v e x) a1 a2
metadata f (Node instr meta) = Node instr <$> f meta

irinstr :: Traversal (Node a v1 e x) (Node a v2 e x)
                  (IRInstr v1 e x) (IRInstr v2 e x)
irinstr f (Node instr meta) = Node <$> f instr <*> pure meta

data NodeV a v = NodeCO { getNodeCO :: Node a v C O }
               | NodeOO { getNodeOO :: Node a v O O }
               | NodeOC { getNodeOC :: Node a v O C }

instance Functor (NodeV v) where
    fmap f (NodeCO n) = NodeCO (over (irinstr.variables) f n)
    fmap f (NodeOO n) = NodeOO (over (irinstr.variables) f n)
    fmap f (NodeOC n) = NodeOC (over (irinstr.variables) f n)

blockInfo :: (Hoopl.Label -> Int)
          -> BlockInfo (Block (Node a IRVar) C C)
                      (Block (Node a Reg) C C)
                      (NodeV a IRVar)
                      (NodeV a Reg)
blockInfo getBlockId = BlockInfo
    { blockId = getBlockId . entryLabel

    , blockSuccessors = Prelude.map getBlockId . successors

    , blockOps = \(BlockCC a b z) ->
        ([NodeCO a], Prelude.map NodeOO (blockToList b), [NodeOC z])

    , setBlockOps = \_ [a] b [z] ->
        BlockCC
            (getNodeCO a)
            (blockFromList (Prelude.map getNodeOO b))
            (getNodeOC z)
    }

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

opInfo :: OpInfo StackInfo (NodeV a IRVar) (NodeV a Reg)
opInfo = OpInfo
    { opKind = \n -> case n of
           NodeOO (Node i _) -> case i of
               Call {} -> IsCall
               -- jww (2015-01-18): Identification of loop boundaries allows
               -- the allocator to perform a block ordering optimization to
               -- avoid excessive saves and restores, but it is optional.
               -- ?       -> LoopBegin
               -- ?       -> LoopEnd
               _ -> IsNormal
           NodeOC (Node i _) -> case i of
               Jump {}   -> IsBranch
               Branch {} -> IsBranch
               Strb {}   -> IsBranch
               Stwb {}   -> IsBranch
               _ -> IsNormal
           _ -> IsNormal

    , opRefs = \n -> let f = getReferences in case n of
           NodeCO o -> f o
           NodeOO o -> f o
           NodeOC o -> f o

    , moveOp = \sr dr -> do
        let mv = Move sr dr
        return [NodeOO (Node mv (error "no move meta"))]

    , swapOp = \sr dr ->
        liftA2 (++) (mkRestoreOp Nothing dr)
                    (mkSaveOp sr Nothing)

    , saveOp = mkSaveOp
    , restoreOp = mkRestoreOp

      -- Apply allocations, which changes IRVar's into Reg's.
    , applyAllocs = \node m -> [fmap (setRegister m) node]
    }
  where
    go :: Instruction IRVar -> [VarInfo]
    go Nop = mempty
    go (Add s1 s2 d1) =
        mkv Input s1 <> mkv Input s2 <> mkv Output d1

    mkv :: VarKind -> IRVar -> [VarInfo]
    mkv k (IRVar (PhysicalIV n) _)  = [vinfo k (Left n)]
    mkv k (IRVar (VirtualIV n _) _) = [vinfo k (Right n)]

    vinfo k en = VarInfo
        { varId   = en
        , varKind = k
          -- If there are variables which can be used directly from
          -- memory, then this can be False, which relaxes some
          -- requirements.
        , regRequired = True
        }

    getReferences :: Node a IRVar e x -> [VarInfo]
    getReferences (Node (Label _) _)         = mempty
    getReferences (Node (Instr i) _)         = go i
    getReferences (Node (Jump _) _)          = mempty
    getReferences (Node (Move src dst) _)    = mkv Input src <> mkv Output dst
    getReferences (Node (LoadConst _ v) _)   = mkv Output v
    getReferences (Node (Branch _ v _ _) _)  = mkv Input v
    getReferences (Node (ReturnInstr _ i) _) = go i
    getReferences n = error $ "getReferences: unhandled node: " ++ show n

    setRegister :: [(Int, PhysReg)] -> IRVar -> Reg
    setRegister _ (IRVar (PhysicalIV r) _)  = r
    setRegister m (IRVar (VirtualIV n _) _) =
        fromMaybe (error $ "Allocation failed for variable " ++ show n)
                  (Data.List.lookup n m)

mkSaveOp r vid = do
    stack <- get
    off' <- case M.lookup vid (stackSlots stack) of
        Just off -> return off
        Nothing -> do
            let off = stackPtr stack
            put StackInfo
                 { stackPtr   = off + 8
                 , stackSlots =
                     M.insert vid off (stackSlots stack)
                 }
            return off
    let sv = Save (Linearity False) r off'
    return [NodeOO (Node sv (error "no save meta"))]

mkRestoreOp vid r = do
    stack <- get
    let off = fromMaybe (-1) (M.lookup vid (stackSlots stack))
        rs  = Restore (Linearity False) off r
    return [NodeOO (Node rs (error "no restore meta"))]

var :: Int -> IRVar
var i = IRVar { _ivVar = VirtualIV i Atom
              , _ivSrc = Nothing
              }

fixed :: Int -> IRVar
fixed i = IRVar { _ivVar = PhysicalIV i
                , _ivSrc = Nothing
                }

reg :: PhysReg -> PhysReg
reg r = r

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
r33 = reg 33
r34 = reg 34
r35 = reg 35

type BodyF v = Free ((,) (Node () v O O)) ()

nodesToList :: BodyF v -> [Node () v O O]
nodesToList (Pure ()) = []
nodesToList (Free (Node n meta, xs)) = Node n meta : nodesToList xs

data ProgramF m v
    = FreeLabel
      { labelEntry :: Label
      , labelBody  :: BodyF v
      , labelClose :: m (Node () v O C)
      }

type Program v m a = FreeT ((,) (ProgramF m v)) m a

type Labels = M.Map String Label

getLabel :: Engine m => String -> m Label
getLabel str = do
    l <- use (at str)
    case l of
        Just lbl -> return lbl
        Nothing -> do
            lbl <- freshLabel
            at str .= Just lbl
            return lbl

label :: Engine m => String -> BodyF v -> m (Node () v O C) -> Program v m ()
label str body close = do
    lbl <- lift $ getLabel str
    liftF (FreeLabel lbl body close, ())

label_ :: Engine m => String -> m (Node () v O C) -> Program v m ()
label_ str close = do
    lbl <- lift $ getLabel str
    liftF (FreeLabel lbl (Pure ()) close, ())

compile :: (Engine m, m ~ StateT Labels SimpleUniqueMonad, NonLocal (Node () v))
        => Program v m () -> (Graph (Node () v) C C, Hoopl.Label)
compile prog = runSimpleUniqueMonad $
    flip evalStateT (mempty :: M.Map String Label) $ do
        body  <- go prog
        entry <- use (at "entry")
        case entry of
            Nothing -> error "Missing 'entry' label"
            Just lbl -> return (bodyGraph body, lbl)
  where
    go m = do
        p <- runFreeT m
        case p of
            TF.Pure ()        -> return emptyBody
            TF.Free (blk, xs) -> addBlock <$> comp blk <*> go xs

    comp (FreeLabel lbl body close) = do
        close' <- close
        return $ BlockCC (Node (Label lbl) ())
                         (blockFromList (nodesToList body)) close'

add :: v -> v -> v -> BodyF v
add x0 x1 x2 = Free (Node (Instr (Add x0 x1 x2)) (), Pure ())

move :: v -> v -> BodyF v
move x0 x1 = Free (Node (Move x0 x1) (), Pure ())

lc :: v -> BodyF v
lc x0 = Free (Node (LoadConst Constant x0) (), Pure ())

return_ :: Monad m => m (Node () v O C)
return_ = return $ Node (ReturnInstr [] Nop) ()

branch :: Engine m => Test -> v -> String -> String -> m (Node () v O C)
branch tst v good bad = do
    lblg <- getLabel good
    lblb <- getLabel bad
    return $ Node (Branch tst v lblg lblb) ()

jump :: Engine m => String -> m (Node () v O C)
jump dest = do
    lbl <- getLabel dest
    return $ Node (Jump lbl) ()

save :: PhysReg -> Dst Reg -> BodyF Reg
save r dst = Free (Node (Save (Linearity False) r dst) (), Pure ())

restore :: Src Reg -> PhysReg -> BodyF Reg
restore src r = Free (Node (Restore (Linearity False) src r) (), Pure ())
