{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Tempest where

import           Compiler.Hoopl as Hoopl hiding ((<*>))
import           Control.Applicative
import           Control.Exception
import           Control.Lens
import           Control.Monad.Free
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           Data.Foldable
import           Data.IntMap
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Monoid
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

data Test = Test deriving (Eq, Show)

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
  deriving (Eq, Show, Foldable, Functor)

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

asmTest :: Program IRVar -> Program Reg -> Expectation
asmTest (compile -> (prog, entry)) (compile -> (result, _)) =
    go $ M.fromList $ zip (Prelude.map entryLabel blocks) [(1 :: Int)..]
  where
    GMany NothingO body NothingO = prog
    blocks = postorder_dfs_from body entry

    go blockIds =
        case allocate (blockInfo getBlockId) opInfo varInfo
                      (Prelude.map BlockWrapVar blocks)
                      (newSpillStack 0) of
            Left e -> error $ "Allocation failed: " ++ e
            Right (blks, _) -> do
                let graph' = newGraph (Prelude.map getBlockWrapVar blks)
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

newtype IRInstrWrap e x v = IRInstrWrap { getIRInstrWrap :: IRInstr v e x }

instance Functor (IRInstrWrap e x) where
    fmap f (IRInstrWrap m) = IRInstrWrap (go m)
      where
        go (Label x)                     = Label x
        go (Alloc ag msrc dst)           = Alloc ag (f <$> msrc) (f dst)
        go (Reclaim src)                 = Reclaim (f src)
        go (Instr i)                     = Instr (fmap f i)
        go (LoadConst c dst)             = LoadConst c (f dst)
        go (Move src dst)                = Move (f src) (f dst)
        go (Copy src dst)                = Copy (f src) (f dst)
        go (Save lin src x)              = Save lin (f src) x
        go (Restore x1 x2 dst)           = Restore x1 x2 (f dst)
        go (SaveOffset lin off src x)    = SaveOffset lin off (f src) x
        go (RestoreOffset lin off x dst) = RestoreOffset lin off x (f dst)
        go (Jump x)                      = Jump x
        go (Branch x1 cond x2 x3)        = Branch x1 (f cond) x2 x3
        go (Stwb x1 src dst x2 x3)       = Stwb x1 (f src) (f dst) x2 x3
        go (Strb src dst x2 x3)          = Strb (f src) (f dst) x2 x3
        go (Call cc i)                   = Call cc (fmap f i)
        go (ReturnInstr liveInRegs i)    = ReturnInstr liveInRegs (fmap f i)

instance Foldable (IRInstrWrap e x) where
    foldMap f (IRInstrWrap m) = go m
      where
        go (Label _x)                       = mempty
        go (Alloc _ag Nothing dst)          = f dst
        go (Alloc _ag (Just src) dst)       = f src <> f dst
        go (Reclaim src)                    = f src
        go (Instr i)                        = foldMap f i
        go (LoadConst _c dst)               = f dst
        go (Move src dst)                   = f src <> f dst
        go (Copy src dst)                   = f src <> f dst
        go (Save _lin src _x)               = f src
        go (Restore _x1 _x2 dst)            = f dst
        go (SaveOffset _lin _off src _x)    = f src
        go (RestoreOffset _lin _off _x dst) = f dst
        go (Jump _x)                        = mempty
        go (Branch _x1 cond _x2 _x3)        = f cond
        go (Stwb _x1 src dst _x2 _x3)       = f src <> f dst
        go (Strb src dst _x2 _x3)           = f src <> f dst
        go (Call _cc i)                     = foldMap f i
        go (ReturnInstr _liveInRegs i)      = foldMap f i

newtype NodeWrapVar a e x v = NodeWrapVar { getNodeWrapVar :: Node a v e x }

instance Functor (NodeWrapVar v e x) where
    fmap f (NodeWrapVar (Node instr meta)) =
        NodeWrapVar (Node (getIRInstrWrap . fmap f . IRInstrWrap $ instr) meta)

instance Foldable (NodeWrapVar v e x) where
    foldMap f (NodeWrapVar (Node instr _meta)) = foldMap f . IRInstrWrap $ instr

data NodeV a v = NodeCO { getNodeCO :: NodeWrapVar a C O v }
               | NodeOO { getNodeOO :: NodeWrapVar a O O v }
               | NodeOC { getNodeOC :: NodeWrapVar a O C v }

instance Functor (NodeV v) where
    fmap f (NodeCO n) = NodeCO (fmap f n)
    fmap f (NodeOO n) = NodeOO (fmap f n)
    fmap f (NodeOC n) = NodeOC (fmap f n)

instance Foldable (NodeV v) where
    foldMap f (NodeCO n) = foldMap f n
    foldMap f (NodeOO n) = foldMap f n
    foldMap f (NodeOC n) = foldMap f n

newtype BlockWrapVar a e x v =
    BlockWrapVar { getBlockWrapVar :: Block (Node a v) e x }

instance Functor (BlockWrapVar v e x) where
    fmap f (BlockWrapVar b) =
        BlockWrapVar (mapBlock (getNodeWrapVar . fmap f . NodeWrapVar) b)

instance Foldable (BlockWrapVar v C C) where
    foldMap f (BlockWrapVar b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest) )
            b mempty

instance Foldable (BlockWrapVar v C O) where
    foldMap f (BlockWrapVar b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest) )
            b mempty

instance Foldable (BlockWrapVar v O C) where
    foldMap f (BlockWrapVar b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest) )
            b mempty

instance Foldable (BlockWrapVar v O O) where
    foldMap f (BlockWrapVar b) =
        foldBlockNodesF3
            ( (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest)
            , (\node rest -> foldMap f (NodeWrapVar node) <> rest) )
            b mempty

blockInfo :: (Hoopl.Label -> Int)
          -> BlockInfo (BlockWrapVar a C C) (NodeV a) IRVar Reg
blockInfo getBlockId = BlockInfo
    { blockId = getBlockId . entryLabel . getBlockWrapVar

    , blockSuccessors = Prelude.map getBlockId . successors . getBlockWrapVar

    , blockOps = \(BlockWrapVar (BlockCC a b z)) ->
        NodeCO (NodeWrapVar a) :
        NodeOC (NodeWrapVar z) :
        Prelude.map (NodeOO . NodeWrapVar) (blockToList b)

    , setBlockOps = \_ ops ->
        BlockWrapVar $ BlockCC
            (getNodeWrapVar (getNodeCO (head ops)))
            (blockFromList (Prelude.map (getNodeWrapVar . getNodeOO)
                                  (tail (tail ops))))
            (getNodeWrapVar (getNodeOC (ops !! 1)))
    }

data StackInfo = StackInfo
    { stackPtr   :: Int
    , stackSlots :: IntMap Int
    }
    deriving (Eq, Show)

newSpillStack :: Int -> StackInfo
newSpillStack offset = StackInfo
    { stackPtr   = offset
    , stackSlots = mempty
    }

opInfo :: OpInfo StackInfo (NodeV a) (Int, VarKind) IRVar Reg
opInfo = OpInfo
    { opKind = \n -> case n of
           NodeOO (NodeWrapVar (Node i _)) -> case i of
               Call {} -> IsCall
               -- jww (2015-01-18): Identification of loop boundaries allows
               -- the allocator to perform a block ordering optimization to
               -- avoid excessive saves and restores, but it is optional.
               -- ?       -> LoopBegin
               -- ?       -> LoopEnd
               _ -> IsNormal
           NodeOC (NodeWrapVar (Node i _)) -> case i of
               Jump {}   -> IsBranch
               Branch {} -> IsBranch
               Strb {}   -> IsBranch
               Stwb {}   -> IsBranch
               _ -> IsNormal
           _ -> IsNormal

    , opRefs = \n ->
       let f = getReferences . getNodeWrapVar in
       case n of
           NodeCO o -> f o
           NodeOO o -> f o
           NodeOC o -> f o

    , moveOp = \sr dr stack ->
        let mv = Move sr dr in
        (NodeOO (NodeWrapVar (Node mv (error "no move meta"))), stack)

    , saveOp = \vid r stack ->
        let (stack', off') =
                case Data.IntMap.lookup vid (stackSlots stack) of
                    Just off -> (stack, off)
                    Nothing ->
                        let off = stackPtr stack in
                        (StackInfo
                             { stackPtr   = off + 8
                             , stackSlots =
                                 Data.IntMap.insert vid off (stackSlots stack)
                             },
                         off)
            sv = Save (Linearity False) r off' in
        (NodeOO (NodeWrapVar (Node sv (error "no save meta"))), stack')

    , restoreOp = \vid r stack ->
        let off =
                fromMaybe (error "Restore requested but not stack allocated")
                          (Data.IntMap.lookup vid (stackSlots stack))
            rs = Restore (Linearity False) off r in
        (NodeOO (NodeWrapVar (Node rs (error "no restore meta"))), stack)

      -- Apply allocations, which changes IRVar's into Reg's.
    , applyAllocs = \node m -> fmap (setRegister (fromList m)) node
    }
  where
    go :: Instruction IRVar -> ([(Int, VarKind)], [PhysReg])
    go (Add s1 s2 d1) =
        mkv Input s1 <> mkv Input s2 <> mkv Output d1
      where
        mkv :: VarKind -> IRVar -> ([(Int, VarKind)], [PhysReg])
        mkv _ (IRVar (PhysicalIV n) _)    = ([], [n])
        mkv k (IRVar (VirtualIV n _) _) = ([(n, k)], [])
    go Nop = mempty

    getReferences :: Node a IRVar e x -> ([(Int, VarKind)], [PhysReg])
    getReferences (Node (Label _) _) = mempty
    getReferences (Node (Instr i) _) = go i
    getReferences (Node (ReturnInstr _ i) _) = go i
    getReferences n = error $ "getReferences: unhandled node: " ++ show n

    setRegister :: IntMap PhysReg -> IRVar -> Reg
    setRegister _ (IRVar (PhysicalIV r) _) = r
    setRegister m (IRVar (VirtualIV n _) _) =
        fromMaybe (error $ "Allocation failed for variable " ++ show n)
                  (Data.IntMap.lookup n m)

varInfo :: VarInfo (Int, VarKind)
varInfo = VarInfo
    { varId   = fst
    , varKind = snd

      -- If there are variables which can be used directly from memory, then
      -- this can be False, which relaxes some requirements.
    , regRequired = const True
    }

assignVar :: IntMap PhysReg -> IRVar -> IRVar
assignVar _ v@(IRVar (PhysicalIV _) _) = v
assignVar m (IRVar (VirtualIV n _) x) = case Data.IntMap.lookup n m of
    Just r -> IRVar (PhysicalIV r) x
    a -> error $ "Unexpected allocation " ++ show a
             ++ " for variable " ++ show n

convertNode :: Show a => Node a IRVar O O -> ([(VarKind, IRVar)], [PhysReg])
convertNode (Node (Instr i) _) = go i
  where
    go :: Instruction IRVar -> ([(VarKind, IRVar)], [PhysReg])
    go (Add a b c) = mkv Input a <> mkv Input b <> mkv Output c
    go x = error $ "convertNode.go: Unexpected " ++ show x

    mkv :: VarKind -> IRVar -> ([(VarKind, IRVar)], [PhysReg])
    mkv _ (IRVar (PhysicalIV r) _) = ([], [r])
    mkv k v = ([(k, v)], [])

convertNode x = error $ "convertNode: Unexpected" ++ show x

var :: Int -> IRVar
var i = IRVar { _ivVar = VirtualIV i Atom
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

nodesToList :: Free ((,) (Node () v O O)) () -> [Node () v O O]
nodesToList (Pure ()) = []
nodesToList (Free (Node n meta, xs)) = Node n meta : nodesToList xs

data ProgramF v
    = FreeLabel
      { labelString :: String
      , labelBody   :: Free ((,) (Node () v O O)) ()
      , labelClose  :: Node () v O C
      }

type Program v = Free ((,) (ProgramF v)) ()

label :: String -> Free ((,) (Node () v O O)) () -> Node () v O C
      -> Program v
label str body close = Free (FreeLabel str body close, Pure ())

compile :: NonLocal (Node () v)
        => Program v -> (Graph (Node () v) C C, Hoopl.Label)
compile prog = runSimpleUniqueMonad $
    flip evalStateT (mempty :: M.Map String Label) $ do
        body  <- go prog
        entry <- firstLabel prog
        return (bodyGraph body, entry)
  where
    go (Pure ())        = return emptyBody
    go (Free (blk, xs)) = addBlock <$> comp blk <*> go xs

    comp (FreeLabel str body close) = do
        lbl <- lift freshLabel
        at str .= Just lbl
        return $ BlockCC (Node (Label lbl) ())
                         (blockFromList (nodesToList body)) close

    firstLabel (Pure ()) = error "body is empty!"
    firstLabel (Free (FreeLabel str _ _, _)) =
        fromMaybe (error "firstLabel failed") <$> use (at str)

add :: v -> v -> v -> Free ((,) (Node () v O O)) ()
add x0 x1 x2 = Free (Node (Instr (Add x0 x1 x2)) (), Pure ())

return_ :: Node () v O C
return_ = Node (ReturnInstr [] Nop) ()

save :: PhysReg -> Dst Reg -> Free ((,) (Node () Reg O O)) ()
save r dst = Free (Node (Save (Linearity False) r dst) (), Pure ())

restore :: PhysReg -> Src Reg -> Free ((,) (Node () Reg O O)) ()
restore r src = Free (Node (Restore (Linearity False) src r) (), Pure ())
