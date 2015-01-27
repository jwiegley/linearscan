{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -Werror #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Tempest where

-- import Debug.Trace
import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Data.Foldable
import Data.IntMap
import Data.Monoid
import LinearScan
import Test.Hspec

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

data Reg = Reg Int deriving (Eq, Show)

data Label = TLabel deriving (Eq, Show)

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
  Branch        :: Test -> v -> Success Label -> Failure Label -> IRInstr v O C
  Stwb          :: Linearity -> Src v -> Dst v ->
                   Success Label -> Failure Label -> IRInstr v O C
  Strb          :: Src v -> Dst v -> Success Label -> Failure Label -> IRInstr v O C
  ReturnInstr   :: [Reg] -> Instruction v -> IRInstr v O C

deriving instance Eq v => Eq (IRInstr v e x)

instance Show v => Show (IRInstr v e x) where
  show (Label l)        = show l ++ ":"
  show (Alloc g x1 x2)  = "\t@alloc " ++ show g ++
                          (case x1 of Just v -> " " ++ show v ; _ -> " _")
                          ++ " " ++ show x2
  show (Reclaim v)      = "\t@reclaim " ++ show v
  show (Instr i)        = "\n\t" ++ show i
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

newtype NodeWrapVar a e x v = NodeWrapVar { getNodeWrapVar :: Node a v e x }

instance Functor (NodeWrapVar v e x) where
    fmap f (NodeWrapVar (Node instr meta)) =
        NodeWrapVar (Node (getIRInstrWrap . fmap f . IRInstrWrap $ instr) meta)

data Node a v e x = Node
  { _nodeIRInstr :: IRInstr v e x
  , _nodeMeta    :: a
  } deriving Eq

instance Show v => Show (Node a v e x) where
    show (Node i _) = show i

data C = C
data O = O

data PNode v e x a = PNode (Node a v e x) deriving Eq

instance (Show a, Show v) => Show (PNode v e x a) where
    show (PNode n) = show n

instance Functor (PNode v e x) where
    fmap f (PNode (Node x y)) = PNode (Node x (f y))

data PBlock v e x a = PBlock (Node a v e x) deriving (Eq, Show)

data Block v e x a = Block
    { blockNum :: Int
    , getBlock :: [PNode v e x a]
    }
    deriving (Eq, Show)

nodeToOpList :: (Show a, Show v) => Node a v e x -> [Instruction v]
nodeToOpList (Node (Instr i) _) = [i]
nodeToOpList n = error $ "nodeToOpList: NYI for " ++ show n

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

asmTest (compile -> body) (compile -> result) =
    case allocate binfo oinfo vinfo [body] () of
        Left e   -> error $ "Allocation failed: " ++ e
        Right (xs, _) -> do
            print ("----" :: String)
            print xs
            print ("----" :: String)
            print result
            print ("----" :: String)
            length xs `shouldBe` length [result]
            zipWithM_ shouldBe xs [result]
  where
    binfo = BlockInfo
        { blockId         = blockNum
        , blockSuccessors = const []  -- jww (2015-01-27): NYI
        , blockOps        = getBlock
        , setBlockOps     = \b new -> b { getBlock = new }
        }
    oinfo = OpInfo
        { opKind      = const IsNormal -- jww (2015-01-27): NYI
        , opRefs      = convertNode
        , saveOp      = \_off _vid _reg -> error "jww (2015-01-27): NYI: saveOp"
        , restoreOp   = \_off _vid _reg -> error "jww (2015-01-27): NYI: restoreOp"
        , applyAllocs = \o m -> conv (fromList m) o
        }
    vinfo = VarInfo
        { varId       = \(_, v) -> case v of
               IRVar (VirtualIV n _) _ -> n
               _ -> error $ "Unexpected variable: " ++ show v
        , varKind     = fst
        , regRequired = const True
        }

    conv m (PNode (Node i meta)) = PNode $ Node (convInstr m i) meta
    convInstr m = getIRInstrWrap . fmap (assignVar m) . IRInstrWrap

assignVar :: IntMap PhysReg -> IRVar -> IRVar
assignVar _ v@(IRVar (PhysicalIV _) _) = v
assignVar m (IRVar (VirtualIV n _) x) = case Data.IntMap.lookup n m of
    Just r -> IRVar (PhysicalIV r) x
    a -> error $ "Unexpected allocation " ++ show a
             ++ " for variable " ++ show n

convertNode :: Show a => PNode IRVar O O a -> ([(VarKind, IRVar)], [PhysReg])
convertNode (PNode (Node (Instr i) _)) = go i
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

reg :: PhysReg -> IRVar
reg r = IRVar { _ivVar = PhysicalIV r
              , _ivSrc = Nothing
              }

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

type Program a = Free (PNode IRVar O O) a

compile :: Program () -> Block IRVar O O ()
compile (Pure ()) = Block 0 []
compile (Free (PNode (Node n x))) =
    Block 0 (PNode (Node n ()) : getBlock (compile x))

add :: IRVar -> IRVar -> IRVar -> Program ()
add x0 x1 x2 = Free (PNode (Node (Instr (Add x0 x1 x2)) (Pure ())))
