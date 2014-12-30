{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -Werror #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Tempest where

import Compiler.Hoopl
import Control.Monad
import Control.Monad.Free
import Data.Foldable
import Data.Map
import LinearScan
import qualified LinearScan.Main as LS
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

data AtomicGroup = AtomicGroup deriving Show
type Name = String

newtype Linearity = Linearity { isLinear :: Bool }
  deriving (Eq, Show)

data Test = Test deriving Show

data CConv
  = CConvC {
      ccArgs     :: [Reg],
      ccResults  :: [Reg],
      ccIsBrack  :: Bool
    }
  | InlineC
  deriving Show

data Constant = Constant deriving Show

type Src a      = a

-- | Type synonym for indicating destination operands
type Dst a      = a

-- | Type synonym for indicating success or true branch
type Success a  = a

-- | Type synonym for indicating failure or false branch
type Failure a  = a

-- | Type synonym for indicating an external name
type Imported a = a

data Reg = Reg deriving Show

data Instruction reg
  = Add          reg reg reg
  | Endt
  deriving (Show, Foldable)

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

showInstr :: (Show v) => Instruction v -> String
showInstr i = show i ++ foldMap (\r -> " " ++ show r) i

instance Show v => Show (IRInstr v e x) where
  show (Label l)        = show l ++ ":"
  show (Alloc g x1 x2)  = "\t@alloc " ++ show g ++
                          (case x1 of Just v -> " " ++ show v ; _ -> " _")
                          ++ " " ++ show x2
  show (Reclaim v)      = "\t@reclaim " ++ show v
  show (Instr i)        = "\t" ++ showInstr i
  show (Call c i)       = "\t@call " ++ show c ++ " " ++ showInstr i
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
  show (ReturnInstr liveRegs i)   = "\t@return " ++ show liveRegs ++ " " ++ showInstr i

data Node a v e x = Node
  { _nodeIRInstr :: IRInstr v e x
  , _nodeMeta    :: a
  } deriving Show

data PNode v e x a = PNode (Node a v e x)

instance Functor (PNode v e x) where
    fmap f (PNode (Node x y)) = PNode (Node x (f y))

nodeToOpList :: (Show a, Show v) => Node a v e x -> [Instruction v]
nodeToOpList (Node (Instr i) _) = [i]
nodeToOpList n = error $ "nodeToOpList: NYI for " ++ show n

instance Show (LS.OpData (Node () IRVar O O)) where
    show (LS.Build_OpData a _b c d) =
        "LS.OpData " ++ show a ++ " " ++ show c ++ " " ++ show d

instance NonLocal (Node a v) where
  entryLabel (Node (Label l)         _) = l
  successors (Node (Jump l)          _) = [l]
  successors (Node (Branch _ _ t f)  _) = [t, f]
  successors (Node (Stwb _ _ _ s f)  _) = [s, f]
  successors (Node (Strb _ _ s f)    _) = [s, f]
  successors (Node (ReturnInstr _ _) _) = []

data Procedure a v = Procedure
  { procEntry       :: Label,
    procCConv       :: CConv,
    procNamedLabels :: Map Label Name,
    procBody        :: Graph (Node a v) C C
  }

data Spillability = MaySpill | Unspillable deriving Show

data AtomKind = Atom deriving Show
data Var = Var deriving Show

data IRVar' = PhysicalIV !Reg
            | VirtualIV !Int !AtomKind !Spillability
            deriving Show

-- | Virtual IR variable together with an optional AST variable
data IRVar =
  IRVar
  { _ivVar :: !IRVar' -- ^ The virtual or physical register
  , _ivSrc :: !(Maybe Var) -- ^ An optional corresponding AST variable for
                       -- informational purposes.
  }
  deriving Show

type Input a  = Procedure a IRVar
type Output a = Procedure a Reg

instrVarRefs :: Show a => Node a IRVar e x -> [VarInfo]
instrVarRefs (Node (Instr (Add a b c)) _) = varsIn a ++ varsIn b ++ varsIn c
  where
    varsIn (IRVar (VirtualIV n _ _) _) = [VarInfo n Input False]
    varsIn _ = []
instrVarRefs i = error $ "instrVarRefs: NYI for " ++ show i

lblMapOfCC :: Graph' block n C C -> LabelMap (block n C C)
lblMapOfCC (GMany NothingO lm NothingO) = lm

asmTest body result = do
    let entry = runSimpleUniqueMonad freshLabel
    let p b = Procedure
            { procEntry = entry
            , procCConv = InlineC
            , procNamedLabels = singleton entry "entry"
            , procBody =
                blockGraph
                  (blockJoin
                    (Node (Label entry) ())
                    b
                    (Node (ReturnInstr [] Endt) ()))
            }
    let blocks b =
            postorder_dfs_from (lblMapOfCC (procBody (p b))) entry
        oinfo = OpInfo
            { isLoopBegin = const False
            , isLoopEnd   = const False
            , isCall      = const Nothing
            , hasRefs     = const False
            , varRefs     = instrVarRefs
            , regRefs     = const []
            }
        binfo = BlockInfo
            { blockToOpList = \block ->
               let (beg, m, end) = blockSplit block in
               blockToList m
            }

    let body'   = blocks $ compile body
    let result' = render oinfo result
    case allocate body' oinfo binfo of
        Left e   -> error $ "Allocation failed: " ++ e
        Right xs -> do
            length xs `shouldBe` length result'

            let test x y = x `shouldBe` y
            zipWithM_ shouldBe xs result'

var :: Int -> IRVar
var i = IRVar { _ivVar = VirtualIV i Atom MaySpill
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


type Program a = Free (PNode IRVar O O) a

compile :: Program () -> Block (Node () IRVar) O O
compile (Pure ()) = emptyBlock
compile (Free (PNode (Node n x))) = blockCons (Node n ()) (compile x)

add :: IRVar -> IRVar -> IRVar -> Program ()
add x0 x1 x2 = Free (PNode (Node (Instr (Add x0 x1 x2)) (Pure ())))


data VarAlloc = VarAlloc
    { raVarNum   :: Int
    , raVarAlloc :: LS.Allocation
    }
    deriving (Eq, Show)

data OpAlloc a = OpAlloc
    { opAllocs :: [VarAlloc]
    , opVar    :: a
    }
    deriving (Eq, Show, Functor)

render :: OpInfo opType -> Allocs () -> [OpData opType]
render oinfo = go 1
  where
    go _ (Pure ()) = []
    go n (Free (Operation (OpAlloc as xs))) =
        mkop oinfo n (Prelude.map (\(VarAlloc v a) -> (v, a)) as)
            : go (n+2) xs

mkop :: OpInfo opType -> Int -> [(LS.VarId, LS.Allocation)] -> OpData opType
mkop oinfo i xs = OpData
    { baseOp  = error $ "baseOp#" ++ show i
    , opInfo  = oinfo
    , opId    = i
    , opAlloc = xs
    }

type Alloc a = Free OpAlloc a

data Operation a = Operation (OpAlloc a) deriving Functor

type Allocs a = Free Operation a

alloc :: Int -> Int -> Alloc ()
alloc v n = Free (OpAlloc [VarAlloc v (LS.Register n)] (Pure ()))

allocs :: [(Int, Int)] -> Alloc ()
allocs []         = return ()
allocs ((v,n):xs) = alloc v n >> allocs xs

regs :: Alloc () -> Allocs ()
regs a = Free (Operation (OpAlloc (reduce a) (Pure ())))
  where
    reduce (Pure ()) = []
    reduce (Free (OpAlloc as xs)) = as ++ reduce xs
