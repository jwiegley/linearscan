{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -Werror #-}

module Main where

import Compiler.Hoopl
import Data.Foldable
import Data.Map
import LinearScan
import Test.Hspec

------------------------------------------------------------------------------
-- The input from the Tempest compiler has the following shape: Procedure a
-- IRVar, which means that instructions will ultimately refer to either
-- physical registers, or virtual variables.
--
-- The output should be as close to the input as possible, with the difference
-- that it has type Procedure a Reg, meaning that only physical registers are
-- referenced.
--
-- The main allocation algorithm roughly has this type at present:
--
--     regAlloc :: Procedure a IRVar -> Procedure a Reg
------------------------------------------------------------------------------

-- data Map k v
-- data Graph (n :: * -> * -> *) b c

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
  show (Alloc g v1 v2)  = "\t@alloc " ++ show g ++
                          (case v1 of Just v -> " " ++ show v ; _ -> " _")
                          ++ " " ++ show v2
  show (Reclaim v)      = "\t@reclaim " ++ show v
  show (Instr i)        = "\t" ++ showInstr i
  show (Call c i)       = "\t@call " ++ show c ++ " " ++ showInstr i
  show (LoadConst c v)  = "\t@lc " ++ show v ++ " " ++ show c
  show (Move v1 v2)     = "\t@mvrr " ++ show v1 ++ " " ++ show v2
  show (Copy v1 v2)     = "\t@cprr " ++ show v1 ++ " " ++ show v2
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
  show (Stwb lin v1 v2 t f)
                        = (if isLinear lin then "\t@stwlb " else "\t@stwb ")
                            ++ show v1 ++ " " ++ show v2
                            ++ " " ++ show f ++ "; @jmp " ++ show t
  show (Strb v1 v2 t f) = "\t@strb " ++ show v1 ++ " " ++ show v2
                            ++ " " ++ show f ++ "; @jmp " ++ show t
  show (ReturnInstr liveRegs i)   = "\t@return " ++ show liveRegs ++ " " ++ showInstr i

data Node a v e x = Node
  { _nodeIRInstr :: IRInstr v e x
  , _nodeMeta    :: a
  } deriving Show

nodeToOpList :: (Show a, Show v) => Node a v e x -> [Instruction v]
nodeToOpList (Node (Instr i) _) = [i]
nodeToOpList n = error $ "nodeToOpList: NYI for " ++ show n

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

-- From Compiler.Hoopl:
--
-- postorder_dfs :: NonLocal (block n) => Graph' block n O x -> [block n C C]

lblMapOfCC :: Graph' block n C C -> LabelMap (block n C C)
lblMapOfCC (GMany NothingO lm NothingO) = lm

main :: IO ()
main = hspec $
    describe "first test" $ do
        let entry = runSimpleUniqueMonad freshLabel
        let a = IRVar { _ivVar = VirtualIV 0 Atom MaySpill
                      , _ivSrc = Nothing
                      }
        let b = IRVar { _ivVar = VirtualIV 1 Atom MaySpill
                      , _ivSrc = Nothing
                      }
        let c = IRVar { _ivVar = VirtualIV 2 Atom MaySpill
                      , _ivSrc = Nothing
                      }
        let p = Procedure
                { procEntry = entry
                , procCConv = InlineC
                , procNamedLabels = singleton entry "entry"
                , procBody =
                    blockGraph
                      (blockJoin
                        (Node (Label entry) ())
                        (blockCons (Node (Instr (Add a b c)) ()) emptyBlock)
                        (Node (ReturnInstr [] Endt) ()))
                }
        let blocks = postorder_dfs_from (lblMapOfCC (procBody p)) entry
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
        it "Passes a basic check" $
            allocate blocks oinfo binfo `shouldBe` Right
                [ OpData
                      { baseOp  = error "baseOp#1"
                      , opInfo  = oinfo
                      , opId    = 1
                      , opAlloc = []
                      }
                ]
