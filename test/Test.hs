{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -Werror #-}

module Main where

{-

The objective of these tests is to present a real world instruction stream to
the register allocator algorithm, and verify that for certain inputs we get
the expected outputs.  I've extracted several of the types from the Tempest
compiler for which this algorithm was originally developed.  We link from this
module to the Haskell interface code (LinearScan), which calls into the
Haskell code that was extracted from Coq.

-}

import Compiler.Hoopl
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

-- From Compiler.Hoopl:
--
-- postorder_dfs :: NonLocal (block n) => Graph' block n O x -> [block n C C]

lblMapOfCC :: Graph' block n C C -> LabelMap (block n C C)
lblMapOfCC (GMany NothingO lm NothingO) = lm

main :: IO ()
main = hspec $
    describe "first test" $ do
        let entry = runSimpleUniqueMonad freshLabel
        let r0  = mkvar 0
        let r1  = mkvar 1
        let r2  = mkvar 2
        let r3  = mkvar 3
        let r4  = mkvar 4
        let r5  = mkvar 5
        let r6  = mkvar 6
        let r7  = mkvar 7
        let r8  = mkvar 8
        let r9  = mkvar 9
        let r10 = mkvar 10
        let r11 = mkvar 11
        let r12 = mkvar 12
        let r13 = mkvar 13
        let r14 = mkvar 14
        let r15 = mkvar 15
        let r16 = mkvar 16
        let r17 = mkvar 17
        let r18 = mkvar 18
        let r19 = mkvar 19
        let r20 = mkvar 20
        let r21 = mkvar 21
        let r22 = mkvar 22
        let r23 = mkvar 23
        let r24 = mkvar 24
        let r25 = mkvar 25
        let r26 = mkvar 26
        let r27 = mkvar 27
        let r28 = mkvar 28
        let r29 = mkvar 29
        let r30 = mkvar 30
        let r31 = mkvar 31
        let r32 = mkvar 32
        let r33 = mkvar 33
        let r34 = mkvar 34
        let r35 = mkvar 35
        let p body = Procedure
                { procEntry = entry
                , procCConv = InlineC
                , procNamedLabels = singleton entry "entry"
                , procBody =
                    blockGraph
                      (blockJoin
                        (Node (Label entry) ())
                        body
                        (Node (ReturnInstr [] Endt) ()))
                }
        let blocks body = postorder_dfs_from (lblMapOfCC (procBody (p body))) entry
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

        it "Works for a single instruction" $ do
            let body = blockCons (Node (Instr (Add r0 r1 r2)) ()) emptyBlock
            allocate (blocks body) oinfo binfo `shouldBe` Right
                [ mkop oinfo 1 [ (2, LS.Register 0)
                               , (1, LS.Register 1)
                               , (0, LS.Register 2) ] ]

        it "Works for multiple instructions" $ do
            let body =
                    blockCons (Node (Instr (Add r0 r1 r2)) ()) $
                    blockCons (Node (Instr (Add r0 r1 r2)) ()) $
                    blockCons (Node (Instr (Add r0 r1 r2)) ()) emptyBlock
            allocate (blocks body) oinfo binfo `shouldBe` Right
                [ mkop oinfo 1 [ (2, LS.Register 0)
                               , (1, LS.Register 1)
                               , (0, LS.Register 2) ]
                , mkop oinfo 3 [ (2, LS.Register 0)
                               , (1, LS.Register 1)
                               , (0, LS.Register 2) ]
                , mkop oinfo 5 [ (2, LS.Register 0)
                               , (1, LS.Register 1)
                               , (0, LS.Register 2) ] ]

        it "Another case with multiple instructions" $ do
            let body =
                    blockCons (Node (Instr (Add r0 r1 r2)) ()) $
                    blockCons (Node (Instr (Add r0 r1 r3)) ()) $
                    blockCons (Node (Instr (Add r0 r1 r2)) ()) emptyBlock
            allocate (blocks body) oinfo binfo `shouldBe` Right
                [ mkop oinfo 1 [ (2, LS.Register 0)
                               , (1, LS.Register 1)
                               , (0, LS.Register 2) ]
                , mkop oinfo 3 [ (3, LS.Register 3)
                               , (1, LS.Register 1)
                               , (0, LS.Register 2) ]
                , mkop oinfo 5 [ (2, LS.Register 0)
                               , (1, LS.Register 1)
                               , (0, LS.Register 2) ] ]

        it "Trivial case using too many variables" $ do
            let body =
                    blockCons (Node (Instr (Add r0 r1 r2)) ()) $
                    blockCons (Node (Instr (Add r3 r4 r5)) ()) $
                    blockCons (Node (Instr (Add r6 r7 r8)) ()) $
                    blockCons (Node (Instr (Add r9 r10 r11)) ()) $
                    blockCons (Node (Instr (Add r12 r13 r14)) ()) $
                    blockCons (Node (Instr (Add r15 r16 r17)) ()) $
                    blockCons (Node (Instr (Add r18 r19 r20)) ()) $
                    blockCons (Node (Instr (Add r21 r22 r23)) ()) $
                    blockCons (Node (Instr (Add r24 r25 r26)) ()) $
                    blockCons (Node (Instr (Add r27 r28 r29)) ()) $
                    blockCons (Node (Instr (Add r30 r31 r32)) ()) $
                    blockCons (Node (Instr (Add r33 r34 r35)) ()) emptyBlock
            allocate (blocks body) oinfo binfo `shouldBe` Right
                [ mkop oinfo  1 [ ( 2, LS.Register 0)
                                , ( 1, LS.Register 1)
                                , ( 0, LS.Register 2) ]
                , mkop oinfo  3 [ ( 5, LS.Register 0)
                                , ( 4, LS.Register 1)
                                , ( 3, LS.Register 2) ]
                , mkop oinfo  5 [ ( 8, LS.Register 0)
                                , ( 7, LS.Register 1)
                                , ( 6, LS.Register 2) ]
                , mkop oinfo  7 [ (11, LS.Register 0)
                                , (10, LS.Register 1)
                                , ( 9, LS.Register 2) ]
                , mkop oinfo  9 [ (14, LS.Register 0)
                                , (13, LS.Register 1)
                                , (12, LS.Register 2) ]
                , mkop oinfo 11 [ (17, LS.Register 0)
                                , (16, LS.Register 1)
                                , (15, LS.Register 2) ]
                , mkop oinfo 13 [ (20, LS.Register 0)
                                , (19, LS.Register 1)
                                , (18, LS.Register 2) ]
                , mkop oinfo 15 [ (23, LS.Register 0)
                                , (22, LS.Register 1)
                                , (21, LS.Register 2) ]
                , mkop oinfo 17 [ (26, LS.Register 0)
                                , (25, LS.Register 1)
                                , (24, LS.Register 2) ]
                , mkop oinfo 19 [ (29, LS.Register 0)
                                , (28, LS.Register 1)
                                , (27, LS.Register 2) ]
                , mkop oinfo 21 [ (32, LS.Register 0)
                                , (31, LS.Register 1)
                                , (30, LS.Register 2) ]
                , mkop oinfo 23 [ (35, LS.Register 0)
                                , (34, LS.Register 1)
                                , (33, LS.Register 2) ] ]

mkvar :: Int -> IRVar
mkvar i = IRVar { _ivVar = VirtualIV i Atom MaySpill
                , _ivSrc = Nothing
                }

mkop :: OpInfo opType -> Int -> [(LS.VarId, LS.Allocation)] -> OpData opType
mkop oinfo i allocs = OpData
    { baseOp  = error $ "baseOp#" ++ show i
    , opInfo  = oinfo
    , opId    = i
    , opAlloc = allocs
    }
