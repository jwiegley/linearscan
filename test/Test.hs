{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -Werror #-}

module Main where

import Compiler.Hoopl
import Data.Map
-- import LinearScan
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

data AtomicGroup
type Name = String

data Test

data CConv
  = CConvC {
      ccArgs     :: [Reg],
      ccResults  :: [Reg],
      ccIsBrack  :: Bool
    }
  | InlineC

data Constant

type Src a      = a

-- | Type synonym for indicating destination operands
type Dst a      = a

-- | Type synonym for indicating success or true branch
type Success a  = a

-- | Type synonym for indicating failure or false branch
type Failure a  = a

-- | Type synonym for indicating an external name
type Imported a = a

data Linearity
data Reg

data Instruction reg
  = Add          reg reg reg
  | Endt

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

data Node a v e x = Node
  { _nodeIRInstr :: IRInstr v e x
  , _nodeMeta    :: a
  }

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

data Spillability = MaySpill | Unspillable

data AtomKind = Atom
data Var

data IRVar' = PhysicalIV !Reg
            | VirtualIV !Int !AtomKind !Spillability

-- | Virtual IR variable together with an optional AST variable
data IRVar =
  IRVar
  { _ivVar :: !IRVar' -- ^ The virtual or physical register
  , _ivSrc :: !(Maybe Var) -- ^ An optional corresponding AST variable for
                       -- informational purposes.
  }

type Input a  = Procedure a IRVar
type Output a = Procedure a Reg

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
            oinfo = undefined
            binfo = undefined
        it "Passes a basic check" $
            True `shouldBe` True
            -- allocate blocks oinfo binfo `shouldBe` Right []
