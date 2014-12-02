{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -Werror #-}

module LinearScan
    ( allocate
    , BlockInfo
    , OpInfo(..)
    ) where

import LinearScan.Main
    ( linearScan
    , SSError(..)
    , BlockInfo
    , OpInfo(..)
    )

allocate :: [block] -> OpInfo op -> BlockInfo op block -> Either String [block]
allocate [] _ _ = Left "No basic blocks were provided"
allocate blocks opInfo blockToOpList =
    case linearScan opInfo blockToOpList blocks of
        Left x -> Left $ case x of
            ECurrentIsSingleton ->
                "Current interval is a singleton"
            ENoIntervalsToSplit ->
                "There are no intervals to split"
            EFailedToAllocateRegister ->
                "Failed to allocate register for current interval"
        Right z -> Right z

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

data Map k v
data Graph (n :: * -> * -> *) b c

data AtomicGroup
data Name

data C
data O
data Test
data Success a
data Failure a
data Label
data Instruction a
data CConv
data Constant
data Src a
data Dst a
data Linearity
data Reg

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

data Procedure a v = Procedure
  { procEntry       :: Label,
    procCConv       :: CConv,
    procNamedLabels :: Map Label Name,
    procBody        :: Graph (Node a v) C C
  }

data Spillability = MaySpill | Unspillable

data AtomKind
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
