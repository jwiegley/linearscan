{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

{-
The objective of these tests is to present a real world instruction stream to
the register allocator algorithm, and verify that for certain inputs we get
the expected outputs.  I've extracted several of the types from the Tempest
compiler for which this algorithm was originally developed.  We link from this
module to the Haskell interface code (LinearScan), which calls into the
Haskell code that was extracted from Coq.
-}

import Tempest
import Test.Hspec

main :: IO ()
main = hspec $ do
    let basicAlloc = regs $ do
            alloc 2 0
            alloc 1 1
            alloc 0 2

    describe "Sanity tests" $ do
        it "Single instruction" $ asmTest
            (add v0 v1 v2)

            basicAlloc

        it "Single, repeated instruction" $ asmTest
            (do add v0 v1 v2
                add v0 v1 v2
                add v0 v1 v2) $ do

            basicAlloc
            basicAlloc
            basicAlloc

        it "Multiple instructions" $ asmTest
            (do add v0 v1 v2
                add v0 v1 v3
                add v0 v1 v2) $ do

            basicAlloc
            regs $ do
                alloc 3 3
                alloc 1 1
                alloc 0 2
            basicAlloc

        it "More variables used than registers" $ asmTest
            (do add v0 v1 v2
                add v3 v4 v5
                add v6 v7 v8
                add v9 v10 v11
                add v12 v13 v14
                add v15 v16 v17
                add v18 v19 v20
                add v21 v22 v23
                add v24 v25 v26
                add v27 v28 v29
                add v30 v31 v32
                add v33 v34 v35) $ do

            basicAlloc
            regs $ do
                alloc  5 0
                alloc  4 1
                alloc  3 2
            regs $ do
                alloc  8 0
                alloc  7 1
                alloc  6 2
            regs $ do
                alloc 11 0
                alloc 10 1
                alloc  9 2
            regs $ do
                alloc 14 0
                alloc 13 1
                alloc 12 2
            regs $ do
                alloc 17 0
                alloc 16 1
                alloc 15 2
            regs $ do
                alloc 20 0
                alloc 19 1
                alloc 18 2
            regs $ do
                alloc 23 0
                alloc 22 1
                alloc 21 2
            regs $ do
                alloc 26 0
                alloc 25 1
                alloc 24 2
            regs $ do
                alloc 29 0
                alloc 28 1
                alloc 27 2
            regs $ do
                alloc 32 0
                alloc 31 1
                alloc 30 2
            regs $ do
                alloc 35 0
                alloc 34 1
                alloc 33 2

        it "Single long-lived variable" $ asmTest
            (do add v0 v1 v2
                add v0 v4 v5
                add v0 v7 v8
                add v0 v10 v11) $ do

            basicAlloc
            regs $ do
                alloc  5 0
                alloc  4 1
                alloc  0 2
            regs $ do
                alloc  8 0
                alloc  7 1
                alloc  0 2
            regs $ do
                alloc  11 0
                alloc  10 1
                alloc  0  2
