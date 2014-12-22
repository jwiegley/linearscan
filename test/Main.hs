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

    describe "first test" $ do
        it "Works for a single instruction" $ asmTest
            (add r0 r1 r2)

            basicAlloc

        it "Works for multiple instructions" $ asmTest
            (do add r0 r1 r2
                add r0 r1 r2
                add r0 r1 r2) $ do

            basicAlloc
            basicAlloc
            basicAlloc

        it "Another case with multiple instructions" $ asmTest
            (do add r0 r1 r2
                add r0 r1 r3
                add r0 r1 r2) $ do

            basicAlloc
            regs $ do
                alloc 3 3
                alloc 1 1
                alloc 0 2
            basicAlloc

        it "Trivial case using too many variables" $ asmTest
            (do add r0 r1 r2
                add r3 r4 r5
                add r6 r7 r8
                add r9 r10 r11
                add r12 r13 r14
                add r15 r16 r17
                add r18 r19 r20
                add r21 r22 r23
                add r24 r25 r26
                add r27 r28 r29
                add r30 r31 r32
                add r33 r34 r35) $ do

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

        it "Case with one long-lived variable" $ asmTest
            (do add r0 r1 r2
                add r0 r4 r5
                add r0 r7 r8
                add r0 r10 r11) $ do
            basicAlloc
            regs $ do
                alloc  4 0
                alloc  5 1
                alloc  0 2
            regs $ do
                alloc  7 0
                alloc  8 1
                alloc  0 2
            regs $ do
                alloc  10 0
                alloc  11 1
                alloc  0  2
