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
import Test.Tasty
import Test.Tasty.Hspec

main :: IO ()
main = makeTests >>= defaultMain

makeTests :: IO TestTree
makeTests = testSpec "Main tests" $
  describe "Sanity tests" sanityTests

sanityTests :: SpecWith ()
sanityTests = do
  it "Single instruction" $ asmTest
    (label "entry"
        (add v0 v1 v2)
        return_) $

    label "entry"
        (add r0 r1 r2)
        return_

  it "Single, repeated instruction" $ asmTest
    (label "entry"
        (do add v0 v1 v2
            add v0 v1 v2
            add v0 v1 v2)
        return_) $

    label "entry"
        (do add r0 r1 r2
            add r0 r1 r2
            add r0 r1 r2)
        return_

  it "Multiple instructions" $ asmTest
    (label "entry"
        (do add v0 v1 v2
            add v0 v1 v3
            add v0 v1 v2)
        return_) $

    label "entry"
        (do add r0 r1 r2
            add r0 r1 r3
            add r0 r1 r2)
        return_

  it "More variables used than registers" $ asmTest
    (label "entry"
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
            add v33 v34 v35)
        return_) $

    label "entry"
        (do add r0 r1 r24
            add r2 r3 r0
            add r4 r5 r1
            add r6 r7 r2
            add r8 r9 r3
            add r10 r11 r4
            add r12 r13 r5
            add r14 r15 r6
            add r16 r17 r7
            add r18 r19 r8
            add r20 r21 r9
            add r22 r23 r10)
        return_

  it "Single long-lived variable" $ asmTest
    (label "entry"
        (do add v0 v1 v2
            add v0 v4 v5
            add v0 v7 v8
            add v0 v10 v11)
        return_) $

    label "entry"
        (do add r0 r1 r5
            add r0 r2 r1
            add r0 r3 r2
            add r0 r4 r3)
        return_

  it "Two long-lived variables" $ asmTest
    (label "entry"
        (do add v0 v1 v2
            add v0 v4 v5
            add v0 v4 v8
            add v0 v4 v11)
        return_) $

    label "entry"
        (do add r0 r1 r3
            add r0 r2 r1
            add r0 r2 r4
            add r0 r2 r5)
        return_

  it "One variable with a long interval" $ asmTest
    (label "entry"
        (do add v0   v1  v2
            add v3   v4  v5
            add v6   v7  v8
            add v9  v10 v11
            add v12 v13 v14
            add v15 v16 v17
            add v18 v19 v20
            add v21 v22 v23
            add v24 v25 v26
            add v27 v28 v29
            add v30 v31 v32
            add v0  v34 v35)
        return_) $

    label "entry"
        (do add r0 r1 r23
            add r2 r3 r1
            add r4 r5 r2
            add r6 r7 r3
            add r8 r9 r4
            add r10 r11 r5
            add r12 r13 r6
            add r14 r15 r7
            add r16 r17 r8
            add r18 r19 r9
            add r20 r21 r10
            add r0 r22 r11)
        return_

  it "Many variables with long intervals" $ asmTest
    (label "entry"
        (do add v0   v1  v2
            add v3   v4  v5
            add v6   v7  v8
            add v9  v10 v11
            add v12 v13 v14
            add v15 v16 v17
            add v18 v19 v20
            add v21 v22 v23
            add v24 v25 v26
            add v27 v28 v29
            add v0   v1  v2
            add v3   v4  v5
            add v6   v7  v8
            add v9  v10 v11
            add v12 v13 v14
            add v15 v16 v17
            add v18 v19 v20
            add v21 v22 v23
            add v24 v25 v26
            add v27 v28 v29)
        return_) $

    label "entry"
        (do add r0 r1 r20
            add r2 r3 r21
            add r4 r5 r22
            add r6 r7 r23
            add r8 r9 r24
            add r10 r11 r25
            add r12 r13 r26
            add r14 r15 r27
            add r16 r17 r28
            add r18 r19 r29
            add r0 r1 r20
            add r2 r3 r21
            add r4 r5 r22
            add r6 r7 r23
            add r8 r9 r24
            add r10 r11 r25
            add r12 r13 r26
            add r14 r15 r27
            add r16 r17 r28
            add r18 r19 r29)
        return_

  it "Spilling one variable" $ asmTest
    (label "entry"
        (do {-  1 -} add v0   v1  v2
            {-  3 -} add v3   v4  v5
            {-  5 -} add v6   v7  v8
            {-  7 -} add v9  v10 v11
            {-  9 -} add v12 v13 v14
            {- 11 -} add v15 v16 v17
            {- 13 -} add v18 v19 v20
            {- 15 -} add v21 v22 v23
            {- 17 -} add v24 v25 v26
            {- 19 -} add v27 v28 v29
            {- 21 -} add v30 v31 v32
            {- 23 -} add v0   v1  v2
            {- 25 -} add v3   v4  v5
            {- 27 -} add v6   v7  v8
            {- 29 -} add v9  v10 v11
            {- 31 -} add v12 v13 v14
            {- 33 -} add v15 v16 v17
            {- 35 -} add v18 v19 v20
            {- 37 -} add v21 v22 v23
            {- 39 -} add v24 v25 v26
            {- 41 -} add v27 v28 v29
            {- 43 -} add v30 v31 v32)
        return_) $

    label "entry"
        (do {-  1 -} add r2 r1 r0
            {-  3 -} add r5 r4 r3
            {-  5 -} add r8 r7 r6
            {-  7 -} add r11 r10 r9
            {-  9 -} add r14 r13 r12
            {- 11 -} add r17 r16 r15
            {- 13 -} add r20 r19 r18
            {- 15 -} add r23 r22 r21
            {- 17 -} add r26 r25 r24
            {- 19 -} add r29 r28 r27

            -- When we reach the 32nd variable considered (which happens
            -- to be v30), we must spill a register because there are not 32
            -- registers.  So we pick the first register, counting from 0,
            -- whose next use position is the furthest from this position.
            -- That happens to be r27, which is next used at position 41.
                     save 27 0
            {- 21 -} add r27 r31 r30

            {- 23 -} add r2 r1 r0
            {- 25 -} add r5 r4 r3
            {- 27 -} add r8 r7 r6
            {- 29 -} add r11 r10 r9
            {- 31 -} add r14 r13 r12
            {- 33 -} add r17 r16 r15
            {- 35 -} add r20 r19 r18
            {- 37 -} add r23 r22 r21
            {- 39 -} add r26 r25 r24

            -- When it comes time to reload v29 (which had been allocated
            -- to r27), we pick the first available register which happens
            -- to be r0 in this case.
                     restore 0 0
            {- 41 -} add r29 r28 r0

            {- 43 -} add r27 r31 r30)
        return_
