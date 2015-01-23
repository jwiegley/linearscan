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
  describe "Sanity tests" $ do
    it "Single instruction" $ asmTest
        (add v0 v1 v2) $

        add l2 l1 l0

    it "Single, repeated instruction" $ asmTest
        (do add v0 v1 v2
            add v0 v1 v2
            add v0 v1 v2) $

        do add l2 l1 l0
           add r2 r1 r0
           add r2 r1 r0

    it "Multiple instructions" $ asmTest
        (do add v0 v1 v2
            add v0 v1 v3
            add v0 v1 v2) $

        do  add l2 l1 l0
            add r2 r1 l3
            add r2 r1 r0

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
            add v33 v34 v35) $

        do  add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0
            add l2 l1 l0

    it "Single long-lived variable" $ asmTest
        (do add v0 v1 v2
            add v0 v4 v5
            add v0 v7 v8
            add v0 v10 v11) $

        do  add l2 l1 l0
            add r2 l1 l0
            add r2 l1 l0
            add r2 l1 l0

    it "Two long-lived variables" $ asmTest
        (do add v0 v1 v2
            add v0 v4 v5
            add v0 v4 v8
            add v0 v4 v11) $

        do  add l2 l1 l0
            add r2 l1 l0
            add r2 r1 l0
            add r2 r1 l0

    it "One variable with a long interval" $ asmTest
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
            add v0  v34 v35) $

        do  add l2 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add l3 l1 l0
            add r2 l1 l0

    it "Many variables with long intervals" $ asmTest
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
            add v27 v28 v29
        ) $

        do  add l2 l1 l0
            add l5 l4 l3
            add l8 l7 l6
            add l11 l10 l9
            add l14 l13 l12
            add l17 l16 l15
            add l20 l19 l18
            add l23 l22 l21
            add l26 l25 l24
            add l29 l28 l27
            add r2 r1 r0
            add r5 r4 r3
            add r8 r7 r6
            add r11 r10 r9
            add r14 r13 r12
            add r17 r16 r15
            add r20 r19 r18
            add r23 r22 r21
            add r26 r25 r24
            add r29 r28 r27

    it "Spilling one variable" $ asmTest
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
            {- 43 -} add v30 v31 v32) $

        do  {-  1 -} add l2 l1 l0
            {-  3 -} add l5 l4 l3
            {-  5 -} add l8 l7 l6
            {-  7 -} add l11 l10 l9
            {-  9 -} add l14 l13 l12
            {- 11 -} add l17 l16 l15
            {- 13 -} add l20 l19 l18
            {- 15 -} add l23 l22 l21
            {- 17 -} add l26 l25 l24
            {- 19 -} add l29 l28 ls27
                     -- When we reach the 32nd variable considered (which
                     -- happens to be v30), we must spill a register because
                     -- there are not 32 registers.  So we pick the first
                     -- register, counting from 0, whose next use position is
                     -- the furthest from this position.  That happens to be
                     -- r27, which is next used at position 41.
            {- 21 -} add l27 l31 l30
            {- 23 -} add r2 r1 r0
            {- 25 -} add r5 r4 r3
            {- 27 -} add r8 r7 r6
            {- 29 -} add r11 r10 r9
            {- 31 -} add r14 r13 r12
            {- 33 -} add r17 r16 r15
            {- 35 -} add r20 r19 r18
            {- 37 -} add r23 r22 r21
            {- 39 -} add r26 r25 r24
                     -- When it comes time to reload v29 (which had been
                     -- allocated to r27), we pick the first available
                     -- register which happens to be r0 in this case.
            {- 41 -} add r29 r28 (restore 0)
            {- 43 -} add r27 r31 r30
