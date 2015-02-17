module Main where

import AsmTest
import Assembly
import DSL
import Test.Hspec

-- | The objective of these tests is to present a program to the register
--   allocator algorithm, and verify that for certain inputs we get the
--   expected outputs.

main :: IO ()
main = hspec $ do
  describe "Sanity tests" sanityTests
  describe "Block tests" blockTests

sanityTests :: SpecWith ()
sanityTests = do
  it "Single instruction" $ asmTest 32
    (label "entry" $ do
        add v0 v1 v2
        return_) $

    label "entry" $ do
        add r0 r1 r2
        return_

  it "Single, repeated instruction" $ asmTest 32
    (label "entry" $ do
        add v0 v1 v2
        add v0 v1 v2
        add v0 v1 v2
        return_) $

    label "entry" $ do
        add r0 r1 r2
        add r0 r1 r2
        add r0 r1 r2
        return_

  it "Multiple instructions" $ asmTest 32
    (label "entry" $ do
        add v0 v1 v2
        add v0 v1 v3
        add v0 v1 v2
        return_) $

    label "entry" $ do
        add r0 r1 r2
        add r0 r1 r3
        add r0 r1 r2
        return_

  it "More variables used than registers" $ asmTest 32
    (label "entry" $ do
        add v0 v1 v2
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
        add v33 v34 v35
        return_) $

    label "entry" $ do
        add r0 r1 r24
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
        add r22 r23 r10
        return_

  it "Single long-lived variable" $ asmTest 32
    (label "entry" $ do
        add v0 v1 v2
        add v0 v4 v5
        add v0 v7 v8
        add v0 v10 v11
        return_) $

    label "entry" $ do
        add r0 r1 r5
        add r0 r2 r1
        add r0 r3 r2
        add r0 r4 r3
        return_

  it "Two long-lived variables" $ asmTest 32
    (label "entry" $ do
        add v0 v1 v2
        add v0 v4 v5
        add v0 v4 v8
        add v0 v4 v11
        return_) $

    label "entry" $ do
        add r0 r1 r3
        add r0 r2 r1
        add r0 r2 r4
        add r0 r2 r5
        return_

  it "One variable with a long interval" $ asmTest 32
    (label "entry" $ do
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
        add v30 v31 v32
        add v0  v34 v35
        return_) $

    label "entry" $ do
        add r0 r1 r23
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
        add r0 r22 r11
        return_

  it "Many variables with long intervals" $ asmTest 32
    (label "entry" $ do
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
        return_) $

    label "entry" $ do
        add r0 r1 r20
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
        add r18 r19 r29
        return_

  it "Spilling one variable" $ asmTest 32
    (label "entry" $ do
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
        add v30 v31 v32
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
        add v30 v31 v32
        return_) $

    label "entry" $ do
        add r0 r1 r22
        add r2 r3 r23
        add r4 r5 r24
        add r6 r7 r25
        add r8 r9 r26
        add r10 r11 r27
        add r12 r13 r28
        add r14 r15 r29
        add r16 r17 r30
        add r18 r19 r31

        -- When we reach the 32nd variable considered (which happens to be
        -- v30), we must spill a register because there are not 32 registers.
        -- So we pick the first register, counting from 0, whose next use
        -- position is the furthest from this position.  That happens to be
        -- r18, which is next used at position 41.
        save r18 0
        add r20 r21 r18
        add r0 r1 r22
        add r2 r3 r23
        add r4 r5 r24
        add r6 r7 r25
        add r8 r9 r26
        add r10 r11 r27
        add r12 r13 r28
        add r14 r15 r29
        add r16 r17 r30

        -- When it comes time to reload v29 (which had been allocated to r18),
        -- we pick the first available register which happens to be r0 in this
        -- case.
        restore 0 r0
        add r0 r19 r31
        add r20 r21 r18
        return_

  it "Inserts only necessary saves and restores" $ asmTest 4
    (label "entry" $ do
        add v0 v1 v2
        add v2 v1 v3
        add v3 v2 v4
        add v4 v1 v0
        return_) $

    label "entry" $ do
        add r1 r0 r2
        add r2 r0 r3
        save r0 0
        add r3 r2 r0
        restore 0 r2
        add r0 r2 r1
        return_

blockTests :: SpecWith ()
blockTests = do
  it "Allocates across blocks" $ asmTest 32
    (do label "entry" $ do
            add v0 v1 v2
            jump "L2"

        label "L2" $ do
            add v2 v3 v4
            add v2 v4 v5
            jump "L3"

        label "L3" $ do
            add v2 v5 v6
            add v2 v6 v7
            add v2 v7 v8
            return_) $

    do label "entry" $ do
           add r0 r1 r3
           jump "L2"

       label "L2" $ do
           add r3 r2 r0
           add r3 r0 r1
           jump "L3"

       label "L3" $ do
           add r3 r1 r0
           add r3 r0 r1
           add r3 r1 r0
           return_

  it "Inserts resolving moves" $ asmTest 4
    (do label "entry" $ do
            add v0 v1 v2
            branch Zero v2 "B3" "B2"

        label "B2" $ do
            add v1 v2 v3
            add v0 v0 v4
            add v0 v0 v5
            add v0 v4 v6
            add v0 v5 v6
            jump "B4"

        label "B3" $ do
            add v1 v2 v3
            jump "B4"

        label "B4" $ do
            add v3 v3 v0
            return_) $

    do label "entry" $ do
           add r0 r1 r2
           branch Zero r2 "B2" "B3"

       label "B2" $ do
           add r1 r2 r3
           jump "B4"

       label "B3" $ do
           add r1 r2 r3
           save r3 16
           save r2 8
           save r1 0
           add r0 r0 r1
           add r0 r0 r2
           add r0 r1 r3
           add r0 r2 r3
           restore 16 r3
           jump "B4"

       label "B4" $ do
           add r3 r3 r0
           return_

  it "Inserts resolving moves another way" $ asmTest 4
    (do label "entry" $ do
            add v0 v1 v2
            branch Zero v2 "B3" "B2"

        label "B2" $ do
            add v1 v2 v3
            jump "B4"

        label "B3" $ do
            add v1 v2 v3
            add v0 v0 v4
            add v0 v0 v5
            add v0 v4 v6
            add v0 v5 v6
            jump "B4"

        label "B4" $ do
            add v3 v3 v0
            return_) $

    do label "entry" $ do
           add r0 r1 r2
           branch Zero r2 "B2" "B3"

       label "B2" $ do
           add r1 r2 r3
           save r3 0
           add r0 r0 r1
           add r0 r0 r2
           add r0 r1 r3
           add r0 r2 r3
           restore 0 r1
           jump "B4"

       label "B3" $ do
           add r1 r2 r3
           move r3 r1
           jump "B4"

       label "B4" $ do
           add r1 r1 r0
           return_

  it "Another resolution case" $ asmTest 4
    (do label "entry" $ do
            lc v3
            lc v4
            lc v15
            lc v20
            jump "L3"

        label "L3" $ do
            move v3 v9
            move v9 v11
            move v11 v10
            move v10 v12
            move v12 v13
            lc v14
            move v15 v5
            jump "L6"

        label "L6" $
	    branch Zero v4 "L3" "L2"

        label "L2" $ do
            lc v21
            move v21 v18
            move v5 v4
            lc v19
            move v20 v17
            jump "L6") $

    do label "entry" $ do
           lc r0
           lc r1
           lc r2
           lc r3
           save r3 0
           jump "L3"

       label "L3" $ do
           restore 8 r0
           move r0 r3
           save r0 8
           move r3 r0
           move r0 r3
           move r3 r0
           move r0 r3
           lc r0
           save r0 16
           move r2 r0
           save r2 24
           jump "L6"

       label "L6" $
           branch Zero r1 "L3" "L2"

       label "L2" $ do
           lc r3
           move r3 r2
           move r0 r1
           save r1 40
           save r0 32
           lc r3
           restore 0 r1
           move r1 r0
           restore 40 r1
           restore 32 r0
           restore 24 r2
           save r1 0
           jump "L6"
