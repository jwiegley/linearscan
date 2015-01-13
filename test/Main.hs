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
  let basicAlloc = op $ alloc 0 2 >> alloc 1 1 >> alloc 2 0

  describe "Sanity tests" $ do
    it "Single instruction" $ asmTest
        (add v0 v1 v2)

        (block basicAlloc)

    it "Single, repeated instruction" $ asmTest
        (do add v0 v1 v2
            add v0 v1 v2
            add v0 v1 v2) $

        block $ do
            basicAlloc
            basicAlloc
            basicAlloc

    it "Multiple instructions" $ asmTest
        (do add v0 v1 v2
            add v0 v1 v3
            add v0 v1 v2) $

        block $ do
            basicAlloc
            op $ alloc 0 2 >> alloc 1 1 >> alloc 3 3
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
            add v33 v34 v35) $

        block $ do
            op $ alloc  0 2 >> alloc  1 1 >> alloc  2 0
            op $ alloc  3 2 >> alloc  4 1 >> alloc  5 0
            op $ alloc  6 2 >> alloc  7 1 >> alloc  8 0
            op $ alloc  9 2 >> alloc 10 1 >> alloc 11 0
            op $ alloc 12 2 >> alloc 13 1 >> alloc 14 0
            op $ alloc 15 2 >> alloc 16 1 >> alloc 17 0
            op $ alloc 18 2 >> alloc 19 1 >> alloc 20 0
            op $ alloc 21 2 >> alloc 22 1 >> alloc 23 0
            op $ alloc 24 2 >> alloc 25 1 >> alloc 26 0
            op $ alloc 27 2 >> alloc 28 1 >> alloc 29 0
            op $ alloc 30 2 >> alloc 31 1 >> alloc 32 0
            op $ alloc 33 2 >> alloc 34 1 >> alloc 35 0

    it "Single long-lived variable" $ asmTest
        (do add v0 v1 v2
            add v0 v4 v5
            add v0 v7 v8
            add v0 v10 v11) $

        block $ do
            op $ alloc  0 2 >> alloc  1 1 >> alloc  2 0
            op $ alloc  0 2 >> alloc  4 1 >> alloc  5 0
            op $ alloc  0 2 >> alloc  7 1 >> alloc  8 0
            op $ alloc  0 2 >> alloc 10 1 >> alloc 11 0

    it "Two long-lived variables" $ asmTest
        (do add v0 v1 v2
            add v0 v4 v5
            add v0 v4 v8
            add v0 v4 v11) $

        block $ do
            op $ alloc  0 2 >> alloc  1 1 >> alloc  2 0
            op $ alloc  0 2 >> alloc  4 1 >> alloc  5 0
            op $ alloc  0 2 >> alloc  4 1 >> alloc  8 0
            op $ alloc  0 2 >> alloc  4 1 >> alloc 11 0

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

        block $ do
            op $ alloc  0 2 >> alloc  1 1 >> alloc  2 0
            op $ alloc  3 2 >> alloc  4 1 >> alloc  5 0
            op $ alloc  6 2 >> alloc  7 1 >> alloc  8 0
            op $ alloc  9 2 >> alloc 10 1 >> alloc 11 0
            op $ alloc 12 2 >> alloc 13 1 >> alloc 14 0
            op $ alloc 15 2 >> alloc 16 1 >> alloc 17 0
            op $ alloc 18 2 >> alloc 19 1 >> alloc 20 0
            op $ alloc 21 2 >> alloc 22 1 >> alloc 23 0
            op $ alloc 24 2 >> alloc 25 1 >> alloc 26 0
            op $ alloc 27 2 >> alloc 28 1 >> alloc 29 0
            op $ alloc 30 2 >> alloc 31 1 >> alloc 32 0
            op $ alloc 33 2 >> alloc 34 1 >> alloc 35 0

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

        block $ do
            op $ alloc  0 2 >> alloc  1 1 >> alloc  2 0
            op $ alloc  3 3 >> alloc  4 1 >> alloc  5 0
            op $ alloc  6 3 >> alloc  7 1 >> alloc  8 0
            op $ alloc  9 3 >> alloc 10 1 >> alloc 11 0
            op $ alloc 12 3 >> alloc 13 1 >> alloc 14 0
            op $ alloc 15 3 >> alloc 16 1 >> alloc 17 0
            op $ alloc 18 3 >> alloc 19 1 >> alloc 20 0
            op $ alloc 21 3 >> alloc 22 1 >> alloc 23 0
            op $ alloc 24 3 >> alloc 25 1 >> alloc 26 0
            op $ alloc 27 3 >> alloc 28 1 >> alloc 29 0
            op $ alloc 30 3 >> alloc 31 1 >> alloc 32 0
            op $ alloc  0 2 >> alloc 34 1 >> alloc 35 0

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

        block $ do
            op $ alloc  0  2 >> alloc  1  1 >> alloc  2  0
            op $ alloc  3  5 >> alloc  4  4 >> alloc  5  3
            op $ alloc  6  8 >> alloc  7  7 >> alloc  8  6
            op $ alloc  9 11 >> alloc 10 10 >> alloc 11  9
            op $ alloc 12 14 >> alloc 13 13 >> alloc 14 12
            op $ alloc 15 17 >> alloc 16 16 >> alloc 17 15
            op $ alloc 18 20 >> alloc 19 19 >> alloc 20 18
            op $ alloc 21 23 >> alloc 22 22 >> alloc 23 21
            op $ alloc 24 26 >> alloc 25 25 >> alloc 26 24
            op $ alloc 27 29 >> alloc 28 28 >> alloc 29 27
            op $ alloc  0  2 >> alloc  1  1 >> alloc  2  0
            op $ alloc  3  5 >> alloc  4  4 >> alloc  5  3
            op $ alloc  6  8 >> alloc  7  7 >> alloc  8  6
            op $ alloc  9 11 >> alloc 10 10 >> alloc 11  9
            op $ alloc 12 14 >> alloc 13 13 >> alloc 14 12
            op $ alloc 15 17 >> alloc 16 16 >> alloc 17 15
            op $ alloc 18 20 >> alloc 19 19 >> alloc 20 18
            op $ alloc 21 23 >> alloc 22 22 >> alloc 23 21
            op $ alloc 24 26 >> alloc 25 25 >> alloc 26 24
            op $ alloc 27 29 >> alloc 28 28 >> alloc 29 27

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

        block $ do
            op $ alloc  0  2 >> alloc  1  1 >> alloc  2  0
            op $ alloc  3  5 >> alloc  4  4 >> alloc  5  3
            op $ alloc  6  8 >> alloc  7  7 >> alloc  8  6
            op $ alloc  9 11 >> alloc 10 10 >> alloc 11  9
            op $ alloc 12 14 >> alloc 13 13 >> alloc 14 12
            op $ alloc 15 17 >> alloc 16 16 >> alloc 17 15
            op $ alloc 18 20 >> alloc 19 19 >> alloc 20 18
            op $ alloc 21 23 >> alloc 22 22 >> alloc 23 21
            op $ alloc 24 26 >> alloc 25 25 >> alloc 26 24
            op $ alloc 27 29 >> alloc 28 28 >> alloc 29 27
            op $ alloc 30 27 >> alloc 31 31 >> alloc 32 30
            op $ alloc  0  2 >> alloc  1  1 >> alloc  2  0
            op $ alloc  3  5 >> alloc  4  4 >> alloc  5  3
            op $ alloc  6  8 >> alloc  7  7 >> alloc  8  6
            op $ alloc  9 11 >> alloc 10 10 >> alloc 11  9
            op $ alloc 12 14 >> alloc 13 13 >> alloc 14 12
            op $ alloc 15 17 >> alloc 16 16 >> alloc 17 15
            op $ alloc 18 20 >> alloc 19 19 >> alloc 20 18
            op $ alloc 21 23 >> alloc 22 22 >> alloc 23 21
            op $ alloc 24 26 >> alloc 25 25 >> alloc 26 24
            op $ alloc 27 29 >> alloc 28 28 >> alloc 29 27
            op $ alloc 30 27 >> alloc 31 31 >> alloc 32 30
