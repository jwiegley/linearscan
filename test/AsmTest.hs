{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module AsmTest where

import           Assembly
import           Compiler.Hoopl as Hoopl hiding ((<*>))
import           Control.Exception
import           Control.Monad.Trans.State (evalState)
import           DSL
import           Data.Foldable
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Hoopl
import           LinearScan
import           Test.Hspec

asmTest :: Int -> Program (Node IRVar) -> Program (Node PhysReg) -> Expectation
asmTest regs (compile "entry" -> (prog, entry))
             (compile "entry" -> (result, _)) =
    go $ M.fromList $ zip (Prelude.map entryLabel blocks) [(1 :: Int)..]
  where
    GMany NothingO body NothingO = prog
    blocks = postorder_dfs_from body entry

    alloc blockIds = allocate regs (blockInfo getBlockId) opInfo blocks
      where
        getBlockId :: Hoopl.Label -> Int
        getBlockId lbl = fromMaybe (error "The impossible happened")
                                   (M.lookup lbl blockIds)

    go blockIds = case evalState (alloc blockIds) (newSpillStack 0) of
        Left err -> error $ "Allocation failed: " ++ err
        Right blks -> do
            let graph' = newGraph blks
            catch (showGraph show graph' `shouldBe`
                   showGraph show result) $ \e -> do
                putStrLn $ "---- Expecting ----\n" ++ showGraph show result
                putStrLn $ "---- Compiled  ----\n" ++ showGraph show graph'
                putStrLn "-------------------"
                throwIO (e :: SomeException)
      where
        newBody = Data.Foldable.foldl' (flip addBlock) emptyBody
        newGraph xs = GMany NothingO (newBody xs) NothingO
