module DSL where

import           Compiler.Hoopl as Hoopl hiding ((<*>))
import           Control.Applicative
import           Control.Monad.Free
import           Control.Monad.Trans.Class
import qualified Control.Monad.Trans.Free as TF
import           Control.Monad.Trans.Free hiding (FreeF(..), Free)
import           Control.Monad.Trans.State (StateT, evalStateT, gets, modify)
import qualified Data.Map as M
import           Data.Monoid

type Labels = M.Map String Label

-- | The 'Asm' monad lets us create labels by name and refer to them later.
type Asm = StateT Labels SimpleUniqueMonad

getLabel :: String -> Asm Label
getLabel str = do
    l <- gets (M.lookup str)
    case l of
        Just lbl -> return lbl
        Nothing -> do
            lbl <- lift freshLabel
            modify (M.insert str lbl)
            return lbl

-- | A series of 'Nodes' is a set of assembly instructions that ends with some
--   kind of closing operation, such as a jump, branch or return.
type Nodes n a = Free ((,) (n O O)) a

-- | The 'Nodes' free monad is really just a convenient way to describe a list
--   that must result in a closing operation at the end.
nodesToList :: Nodes n a -> (a, [n O O])
nodesToList (Pure a) = (a, [])
nodesToList (Free (n, xs)) = (n :) <$> nodesToList xs

type BodyNode n = Nodes n ()

bodyNode :: n O O -> BodyNode n
bodyNode n = Free (n, Pure ())

type EndNode n = Nodes n (Asm (n O C))

endNode :: Asm (n O C) -> EndNode n
endNode = return

-- | A program is a series of 'Nodes', each associated with a label.
data ProgramF n = FreeBlock
    { labelEntry :: Label
    , labelBody  :: EndNode n
    }
type Program n = FreeT ((,) (ProgramF n)) Asm ()

label :: String -> EndNode n -> Program n
label str body = do
    lbl <- lift $ getLabel str
    liftF (FreeBlock lbl body, ())

jump :: HooplNode n => String -> EndNode n
jump dest = endNode $ mkBranchNode <$> getLabel dest

-- | When we compile a program, the result is a closed Hoopl Graph and the
--   label corresponding to the requested entry label name.
compile :: (NonLocal n, HooplNode n)
        => String -> Program n -> (Graph n C C, Label)
compile name prog
    = runSimpleUniqueMonad
    $ flip evalStateT (mempty :: Labels)
    $ do body  <- go prog
         entry <- gets (M.lookup name)
         case entry of
             Nothing  -> error $ "Missing label: " ++ name
             Just lbl -> return (bodyGraph body, lbl)
  where
    go m = do
        p <- runFreeT m
        case p of
            TF.Pure () -> return emptyBody
            TF.Free (blk, xs) -> addBlock <$> comp blk <*> go xs

    comp (FreeBlock lbl body) = do
        let (close, blocks) = nodesToList body
        BlockCC (mkLabelNode lbl) (blockFromList blocks) <$> close
