#!/usr/bin/env perl

while (<>) {
    s/import qualified (.*)/import qualified LinearScan.\1 as \1/;
    s/import qualified LinearScan\.GHC/import qualified GHC/;
    s{import qualified LinearScan\.Prelude as Prelude}{
import Debug.Trace (trace, traceShow)
import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified Hask.Utils
};

    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/module (.+?) where/module LinearScan.\1 where/;

    # Sometimes when generating type synonyms, the extraction mechanism will
    # inexplicably flip type arguments. We undo these bugs here.
    s/o -> Prelude.Either a \(\(,\) errType i\)/i -> Prelude.Either errType ((,) a o)/;
    s/a -> \(,\) i o/i -> (,) a o/;
    s/b -> \[\] \(LinearScan__Block g\)/g -> [] (LinearScan__Block b)/;
    s/opType -> \[\] blockType/blockType -> [] opType/;

    s/data Coq_simpl_fun/newtype Coq_simpl_fun/;
    s/_LinearScan__//g; s/LinearScan__//g;
    s/_Allocate__//g; s/Allocate__//g;
    s/_Blocks__//g; s/Blocks__//g;
    s/_MLS__MS__//g; s/MLS__MS__//g;

    s/morphlen_transport maxReg b b' =/morphlen_transport maxReg b b' = GHC.Base.id/;

    s/\(,\) \(\(Prelude\.succ\) \(\(Prelude\.succ\) \(unsafeCoerce n\)\)\)/(,) ((Prelude.succ) ((Prelude.succ) (unsafeCoerce n :: Prelude.Int)))/;

    s/_MyMachine__maxReg = 4/_MyMachine__maxReg = MAX_REG/;
    s/_MyMachine__regSize = 32/_MyMachine__regSize = REG_SIZE/;

    s/\(Prelude\.map  \( rs\)\)/rs/;
    s/\(Data\.IntMap\.map  ranges\)/ranges/;

    print;
}
