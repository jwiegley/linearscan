#!/usr/bin/env perl

while (<>) {
    s/import qualified (?<!LinearScan)(.*)/import qualified LinearScan.\1 as \1/;
    s/import qualified LinearScan\.GHC/import qualified GHC/;
    s{import qualified LinearScan\.Prelude as Prelude}{
import Debug.Trace (trace, traceShow, traceShowId)
import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified Hask.Utils
};

    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/module (?<!LinearScan)(.+?) where/module LinearScan.\1 where/;

    s/data Coq_simpl_fun/newtype Coq_simpl_fun/;
    s/_LinearScan__//g; s/LinearScan__//g;
    s/_Allocate__//g; s/Allocate__//g;
    s/_Blocks__//g; s/Blocks__//g;
    s/_MLS__MS__//g; s/MLS__MS__//g;

    print;
}
