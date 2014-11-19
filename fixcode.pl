#!/usr/bin/env perl

while (<>) {
    s/import qualified (.*)/import qualified LinearScan.\1 as \1/;
    s/import qualified LinearScan\.GHC/import qualified GHC/;
    s{import qualified LinearScan\.Prelude as Prelude}{
import qualified Prelude
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils
};

    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/module (.+?) where/module LinearScan.\1 where/;
    s/module LinearScan..+?.Utils where/module LinearScan.Utils where/;

    s/o -> Prelude.Either a \(\(,\) errType i\)/i -> Prelude.Either errType ((,) a o)/;
    s/a -> \(,\) i o/i -> (,) a o/;
    s/b -> \[\] \(LinearScan__Block g\)/g -> [] (LinearScan__Block b)/;

    s/data Coq_simpl_fun/newtype Coq_simpl_fun/;
    s/_LinearScan__//g;
    s/LinearScan__//g;
    s/_MLS__MS__//g;
    s/MLS__MS__//g;

    print;
}
