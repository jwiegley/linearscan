module LinearScan.Utils where

import Data.List

boundedTransport' maxVirtReg pos n _top_assumption_ = _top_assumption_

snoc _ xs x = xs ++ [x]

set_nth _ xs n x = take n xs ++ x : drop n xs

vfoldl' _ = Data.List.foldl'

vmap _ = Data.List.map

foldl'_with_index _ f = go 0
  where
    go _ z [] = z
    go n z (x:xs) = go (n+1) (f n z x) xs

nth _ xs i = xs !! i

list_rect :: b -> (Int -> a -> [a] -> b -> b) -> Int -> [a] -> b
list_rect z f _ = go z
  where
    go z [] = z
    go z (x:xs) = go (f err x xs z) xs

    err = error "list_rect: attempt to use size"
