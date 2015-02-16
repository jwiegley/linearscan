module LinearScan.Utils where

import Data.Char
import Data.List as L
import Data.IntMap as M
import Debug.Trace

trace = Debug.Trace.trace . L.map chr

boundedTransport' pos n _top_assumption_ = _top_assumption_

snoc _ xs x = xs ++ [x]

set_nth _ xs n x = take n xs ++ x : drop (n+1) xs

vmap _ = L.map

vfoldl' _ = L.foldl'

vfoldl'_with_index _ f = go 0
  where
    go _ z [] = z
    go n z (x:xs) = go (n+1) (f n z x) xs

nth _ = (!!)

list_rect :: b -> (Int -> a -> [a] -> b -> b) -> Int -> [a] -> b
list_rect z f _ = go z
  where
    go z [] = z
    go z (x:xs) = go (f err x xs z) xs

    err = error "list_rect: attempt to use size"

uncons :: [a] -> Maybe (a, [a])
uncons [] = Nothing
uncons (x:xs) = Just (x, xs)

intMap_mergeWithKey'
    :: (Int -> a -> b -> Maybe c)
    -> ([(Int, a)] -> [(Int, c)])
    -> ([(Int, b)] -> [(Int, c)])
    -> ([(Int, a)]) -> ([(Int, b)])
    -> [(Int, c)]
intMap_mergeWithKey' combine only1 only2 m1 m2 =
    M.toList $ M.mergeWithKey combine
        (M.fromList . only1 . M.toList)
        (M.fromList . only2 . M.toList)
        (M.fromList m1) (M.fromList m2)
