module LinearScan where

import Control.Monad.ST
import Data.STRef
import Data.Set as Set

import Data.Foldable
import Data.Traversable
import System.IO.Unsafe

-- The linear scan algorithm in this module is documented in the paper
-- "Optimized Interval Splitting in a Linear Scan Register Allocator" by
-- Christian Wimmer and Hanspeter Mӧssenbӧck:
--
-- https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf

data NodeGraph a
data VReg
data PReg

linearScan :: NodeGraph VReg -> NodeGraph PReg
linearScan = runST $ do
    unhandled <- newSTRef intervals
    active    <- newSTRef Set.empty
    inactive  <- newSTRef Set.empty
    handled   <- newSTRef Set.empty
    return undefined
  where
    intervals = undefined

-- unhandled = list of intervals sorted by increasing start positions
-- active = { }; inactive = { }; handled = { }
--
-- while unhandled /= { } do
--   current = pick and remove first interval from unhandled
--   position = start position of current
--
--   // check for intervals in active that are handled or inactive
--   for each interval it in active do
--     if it ends before position then
--       move it from active to handled
--     else if it does not cover position then
--       move it from active to inactive
--
--   // check for intervals in inactive that are handled or active
--   for each interval it in inactive do
--     if it ends before position then
--       move it from inactive to handled
--     else if it covers position then
--       move it from inactive to active
--
--   // find a register for current
--   tryAllocateFreeReg
--   if allocation failed then
--     allocateBlockedReg
--
--   if current has a register assigned then
--     add current to active

tryAllocateFreeReg :: ST s ()
tryAllocateFreeReg = undefined

-- set freeUntilPos of all physical registers to maxInt
--
-- for each interval it in active do
--   freeUntilPos[it.reg] = 0
--
-- for each interval it in inactive intersecting with current do
--   freeUntilPos[it.reg] = next intersection of it with current
--
-- reg = register with highest freeUntilPos
-- if freeUntilPos[reg] = 0 then
--   // no register available without spilling
--   allocation failed
-- else if current ends before freeUntilPos[reg] then
--   // register available for the whole interval
--   current.reg = reg
-- else
--   // register available for the first part of the interval
--   current.reg = reg
--   split current before freeUntilPos[reg]

allocateBlockedReg :: ST s ()
allocateBlockedReg = undefined

-- set nextUsePos of all physical registers to maxInt
--
-- for each interval it in active do
--   nextUsePos[it.reg] = next use of it after start of current
-- for each interval it in inactive intersecting with current do
--   nextUsePos[it.reg] = next use of it after start of current
--
-- reg = register with highest nextUsePos
-- if first usage of current is after nextUsePos[reg] then
--   // all other intervals are used before current, so it is best
--   // to spill current itself

--   assign spill slot to current
--   split current before its first use position that requires a register
-- else
--   // spill intervals that currently block reg
--   current.reg = reg
--   split active interval for reg at position
--   split any inactive interval for reg at the end of its lifetime hole
--
-- // make sure that current does not intersect with
-- // the fixed interval for reg
-- if current intersects with the fixed interval for reg then
--   splse current before this intersection
