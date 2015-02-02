{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.ScanState where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Interval as Interval
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Ssrnat as Ssrnat



--unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base as GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified LinearScan.IOExts as IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

type PhysReg = Prelude.Int

type FixedIntervalsType = [] (Prelude.Maybe Interval.IntervalDesc)

data ScanStateDesc =
   Build_ScanStateDesc Prelude.Int ([] Interval.IntervalDesc) FixedIntervalsType 
 ([] ((,) Prelude.Int Prelude.Int)) ([] ((,) Prelude.Int PhysReg)) ([]
                                                                   ((,)
                                                                   Prelude.Int
                                                                   PhysReg)) 
 ([] ((,) Prelude.Int PhysReg))

nextInterval :: Prelude.Int -> ScanStateDesc -> Prelude.Int
nextInterval maxReg s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0 unhandled0
    active0 inactive0 handled0 -> nextInterval0}

type IntervalId = Prelude.Int

intervals :: Prelude.Int -> ScanStateDesc -> [] Interval.IntervalDesc
intervals maxReg s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0 unhandled0
    active0 inactive0 handled0 -> intervals0}

fixedIntervals :: Prelude.Int -> ScanStateDesc -> FixedIntervalsType
fixedIntervals maxReg s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0 unhandled0
    active0 inactive0 handled0 -> fixedIntervals0}

unhandled :: Prelude.Int -> ScanStateDesc -> [] ((,) IntervalId Prelude.Int)
unhandled maxReg s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0 unhandled0
    active0 inactive0 handled0 -> unhandled0}

active :: Prelude.Int -> ScanStateDesc -> [] ((,) IntervalId PhysReg)
active maxReg s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0 unhandled0
    active0 inactive0 handled0 -> active0}

inactive :: Prelude.Int -> ScanStateDesc -> [] ((,) IntervalId PhysReg)
inactive maxReg s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0 unhandled0
    active0 inactive0 handled0 -> inactive0}

handled :: Prelude.Int -> ScanStateDesc -> [] ((,) IntervalId PhysReg)
handled maxReg s =
  case s of {
   Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0 unhandled0
    active0 inactive0 handled0 -> handled0}

registerWithHighestPos :: Prelude.Int -> ([] (Prelude.Maybe Prelude.Int)) ->
                          (,) Prelude.Int (Prelude.Maybe Prelude.Int)
registerWithHighestPos maxReg =
  (LinearScan.Utils.vfoldl'_with_index) maxReg (\reg res x ->
    case res of {
     (,) r o ->
      case o of {
       Prelude.Just n ->
        case x of {
         Prelude.Just m ->
          case (Prelude.<=) ((Prelude.succ) n) m of {
           Prelude.True -> (,) reg (Prelude.Just m);
           Prelude.False -> (,) r (Prelude.Just n)};
         Prelude.Nothing -> (,) reg Prelude.Nothing};
       Prelude.Nothing -> (,) r Prelude.Nothing}}) ((,) ( 0) (Prelude.Just
    0))

isWithin :: Interval.IntervalDesc -> Prelude.Int -> Prelude.Int ->
            Prelude.Bool
isWithin int vid opid =
  (Prelude.&&)
    (Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce (Interval.ivar int))
      (unsafeCoerce vid))
    ((Prelude.&&) ((Prelude.<=) (Interval.ibeg int) opid)
      ((Prelude.<=) ((Prelude.succ) opid) (Interval.iend int)))

lookupInterval :: Prelude.Int -> ScanStateDesc -> a1 -> Prelude.Int ->
                  Prelude.Int -> Prelude.Maybe IntervalId
lookupInterval maxReg sd st vid opid =
  let {
   f = \idx acc int ->
    case acc of {
     Prelude.Just x -> Prelude.Just x;
     Prelude.Nothing ->
      case isWithin ( int) vid opid of {
       Prelude.True -> Prelude.Just idx;
       Prelude.False -> Prelude.Nothing}}}
  in
  (LinearScan.Utils.vfoldl'_with_index) (nextInterval maxReg sd) f
    Prelude.Nothing (intervals maxReg sd)

lookupRegister :: Prelude.Int -> ScanStateDesc -> a1 ->
                  Eqtype.Equality__Coq_sort -> Prelude.Maybe PhysReg
lookupRegister maxReg sd st intid =
  Lib.forFold Prelude.Nothing
    ((Prelude.++) (unsafeCoerce (handled maxReg sd))
      ((Prelude.++) (unsafeCoerce (active maxReg sd))
        (unsafeCoerce (inactive maxReg sd)))) (\acc x ->
    case x of {
     (,) xid reg ->
      case acc of {
       Prelude.Just r -> Prelude.Just r;
       Prelude.Nothing ->
        case Eqtype.eq_op (Fintype.ordinal_eqType (nextInterval maxReg sd))
               xid intid of {
         Prelude.True -> Prelude.Just reg;
         Prelude.False -> Prelude.Nothing}}})

data ScanStateStatus =
   Pending
 | InUse

type ScanStateSig = ScanStateDesc

packScanState :: Prelude.Int -> ScanStateStatus -> ScanStateDesc ->
                 ScanStateDesc
packScanState maxReg b sd =
  sd

