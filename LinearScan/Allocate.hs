{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Allocate where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Cursor as Cursor
import qualified LinearScan.IState as IState
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Lib as Lib
import qualified LinearScan.Morph as Morph
import qualified LinearScan.Range as Range
import qualified LinearScan.ScanState as ScanState
import qualified LinearScan.Specif as Specif
import qualified LinearScan.Split as Split
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Seq as Seq
import qualified LinearScan.Ssrbool as Ssrbool
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

__ :: any
__ = Prelude.error "Logical or arity value used"

type PhysReg = Prelude.Int

intersectsWithFixedInterval :: Prelude.Int -> ScanState.ScanStateDesc ->
                               PhysReg -> Morph.SState () ()
                               (Prelude.Maybe Prelude.Int)
intersectsWithFixedInterval maxReg pre reg =
  Cursor.withCursor maxReg pre (\sd _ ->
    let {int = Cursor.curIntDetails maxReg sd} in
    Morph.return_
      (LinearScan.Utils.vfoldl' maxReg (\mx v ->
        Lib.option_choose mx
          (case v of {
            Prelude.Just i -> Interval.intervalIntersectionPoint ( int) ( i);
            Prelude.Nothing -> Prelude.Nothing})) Prelude.Nothing
        (ScanState.fixedIntervals maxReg sd)))

updateRegisterPos :: Prelude.Int -> ([] (Prelude.Maybe Prelude.Int)) ->
                     Prelude.Int -> (Prelude.Maybe Prelude.Int) -> []
                     (Prelude.Maybe Prelude.Int)
updateRegisterPos n v r p =
  case p of {
   Prelude.Just x ->
    LinearScan.Utils.set_nth n v r (Prelude.Just
      (case LinearScan.Utils.nth n v r of {
        Prelude.Just n0 -> Prelude.min n0 x;
        Prelude.Nothing -> x}));
   Prelude.Nothing -> v}

tryAllocateFreeReg :: Prelude.Int -> ScanState.ScanStateDesc -> Morph.SState
                      () () (Prelude.Maybe (Morph.SState () () PhysReg))
tryAllocateFreeReg maxReg pre =
  Cursor.withCursor maxReg pre (\sd _ ->
    let {
     go = \f v p ->
      case p of {
       (,) i r -> updateRegisterPos maxReg v r (f i)}}
    in
    let {
     freeUntilPos' = Data.List.foldl' (go (\x -> Prelude.Just 0))
                       (Data.List.replicate maxReg Prelude.Nothing)
                       (ScanState.active maxReg sd)}
    in
    let {
     intersectingIntervals = Prelude.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (Cursor.curIntDetails maxReg sd))
                                 (
                                   (LinearScan.Utils.nth
                                     (ScanState.nextInterval maxReg sd)
                                     (ScanState.intervals maxReg sd)
                                     (Prelude.fst x))))
                               (ScanState.inactive maxReg sd)}
    in
    let {
     freeUntilPos = Data.List.foldl'
                      (go (\i ->
                        Interval.intervalIntersectionPoint
                          (
                            (LinearScan.Utils.nth
                              (ScanState.nextInterval maxReg sd)
                              (ScanState.intervals maxReg sd) i))
                          ( (Cursor.curIntDetails maxReg sd)))) freeUntilPos'
                      intersectingIntervals}
    in
    case ScanState.registerWithHighestPos maxReg freeUntilPos of {
     (,) reg mres ->
      let {
       success = Morph.stbind (\x -> Morph.return_ reg)
                   (Morph.moveUnhandledToActive maxReg pre reg)}
      in
      let {
       maction = case mres of {
                  Prelude.Just n ->
                   case Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce n)
                          (unsafeCoerce 0) of {
                    Prelude.True -> Prelude.Nothing;
                    Prelude.False -> Prelude.Just
                     (case (Prelude.<=) ((Prelude.succ)
                             (Interval.intervalEnd
                               ( (Cursor.curIntDetails maxReg sd)))) n of {
                       Prelude.True -> success;
                       Prelude.False ->
                        Morph.stbind (\x ->
                          Morph.stbind (\x0 -> Morph.return_ reg)
                            (Morph.moveUnhandledToActive maxReg pre reg))
                          (Split.splitCurrentInterval maxReg pre
                            (Interval.BeforePos n))})};
                  Prelude.Nothing -> Prelude.Just success}}
      in
      Morph.return_ maction})

allocateBlockedReg :: Prelude.Int -> ScanState.ScanStateDesc -> Morph.SState
                      () () (Prelude.Maybe PhysReg)
allocateBlockedReg maxReg pre =
  Cursor.withCursor maxReg pre (\sd _ ->
    let {start = Interval.intervalStart ( (Cursor.curIntDetails maxReg sd))}
    in
    let {pos = Cursor.curPosition maxReg sd} in
    let {
     go = \v p ->
      case p of {
       (,) i r ->
        let {
         atPos = \u ->
          Eqtype.eq_op Ssrnat.nat_eqType (unsafeCoerce pos)
            (unsafeCoerce (Range.uloc u))}
        in
        let {
         pos' = case Interval.findIntervalUsePos
                       (Interval.getIntervalDesc
                         (
                           (LinearScan.Utils.nth
                             (ScanState.nextInterval maxReg sd)
                             (ScanState.intervals maxReg sd) i))) atPos of {
                 Prelude.Just p0 -> Prelude.Just 0;
                 Prelude.Nothing ->
                  Interval.nextUseAfter
                    (Interval.getIntervalDesc
                      (
                        (LinearScan.Utils.nth
                          (ScanState.nextInterval maxReg sd)
                          (ScanState.intervals maxReg sd) i))) start}}
        in
        updateRegisterPos maxReg v r pos'}}
    in
    let {
     nextUsePos' = Data.List.foldl' go
                     (Data.List.replicate maxReg Prelude.Nothing)
                     (ScanState.active maxReg sd)}
    in
    let {
     intersectingIntervals = Prelude.filter (\x ->
                               Interval.intervalsIntersect
                                 ( (Cursor.curIntDetails maxReg sd))
                                 (
                                   (LinearScan.Utils.nth
                                     (ScanState.nextInterval maxReg sd)
                                     (ScanState.intervals maxReg sd)
                                     (Prelude.fst x))))
                               (ScanState.inactive maxReg sd)}
    in
    let {nextUsePos = Data.List.foldl' go nextUsePos' intersectingIntervals}
    in
    case ScanState.registerWithHighestPos maxReg nextUsePos of {
     (,) reg mres ->
      case case mres of {
            Prelude.Just n -> (Prelude.<=) ((Prelude.succ) n) start;
            Prelude.Nothing -> Prelude.False} of {
       Prelude.True ->
        Morph.stbind (\x ->
          Morph.stbind (\mloc ->
            Morph.stbind (\x0 ->
              Morph.stbind (\x1 -> Morph.return_ Prelude.Nothing)
                (Morph.weakenHasLen_ maxReg pre))
              (case mloc of {
                Prelude.Just n ->
                 Split.splitCurrentInterval maxReg pre (Interval.BeforePos n);
                Prelude.Nothing -> Morph.return_ ()}))
            (intersectsWithFixedInterval maxReg pre reg))
          (Split.splitCurrentInterval maxReg pre
            Interval.BeforeFirstUsePosReqReg);
       Prelude.False ->
        Morph.stbind (\x ->
          Morph.stbind (\x0 ->
            Morph.stbind (\mloc ->
              Morph.stbind (\x1 ->
                Morph.stbind (\x2 -> Morph.return_ (Prelude.Just reg))
                  (Morph.moveUnhandledToActive maxReg pre reg))
                (case mloc of {
                  Prelude.Just n ->
                   Split.splitCurrentInterval maxReg pre (Interval.BeforePos
                     n);
                  Prelude.Nothing -> Morph.return_ ()}))
              (intersectsWithFixedInterval maxReg pre reg))
            (Split.splitActiveIntervalForReg maxReg pre reg pos))
          (Split.splitAnyInactiveIntervalForReg maxReg pre reg)}})

morphlen_transport :: Prelude.Int -> ScanState.ScanStateDesc ->
                      ScanState.ScanStateDesc -> ScanState.IntervalId ->
                      ScanState.IntervalId
morphlen_transport maxReg b b' = GHC.Base.id
  

mt_fst :: Prelude.Int -> ScanState.ScanStateDesc -> ScanState.ScanStateDesc
          -> ((,) ScanState.IntervalId PhysReg) -> (,) ScanState.IntervalId
          PhysReg
mt_fst maxReg b b' x =
  case x of {
   (,) xid reg -> (,) (morphlen_transport maxReg b b' xid) reg}

type Coq_int_reg_seq = [] ((,) ScanState.IntervalId PhysReg)

type Coq_intermediate_result = Specif.Coq_sig2 ScanState.ScanStateDesc

goActive :: Prelude.Int -> Prelude.Int -> ScanState.ScanStateDesc ->
            ScanState.ScanStateDesc -> ((,) ScanState.IntervalId PhysReg) ->
            Coq_int_reg_seq -> Coq_intermediate_result
goActive maxReg pos sd z x xs =
  case (Prelude.<=) ((Prelude.succ)
         (Interval.intervalEnd
           (
             (LinearScan.Utils.nth (ScanState.nextInterval maxReg z)
               (ScanState.intervals maxReg z) (Prelude.fst x))))) pos of {
   Prelude.True -> Morph.moveActiveToHandled maxReg z (unsafeCoerce x);
   Prelude.False ->
    case Prelude.not
           (Interval.intervalCoversPos
             (
               (LinearScan.Utils.nth (ScanState.nextInterval maxReg z)
                 (ScanState.intervals maxReg z) (Prelude.fst x))) pos) of {
     Prelude.True -> Morph.moveActiveToInactive maxReg z (unsafeCoerce x);
     Prelude.False -> z}}

checkActiveIntervals :: Prelude.Int -> ScanState.ScanStateDesc -> Prelude.Int
                        -> Morph.SState () () ()
checkActiveIntervals maxReg pre pos =
  Morph.withScanStatePO maxReg pre (\sd _ ->
    let {
     res = Lib.dep_foldl_inv (\s ->
             Eqtype.prod_eqType
               (Fintype.ordinal_eqType (ScanState.nextInterval maxReg s))
               (Fintype.ordinal_eqType maxReg)) sd
             (unsafeCoerce (ScanState.active maxReg sd))
             (Data.List.length (ScanState.active maxReg sd))
             (unsafeCoerce (ScanState.active maxReg))
             (unsafeCoerce (\x x0 _ -> mt_fst maxReg x x0))
             (unsafeCoerce (\x _ x0 x1 _ -> goActive maxReg pos sd x x0 x1))}
    in
    IState.iput (Morph.Build_SSInfo res __))

moveInactiveToActive' :: Prelude.Int -> ScanState.ScanStateDesc -> ((,)
                         ScanState.IntervalId PhysReg) -> Coq_int_reg_seq ->
                         Prelude.Either Morph.SSError
                         (Specif.Coq_sig2 ScanState.ScanStateDesc)
moveInactiveToActive' maxReg z x xs =
  let {
   filtered_var = Prelude.not
                    (Ssrbool.in_mem (Prelude.snd (unsafeCoerce x))
                      (Ssrbool.mem
                        (Seq.seq_predType (Fintype.ordinal_eqType maxReg))
                        (unsafeCoerce
                          (Prelude.map (\i -> Prelude.snd i)
                            (ScanState.active maxReg z)))))}
  in
  case filtered_var of {
   Prelude.True ->
    let {
     filtered_var0 = Morph.moveInactiveToActive maxReg z (unsafeCoerce x)}
    in
    Prelude.Right filtered_var0;
   Prelude.False -> Prelude.Left (Morph.ERegisterAssignmentsOverlap
    ( (Prelude.snd x)))}

goInactive :: Prelude.Int -> Prelude.Int -> ScanState.ScanStateDesc ->
              ScanState.ScanStateDesc -> ((,) ScanState.IntervalId PhysReg)
              -> Coq_int_reg_seq -> Prelude.Either Morph.SSError
              Coq_intermediate_result
goInactive maxReg pos sd z x xs =
  let {f = \sd' -> Prelude.Right sd'} in
  case (Prelude.<=) ((Prelude.succ)
         (Interval.intervalEnd
           (
             (LinearScan.Utils.nth (ScanState.nextInterval maxReg z)
               (ScanState.intervals maxReg z) (Prelude.fst x))))) pos of {
   Prelude.True ->
    let {
     filtered_var = Morph.moveInactiveToHandled maxReg z (unsafeCoerce x)}
    in
    f filtered_var;
   Prelude.False ->
    case Interval.intervalCoversPos
           (
             (LinearScan.Utils.nth (ScanState.nextInterval maxReg z)
               (ScanState.intervals maxReg z) (Prelude.fst x))) pos of {
     Prelude.True ->
      let {filtered_var = moveInactiveToActive' maxReg z x xs} in
      case filtered_var of {
       Prelude.Left err -> Prelude.Left err;
       Prelude.Right s -> f s};
     Prelude.False -> f z}}

checkInactiveIntervals :: Prelude.Int -> ScanState.ScanStateDesc ->
                          Prelude.Int -> Morph.SState () () ()
checkInactiveIntervals maxReg pre pos =
  Morph.withScanStatePO maxReg pre (\sd _ ->
    let {
     eres = Lib.dep_foldl_invE (\s ->
              Eqtype.prod_eqType
                (Fintype.ordinal_eqType (ScanState.nextInterval maxReg s))
                (Fintype.ordinal_eqType maxReg)) sd
              (unsafeCoerce (ScanState.inactive maxReg sd))
              (Data.List.length (ScanState.inactive maxReg sd))
              (unsafeCoerce (ScanState.inactive maxReg))
              (unsafeCoerce (\x x0 _ -> mt_fst maxReg x x0))
              (unsafeCoerce (\x _ x0 x1 _ ->
                goInactive maxReg pos sd x x0 x1))}
    in
    case eres of {
     Prelude.Left err -> Morph.error_ err;
     Prelude.Right s -> IState.iput (Morph.Build_SSInfo s __)})

handleInterval :: Prelude.Int -> ScanState.ScanStateDesc -> Morph.SState 
                  () () (Prelude.Maybe PhysReg)
handleInterval maxReg pre =
  Cursor.withCursor maxReg pre (\sd _ ->
    let {position = Cursor.curPosition maxReg sd} in
    Morph.stbind (\x ->
      Morph.stbind (\x0 ->
        Morph.stbind (\mres ->
          case mres of {
           Prelude.Just x1 -> IState.imap (\x2 -> Prelude.Just x2) x1;
           Prelude.Nothing -> allocateBlockedReg maxReg pre})
          (tryAllocateFreeReg maxReg pre))
        (Morph.liftLen maxReg pre (\sd0 ->
          checkInactiveIntervals maxReg sd0 position)))
      (Morph.liftLen maxReg pre (\sd0 ->
        checkActiveIntervals maxReg sd0 position)))

walkIntervals :: Prelude.Int -> ScanState.ScanStateDesc -> Prelude.Int ->
                 Prelude.Either Morph.SSError ScanState.ScanStateSig
walkIntervals maxReg sd positions =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.Left
    Morph.EFuelExhausted)
    (\n ->
    let {
     go = let {
           go count0 ss =
             (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
               (\_ -> Prelude.Right (Morph.Build_SSInfo
               (Morph.thisDesc maxReg sd ss)
               __))
               (\cnt ->
               case handleInterval maxReg sd ss of {
                Prelude.Left err -> Prelude.Left err;
                Prelude.Right p ->
                 case p of {
                  (,) o ss' ->
                   case Morph.strengthenHasLen maxReg sd
                          (Morph.thisDesc maxReg sd ss') of {
                    Prelude.Just _ ->
                     go cnt (Morph.Build_SSInfo
                       (Morph.thisDesc maxReg sd ss') __);
                    Prelude.Nothing ->
                     (\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))
                       (\_ -> Prelude.Right
                       ss')
                       (\n0 -> Prelude.Left
                       Morph.EUnexpectedNoMoreUnhandled)
                       cnt}}})
               count0}
          in go}
    in
    case LinearScan.Utils.uncons (ScanState.unhandled maxReg sd) of {
     Prelude.Just s ->
      case s of {
       (,) x s0 ->
        case x of {
         (,) i pos ->
          case go
                 (Seq.count (\x0 ->
                   Eqtype.eq_op Ssrnat.nat_eqType
                     (Prelude.snd (unsafeCoerce x0)) (unsafeCoerce pos))
                   (ScanState.unhandled maxReg sd)) (Morph.Build_SSInfo sd
                 __) of {
           Prelude.Left err -> Prelude.Left err;
           Prelude.Right ss ->
            walkIntervals maxReg (Morph.thisDesc maxReg sd ss) n}}};
     Prelude.Nothing -> Prelude.Right
      (ScanState.packScanState maxReg ScanState.InUse sd)})
    positions

