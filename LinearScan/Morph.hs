{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Morph where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.IState as IState
import qualified LinearScan.Logic as Logic
import qualified LinearScan.ScanState as ScanState
import qualified LinearScan.Specif as Specif
import qualified LinearScan.Eqtype as Eqtype
import qualified LinearScan.Fintype as Fintype
import qualified LinearScan.Seq as Seq
import qualified LinearScan.Ssrbool as Ssrbool



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

data SSError =
   ECannotSplitSingleton Prelude.Int
 | ECannotSplitAssignedSingleton Prelude.Int
 | ENoIntervalsToSplit
 | ERegisterAlreadyAssigned Prelude.Int
 | ERegisterAssignmentsOverlap Prelude.Int
 | EFuelExhausted
 | EUnexpectedNoMoreUnhandled

stbind :: (a4 -> IState.IState SSError a2 a3 a5) -> (IState.IState SSError 
          a1 a2 a4) -> IState.IState SSError a1 a3 a5
stbind f x =
  IState.ijoin (IState.imap f x)

error_ :: SSError -> IState.IState SSError a1 a2 a3
error_ err x =
  Prelude.Left err

return_ :: a3 -> IState.IState a1 a2 a2 a3
return_ =
  IState.ipure

data SSInfo p =
   Build_SSInfo ScanState.ScanStateDesc p

thisDesc :: Prelude.Int -> ScanState.ScanStateDesc -> (SSInfo a1) ->
            ScanState.ScanStateDesc
thisDesc maxReg startDesc s =
  case s of {
   Build_SSInfo thisDesc0 thisHolds -> thisDesc0}

type SState p q a = IState.IState SSError (SSInfo p) (SSInfo q) a

withScanStatePO :: Prelude.Int -> ScanState.ScanStateDesc ->
                   (ScanState.ScanStateDesc -> () -> SState () () a1) ->
                   SState () () a1
withScanStatePO maxReg pre f i =
  case i of {
   Build_SSInfo thisDesc0 _ ->
    let {f0 = f thisDesc0 __} in
    let {x = Build_SSInfo thisDesc0 __} in
    let {x0 = f0 x} in
    case x0 of {
     Prelude.Left s -> Prelude.Left s;
     Prelude.Right p -> Prelude.Right
      (case p of {
        (,) a0 s -> (,) a0
         (case s of {
           Build_SSInfo thisDesc1 _ -> Build_SSInfo thisDesc1 __})})}}

liftLen :: Prelude.Int -> ScanState.ScanStateDesc -> (ScanState.ScanStateDesc
           -> SState () () a1) -> SState () () a1
liftLen maxReg pre f _top_assumption_ =
  let {
   _evar_0_ = \sd ->
    let {ss = Build_SSInfo sd __} in
    let {_evar_0_ = \err -> Prelude.Left err} in
    let {
     _evar_0_0 = \_top_assumption_0 ->
      let {
       _evar_0_0 = \x _top_assumption_1 ->
        let {_evar_0_0 = \sd' -> Prelude.Right ((,) x (Build_SSInfo sd' __))}
        in
        case _top_assumption_1 of {
         Build_SSInfo x0 x1 -> _evar_0_0 x0}}
      in
      case _top_assumption_0 of {
       (,) x x0 -> _evar_0_0 x x0}}
    in
    case f sd ss of {
     Prelude.Left x -> _evar_0_ x;
     Prelude.Right x -> _evar_0_0 x}}
  in
  case _top_assumption_ of {
   Build_SSInfo x x0 -> _evar_0_ x}

weakenHasLen_ :: Prelude.Int -> ScanState.ScanStateDesc -> SState () () ()
weakenHasLen_ maxReg pre hS =
  Prelude.Right ((,) ()
    (case hS of {
      Build_SSInfo thisDesc0 _ -> Build_SSInfo thisDesc0 __}))

strengthenHasLen :: Prelude.Int -> ScanState.ScanStateDesc ->
                    ScanState.ScanStateDesc -> Prelude.Maybe ()
strengthenHasLen maxReg pre sd =
  let {_evar_0_ = \_ -> Prelude.Nothing} in
  let {_evar_0_0 = \_a_ _l_ -> Prelude.Just __} in
  case ScanState.unhandled maxReg sd of {
   [] -> _evar_0_ __;
   (:) x x0 -> _evar_0_0 x x0}

moveUnhandledToActive :: Prelude.Int -> ScanState.ScanStateDesc -> PhysReg ->
                         SState () () ()
moveUnhandledToActive maxReg pre reg x =
  case x of {
   Build_SSInfo thisDesc0 _ ->
    case thisDesc0 of {
     ScanState.Build_ScanStateDesc nextInterval0 intervals0 fixedIntervals0
      unhandled0 active0 inactive0 handled0 ->
      case unhandled0 of {
       [] -> Logic.coq_False_rect;
       (:) p unhandled1 ->
        let {
         _evar_0_ = \_ -> Prelude.Right ((,) () (Build_SSInfo
          (ScanState.Build_ScanStateDesc nextInterval0 intervals0
          fixedIntervals0 unhandled1 ((:) ((,) (Prelude.fst p) reg) active0)
          inactive0 handled0) __))}
        in
        let {
         _evar_0_0 = \_ -> Prelude.Left (ERegisterAlreadyAssigned ( reg))}
        in
        case Prelude.not
               (Ssrbool.in_mem (unsafeCoerce reg)
                 (Ssrbool.mem
                   (Seq.seq_predType (Fintype.ordinal_eqType maxReg))
                   (unsafeCoerce (Prelude.map (\i -> Prelude.snd i) active0)))) of {
         Prelude.True -> _evar_0_ __;
         Prelude.False -> _evar_0_0 __}}}}

moveActiveToHandled :: Prelude.Int -> ScanState.ScanStateDesc ->
                       Eqtype.Equality__Coq_sort -> Specif.Coq_sig2
                       ScanState.ScanStateDesc
moveActiveToHandled maxReg sd x =
  ScanState.Build_ScanStateDesc (ScanState.nextInterval maxReg sd)
    (ScanState.intervals maxReg sd) (ScanState.fixedIntervals maxReg sd)
    (ScanState.unhandled maxReg sd)
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (ScanState.nextInterval maxReg sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (ScanState.active maxReg sd))))
    (ScanState.inactive maxReg sd) ((:) (unsafeCoerce x)
    (ScanState.handled maxReg sd))

moveActiveToInactive :: Prelude.Int -> ScanState.ScanStateDesc ->
                        Eqtype.Equality__Coq_sort -> Specif.Coq_sig2
                        ScanState.ScanStateDesc
moveActiveToInactive maxReg sd x =
  ScanState.Build_ScanStateDesc (ScanState.nextInterval maxReg sd)
    (ScanState.intervals maxReg sd) (ScanState.fixedIntervals maxReg sd)
    (ScanState.unhandled maxReg sd)
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (ScanState.nextInterval maxReg sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (ScanState.active maxReg sd)))) ((:) (unsafeCoerce x)
    (ScanState.inactive maxReg sd)) (ScanState.handled maxReg sd)

moveInactiveToActive :: Prelude.Int -> ScanState.ScanStateDesc ->
                        Eqtype.Equality__Coq_sort -> Specif.Coq_sig2
                        ScanState.ScanStateDesc
moveInactiveToActive maxReg sd x =
  ScanState.Build_ScanStateDesc (ScanState.nextInterval maxReg sd)
    (ScanState.intervals maxReg sd) (ScanState.fixedIntervals maxReg sd)
    (ScanState.unhandled maxReg sd) ((:) (unsafeCoerce x)
    (ScanState.active maxReg sd))
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (ScanState.nextInterval maxReg sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (ScanState.inactive maxReg sd))))
    (ScanState.handled maxReg sd)

moveInactiveToHandled :: Prelude.Int -> ScanState.ScanStateDesc ->
                         Eqtype.Equality__Coq_sort -> Specif.Coq_sig2
                         ScanState.ScanStateDesc
moveInactiveToHandled maxReg sd x =
  ScanState.Build_ScanStateDesc (ScanState.nextInterval maxReg sd)
    (ScanState.intervals maxReg sd) (ScanState.fixedIntervals maxReg sd)
    (ScanState.unhandled maxReg sd) (ScanState.active maxReg sd)
    (unsafeCoerce
      (Seq.rem
        (Eqtype.prod_eqType
          (Fintype.ordinal_eqType (ScanState.nextInterval maxReg sd))
          (Fintype.ordinal_eqType maxReg)) x
        (unsafeCoerce (ScanState.inactive maxReg sd)))) ((:) (unsafeCoerce x)
    (ScanState.handled maxReg sd))

