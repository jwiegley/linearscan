{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LinearScan.Split where


import qualified Prelude
import qualified Data.IntMap
import qualified Data.IntSet
import qualified Data.List
import qualified Data.Ord
import qualified Data.Functor.Identity
import qualified LinearScan.Utils

import qualified LinearScan.Datatypes as Datatypes
import qualified LinearScan.Interval as Interval
import qualified LinearScan.Logic as Logic
import qualified LinearScan.Morph as Morph
import qualified LinearScan.ScanState as ScanState
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

splitInterval :: Prelude.Int -> ScanState.ScanStateDesc ->
                 ScanState.IntervalId -> Interval.SplitPosition ->
                 Prelude.Bool -> Prelude.Either Morph.SSError
                 (Prelude.Maybe ScanState.ScanStateSig)
splitInterval maxReg sd uid pos forCurrent =
  let {
   _evar_0_ = \_nextInterval_ ints _fixedIntervals_ unh _active_ _inactive_ _handled_ uid0 ->
    let {
     _evar_0_ = \uid1 -> Prelude.Left (Morph.ECannotSplitSingleton ( uid1))}
    in
    let {
     _evar_0_0 = \_top_assumption_ ->
      let {
       _evar_0_0 = \u beg us uid1 ->
        let {int = LinearScan.Utils.nth _nextInterval_ ints uid1} in
        let {
         _evar_0_0 = \splitPos ->
          let {
           _evar_0_0 = \_ ->
            (Prelude.flip (Prelude.$)) __ (\_ ->
              let {
               _evar_0_0 = \iv ib ie _iknd_ rds ->
                let {
                 _top_assumption_0 = Interval.intervalSpan rds splitPos iv ib
                                       ie _iknd_}
                in
                let {
                 _evar_0_0 = \_top_assumption_1 ->
                  let {
                   _evar_0_0 = \_top_assumption_2 _top_assumption_3 ->
                    let {
                     _evar_0_0 = \_top_assumption_4 ->
                      let {
                       _evar_0_0 = \_ ->
                        let {
                         _evar_0_0 = \_ ->
                          let {
                           _evar_0_0 = \_ ->
                            (Prelude.flip (Prelude.$)) __
                              (let {
                                new_unhandled = ScanState.Build_ScanStateDesc
                                 ((Prelude.succ) _nextInterval_)
                                 (LinearScan.Utils.snoc _nextInterval_
                                   (LinearScan.Utils.set_nth _nextInterval_
                                     ints uid1 _top_assumption_2)
                                   _top_assumption_4) _fixedIntervals_
                                 (Data.List.insertBy
                                   (Data.Ord.comparing Prelude.snd) ((,)
                                   ( _nextInterval_)
                                   (Interval.ibeg _top_assumption_4)) ((:)
                                   (Prelude.id ((,) u beg))
                                   (Prelude.map Prelude.id us)))
                                 (Prelude.map Prelude.id _active_)
                                 (Prelude.map Prelude.id _inactive_)
                                 (Prelude.map Prelude.id _handled_)}
                               in
                               \_ -> Prelude.Right (Prelude.Just
                               (ScanState.packScanState maxReg
                                 ScanState.InUse new_unhandled)))}
                          in
                           _evar_0_0 __}
                        in
                         _evar_0_0 __}
                      in
                      let {
                       _evar_0_1 = \_ -> Prelude.Left
                        (Morph.ECannotSplitSingleton ( uid1))}
                      in
                      case (Prelude.<=) ((Prelude.succ) beg)
                             (Interval.ibeg _top_assumption_4) of {
                       Prelude.True -> _evar_0_0 __;
                       Prelude.False -> _evar_0_1 __}}
                    in
                    let {
                     _evar_0_1 = \_ ->
                      let {
                       _evar_0_1 = Prelude.Left (Morph.ECannotSplitSingleton
                        ( uid1))}
                      in
                      let {
                       _evar_0_2 = let {
                                    _evar_0_2 = \_ ->
                                     let {
                                      _evar_0_2 = \_ ->
                                       let {
                                        set_int_desc = ScanState.Build_ScanStateDesc
                                         _nextInterval_
                                         (LinearScan.Utils.set_nth
                                           _nextInterval_ ints uid1
                                           _top_assumption_2)
                                         _fixedIntervals_ ((:) ((,) u beg)
                                         us) _active_ _inactive_ _handled_}
                                       in
                                       Prelude.Right (Prelude.Just
                                       (ScanState.packScanState maxReg
                                         ScanState.InUse set_int_desc))}
                                     in
                                      _evar_0_2 __}
                                   in
                                    _evar_0_2 __}
                      in
                      case forCurrent of {
                       Prelude.True -> _evar_0_1;
                       Prelude.False -> _evar_0_2}}
                    in
                    case _top_assumption_3 of {
                     Prelude.Just x -> (\_ -> _evar_0_0 x);
                     Prelude.Nothing -> _evar_0_1}}
                  in
                  let {
                   _evar_0_1 = \_top_assumption_2 ->
                    let {
                     _evar_0_1 = \_top_assumption_3 ->
                      let {
                       _evar_0_1 = \_ ->
                        (Prelude.flip (Prelude.$)) __
                          (let {
                            new_unhandled = ScanState.Build_ScanStateDesc
                             ((Prelude.succ) _nextInterval_)
                             (LinearScan.Utils.snoc _nextInterval_ ints
                               _top_assumption_3) _fixedIntervals_
                             (Data.List.insertBy
                               (Data.Ord.comparing Prelude.snd) ((,)
                               ( _nextInterval_)
                               (Interval.ibeg _top_assumption_3)) ((:)
                               (Prelude.id ((,) u beg))
                               (Prelude.map Prelude.id us)))
                             (Prelude.map Prelude.id _active_)
                             (Prelude.map Prelude.id _inactive_)
                             (Prelude.map Prelude.id _handled_)}
                           in
                           \_ -> Prelude.Right (Prelude.Just
                           (ScanState.packScanState maxReg ScanState.InUse
                             new_unhandled)))}
                      in
                      let {
                       _evar_0_2 = \_ -> Prelude.Left
                        (Morph.ECannotSplitSingleton ( uid1))}
                      in
                      case (Prelude.<=) ((Prelude.succ) beg)
                             (Interval.ibeg _top_assumption_3) of {
                       Prelude.True -> _evar_0_1 __;
                       Prelude.False -> _evar_0_2 __}}
                    in
                    let {_evar_0_2 = \_ -> Logic.coq_False_rect} in
                    case _top_assumption_2 of {
                     Prelude.Just x -> (\_ -> _evar_0_1 x);
                     Prelude.Nothing -> _evar_0_2}}
                  in
                  case _top_assumption_1 of {
                   Prelude.Just x -> _evar_0_0 x;
                   Prelude.Nothing -> _evar_0_1}}
                in
                case _top_assumption_0 of {
                 (,) x x0 -> _evar_0_0 x x0 __}}
              in
              case int of {
               Interval.Build_IntervalDesc x x0 x1 x2 x3 ->
                _evar_0_0 x x0 x1 x2 x3})}
          in
          let {
           _evar_0_1 = \_ -> Prelude.Left (Morph.ECannotSplitSingleton
            ( uid1))}
          in
          case (Prelude.&&)
                 ((Prelude.<=) ((Prelude.succ) (Interval.ibeg ( int)))
                   splitPos)
                 ((Prelude.<=) ((Prelude.succ) splitPos)
                   (Interval.iend ( int))) of {
           Prelude.True -> _evar_0_0 __;
           Prelude.False -> _evar_0_1 __}}
        in
        let {_evar_0_1 = Prelude.Right Prelude.Nothing} in
        case Interval.splitPosition ( int) pos of {
         Prelude.Just x -> _evar_0_0 x;
         Prelude.Nothing -> _evar_0_1}}
      in
      (\us _ uid1 ->
      case _top_assumption_ of {
       (,) x x0 -> _evar_0_0 x x0 us uid1})}
    in
    case unh of {
     [] -> _evar_0_ uid0;
     (:) x x0 -> _evar_0_0 x x0 __ uid0}}
  in
  case sd of {
   ScanState.Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
    _evar_0_ x x0 x1 x2 x3 x4 x5 uid}

splitCurrentInterval :: Prelude.Int -> ScanState.ScanStateDesc ->
                        Interval.SplitPosition -> Morph.SState () () 
                        ()
splitCurrentInterval maxReg pre pos ssi =
  let {
   _evar_0_ = \desc ->
    let {
     _evar_0_ = \_nextInterval_ intervals0 _fixedIntervals_ unhandled0 _active_ _inactive_ _handled_ ->
      let {_evar_0_ = \_ _ _ _ _ -> Logic.coq_False_rect} in
      let {
       _evar_0_0 = \_top_assumption_ ->
        let {
         _evar_0_0 = \uid beg us ->
          let {
           desc0 = ScanState.Build_ScanStateDesc _nextInterval_ intervals0
            _fixedIntervals_ ((:) ((,) uid beg) us) _active_ _inactive_
            _handled_}
          in
          (\_ _ _ _ ->
          let {
           _top_assumption_0 = splitInterval maxReg desc0 uid pos
                                 Prelude.True}
          in
          let {_evar_0_0 = \err -> Prelude.Left err} in
          let {
           _evar_0_1 = \_top_assumption_1 ->
            let {
             _evar_0_1 = \_top_assumption_2 -> Prelude.Right ((,) ()
              (Morph.Build_SSInfo _top_assumption_2 __))}
            in
            let {
             _evar_0_2 = Prelude.Left (Morph.ECannotSplitSingleton ( uid))}
            in
            case _top_assumption_1 of {
             Prelude.Just x -> _evar_0_1 x;
             Prelude.Nothing -> _evar_0_2}}
          in
          case _top_assumption_0 of {
           Prelude.Left x -> _evar_0_0 x;
           Prelude.Right x -> _evar_0_1 x})}
        in
        (\us _ ->
        case _top_assumption_ of {
         (,) x x0 -> _evar_0_0 x x0 us})}
      in
      case unhandled0 of {
       [] -> _evar_0_ __;
       (:) x x0 -> _evar_0_0 x x0 __}}
    in
    case desc of {
     ScanState.Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
      _evar_0_ x x0 x1 x2 x3 x4 x5 __ __ __}}
  in
  case ssi of {
   Morph.Build_SSInfo x x0 -> _evar_0_ x __}

splitAssignedIntervalForReg :: Prelude.Int -> ScanState.ScanStateDesc ->
                               PhysReg -> Interval.SplitPosition ->
                               Prelude.Bool -> Morph.SState () () ()
splitAssignedIntervalForReg maxReg pre reg pos trueForActives ssi =
  let {
   _evar_0_ = \desc ->
    let {
     intlist = case trueForActives of {
                Prelude.True -> ScanState.active maxReg desc;
                Prelude.False -> ScanState.inactive maxReg desc}}
    in
    (Prelude.flip (Prelude.$)) __ (\_ ->
      let {
       intids = Prelude.map (\i -> Prelude.fst i)
                  (Prelude.filter (\i ->
                    Eqtype.eq_op (Fintype.ordinal_eqType maxReg)
                      (Prelude.snd (unsafeCoerce i)) (unsafeCoerce reg))
                    intlist)}
      in
      (Prelude.flip (Prelude.$)) __ (\_ ->
        let {
         _evar_0_ = \_nextInterval_ intervals0 _fixedIntervals_ _unhandled_ active0 inactive0 _handled_ intlist0 intids0 ->
          let {
           desc0 = ScanState.Build_ScanStateDesc _nextInterval_ intervals0
            _fixedIntervals_ _unhandled_ active0 inactive0 _handled_}
          in
          (\_ _ _ _ ->
          let {_evar_0_ = \_ -> Prelude.Left Morph.ENoIntervalsToSplit} in
          let {
           _evar_0_0 = \aid aids iHaids ->
            let {
             _top_assumption_ = splitInterval maxReg desc0 aid pos
                                  Prelude.False}
            in
            let {_evar_0_0 = \err -> Prelude.Left err} in
            let {
             _evar_0_1 = \_top_assumption_0 ->
              let {
               _evar_0_1 = \_top_assumption_1 -> Prelude.Right ((,) ()
                (let {
                  _evar_0_1 = \_ ->
                   (Prelude.flip (Prelude.$)) __
                     (let {
                       act_to_inact = ScanState.Build_ScanStateDesc
                        (ScanState.nextInterval maxReg _top_assumption_1)
                        (ScanState.intervals maxReg _top_assumption_1)
                        (ScanState.fixedIntervals maxReg _top_assumption_1)
                        (ScanState.unhandled maxReg _top_assumption_1)
                        (unsafeCoerce
                          (Seq.rem
                            (Eqtype.prod_eqType
                              (Fintype.ordinal_eqType
                                (ScanState.nextInterval maxReg
                                  _top_assumption_1))
                              (Fintype.ordinal_eqType maxReg))
                            (unsafeCoerce ((,) ( aid) reg))
                            (unsafeCoerce
                              (ScanState.active maxReg _top_assumption_1))))
                        ((:) ((,) ( aid) reg)
                        (ScanState.inactive maxReg _top_assumption_1))
                        (ScanState.handled maxReg _top_assumption_1)}
                      in
                      \_ -> Morph.Build_SSInfo act_to_inact __)}
                 in
                 let {
                  _evar_0_2 = \_ -> Morph.Build_SSInfo _top_assumption_1 __}
                 in
                 case Ssrbool.in_mem (unsafeCoerce ((,) ( aid) reg))
                        (Ssrbool.mem
                          (Seq.seq_predType
                            (Eqtype.prod_eqType
                              (Fintype.ordinal_eqType
                                (ScanState.nextInterval maxReg
                                  _top_assumption_1))
                              (Fintype.ordinal_eqType maxReg)))
                          (unsafeCoerce
                            (ScanState.active maxReg _top_assumption_1))) of {
                  Prelude.True -> _evar_0_1 __;
                  Prelude.False -> _evar_0_2 __}))}
              in
              let {
               _evar_0_2 = Prelude.Left (Morph.ECannotSplitSingleton ( aid))}
              in
              case _top_assumption_0 of {
               Prelude.Just x -> _evar_0_1 x;
               Prelude.Nothing -> _evar_0_2}}
            in
            case _top_assumption_ of {
             Prelude.Left x -> _evar_0_0 x;
             Prelude.Right x -> _evar_0_1 x}}
          in
          Datatypes.list_rect _evar_0_ (\aid aids iHaids _ ->
            _evar_0_0 aid aids iHaids) intids0 __)}
        in
        case desc of {
         ScanState.Build_ScanStateDesc x x0 x1 x2 x3 x4 x5 ->
          _evar_0_ x x0 x1 x2 x3 x4 x5 intlist intids})) __ __ __}
  in
  case ssi of {
   Morph.Build_SSInfo x x0 -> _evar_0_ x __}

splitActiveIntervalForReg :: Prelude.Int -> ScanState.ScanStateDesc ->
                             PhysReg -> Prelude.Int -> Morph.SState () 
                             () ()
splitActiveIntervalForReg maxReg pre reg pos =
  splitAssignedIntervalForReg maxReg pre reg (Interval.BeforePos pos)
    Prelude.True

splitAnyInactiveIntervalForReg :: Prelude.Int -> ScanState.ScanStateDesc ->
                                  PhysReg -> Morph.SState () () ()
splitAnyInactiveIntervalForReg maxReg pre reg ss =
  (Prelude.flip (Prelude.$)) (\s ->
    splitAssignedIntervalForReg maxReg s reg Interval.EndOfLifetimeHole
      Prelude.False) (\_top_assumption_ ->
    let {_top_assumption_0 = _top_assumption_ pre ss} in
    let {_evar_0_ = \err -> Prelude.Right ((,) () ss)} in
    let {
     _evar_0_0 = \_top_assumption_1 ->
      let {_evar_0_0 = \_the_1st_wildcard_ ss' -> Prelude.Right ((,) () ss')}
      in
      case _top_assumption_1 of {
       (,) x x0 -> _evar_0_0 x x0}}
    in
    case _top_assumption_0 of {
     Prelude.Left x -> _evar_0_ x;
     Prelude.Right x -> _evar_0_0 x})

