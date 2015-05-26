Require Import LinearScan.Lib.
Require Import LinearScan.Range.
Require Import LinearScan.Interval.
Require Import LinearScan.ScanState.
Require Import LinearScan.Spec.
Require Import LinearScan.Morph.
Require Import LinearScan.Context.
Require Import LinearScan.Spill.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Split.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg := 'I_maxReg.

Inductive SplitPosition : Set :=
  | BeforePos of oddnum
  | EndOfLifetimeHole of oddnum.

(* Given an interval, determine its optimal split position.  If no split
   position can be found, it means the interval may be safely spilled, and all
   further variable references should be accessed directly from memory. *)
Program Definition splitPosition `(i : Interval d) (pos : SplitPosition) :
  oddnum :=
  match pos with
  | BeforePos n => n
  | EndOfLifetimeHole n => afterLifetimeHole i n
  end.

Definition splitUnhandledInterval `(st : ScanState InUse sd)
  `(Hunh : unhandled sd = (uid, beg) :: us) (pos : SplitPosition)
  (e : seq SSTrace) :
  seq SSTrace + { ss : ScanStateSig maxReg InUse | SSMorphLen sd ss.1 }.
Proof.
  pose e2 := ESplitUnhandledInterval :: e.
  case: sd => /= [? ints ? unh ? ? ?] in st uid us Hunh *.
  set int := vnth ints uid.

  case: (splitPosition int.2 pos) => [splitPos Hodd].

  (* Ensure that the [splitPos] falls within the interval, otherwise our
     action can have no effect.

     jww (2015-03-05): Evidence should be given so we do not need this
     check. *)
  case Hmid: (ibeg int.1 < splitPos <= iend int.1); last first.
    case Hbeg2: (beg <= ibeg int.1); last first.
      exact: inl (ENoValidSplitPosition uid :: e).

    move: st.
    set sd := (X in ScanState _ X).
    move=> st.

    case: (spillInterval st Hunh Hbeg2 (UnhandledToHandled (refl_equal _)) e)
      => [err|[ss H]].
      exact: inl err.
    case: (firstUseReqReg int.2) => [[? ?]|] in H.
      case: H => [[?] ?].
      apply: inr (ss; _).
      exact: Build_SSMorphLen.
    exact: inl (ENoValidSplitPosition uid :: e).

  case Hint: int => [d i] in Hmid *.
  case: d => [iv ib ie rds] /= in i Hint Hmid *.

  case: (splitInterval i Hodd Hmid) => [[i0 i1] [/= H1 H2 H3]] //.

  (* The interval was split into two parts.  The first part will be dealt with
     by the caller (either moved to the active list to represent a register
     assignment, or move to the handled list to indicate a spill to the
     stack); the second goes back onto the unhandled list for processing
     later, unless it is empty (i.e., ibeg i == iend i, *and* there are no use
     positions). *)

  (* Update the state with the new dimensions of the first interval. *)
  move: (ScanState_setInterval st) => /= /(_ uid i0.1 i0.2).
  move: Hint; rewrite /int => ->.
  move/eqP in H2; rewrite eq_sym in H2; move/(_ H2).
  have Hend : iend i0.1 <= ie.
    rewrite H3.
    move: (Interval_bounded i1.2).
    by ordered.
  move/(_ Hend).
  rewrite /= => {st} st.

  (* Establish that beg == ibeg i0.1. *)
  clear int.
  case U: unh => // [x xs] in uid st us Hunh *.
  have Hin : (uid, beg) \in unh.
    rewrite U Hunh.
    exact: mem_head.
  rewrite -U in st *.
  move/eqP: (beginnings (maxReg:=maxReg) st Hin) => Heqe.

  (* The second interval goes back on the unhandled list, to be processed in a
     later iteration.  Note: this cannot change the head of the unhandled
     list. *)
  have := ScanState_newUnhandled st i1.2.
  rewrite U Hunh => /=.
  have Hincr: (beg < ibeg i1.1).
    clear -Hmid H1 H2 H3 x Hunh Heqe.
    inversion Hunh.
    rewrite -Heqe /= vnth_vreplace /=.
    move/andP: Hmid => [? ?].
    by ordered.
  move/(_ Hincr).
  rewrite /= => {st} st.

  apply: inr (packScanState st; _).
  apply Build_SSMorphLen.
  apply Build_SSMorph => //=.
  by rewrite insert_size.
Defined.

Definition splitCurrentInterval {pre} (pos : SplitPosition) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> e ssi.
  case: ssi => desc.
  case=> H. case: H => /=; case.
  case Hunh: (unhandled desc) => //= [[uid beg] us].
  move=> H1 H2 H3.
  move/splitUnhandledInterval/(_ uid beg us Hunh pos e).
  case: desc => /= ? intervals0 ? unhandled0 ? ? ? in uid us Hunh H1 H2 H3 *.
  case=> [err|[[sd st] [[/= ? H]]]].
    exact: inl err.
  apply: (inr (tt, _)).
  apply: (Build_SSInfo _ st).
  rewrite Hunh /= in H.
  specialize (H (ltn0Sn _)).
  apply Build_SSMorphHasLen;
  try apply Build_SSMorphLen;
  try apply Build_SSMorph;
  rewrite ?insert_size ?size_map //;
  try move=> Hpre;
  exact: (leq_trans H1 _).
Defined.

Definition splitActiveOrInactiveInterval `(st : ScanState InUse sd)
  `(Hunh : unhandled sd = (uid, beg) :: us)
  (xid : IntervalId sd) (pos : SplitPosition) (reg : PhysReg)
  (Hbeg : beg <= (splitPosition (getInterval xid) pos).1)
  (Hin : ((xid, reg) \in active sd) + ((xid, reg) \in inactive sd))
  (e : seq SSTrace) :
  seq SSTrace + { ss : ScanStateSig maxReg InUse | SSMorphHasLen sd ss.1 }.
Proof.
  have e2 := ESplitActiveOrInactiveInterval
               (match Hin with inl _ => true | inr _ => false end) :: e.
  case: sd => /= [ni ints ? unh ? ? ?] in st uid us xid Hunh Hbeg Hin *.
  set int := vnth ints xid.

  case: (splitPosition int.2 pos) => [splitPos Hodd] in Hbeg *.

  move: st.
  set sd := (X in ScanState _ X).
  move=> st.
  have Heqe: (vnth (intervals sd) xid = int) by reflexivity.

  (* Ensure that the [splitPos] falls within the interval. *)
  case Hmid: (ibeg int.1 < splitPos <= iend int.1); last first.
    (* If the [splitPos] is before the beginning, there's really nothing we
       can do except fail.  But if our interval begins at or after [beg], then
       we can try to spill the first part of the interval (or all of it, if
       there are no use positions requiring registers). *)
    case Hbeg2: (beg <= ibeg int.1); last first.
      exact: inl (ENoValidSplitPosition xid :: e2).

    case: Hin => [Hin|Hin].
      case: (spillInterval st Hunh Hbeg2 (ActiveToHandled uid Heqe Hin) e2)
        => [err|[ss [[[/= ?] ?] ?]]].
        exact: inl err.
      exact: inr (ss; _).
    case: (spillInterval st Hunh Hbeg2 (InactiveToHandled uid Heqe Hin) e2)
      => [err|[ss [[[/= ?] ?] ?]]].
      exact: inl err.
    exact: inr (ss; _).

  case Hint: int => [d i] in Hmid *.
  case: d => [iv ib ie rds] /= in i Hint Hmid *.

  case: (splitInterval i Hodd Hmid) => [[i0 i1] [/= H1 H2 H3]] //.

  (* The interval was split into two parts.  The first part is left where it
     was (it is simply shorter now, but it's beginning has not changed), while
     the second part is spilled -- unless the second part contains a use
     position that requires a register, in which case we split at that point,
     and the first part of that split child is spilled, and the second part is
     put on the unhandled list. *)

  (* Update the state with the new dimensions of the first interval. *)
  move: (ScanState_setInterval st) => /= /(_ xid i0.1 i0.2).
  move: Hint; rewrite /int => ->.
  move/eqP in H2; rewrite eq_sym in H2; move/(_ H2).
  have Hend : iend i0.1 <= ie.
    rewrite H3.
    move: (Interval_bounded i1.2).
    by ordered.
  move/(_ Hend).
  rewrite /= => {Heqe sd st} st.

  move: st.
  set sd := (X in ScanState _ X).
  move=> st.

  have Hbeg2 : beg <= ibeg i1.1
    by clear -H1 Hbeg; rewrite /= in Hbeg; ordered.

  have Hsize2 : 0 < size (unhandled sd).
    rewrite /= in sd st *.
    by rewrite /sd /= Hunh.

  have Hle : ni <= nextInterval sd by [].

  (* Spill the second interval, unless it has a use position that requires a
     register, in which case we spill the first place and add the second part
     back onto the unhandled list for processing later. *)
  case: (spillInterval st Hunh Hbeg2 (NewToHandled _ i1) e2)
    => [err|[ss [[[/= ?] ?] ?]]].
    exact: inl err.
  exact: inr (ss; _).
Defined.

(** If [pos] is [None], it means "split at the end of its lifetime hole". *)
Definition splitAssignedIntervalForReg {pre}
  (reg : PhysReg) (pos : SplitPosition) (trueForActives : bool) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> e ssi.
  pose e2 := ESplitAssignedIntervalForReg reg :: e.
  case: ssi => desc.
  case=> H. case: H => /=; case.

  (* There is an opportunity here for optimization: finding the best inactive
     interval to split, for example one with a large lifetime hole, or one
     that does not cover loops. *)
  pose intlist := if trueForActives then active desc else inactive desc.
  have Hintlist:
    intlist = if trueForActives then active desc else inactive desc by [].
  set intids := [seq fst i | i <- intlist & snd i == reg].
  have /allP /= Hin: all (fun x => (x, reg) \in intlist) intids
    by exact: map_fst_filter_snd.
  move: intlist Hintlist intids Hin.

  case Hunh: (unhandled desc) => //= [[uid beg] us].
  case: desc => /= ? intervals0 ? ? active0 inactive0 ? in uid us Hunh *.
  move=> intlist Hintlist intids Hin H1 H2 H3 st.

  elim Hintids: intids => /= [|aid aids IHaids] in Hin *.
    apply: (inr (tt, (Build_SSInfo _ st))).
    apply Build_SSMorphHasLen;
    try apply Build_SSMorphHasLen;
    try apply Build_SSMorphLen;
    try apply Build_SSMorph => //=;
    by rewrite Hunh.

  case Hbeg: (beg <= (splitPosition (getInterval aid) pos).1); last first.
    exact: inl (ECannotSplitSingleton aid :: e2).

  move/splitActiveOrInactiveInterval: st
    => /(_ uid beg us Hunh aid pos reg Hbeg) /=.

  have Hin' : (((aid, reg) \in active0) + ((aid, reg) \in inactive0))%type.
    case: trueForActives in Hintlist;
    pose H := (Hin aid _);
    specialize (H (mem_head _ _));
    rewrite Hintlist in H.
      exact: inl _.
    exact: inr _.
  move=> /(_ Hin' e2) {Hin'}.

  case=> [err|[[sd st] [[/= [Hincr] H ?]]]].
    exact: inl err.
  apply: (inr (tt, _)).

  (* When splitting an active interval, we must move the first half over to
     the inactive list, since it no longer intersects with the current
     position.  This is only valid when [trueForActives] is [true], and only
     if [splitAtInterval] does not modify the actives list.  It doesn't hurt
     to always check whether it's a member, though we should prove that
     [splitAtInterval] has the right behavior. *)
  case E: ((widen_ord Hincr aid, reg) \in active sd) => //;
    first
      (have /= := ScanState_moveActiveToInactive st E;
       move=> {st};
       set act_to_inact := Build_ScanStateDesc _ _ _ _ _ _;
       simpl in act_to_inact;
       move=> st);

  rewrite Hunh /= in H;
  specialize (H (ltn0Sn _));
  apply: (Build_SSInfo _ st);
  apply Build_SSMorphHasLen;
  try apply Build_SSMorphHasLen;
  try apply Build_SSMorphLen;
  try apply Build_SSMorph;
  rewrite ?insert_size ?size_map //;
  try move=> Hpre;
  exact: (leq_trans H1 _).
Defined.

Definition splitActiveIntervalForReg {pre} (reg : PhysReg) (pos : oddnum) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit :=
  context (ESplitActiveIntervalForReg reg) $
    splitAssignedIntervalForReg reg (BeforePos pos) true.

Definition splitAnyInactiveIntervalForReg {pre} (reg : PhysReg) (pos : oddnum) :
  SState pre (@SSMorphHasLen maxReg) (@SSMorphHasLen maxReg) unit.
Proof.
  move=> e ss.
  pose e2 := ESplitAnyInactiveIntervalForReg reg :: e.
  have := splitAssignedIntervalForReg reg (EndOfLifetimeHole pos) false.
  move=> /(_ pre e2 ss).
  case=> [err|[_ ss']]; right; split; try constructor.
    exact: ss.
  exact: ss'.
Defined.

End Split.
