Require Import LinearScan.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
    uloc   : nat;
    regReq : bool
}.

Coercion uloc : UsePos >-> nat.

Module UsePosNotations.
Notation " (| x |) " := {| uloc := x; regReq := false |}.
Notation " (! x !) " := {| uloc := x; regReq := true |}.
End UsePosNotations.

Definition upos_lt (x y : UsePos) : bool := uloc x < uloc y.
Arguments upos_lt x y /.

Program Instance upos_lt_trans : Transitive upos_lt.
Obligation 1. exact: (ltn_trans H). Qed.

Lemma NE_StronglySorted_UsePos_impl : forall xs,
  NE_StronglySorted upos_lt xs -> NE_head xs < (NE_last xs).+1.
Proof.
  intros.
  induction xs; simpl in *; auto.
  inversion H.
  apply NE_Forall_last in H3.
  exact/ltnW.
Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosSublistsOf (before : nat)
  `(H : NE_StronglySorted upos_lt l) :=
  { p : option (NonEmpty UsePos) * option (NonEmpty UsePos)
  | let f x := x < before in match p with
    | (Some l1, Some l2) =>
        [ /\ l = NE_append l1 l2
        &    NE_last l1 < before <= NE_head l2
        ]

    | (Some l1, None) => l = l1 /\ NE_last l1 < before
    | (None, Some l2) => l = l2 /\ before <= NE_head l2
    | (None, None)    => False
    end
  }.

(** Return two sublists of [l] such that for every element in the first
    sublist, [f elem] return [true]. *)
Fixpoint usePosSpan (before : nat) `(H : NE_StronglySorted upos_lt l) :
  UsePosSublistsOf before H.
Proof.
  destruct l as [x|x xs] eqn:Heqe.
    destruct (x < before) eqn:Heqef.
      exists (Some (NE_Sing x), None).
      by split.
    exists (None, Some (NE_Sing x)).
      by split; try rewrite leqNgt Heqef.

  destruct (x < before) eqn:Heqef.
  - Case "x < before".
    destruct (usePosSpan before xs)
      as [[[l1| ] [l2| ]] Hsublists];
    try match goal with
          [ |- NE_StronglySorted _ _ ] => by inversion H
        end;
    inversion Hsublists;

    [ SCase "sublists = (Some, Some)";
      eexists (Some (NE_Cons x l1), Some l2)
    | SCase "sublists = (Some, None)";
      eexists (Some (NE_Cons x l1), None)
    | SCase "sublists = (None, Some)";
      eexists (Some (NE_Sing x), Some l2) ];
    simpl; split; f_equal; try assumption;
    intuition; constructor; assumption.

  - Case "before <= x".
    eexists (None, Some (NE_Cons x xs)).
    by split; try rewrite leqNgt Heqef.
Defined.

Lemma usePosSpan_spec (before : nat) `(H : NE_StronglySorted upos_lt l) :
  (usePosSpan before H).1 <> (None, None).
Proof. by case: (usePosSpan before H) => [[[?| ] [?| ]] ?]. Qed.

(** ** RangeDesc *)

(** A [RangeDesc] is built up from a set of use positions, and defines the
    inclusive range of those positions.  It can be extended, or split, but
    never shrunk.  Also, the non-empty list of use positions is not guaranteed
    to be in any order, and overlapping use positions are accepted, where the
    most recent one "wins".

    Although minimally there is at least one position fixing the beginning and
    end of the range, it's possible for the range to extend before or beyond
    the first and last use positions; for example, in the case of a use
    position ranging over the scope of a loop. *)

Record RangeDesc : Set := {
    rbeg : nat;
    rend : nat;                 (* 1 past the last use position *)
    ups  : NonEmpty UsePos
}.

(** ** Range *)

(** A [Range] constrains how a [RangeDesc] may be constructed, and maintains
    any invariants. *)

Inductive Range : RangeDesc -> Prop :=
  (** A [Range] built from a single use position covers that use positions, so
      that it begins at the use position, and ends one step after it (range
      ends are always exclusive). *)
  | R_Sing u : odd (uloc u) ->
    Range {| rbeg := uloc u
           ; rend := (uloc u).+1
           ; ups  := [::: u]
           |}

  (** A [Range] can be extended by adding a use position to the beginning.
      This means that they must be built up in reverse. *)
  | R_Cons u x : odd (uloc u) -> Range x
      -> forall (H : upos_lt u (NE_head (ups x))),
    Range {| rbeg := uloc u
           ; rend := rend x
           ; ups  := NE_Cons u (ups x)
           |}

  (** The address bounds of a [Range] may be arbitrarily set beyond its use
      positions.  This is useful when all of the use positions occur in a
      loop, for example, and you wish for the [Range] to bound the entire
      loop. *)
  | R_Extend x b' e' : Range x ->
    Range {| rbeg := minn b' (NE_head (ups x))
           ; rend := maxn e' (NE_last (ups x)).+1
           ; ups  := ups x
           |}.

Tactic Notation "Range_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "R_Sing"
  | Case_aux c "R_Cons"
  | Case_aux c "R_Extend"
  ].

Definition getRangeDesc `(r : Range d) := d.
Arguments getRangeDesc [d] r /.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition packRange `(r : Range d) := exist Range d r.
Arguments packRange [d] r /.

Notation RangeSig := { rd : RangeDesc | Range rd }.

Definition BoundedRange (pos : nat) :=
  { r : RangeSig | pos <= NE_head (ups r.1) }.

Definition transportBoundedRange `(Hlt : base < prev)
  (x : BoundedRange prev) : BoundedRange base.
  case: x => [r H].
  apply: exist.
  apply: r.
  exact/(leq_trans _ H)/ltnW.
Defined.

Definition range_lt {pos} (x y : BoundedRange pos) : Prop :=
  rend x.1.1 < rbeg y.1.1.

Lemma range_lt_transport {base prev} : forall x y (Hlt : base < prev),
  range_lt x y
    -> range_lt (transportBoundedRange Hlt x)
                (transportBoundedRange Hlt y).
Proof.
  move=> [x Hx] [y Hy] Hlt /=.
  by rewrite /range_lt.
Qed.

Lemma NE_Forall_transport {base prev} : forall r rs (Hlt : base < prev),
  NE_Forall (range_lt r) rs
    -> NE_Forall (range_lt (transportBoundedRange Hlt r))
                 (NE_map (transportBoundedRange Hlt) rs).
Proof.
  move=> [r Hr] rs Hlt.
  elim: rs => [x|x xs IHxs] H.
    constructor.
    move/NE_Forall_head in H.
    exact: range_lt_transport.
  constructor.
    move/NE_Forall_head in H.
    exact: range_lt_transport.
  rewrite -/NE_map.
  apply: IHxs.
  by inversion H.
Qed.

Definition SortedBoundedRanges (pos : nat) :=
  { rs : NonEmpty (BoundedRange pos) | NE_StronglySorted range_lt rs }.

Lemma Range_beg_bounded `(r : Range rd) : rbeg rd <= uloc (NE_head (ups rd)).
Proof. induction r; auto. simpl. apply leq_min. by []. Qed.

Lemma Range_end_bounded `(r : Range rd) : uloc (NE_last (ups rd)) < rend rd.
Proof. induction r; auto. apply ltn_max. by []. Qed.

Theorem Range_sorted `(r : Range rd) : NE_StronglySorted upos_lt (ups rd).
Proof.
  Range_cases (induction r) Case; simpl.
  - Case "R_Sing". constructor.
  - Case "R_Cons".
    pose (Range_beg_bounded r).
    constructor. apply IHr.
    inversion IHr as [? H2|? ? ? ? H2];
    rewrite <- H2 in *; simpl in *.
      by constructor.
    constructor. by [].
    apply NE_Forall_impl
      with (P := (fun y : UsePos => a < y)); last by [].
    move=> *.
    exact: (ltn_trans H0).
  - Case "R_Extend". by [].
Qed.

Theorem Range_all_odd `(r : Range rd) : NE_Forall (odd \o uloc) (ups rd).
Proof.
  Range_cases (induction r) Case; simpl.
  - Case "R_Sing". by constructor.
  - Case "R_Cons".
    constructor. auto. apply IHr.
  - Case "R_Extend". assumption.
Qed.

Lemma Range_bounded `(r : Range rd) : rbeg rd < rend rd.
Proof.
  Range_cases (induction r) Case; simpl in *.
  - Case "R_Sing". by [].
  - Case "R_Cons".
    pose (Range_beg_bounded r).
    pose (Range_end_bounded r).
    pose (Range_sorted r).
    inversion n as [? H2|? ? ? ? H2];
    rewrite <- H2 in *; simpl in *.
      exact: (ltn_trans H0).
    apply NE_Forall_last in H3.
    exact/(ltn_trans H0)/(ltn_trans H3).
  - Case "R_Extend".
    apply/ltn_min/ltn_max.
    by move/NE_StronglySorted_UsePos_impl: (Range_sorted r).
Qed.

Lemma Range_ups_bounded `(r : Range rd) : NE_head (ups rd) <= NE_last (ups rd).
Proof.
  Range_cases (induction r) Case; simpl in *.
  - Case "R_Sing".   by [].
  - Case "R_Cons".   apply ltnW in H0. exact: (leq_trans H0).
  - Case "R_Extend". by [].
Qed.

Definition Range_fromList `(us : NonEmpty UsePos) :
  NE_StronglySorted upos_lt us
    -> NE_Forall (odd \o uloc) us
    -> Range {| rbeg := uloc (NE_head us)
              ; rend := (uloc (NE_last us)).+1
              ; ups  := us |}.
Proof.
  elim: us => [a|a us IHus] Hsorted Hforall.
    by apply R_Sing; inv Hforall.
  inv Hsorted; inv Hforall; simpl in *.
  specialize (IHus H1 H4).
  apply (R_Cons H3 IHus). simpl.
  by inversion H2; auto.
Defined.

Definition Range_change_beg (b : nat) `(r : Range rd) :
  b <= NE_head (ups rd)
    -> Range {| rbeg := b; rend := rend r; ups := ups rd |}.
Proof.
  move=> Hlt.
  move: (R_Extend b (rend r) r) => /=.
  move: (Range_end_bounded r) => /= Hgt.
  by rewrite (minn_idPl Hlt) (maxn_idPl Hgt).
Defined.

Definition Range_change_end (e : nat) `(r : Range rd) :
  NE_last (ups rd) < e
    -> Range {| rbeg := rbeg r; rend := e; ups := ups rd |}.
Proof.
  move=> Hgt.
  move: (R_Extend (rbeg r) e r) => /=.
  move: (Range_beg_bounded r) => /= Hlt.
  by rewrite (minn_idPl Hlt) (maxn_idPl Hgt).
Defined.

Lemma NE_StronglySorted_UsePos_cons : forall u us,
  NE_StronglySorted upos_lt (NE_Cons u us) -> u < NE_head us.
Proof.
  move=> u us.
  invert; subst.
  by move/NE_Forall_head in H2.
Qed.

Definition Range_cat `(r1 : Range rd1) `(r2 : Range rd2) :
  rend r1 == rbeg r2
    -> Range {| rbeg := rbeg rd1
              ; rend := rend rd2
              ; ups  := NE_append (ups rd1) (ups rd2) |}.
Proof.
  move=> /eqP Heqe.

  move: (Range_all_odd r1).
  move: (Range_sorted r1).
  move: (Range_bounded r1).
  move: (Range_beg_bounded r1).
  move: (Range_end_bounded r1).
  move: (Range_beg_bounded r2).
  move: (Range_end_bounded r2).

  elim: (ups rd1) => [u|u us IHus] /= H1 H2 H3 H4 H5 Hsort Hodd.
    have Hlt': upos_lt u (NE_head (ups rd2)).
      rewrite {}Heqe in H3.
      exact: ltn_leq_trans H3 _.
    move/NE_Forall_head: Hodd => /= Hodd.
    have r := (R_Cons Hodd r2 Hlt').
    move: (R_Extend (rbeg rd1) (rend rd2) r) => /=.
    by rewrite (minn_idPl H4) (maxn_idPl H1).

  have Hlt: rbeg rd1 <= NE_head us.
    apply: (leq_trans H4 _).
    inversion Hsort; subst.
    move/NE_Forall_head in H7.
    exact/ltnW.
  have Hsort': NE_StronglySorted (fun x y : UsePos => upos_lt x y) us
    by inversion Hsort.
  have Hodd': NE_Forall (fun x : UsePos => (odd \o uloc) x) us
    by inversion Hodd.

  specialize (IHus H1 H2 H3 Hlt H5 Hsort' Hodd').

  have Hlt': upos_lt u (NE_head (NE_append us (ups rd2))).
    rewrite NE_head_append_spec.
    inversion Hsort; subst.
    by move/NE_Forall_head in H7.

  move/NE_Forall_head=> /= in Hodd.
  move: (R_Extend (rbeg rd1) (rend rd2)
                  (R_Cons Hodd IHus Hlt')) => /=.
  by rewrite NE_last_append_spec (minn_idPl H4) (maxn_idPl _).
Defined.

Definition RangeSigs_cons `(r : Range rd) (rs : NonEmpty RangeSig) :
  NonEmpty RangeSig.
Proof.
  case E: (rend rd == rbeg (NE_head rs).1);
    last exact: (NE_Cons (packRange r) rs).
  case: rs => [x|x xs] in E *;
  have r' := packRange (@Range_cat _ r _ x.2 E).
    exact: (NE_Sing r').
  exact: (NE_Cons r' xs).
Defined.

Definition Range_append_fst
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  forall rend, NE_last l1 < rend <= NE_head l2
    -> Range {| rbeg := rbeg0
              ; rend := rend
              ; ups  := l1 |}.
Proof.
  move=> rend /andP [Hlt1 Hlt2].
  move/NE_StronglySorted_inv_app: (Range_sorted r) => [Hsortedl _].
  move/NE_Forall_append: (Range_all_odd r) => /= [Hforall _].
  move: (@NE_head_append_spec) (Range_beg_bounded r) => /= -> Hbeg.
  move: (Range_fromList Hsortedl Hforall) => r'.
  move: (R_Extend rbeg0 rend r') => /=.
  by rewrite (minn_idPl Hbeg) (maxn_idPl Hlt1).
Defined.

Definition Range_append_snd
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  Range {| rbeg := uloc (NE_head l2)
         ; rend := rend0
         ; ups  := l2 |}.
Proof.
  move/NE_StronglySorted_inv_app: (Range_sorted r) => [_ Hsortedr].
  move/NE_Forall_append: (Range_all_odd r) => /= [_ Hforall].
  move: (@NE_last_append_spec) (Range_end_bounded r) => /= -> Hbeg.
  move: (Range_fromList Hsortedr Hforall) => r'.
  move: (R_Extend (NE_head l2) rend0 r') => /=.
  by rewrite (minnn _) (maxn_idPl Hbeg).
Defined.

Lemma Range_append_spec
  `(r : Range {| rbeg := rbeg0
               ; rend := rend0
               ; ups  := NE_append l1 l2 |}) :
  (uloc (NE_last l1)).+1 < uloc (NE_head l2).
Proof.
  move/NE_StronglySorted_impl_app: (Range_sorted r) => Hlt.
  move/NE_Forall_append: (Range_all_odd r) => /= [Hfal Hfar].
  apply NE_Forall_last in Hfal.
  apply NE_Forall_head in Hfar.
  rewrite /upos_lt in Hlt.
  apply ltn_odd.
  exact/andP. done.
Qed.

Definition rangesIntersect `(Range x) `(Range y) : bool :=
  if rbeg x < rbeg y
  then rbeg y < rend x
  else rbeg x < rend y.

Definition rangeIntersectionPoint `(xr : Range x) `(yr : Range y) : option nat :=
  if rangesIntersect xr yr
  then Some (minn (rbeg x) (rbeg y))
  else None.

Definition findRangeUsePos `(Range r) (f : UsePos -> bool) : option UsePos :=
  let fix go xs := match xs with
      | NE_Sing x    => if f x then Some x else None
      | NE_Cons x xs => if f x then Some x else go xs
      end in
  go (ups r).

Record DividedRange `(r : Range rd) (before : nat)
  `(r1 : Range rd1) `(r2 : Range rd2) : Prop := {
    _ : ups rd = NE_append (ups rd1) (ups rd2);
    _ : rend rd1 <= before <= rbeg rd2;
    _ : rbeg r == rbeg rd1;
    _ : rend r == rend rd2
}.

Definition SubRangesOf `(r : Range rd) (before : nat)
  (p : option RangeSig * option RangeSig) :=
  match p with
  | (Some r1, Some r2) => DividedRange r before r1.2 r2.2
  | (Some r1, None)    => [/\ ups rd = ups r1.1
                          ,   rbeg rd = rbeg r1.1
                          ,   rend r1.1 <= rend rd
                          &   rend r1.1 <= before ]
  | (None, Some r2)    => [/\ ups rd = ups r2.1
                          ,   rend rd = rend r2.1
                          ,   rbeg rd <= rbeg r2.1
                          &   before <= rbeg r2.1]
  | (None, None)       => False
  end.

Definition makeDividedRange `(r : Range rd) (before : nat)
  (l1 l2 : NonEmpty UsePos)
  (Heqe : ups rd = NE_append l1 l2)
  (Hu : NE_last l1 < before <= NE_head l2) :
  { p : option RangeSig * option RangeSig | SubRangesOf r before p }.
Proof.
  destruct rd; simpl in *; subst.
  exists (Some ({| rbeg := rbeg0
                 ; rend := before
                 ; ups  := l1 |}; Range_append_fst r Hu),
          Some ({| rbeg := uloc (NE_head l2)
                 ; rend := rend0
                 ; ups  := l2 |}; Range_append_snd r)).
  constructor => //=.
  move/andP: Hu => [*].
  by apply/andP; split.
Defined.

Section rangeSpan.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition rangeSpan (before : nat) `(r : Range rd) :
  { p : option RangeSig * option RangeSig | SubRangesOf r before p }.
Proof.
  case: (usePosSpan before (Range_sorted r)) => [[[o1 |] [o2 |]] [Heqe Hu]] /=.
  - Case "(Some, Some)".
    exact: (makeDividedRange r Heqe Hu).
  - Case "(Some, None)".
    pose rd' := {| rbeg := rbeg rd
                 ; rend := minn before (rend rd)
                 ; ups  := ups rd |}.
    eexists (Some (exist Range rd' _), None).
    split => //=.
      exact/geq_minr.
    exact/geq_minl.
  - Case "(None, Some)".
    pose rd' := {| rbeg := maxn before (rbeg rd)
                 ; rend := rend rd
                 ; ups  := ups rd |}.
    eexists (None, Some (exist Range rd' _)).
    split => //=.
      exact/leq_maxr.
    exact/leq_maxl.

  Grab Existential Variables.
  - rewrite -Heqe in Hu.
    rewrite /rd'.
    case E: (before <= rbeg rd).
      rewrite (maxn_idPr E).
      replace {| rbeg := rbeg rd; rend := rend rd; ups := ups rd |}
        with rd => //.
      by destruct rd.
    have H: rbeg rd <= before.
      move/negbT in E.
      rewrite -ltnNge in E.
      exact/ltnW.
    rewrite (maxn_idPl H).
    exact: (Range_change_beg r Hu).
  - rewrite -Heqe in Hu.
    rewrite /rd'.
    case E: (before <= rend rd).
      rewrite (minn_idPl E).
      exact: (Range_change_end r Hu).
    have H: rend rd <= before.
      move/negbT in E.
      rewrite -ltnNge in E.
      exact/ltnW.
    rewrite (minn_idPr H).
    replace {| rbeg := rbeg rd; rend := rend rd; ups := ups rd |}
      with rd => //.
    by destruct rd.
Defined.

End rangeSpan.

Lemma rangeSpan_spec (before : nat) `(r : Range rd) :
  forall res, res = rangeSpan before r -> res.1 <> (None, None).
Proof. case: rd => _ _ _ _ [[[_| ] [_| ]] _] _ // in r *. Qed.

Module RangeTests.

Module Import E := NonEmptyNotations.
Module Import U := UsePosNotations.

Open Scope list_scope.

Fixpoint generateRangeBuilder
  (start index : nat) (Hodd : odd start) {struct index} :
  { rd : RangeDesc | Range rd & uloc (NE_head (ups rd)) = start }.
Proof.
  destruct index as [|index].
    pose (@R_Sing (|start|) Hodd).
    exists r. apply r. auto.
  pose (generateRangeBuilder start.+2 index) as r.
  destruct r as [rd r Hr].
    assert (upos_lt (|start|) (|start.+2|)) as Hlt.
      by unfold upos_lt; auto.
    by rewrite odd_succ_succ.
  have: (|start|) < NE_head (ups rd) by rewrite Hr.
  move=> Hlt.
  pose (@R_Cons (|start|) rd Hodd r Hlt) as r'.
  exists r'. apply r'. auto.
Defined.

Definition generateRange (start finish : nat) (Hodd : odd start)
  (H : start < finish) : RangeSig.
Proof.
  pose (@generateRangeBuilder start ((finish - start)./2 - 1) Hodd).
  destruct s. exists x. apply r.
Defined.

Definition testRangeSpan (start finish : nat) (Hodd : odd start)
  (H : start < finish) (before : nat) :=
  let r := (rangeSpan before (generateRange Hodd H).2).1 in
  (option_map (fun x => ups x.1) (fst r),
   option_map (fun x => ups x.1) (snd r)).

Example lt_1_9 : 1 < 9. done. Qed.

Example testRangeSpan_1 :
  testRangeSpan odd_1 lt_1_9 1 = (None, Some [(|1|); (|3|); (|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_2 :
  testRangeSpan odd_1 lt_1_9 3 = (Some [::: (|1|)], Some [(|3|); (|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_3 :
  testRangeSpan odd_1 lt_1_9 5 = (Some [(|1|); (|3|)], Some [(|5|); (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_4 :
  testRangeSpan odd_1 lt_1_9 7 = (Some [(|1|); (|3|); (|5|)], Some [::: (|7|)]).
Proof. reflexivity. Qed.

Example testRangeSpan_5 :
  testRangeSpan odd_1 lt_1_9 9 = (Some [(|1|); (|3|); (|5|); (|7|)], None).
Proof. reflexivity. Qed.

End RangeTests.
