Require Import LinearScan.Lib.
Require Import LinearScan.Ltac.
Require Import LinearScan.Range.
Require Import LinearScan.UsePos.

Require Import Coq.Sorting.Sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Record ProtoRange (prBound : nat) := {
  prBeg        : nat;
  prBegOdd     : odd prBeg;
  prEnd        : nat;
  prOrdered    : prBeg < prEnd;
  prUseLocs    : seq UsePos;
  prUseSorted  : StronglySorted upos_lt prUseLocs;
  prUseBounded : all (fun u => prBound <= uloc u < prEnd) prUseLocs
}.

Definition emptyProtoRange (b e : nat) (Hodd : odd b) (Hlt : b < e) :
  ProtoRange e :=
  {| prBeg        := b
   ; prBegOdd     := Hodd
   ; prEnd        := e
   ; prOrdered    := Hlt
   ; prUseLocs    := [::]
   ; prUseSorted  := SSorted_nil upos_lt
   ; prUseBounded := all_nil (fun u => e <= uloc u < e)
   |}.

(*
Definition catProtoRanges `(x : ProtoRange blimx) `(y : ProtoRange blimy) :
  prEnd x <= prBeg y -> ProtoRange blimx.
Proof.
  move=> H.
  case: x => [begx Hbegx endx Hordx usx Hsortx Hbndx] in H *.
  case: y => [begy Hbegy endy Hordy usy Hsorty Hbndy] in H *.
  rewrite /= in H.

  move: Hordx Hordy => /andP [Hordx1 Hordx2] /andP [Hordy1 Hordy2].

  apply:
    {| prBeg        := begx
     ; prBegOdd     := Hbegx
     ; prEnd        := endy
     ; prUseLocs    := usx ++ usy |} => //.

  - apply/andP; split=> //.
    apply: (leq_trans Hordx2 _).
    apply: (leq_trans H _).
    exact: (leq_trans Hordy1 _).

  - elim E: usx => [|u us IHus] //= in Hsortx Hbndx *.
    constructor.
      apply: IHus=> //.
        by inversion Hsortx.
      by move/andP: Hbndx => [? ?].
    apply/Forall_append; split.
      by inversion Hsortx; subst.
    inversion Hsortx; subst; clear Hsortx.
    case: usy => //= [y ys] in Hsorty Hbndy IHus *.
    move/andP: Hbndx => [/andP [H4 H5] H6].
    move/andP: Hbndy => [/andP [H7 H8] H9].
    constructor.
      apply: (ltn_trans H5 _).
      apply: (leq_ltn_trans H _).
      apply: (leq_ltn_trans Hordy1 _).
      admit.
    apply/Forall_all.
    move/allP in H9.
    apply/allP.
    move=> x Hin.
    move: H9 => /(_ x Hin) /andP [H10 H11].
    apply: (ltn_trans H5 _).
    apply: (leq_ltn_trans H _).
    apply: (leq_ltn_trans Hordy1 _).
      by apply: (ltn_leq_trans H4 _).

  - rewrite all_cat.
    apply/andP; split.
      exact: Husx.
    apply: (all_leq Husy).
    apply: (leq_trans _ Hbby).
    apply: (leq_trans _ H).
    move/allP in Husx.
    move/allP in Hebx.
    exact/ltnW.

  - rewrite all_cat.
    apply/andP; split;
      last exact: Heby.
    apply: (all_ltn Hebx).
    apply: (leq_trans H _).
    exact/ltnW.
Defined.
*)

Definition transportProtoRange
  `(Hlt : base < prev) `(x : ProtoRange prev) : ProtoRange base.
  case: x => [begx ? ? H ? ? Hbound] /= in Hlt *.
  apply: (@Build_ProtoRange _ begx) => //.
  by match_all.
Defined.

Definition proto_lt {blimx blimy}
  (x : ProtoRange blimx) (y : ProtoRange blimy) : Prop :=
  prEnd x < prBeg y.

(*
Lemma proto_lt_spec `(x : ProtoRange prev) `(y : ProtoRange prev)
  `(Hlt : prBeg x <= base < prev) :
  proto_lt x y -> prBeg y <= base < prev.
Proof.
  rewrite /proto_lt.
  case: x => /= [? _ ? ? ? _ _] in Hlt *.
  case: y => /= [? _ ? ? ? _ _] in Hlt *.
  move=> ?.
  by ordered.
Qed.
*)

Lemma proto_lt_transport `(Hlt : base < prev)
  (x : ProtoRange prev) (y : ProtoRange prev) (Hpr : proto_lt x y) :
  proto_lt (transportProtoRange Hlt x)
           (transportProtoRange Hlt y).
Proof.
  destruct x; destruct y.
  rewrite /proto_lt /transportProtoRange //=.
Qed.

Lemma NE_Forall_transport {base prev} :
  forall (Hlt : base < prev) (r : ProtoRange prev) rs,
  NE_Forall (proto_lt r) rs
    -> NE_Forall (proto_lt (transportProtoRange Hlt r))
                 (NE_map (transportProtoRange Hlt) rs).
Proof.
  move=> Hlt r rs.
  elim: rs => [x|x xs IHxs] H.
    constructor.
    move/NE_Forall_head in H.
    exact: proto_lt_transport.
  constructor.
    move/NE_Forall_head in H.
    exact: proto_lt_transport.
  rewrite -/NE_map.
  apply: IHxs.
  by inversion H.
Qed.

Definition SortedProtoRanges (pos : nat) :=
  { rs : NonEmpty (ProtoRange pos) | NE_StronglySorted proto_lt rs }.

Definition transportSortedProtoRanges {base : nat} `(Hlt : base < prev)
  (sr : SortedProtoRanges prev) : SortedProtoRanges base.
Proof.
  case: sr => [rs Hsort].
  exists (NE_map (transportProtoRange Hlt) rs).
  elim: rs => [r|r rs IHrs] /= in Hsort *.
    by constructor.
  constructor; inversion Hsort; subst.
    exact: IHrs.
  exact: NE_Forall_transport.
Defined.

Require Import LinearScan.Interval.

Definition Interval_fromSortedProtoRanges {pos} (vid : nat)
  (sr : SortedProtoRanges pos) :
  (* Interval {| ivar := vid *)
  (*           ; ibeg := prBeg (NE_head sr.1) *)
  (*           ; iend := prEnd (NE_last sr.1) *)
  (*           ; iknd := Whole *)
  (*           ; rds  := NE_map sval sr.1 |} *)
  IntervalSig.
Proof.
Admitted.
  (* move: sr => [rs Hsort]. *)
  (* elim: rs => [r|r rs /= IHrs] /= in Hsort *. *)
  (*   move: (I_Sing vid Whole r.1.2) => {Hsort}. *)
  (*   by move: r => [[rd r] ?]. *)
  (* apply NE_StronglySorted_inv in Hsort. *)
  (* move: Hsort => [Hsort Hall]. *)
  (* move/IHrs: Hsort => {IHrs} IHrs. *)
  (* have Hlt: rend r.1.1 < rbeg (NE_head (NE_map sval rs)).1. *)
  (*   move/NE_Forall_head in Hall. *)
  (*   by rewrite NE_map_head. *)
  (* rewrite -NE_map_head -NE_map_last in IHrs. *)
  (* move: (I_Cons (i:=vid) (knd:=Whole) IHrs Hlt). *)
  (* by rewrite NE_map_last. *)
(* Defined. *)
