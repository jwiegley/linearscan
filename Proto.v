Require Import LinearScan.Lib.
(* Require Import LinearScan.Machine. *)
Require Import LinearScan.Range.
(* Require Import LinearScan.ScanState. *)
(* Require Import LinearScan.Graph. *)

Require Import Coq.Sorting.Sorted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Record ProtoRange (prLim : nat) := {
  prBeg        : nat;
  prBegOdd     : odd prBeg;
  prBegLim     : prLim <= prBeg;
  prEnd        : nat;
  prEndEven    : ~~ odd prEnd;
  prOrdered    : prBeg < prEnd;
  prUseLocs    : seq UsePos;
  prUseSorted  : StronglySorted upos_lt prUseLocs;
  prBegBounded : all (fun u => prBeg <= uloc u) prUseLocs;
  prEndBounded : all (fun u => uloc u < prEnd) prUseLocs
}.

Definition catProtoRanges `(x : ProtoRange blimx) `(y : ProtoRange blimy) :
  prEnd x <= prBeg y -> ProtoRange blimx.
Proof.
  move=> H.
  case: x => [begx Hbegx Hblimx endx Hendx
              Hordx usx Husx Hbbx Hebx] in H *.
  case: y => [begy Hbegy Hblimy endy Hendy
              Hordy usy Husy Hbby Heby] in H *.
  rewrite /= in H.

  apply:
    {| prBeg        := begx
     ; prBegOdd     := Hbegx
     ; prBegLim     := Hblimx
     ; prEnd        := endy
     ; prEndEven    := Hendy
     ; prOrdered    := _
     ; prUseLocs    := usx ++ usy
     ; prUseSorted  := _
     ; prBegBounded := _
     ; prEndBounded := _ |}.

  - apply: (ltn_leq_trans Hordx _).
    apply: (leq_trans _ Hordy).
    exact/leqW.

  - elim E: usx => [|u us IHus] //= in Husx Hbbx Hebx *.
    constructor.
      apply: IHus.
      + by inversion Husx.
      + by move/andP: Hbbx => [? ?].
      + by move/andP: Hebx => [? ?].
    apply/Forall_append; split.
      by inversion Husx; subst.
    inversion Husx; subst.
    apply/Forall_all.
    apply: (all_leq_ltn Hbby).
    move/andP: Hebx => [H4 H5].
    by apply: (ltn_leq_trans H4 _).

  - rewrite all_cat.
    apply/andP; split.
      exact: Hbbx.
    apply: (all_leq Hbby).
    apply: (leq_trans _ H).
    exact/ltnW.

  - rewrite all_cat.
    apply/andP; split;
      last exact: Heby.
    apply: (all_ltn Hebx).
    apply: (leq_trans H _).
    exact/ltnW.
Defined.

Definition transportProtoRange `(Hlt : base < prev)
  (x : ProtoRange prev) : ProtoRange base.
  case: x => begx ? Hlim ? ? ? ? ? H ?.
  apply: (@Build_ProtoRange _ begx) => //.
  apply: (leq_trans _ Hlim).
  exact/ltnW.
Defined.

Definition proto_lt {blimx blimy}
  (x : ProtoRange blimx) (y : ProtoRange blimy) : Prop :=
  prEnd x < prBeg y.

Lemma proto_lt_transport `(Hlt : base < prev)
  `(x : ProtoRange prev) `(y : ProtoRange prev) :
  proto_lt x y
    -> proto_lt (transportProtoRange Hlt x)
                (transportProtoRange Hlt y).
Proof.
  move=> H /=.
  destruct x; destruct y.
  rewrite /proto_lt /transportProtoRange //=.
Qed.

Lemma NE_Forall_transport {base prev} : forall r rs (Hlt : base < prev),
  NE_Forall (proto_lt r) rs
    -> NE_Forall (proto_lt (transportProtoRange Hlt r))
                 (NE_map (transportProtoRange Hlt) rs).
Proof.
  move=> r rs Hlt.
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
