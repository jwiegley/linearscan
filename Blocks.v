Require Import Allocate.
Require Import Lib.

Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MLinearScan (M : Machine).
Include MAllocate M.

Import EqNotations.

(** * Program graphs *)

Definition VirtReg := nat.

(** * Block *)

(** An incoming [Block] is really a conceptual "set" of use-positions
    ([UsePos]), involving several variables and/or registers -- or none (in
    which case the allocator need not consider it, except to identify the
    beginning and ending of loops). *)

Section Block.

Variable baseType : Set.
Variable maxVirtReg : nat.

(* jww (2014-10-18): I do not know how to handle explicit register mentions in
   the input blocks yet. *)
(* Definition SomeVar := (fin maxVirtReg + fin maxReg)%type. *)
Definition SomeVar := (fin maxVirtReg)%type.

Record Block : Type := {
    original    : baseType;
    loopBound   : bool;
    regRequired : bool;
    refCount    : nat;
    references  : Vec SomeVar refCount
}.

Definition boundedRange (pos : nat) :=
  { rd : RangeDesc | Range rd & pos <= NE_head (ups rd) }.

Definition boundedTriple (pos : nat) :=
  (option nat * option nat * option (boundedRange pos))%type.

Definition boundedRangeVec (pos : nat) := Vec (boundedTriple pos) maxVirtReg.

Lemma boundedTransport (pos : nat) `(Hlt : pos < n) :
  boundedRangeVec n -> boundedRangeVec pos.
Proof.
  rewrite /boundedRangeVec /boundedTriple /boundedRange.
  elim=> [|[p [[rd r Hr]| ]] n' v' IHv].
  - by constructor.
  - constructor; last exact: IHv.
    split. apply p.
    apply Some.
    exists rd. apply r.
    by abstract ssomega.
  - constructor; last exact: IHv.
    split. apply p.
    exact: None.
Qed.

Definition boundedSing (upos : UsePos) (Hodd : odd upos) : boundedRange upos.
Proof. eexists; [ by exact: R_Sing | by [] ]. Defined.

Definition boundedCons (upos : UsePos) (Hodd : odd upos)
  `(Hlt : upos < n) : boundedRange n -> boundedRange upos.
Proof.
  move=> [rd r Hr].
  eexists; [ apply/R_Cons => //; exact: (ltn_leq_trans Hlt) | by [] ].
Defined.

Lemma withRanges (pos : nat) (Hodd : odd pos) (req : bool)
  (upos : UsePos) (Heqe : upos = Build_UsePos pos req)
  `(Hlt : upos < n) : boundedTriple n -> boundedTriple (uloc upos).
Proof.
  move=> [p [[rd r Hr]| ]]; last first.
    split. exact: p.
    apply/Some/boundedSing.
    by rewrite Heqe /=.
  split. exact: p.
  apply/Some/(@boundedCons upos).
  - by rewrite Heqe /=.
  - exact: n.
  - exact: Hlt.
  - by exists rd.
Defined.

Definition applyList (bs : NonEmpty Block)
  (base : forall l, boundedRangeVec l.+2)
  (f : Block -> forall (pos : nat) (Hodd : odd pos),
         boundedRangeVec pos.+2 -> boundedRangeVec pos)
   : boundedRangeVec 1 :=
  let fix go i Hoddi bs :=
      match bs with
        | NE_Sing x => f x i Hoddi (base i)
        | NE_Cons x xs =>
          f x i Hoddi (go i.+2 (rew <- (odd_succ_succ _) in Hoddi) xs)
      end in
  go 1 (RangeTests.odd_1) bs.

Definition emptyBoundedRangeVec (n : nat) : boundedRangeVec n.+2 :=
  V.const (None, None, None) maxVirtReg.

Definition handleBlock (b : Block) (pos : nat) (Hodd : odd pos)
  (rest : boundedRangeVec pos.+2) : boundedRangeVec pos :=
  let liftOr f mx y :=
      Some (match mx with Some x => f x y | None => y end) in
  let savingBound x :=
      if loopBound b
      then let: (mb, me, r) := x in
           (liftOr minn mb pos, liftOr maxn me pos, r)
      else x in
  let consr (x : boundedTriple pos.+2) : boundedTriple pos :=
      let upos := Build_UsePos pos (regRequired b) in
      @withRanges pos Hodd _ upos refl_equal pos.+2 (ltnSSn _) x in
  let rest' := V.map savingBound rest in
  match references b with
  | V.nil => boundedTransport (ltnSSn _) rest'
  | V.cons v _ vs =>
    let x := consr (V.nth rest' (to_vfin v)) in
    V.replace (boundedTransport (ltnSSn _) rest') (to_vfin v) x
  (* jww (2014-10-18): See note above. *)
  (* | V.cons (inr r) _ vs => undefined *)
  end.

Definition extractRange (x : boundedTriple 1) : option RangeSig :=
  let: (mb, me, mr) := x in
  match mr with
  | None => None
  | Some (exist2 rd r _) =>
    let mres := match (mb, me) with
      | (None, None)     => None
      | (Some b, None)   => Some (b, rend rd)
      | (None, Some e)   => Some (rbeg rd, e)
      | (Some b, Some e) => Some (b, e)
      end in
    Some (match mres with
          | None => exist Range rd r
          | Some (b, e) =>
            let r' := R_Extend b e r in
            exist Range (getRangeDesc r') r'
          end)
  end.

(** The list of blocks is processed in reverse, so that the resulting
    sub-lists are also in order. *)
Definition processBlocks (blocks : NonEmpty Block) :
  Vec (option RangeSig) maxVirtReg :=
  let res := applyList blocks emptyBoundedRangeVec handleBlock in
  V.map extractRange res.

Definition determineIntervals (blocks : NonEmpty Block) :
  { sd : ScanStateDesc | ScanState sd } :=
  let mkint (mx : option RangeSig) : option IntervalSig := match mx with
      | None => None
      | Some (exist _ r) =>
        let i := I_Sing r in
        Some (exist Interval (getIntervalDesc i) i)
      end in
  let go (ss : ScanStateSig) (mx : option RangeSig) : ScanStateSig :=
      match mkint mx with
      | None => ss
      | Some (exist idesc i) =>
        let: (exist sd st) := ss in
        let st' := ScanState_newUnhandled st i in
        exist ScanState (getScanStateDesc st') st'
      end in
  let s0 := ScanState_nil in
  let s1 : ScanStateSig := exist ScanState (getScanStateDesc s0) s0 in
  let ranges := processBlocks blocks in
  (* jww (2014-10-19): I need to sort the ranges by starting position, and
     then make this ordering a requirement for building up the unhandled
     intervals in the [ScanState]. *)
  V.fold_left go s1 ranges.

Definition allocateRegisters (blocks : NonEmpty Block) : ScanStateDesc :=
  proj1_sig (uncurry_sig linearScan (determineIntervals blocks)).

End Block.

End MLinearScan.