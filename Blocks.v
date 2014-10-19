Require Import Allocate.
Require Import Fin.
Require Import Lib.
Require Import Machine.
Require Import NonEmpty.
Require Import Range.
Require Import Vector.

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

Record Block := {
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

Definition boundedTransport (pos : nat) `(Hlt : pos < n)
  : boundedRangeVec n -> boundedRangeVec pos.
Proof.
  rewrite /boundedRangeVec /boundedTriple /boundedRange.
  elim=> [|[p [[rd r Hr]| ]] n' v' IHv].
  - by constructor.
  - constructor; last by apply IHv.
    split. apply p.
    apply Some.
    exists rd. apply r.
    by abstract ssomega.
  - constructor; last by apply IHv.
    split. apply p.
    by apply None.
Defined.

Definition boundedSing (upos : UsePos) (Hodd : odd upos) : boundedRange upos.
Proof. eexists; [ by apply/R_Sing | by [] ]. Defined.

Definition boundedCons (upos : UsePos) (Hodd : odd upos)
  `(Hlt : upos < n) : boundedRange n -> boundedRange upos.
Proof.
  move=> [rd r Hr].
  eexists; [ by apply/R_Cons => //; apply (ltn_leq_trans Hlt) | by [] ].
Defined.

Lemma withRanges (pos : nat) (Hodd : odd pos) (req : bool)
  (upos : UsePos) (Heqe : upos = Build_UsePos pos req)
  `(Hlt : upos < n) : boundedTriple n -> boundedTriple (uloc upos).
Proof.
  move=> [p [[rd r Hr]| ]]; last first.
    split. by apply p.
    apply/Some/boundedSing.
    by rewrite Heqe /=.
  split. by apply p.
  apply/Some/(@boundedCons upos).
  - by rewrite Heqe /=.
  - by apply n.
  - by apply Hlt.
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

(** The list of blocks is processed in reverse, so that the resulting
    sub-lists are also in order. *)
Definition processBlocks (blocks : NonEmpty Block)
  : Vec (option RangeSig) maxVirtReg :=
  let liftOr f mx y :=
      Some (match mx with Some x => f x y | None => y end) in

  let handle b pos (Hodd : odd pos) (rest : boundedRangeVec pos.+2)
      : boundedRangeVec pos :=
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
        let x := consr (V.nth rest' v) in
        V.replace (boundedTransport (ltnSSn _) rest') v x
      (* jww (2014-10-18): See note above. *)
      (* | V.cons (inr r) _ vs => undefined *)
      end in

  let res  := applyList blocks emptyBoundedRangeVec handle in
  V.map (fun x =>
    let: (mb, me, mr) := x in
    match mr with
    | None => None
    | Some (exist2 rd r _) => Some (exist _ rd r)
      (* match (mb, me) with *)
      (* | (None, None) => Some (exist _ rd r) *)
      (* end *)
    end) res.

Definition determineIntervals (blocks : NonEmpty Block)
  : { sd : ScanStateDesc | ScanState sd }.
Admitted.

Definition allocateRegisters (blocks : NonEmpty Block)
  : ScanStateDesc :=
  proj1_sig (uncurry_sig linearScan (determineIntervals blocks)).

End Block.

End MLinearScan.