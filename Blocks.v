Require Import Allocate.
Require Import Lib.
Require Import NonEmpty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MLinearScan (M : Machine).

Include MAllocate M.
Import MLS.MS.
Import M.

(** * Block *)

(** An incoming [Block] is really a conceptual "set" of use-positions
    ([UsePos]), involving several variables and/or registers -- or none (in
    which case the allocator need not consider it, except to identify the
    beginning and ending of loops). *)

Section Block.

Variable baseType : Set.
Variable maxVirtReg : nat.

Definition SomeVar := (fin maxVirtReg + fin maxReg)%type.

Record Block : Type := {
    original    : baseType;
    loopBound   : bool;
    regRequired : bool;
    refCount    : nat;
    references  : Vec SomeVar refCount
}.

Definition boundedRange (pos : nat) :=
  { rd : RangeDesc | Range rd & pos <= NE_head (ups rd) }.

Arguments boundedRange pos /.

Definition boundedTriple (pos : nat) :=
  (option nat * option nat * option (boundedRange pos))%type.

Arguments boundedTriple pos /.

Record boundedRangeVec (pos : nat) := {
  vars : Vec (boundedTriple pos) maxVirtReg;
  regs : Vec (boundedTriple pos) maxReg
}.

Lemma transportVecBounds (pos m : nat) `(Hlt : pos < n) :
  Vec (boundedTriple n) m -> Vec (boundedTriple pos) m.
Proof.
  elim=> [|[p [[rd r Hr]| ]] n' v' IHv].
  - by constructor.
  - constructor; last exact: IHv.
    split. apply p.
    apply Some.
    exists rd. apply r.
    apply ltnW in Hlt.
    exact: (leq_trans Hlt).
  - constructor; last exact: IHv.
    split. apply p.
    exact: None.
Qed.

Lemma boundedTransport (pos : nat) `(Hlt : pos < n) :
  boundedRangeVec n -> boundedRangeVec pos.
Proof.
  case=> Hvars Hregs.
  split; exact: (transportVecBounds Hlt).
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

Section applyList.

Import EqNotations.

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

End applyList.

Definition emptyBoundedRangeVec (n : nat) : boundedRangeVec n.+2 :=
  {| vars := vconst (None, None, None) variables_exist
   ; regs := vconst (None, None, None) registers_exist
   |}.

(* jww (2014-11-04): Still to be done:

   Register constraints at method calls are also modeled using fixed
   intervals: Because all registers are destroyed when the call is executed,
   ranges of length 1 are added to all fixed intervals at the call
   site. Therefore, the allocation pass cannot assign a register to any
   interval there, and all intervals are spilled before the call. *)

Definition handleBlock (b : Block) (pos : nat) (Hodd : odd pos)
  (rest : boundedRangeVec pos.+2) : boundedRangeVec pos :=
  (** If the instruction at this position begins or ends a loop, extend the
      current range so that it starts at, or end at, this boundary. *)
  let liftOr f mx y :=
      Some (match mx with Some x => f x y | None => y end) in
  let savingBound x :=
      if loopBound b
      then let: (mb, me, r) := x in
           (liftOr minn mb pos, liftOr maxn me pos, r)
      else x in

  (** Add a new use position to the beginning of the current range. *)
  let consr (x : boundedTriple pos.+2) : boundedTriple pos :=
      let upos := Build_UsePos pos (regRequired b) in
      @withRanges pos Hodd _ upos refl_equal pos.+2 (ltnSSn _) x in

  let restVars' := vmap savingBound (vars rest) in
  let restRegs' := vmap savingBound (regs rest) in
  match references b with
  | V.nil => boundedTransport (ltnSSn _)
               {| vars := restVars'; regs := restRegs' |}

  | V.cons (inl v) _ vs =>
    let x := consr (vnth restVars' v) in
    let restVars'' :=
        replace (transportVecBounds (ltnSSn _) restVars') v x in
    let restRegs'' := transportVecBounds (ltnSSn _) restRegs' in
    {| vars := restVars''; regs := restRegs'' |}

  | V.cons (inr r) _ vs =>
    let x := consr (vnth restRegs' r) in
    let restVars'' := transportVecBounds (ltnSSn _) restVars' in
    let restRegs'' :=
        replace (transportVecBounds (ltnSSn _) restRegs') r x in
    {| vars := restVars''; regs := restRegs'' |}
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
            | None        => packRange r
            | Some (b, e) => packRange (R_Extend b e r)
            end)
  end.

(** The list of blocks is processed in reverse, so that the resulting
    sub-lists are also in order. *)
Definition processBlocks (blocks : NonEmpty Block) :
  Vec (option RangeSig) maxVirtReg * Vec (option RangeSig) maxReg :=
  let: {| vars := vars'; regs := regs' |} :=
       applyList blocks emptyBoundedRangeVec handleBlock in
  (vmap extractRange vars', V.map extractRange regs').

Definition determineIntervals (blocks : NonEmpty Block) : ScanStateSig :=
  let mkint (ss : ScanStateSig) (mx : option RangeSig)
            (f : forall sd, ScanState sd -> forall d, Interval d
                   -> ScanStateSig) :=
      let: (exist sd st) := ss in
      match mx with
      | Some (exist _ r) => f _ st _ (I_Sing r)
      | None => ss
      end in

  let handleVar ss mx := mkint ss mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i) in

  let: (varRanges, regRanges) := processBlocks blocks in
  let regs := vmap (fun mr =>
                if mr is Some r
                then Some (packInterval (I_Sing r.2))
                else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  vfoldl handleVar s2 varRanges.

Definition allocateRegisters (blocks : NonEmpty Block) : ScanStateDesc :=
  proj1_sig (uncurry_sig linearScan (determineIntervals blocks)).

End Block.

End MLinearScan.