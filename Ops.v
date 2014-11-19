Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.NonEmpty.
Require Import LinearScan.Range.
Require Import LinearScan.Vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MOps (Mach : Machine).

Import Mach.

Definition PhysReg := 'I_maxReg.

(** * Block *)

(** An incoming [Block] is really a conceptual "set" of use-positions
    ([UsePos]), involving several variables and/or registers -- or none (in
    which case the allocator need not consider it, except to identify the
    beginning and ending of loops). *)

Section Ops.

Variable opType : Set.

(* SomeVar identifies a variable or register use.  If it is a variable use, an
   index is given with a boolean to indicate if is required to be in a
   register at that point.  If it is a register use, this reserves the
   register for that use position. *)
Definition SomeVar := ((nat * bool) + PhysReg)%type.

Inductive OperationKind :=
  | OILoopBegin
  | OILoopEnd
  | OICall of seq PhysReg.

Section Eqok.

Variables (T : eqType) (x0 : T).
Implicit Type s : OperationKind.

Fixpoint eqok s1 s2 {struct s2} :=
  match s1, s2 with
  | OILoopBegin, OILoopBegin => true
  | OILoopEnd,   OILoopEnd   => true
  | OICall rs1,  OICall rs2  => rs1 == rs2
  | _, _ => false
  end.

Lemma eqokP : Equality.axiom eqok.
Proof.
  move.
  case=> [||l1]; case => [||l2];
  try constructor; try by [].
  case: (l1 =P l2) => /= [<-|neqx].
    rewrite eq_refl.
    by constructor.
  move/eqP in neqx.
  move/negbTE in neqx.
  rewrite neqx.
  constructor.
  move/eqP in neqx.
  move=> H.
  contradiction neqx.
  congruence.
Qed.

Canonical ok_eqMixin := EqMixin eqokP.
Canonical ok_eqType := Eval hnf in EqType OperationKind ok_eqMixin.

Lemma eqokE : eqok = eq_op. Proof. by []. Qed.

Definition OperationKind_eqType (A : eqType) :=
  Equality.Pack ok_eqMixin OperationKind.

End Eqok.

Definition OperationInfo :=
  (seq OperationKind * { refCount : nat & Vec SomeVar refCount })%type.

Definition OpPair := (opType * OperationInfo)%type.
Definition OpList := NonEmpty OpPair.
Definition OpListFromBlock block := block -> OpList.

Inductive AllocationInfo :=
  | AllocatedRegs of opType & (nat -> PhysReg).

Definition boundedRange (pos : nat) :=
  { rd : RangeDesc | Range rd & pos <= NE_head (ups rd) }.

Definition boundedTriple (pos : nat) :=
  (option nat * option nat * option (boundedRange pos))%type.

Record boundedRangeVec (pos : nat) := {
  vars : seq (boundedTriple pos);
  regs : Vec (boundedTriple pos) maxReg
}.

Definition transportTriple {pos : nat} `(Hlt : pos < n)
  (x : boundedTriple n) : boundedTriple pos :=
  let: (o1, o2, mo) := x in match mo with
    | Some o => let: exist2 rd r H := o in
      (o1, o2, Some (exist2 Range _ rd r (ltnW (leq_trans Hlt H))))
    | None => (o1, o2, None)
    end.

Definition transportBounds (pos : nat) `(Hlt : pos < n) :
  seq (boundedTriple n) -> seq (boundedTriple pos) :=
  map (@transportTriple pos n Hlt).

Definition transportVecBounds (pos m : nat) `(Hlt : pos < n) :
  Vec (boundedTriple n) m -> Vec (boundedTriple pos) m :=
  vmap (@transportTriple pos n Hlt).

Definition boundedTransport (pos : nat) `(Hlt : pos < n)
  (xs : boundedRangeVec n) : boundedRangeVec pos :=
  {| vars := transportBounds    Hlt (vars xs)
   ; regs := transportVecBounds Hlt (regs xs)
   |}.

Definition boundedSing (upos : UsePos) (Hodd : odd upos) : boundedRange upos :=
  let r := R_Sing Hodd in exist2 Range _ r r (leqnn upos).

Definition boundedCons (upos : UsePos) (Hodd : odd upos)
  `(Hlt : upos < n) (xs : boundedRange n) : boundedRange upos :=
  let: exist2 rd r H := xs in
  let r' := R_Cons Hodd r (ltn_leq_trans Hlt H) in
  exist2 Range _ r' r' (leqnn upos).

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

Definition applyList (ops : OpList)
  (base : forall l, boundedRangeVec l.+2)
  (f : OpPair -> forall (pos : nat) (Hodd : odd pos),
         boundedRangeVec pos.+2 -> boundedRangeVec pos)
   : boundedRangeVec 1 :=
  let fix go i Hoddi bs :=
      match bs with
        | NE_Sing x => f x i Hoddi (base i)
        | NE_Cons x xs =>
          f x i Hoddi (go i.+2 (rew <- (odd_succ_succ _) in Hoddi) xs)
      end in
  go 1 (RangeTests.odd_1) ops.

End applyList.

Definition emptyBoundedRangeVec (n : nat) : boundedRangeVec n.+2 :=
  {| vars := nil
   ; regs := vconst (None, None, None)
   |}.

(* jww (2014-11-04): Still to be done:

   Register constraints at method calls are also modeled using fixed
   intervals: Because all registers are destroyed when the call is executed,
   ranges of length 1 are added to all fixed intervals at the call
   site. Therefore, the allocation pass cannot assign a register to any
   interval there, and all intervals are spilled before the call. *)

Definition handleBlock (o : OpPair) (pos : nat) (Hodd : odd pos)
  (rest : boundedRangeVec pos.+2) : boundedRangeVec pos :=
  let: (orig, (kinds, existT refCount references)) := o in

  let liftOr f mx y :=
      Some (match mx with Some x => f x y | None => y end) in

  (** If the instruction at this position begins or ends a loop, extend the
      current range so that it starts at, or end at, this boundary. *)
  let savingBound x :=
      if (OILoopBegin \in kinds) || (OILoopEnd \in kinds)
      then let: (mb, me, r) := x in
           (liftOr minn mb pos, liftOr maxn me pos, r)
      else x in

  (** Add a new use position to the beginning of the current range. *)
  let consr (x : boundedTriple pos.+2) req : boundedTriple pos :=
      let upos := Build_UsePos pos req in
      @withRanges pos Hodd _ upos refl_equal pos.+2 (ltnSSn _) x in

  let restVars' := map savingBound (vars rest) in
  let restRegs' := vmap savingBound (regs rest) in
  vec_rect SomeVar (fun _ _ => boundedRangeVec pos)
    (boundedTransport (ltnSSn _) {| vars := restVars'; regs := restRegs' |})
    (fun _ x _ _ =>
       match x with
       | inl (v, req) =>
         let x := consr (nth (None, None, None) restVars' v) req in
         let restVars'' :=
             set_nth (None, None, None)
                     (transportBounds (ltnSSn _) restVars') v x in
         let restRegs'' := transportVecBounds (ltnSSn _) restRegs' in
         {| vars := restVars''; regs := restRegs'' |}

       | inr r =>
         let x := consr (vnth restRegs' r) false in
         let restVars'' := transportBounds (ltnSSn _) restVars' in
         let restRegs'' :=
             vreplace (transportVecBounds (ltnSSn _) restRegs') r x in
         {| vars := restVars''; regs := restRegs'' |}
      end)
    references.

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
Definition processOperations (ops : OpList) :
  seq (option RangeSig) * Vec (option RangeSig) maxReg :=
  let: {| vars := vars'; regs := regs' |} :=
       applyList ops emptyBoundedRangeVec handleBlock in
  (map extractRange vars', vmap extractRange regs').

End Ops.

End MOps.