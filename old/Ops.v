Require Import LinearScan.Lib.
Require Import LinearScan.Machine.
Require Import LinearScan.Range.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Module MOps (Mach : Machine).

Import Mach.

Section Ops.

Definition VarId := nat.

Inductive VarKind := Input | Temp | Output.

(* [VarInfo] abstracts information about the caller's notion of variables
   associated with an operation. *)
Record VarInfo := {
  varId       : VarId;
  varKind     : VarKind;
  regRequired : bool
}.

(* [opType] is the original operation type used by the caller. *)
Variable opType : Set.

(* The [OpInfo] structure is a collection of functions that allow us to
   determine information about each operation coming from the caller's
   side. *)
Record OpInfo := {
  compareOp   : forall x y : opType, {x = y} + {x <> y};
  isLoopBegin : opType -> bool;
  isLoopEnd   : opType -> bool;
  isCall      : opType -> option (seq PhysReg);
  hasRefs     : opType -> bool;
  varRefs     : opType -> seq VarInfo;
  regRefs     : opType -> seq PhysReg
}.

Inductive Allocation := Unallocated | Register of PhysReg | Spill.

Section Eqalloc.

Definition eqalloc a1 a2 :=
  match a1, a2 with
  | Unallocated, Unallocated => true
  | Register r1, Register r2 => r1 == r2
  | Spill,       Spill       => true
  | _, _ => false
  end.

Lemma eqallocP : Equality.axiom eqalloc.
Proof.
  move.
  case=> [|r1|]; case => [|r2|];
  try constructor; try by [].
  case: (r1 =P r2) => /= [<-|neqx].
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

Canonical alloc_eqMixin := EqMixin eqallocP.
Canonical alloc_eqType := Eval hnf in EqType Allocation alloc_eqMixin.

Lemma eqallocE : eqalloc = eqalloc. Proof. by []. Qed.

Definition Allocation_eqType (A : eqType) :=
  Equality.Pack alloc_eqMixin Allocation.

End Eqalloc.

(* [OpData] combines the original operation from the caller, plus any extra
   information that we've generated during the course of our algorithm. *)
Record OpData := {
  baseOp  : opType;
  opInfo  : OpInfo;
  opId    : nat;
  opIdOdd : odd opId;
  opAlloc : seq (VarId * Allocation)
}.

Section Eqop.

Definition eqop o1 o2 :=
  [&& proj1_sig
        (Sumbool.bool_of_sumbool
           (compareOp (opInfo o1) (baseOp o1) (baseOp o2)))
  ,   opId o1 == opId o2
  &   opAlloc o1 == opAlloc o2
  ].

Lemma eqopP : Equality.axiom eqop.
Proof.
  move.
  case=> [a1 b1 c1 d1 e1];
  case => [a2 b2 c2 d2 e2];
  try constructor; try by [].
  rewrite /eqop /=.

  case: (compareOp b1 a1 a2) => [H|H];
  last by constructor; move; invert; contradiction.
  subst.
  rewrite /=.

  case E1: (c1 == c2) => /=;
  move/eqP in E1;
  last by constructor; move; invert; contradiction.

  subst.
  have ->: d1 = d2 by exact: eq_irrelevance.
  case E2: (e1 == e2) => /=;
  move/eqP in E2;
  last by constructor; move; invert; contradiction.

  subst.
  constructor.
  f_equal.
  admit.                  (* jww (2015-01-07): axiom *)
Qed.

Canonical op_eqMixin := EqMixin eqopP.
Canonical op_eqType := Eval hnf in EqType OpData op_eqMixin.

Lemma eqopE : eqop = eq_op. Proof. by []. Qed.

Definition OpData_eqType (A : eqType) :=
  Equality.Pack op_eqMixin OpData.

End Eqop.

(* Finally, when we work with the list of operations, we will be working with
   a list of our [OpData] structures. *)
Inductive OpList : seq OpData -> Type :=
  | OpList_sing op oinfo n nodd :
      OpList [:: {| baseOp  := op
                  ; opInfo  := oinfo
                  ; opId    := n
                  ; opIdOdd := nodd
                  ; opAlloc := nil
                  |} ]

  | OpList_cons op oinfo n nodd f os :
      let o := {| baseOp  := op
                ; opInfo  := oinfo
                ; opId    := n
                ; opIdOdd := nodd
                ; opAlloc := f
                |} in
      OpList [:: o & os ] ->
      OpList [:: {| baseOp  := op
                  ; opInfo  := oinfo
                  ; opId    := n.+2
                  ; opIdOdd := odd_add_2 nodd
                  ; opAlloc := nil
                  |}, o & os ].

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

Definition handleOp (op : OpData) (rest : boundedRangeVec (opId op).+2) :
  boundedRangeVec (opId op) :=
  let pos := opId op in
  let Hodd := opIdOdd op in

  let liftOr f mx y :=
      Some (match mx with Some x => f x y | None => y end) in

  (** If the instruction at this position begins or ends a loop, extend the
      current range so that it starts at, or end at, this boundary. *)
  let savingBound x :=
      if (isLoopBegin (opInfo op) (baseOp op)) ||
         (isLoopEnd (opInfo op) (baseOp op))
      then let: (mb, me, r) := x in
           (liftOr minn mb pos, liftOr maxn me pos, r)
      else x in

  (** Add a new use position to the beginning of the current range. *)
  let consr (x : boundedTriple pos.+2) req : boundedTriple pos :=
      let upos := Build_UsePos pos req in
      @withRanges pos Hodd _ upos refl_equal pos.+2 (ltnSSn _) x in

  let restVars' := map savingBound (vars rest) in
  let restRegs' := vmap savingBound (regs rest) in
  let unchanged :=
      boundedTransport (ltnSSn _)
                       {| vars := restVars'; regs := restRegs' |} in

  let rest2 :=
      let k acc v :=
          let x := consr (nth (None, None, None) restVars' (varId v))
                         (regRequired v) in
          {| vars := set_nth (None, None, None) (vars acc) (varId v) x
           ; regs := regs acc
           |} in
      foldl k unchanged (varRefs (opInfo op) (baseOp op)) in

  let k acc r :=
      let x := consr (vnth restRegs' r) false in
      {| vars := vars acc
       ; regs := vreplace (regs acc) r x
       |} in
  foldl k rest2 (regRefs (opInfo op) (baseOp op)).

Definition extractRange {n} (x : boundedTriple n) : option RangeSig :=
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

Definition applyList (opInfo : OpInfo) (op : opType) (ops : seq opType)
  (base : forall l, boundedRangeVec l.+2)
  (f : forall op : OpData,
         boundedRangeVec (opId op).+2 -> boundedRangeVec (opId op))
   : seq OpData * boundedRangeVec 1 :=
  let fix go i Hoddi x xs : seq OpData * boundedRangeVec i :=
      let newop := {| baseOp  := x
                    ; opInfo  := opInfo
                    ; opId    := i
                    ; opIdOdd := Hoddi
                    ; opAlloc := nil |} in
      match xs with
      | nil => ([:: newop], f newop (base i))
      | y :: ys =>
          let: (ops', next) := go i.+2 (odd_add_2 Hoddi) y ys in
          (newop :: ops', f newop next)
      end in
  go 1 odd_1 op ops.

(** The list of operations is processed in reverse, so that the resulting
    sub-lists are also in order. *)
Definition processOperations (opInfo : OpInfo) (ops : seq opType) :
  seq OpData * seq (option RangeSig) * Vec (option RangeSig) maxReg :=
  match ops with
  | nil => (nil, nil, vconst None)
  | x :: xs =>
      let: (ops', {| vars := vars'; regs := regs' |}) :=
           @applyList opInfo x xs emptyBoundedRangeVec handleOp in
      (ops', map extractRange vars', vmap extractRange regs')
  end.

End Ops.

End MOps.