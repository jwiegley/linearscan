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
  isLoopBegin : opType -> bool;
  isLoopEnd   : opType -> bool;
  isCall      : opType -> option (seq PhysReg);
  hasRefs     : opType -> bool;
  varRefs     : opType -> seq VarInfo;
  regRefs     : opType -> seq PhysReg
}.

Inductive Allocation := Unallocated | Register of PhysReg | Spill.

(* [OpData] combines the original operation from the caller, plus any extra
   information that we've generated during the course of our algorithm. *)
Record OpData := {
  baseOp  : opType;
  opInfo  : OpInfo;
  opId    : nat;
  opIdOdd : odd opId;
  opAlloc : VarId -> Allocation
}.

(* Finally, when we work with the list of operations, we will be working with
   a list of our [OpData] structures. *)
Definition OpList := seq OpData.

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

  let rest2 := match varRefs (opInfo op) (baseOp op) with
      | nil => unchanged
      | v :: vs =>
         let x := consr (nth (None, None, None) restVars' (varId v))
                        (regRequired v) in
         {| vars := set_nth (None, None, None)
                            (vars unchanged) (varId v) x
          ; regs := regs unchanged
          |}
      end in

  match regRefs (opInfo op) (baseOp op) with
  | nil => rest2
  | r :: rs =>
     let x := consr (vnth restRegs' r) false in
     {| vars := vars rest2
      ; regs := vreplace (transportVecBounds (ltnSSn _) restRegs') r x
      |}
  end.

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

Lemma shift_range_vec : forall n m,
  n = m -> boundedRangeVec n -> boundedRangeVec m.
Admitted.

Definition applyList (op : OpData) (ops : seq OpData)
  (base : forall l, boundedRangeVec l.+2)
  (f : forall op : OpData,
         boundedRangeVec (opId op).+2 -> boundedRangeVec (opId op))
   : boundedRangeVec (opId op) :=
  let fix go x xs :=
      match xs with
      | nil     => f x (base (opId x))
      | y :: ys => f x (@shift_range_vec (opId y) (opId x).+2 undefined (go y ys))
      end in
  go op ops.

(** The list of operations is processed in reverse, so that the resulting
    sub-lists are also in order. *)
Definition processOperations (ops : seq OpData) :
  seq (option RangeSig) * Vec (option RangeSig) maxReg :=
  match ops with
  | nil => (nil, vconst None)
  | x :: xs =>
      let: {| vars := vars'; regs := regs' |} :=
           applyList x xs emptyBoundedRangeVec handleOp in
      (map extractRange vars', vmap extractRange regs')
  end.

End Ops.

End MOps.