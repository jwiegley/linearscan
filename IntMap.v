Require Import Ssreflect.ssreflect.
Require Import Ssreflect.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Inductive IntMap (a : Type) :=
  | emptyIntMap
  | getIntMap of seq (nat * a).

Arguments emptyIntMap [a].
Arguments getIntMap [a] _.

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntMap_lookup : forall a, nat -> IntMap a -> option a :=
  fun _ _ _ => None.
Definition IntMap_insert : forall a, nat -> a -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.
Definition IntMap_alter : forall a,
  (option a -> option a) -> nat -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.

Definition IntMap_toList {a} (m : IntMap a) : seq (nat * a) :=
  match m with
    | emptyIntMap => nil
    | getIntMap xs => xs
  end.

Extract Inductive IntMap => "Data.IntMap.IntMap"
  ["Data.IntMap.empty" "Data.IntMap.fromList"] "(\fO fS _ -> fO ())".

Extract Inlined Constant IntMap_lookup => "Data.IntMap.lookup".
Extract Inlined Constant IntMap_insert => "Data.IntMap.insert".
Extract Inlined Constant IntMap_alter  => "Data.IntMap.alter".
Extract Inlined Constant IntMap_toList => "Data.IntMap.toList".

Inductive IntSet :=
  | emptyIntSet
  | getIntSet of seq nat.

Arguments emptyIntSet.
Arguments getIntSet _.

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntSet_member     : nat -> IntSet -> bool      := fun _ _ => false.
Definition IntSet_insert     : nat -> IntSet -> IntSet    := fun _ x => x.
Definition IntSet_union      : IntSet -> IntSet -> IntSet := fun _ x => x.
Definition IntSet_difference : IntSet -> IntSet -> IntSet := fun _ x => x.

Definition IntSet_foldl : forall a, (a -> nat -> a) -> a -> IntSet -> a :=
  fun _ _ z _ => z.

Definition IntSet_forFold {a} (z : a) (m : IntSet) (f: a -> nat -> a) : a :=
  IntSet_foldl f z m.

Extract Inductive IntSet => "Data.IntSet.IntSet"
  ["Data.IntSet.empty" "Data.IntSet.fromList"] "(\fO fS _ -> fO ())".

Extract Inlined Constant IntSet_member     => "Data.IntSet.member".
Extract Inlined Constant IntSet_insert     => "Data.IntSet.insert".
Extract Inlined Constant IntSet_union      => "Data.IntSet.union".
Extract Inlined Constant IntSet_difference => "Data.IntSet.difference".
Extract Inlined Constant IntSet_foldl      => "Data.IntSet.foldl'".
