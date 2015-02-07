Require Import LinearScan.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Inductive IntMap (a : Type) := getIntMap of seq (nat * a).

Arguments getIntMap [a] _.

Definition emptyIntMap {a} := @getIntMap a [::].

(* We needn't bother defining these in Coq, since they only matter to the
   extracted Haskell code, and there we use the definitions from
   [Data.IntMap]. *)
Definition IntMap_lookup : forall a, nat -> IntMap a -> option a :=
  fun _ k m => let: getIntMap x := m in maybeLookup x k.
Definition IntMap_insert : forall a, nat -> a -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.
Definition IntMap_alter : forall a,
  (option a -> option a) -> nat -> IntMap a -> IntMap a :=
  fun _ _ _ x => x.

Definition IntMap_map {a b} (f : a -> b) (m : IntMap a) : IntMap b :=
  match m with
  | getIntMap xs => getIntMap (map (fun x => (fst x, f (snd x))) xs)
  end.

Definition IntMap_mergeWithKey {a b c} (combine : nat -> a -> b -> option c)
  (only1 : IntMap a -> IntMap c) (only2 : IntMap b -> IntMap c)
  (m1 : IntMap a) (m2 : IntMap b) : IntMap c :=
  only1 m1.

Definition IntMap_foldlWithKey
  {a b} (f : a -> nat -> b -> a) (z : a) (m : IntMap b) : a := z.

Definition IntMap_toList {a} (m : IntMap a) : seq (nat * a) :=
  match m with
    | getIntMap xs => xs
  end.

Extract Inductive IntMap => "Data.IntMap.IntMap"
  ["Data.IntMap.fromList"] "(\fS _ -> ())".

Extract Inlined Constant IntMap_lookup       => "Data.IntMap.lookup".
Extract Inlined Constant IntMap_insert       => "Data.IntMap.insert".
Extract Inlined Constant IntMap_alter        => "Data.IntMap.alter".
Extract Inlined Constant IntMap_map          => "Data.IntMap.map".
Extract Inlined Constant IntMap_foldlWithKey => "Data.IntMap.foldlWithKey".
Extract Inlined Constant IntMap_mergeWithKey => "Data.IntMap.mergeWithKey".
Extract Inlined Constant IntMap_toList       => "Data.IntMap.toList".

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
