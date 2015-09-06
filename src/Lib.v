Require Export Hask.Prelude.
Require Export Hask.Ltac.
Require Export Hask.Control.Lens.
Require Export Hask.Control.Monad.
Require Export Hask.Data.IntMap.
Require Export Hask.Data.IntSet.
Require Export Hask.Data.List.
Require Export Hask.Data.NonEmpty.
Require Export Hask.Data.Vector.

Require Export Coq.Program.Wf.
Require Export Coq.Sorting.Sorted.
Require Export Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "p .1" := (proj1_sig p)
  (at level 2, left associativity, format "p .1").
Notation "p .2" := (proj2_sig p)
  (at level 2, left associativity, format "p .2").
Notation "( x ; y )" := (exist _ x y).

Definition widen_fst {n a} p := (@widen_id n (@fst _ a p), snd p).

Extraction Implicit widen_id [ n ].
Extraction Implicit widen_fst [ n ].

Extract Inlined Constant widen_id  => "".
Extract Inlined Constant widen_fst => "Prelude.id".
