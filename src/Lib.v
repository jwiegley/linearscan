Require Export Hask.Prelude.
Require Export Hask.Ltac.
Require Export Hask.Haskell.
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

Lemma widen_ord_spec : forall n x (H : n <= n), widen_ord H x = x.
Proof.
  move=> ? [? ?] ?.
  rewrite /widen_ord.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma widen_ord_inj : forall m n (H : m <= n), injective (widen_ord H).
Proof.
  move=> m n H.
  rewrite /injective => x1 x2.
  by invert; apply ord_inj.
Qed.

Lemma widen_ord_refl : forall n (H : n <= n) x, widen_ord (m := n) H x = x.
Proof.
  move=> n H.
  case=> m Hm.
  rewrite /widen_ord /=.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma map_widen_ord_refl : forall b n (H : n <= n) (xs : seq ('I_n * b)),
  [seq (let: (xid, reg) := i in (widen_ord (m:=n) H xid, reg)) | i <- xs] = xs.
Proof.
  move=> b n H.
  elim=> //= [x xs IHxs].
  rewrite IHxs.
  case: x => [xid reg].
  congr ((_, reg) :: xs).
  exact: widen_ord_refl.
Qed.

Lemma lift_bounded : forall n (x : 'I_n), ord_max != widen_ord (leqnSn n) x.
Proof.
  move=> n.
  case=> /= m Hlt.
  rewrite /ord_max /lift.
  apply/eqP; invert.
  move: H0 Hlt => ->.
  by rewrite ltnn.
Qed.

Definition widen_id {n} := widen_ord (leqnSn n).
Arguments widen_id [n] i /.

Lemma no_ord_max : forall n (xs : seq ('I_n)),
  ord_max \notin [ seq widen_id i | i <- xs ].
Proof.
  move=> n; elim=> // [x xs IHxs] /=.
  rewrite in_cons /=.
  apply/norP; split; last assumption.
  exact: lift_bounded.
Qed.

Definition widen_fst {n a} p := (@widen_id n (@fst _ a p), snd p).

Lemma widen_fst_inj : forall a n, injective (@widen_fst n a).
Proof.
  move=> a n.
  rewrite /injective => [[[x1a H1] x1b] [[x2a H2] x2b]].
  invert.
  congr (_, _).
  rewrite H0 in H1 *.
  congr (Ordinal _).
  exact: eq_irrelevance.
Qed.

Lemma map_widen_fst : forall (a : eqType) n (xs : seq ('I_n * a)),
  [seq fst i | i <- [seq (@widen_fst n a) i | i <- xs]] =
  [seq (@widen_id n) i | i <- [seq fst i | i <- xs]].
Proof. move=> a n xs. by rewrite -!map_comp. Qed.

(* This rather excessively complicated, dependent fold function is needed in
   order to walk through a list of intervals of a [ScanState] (which have a
   type dependent on that [ScanState]), while at the same time mutating the
   same [ScanState] and adjusting the type of the remainder of the interval
   list, such that it is known to still have a relationship with the new
   [ScanState].  See the function [checkActiveIntervals] in Allocate.v, which
   is the only user of this function. *)
Program Fixpoint dep_foldl_inv
  {A : Type}                    (* type of the accumulator *)
  {P : A -> Prop}               (* predicate maintained over the accumulator *)
  {R : A -> A -> Prop}          (* a relation on A that must be preserved *)
  {E : A -> eqType}             (* type of the elements we are folding over *)
  (b : A)                       (* the initial state value *)
  (Pb : P b)                    (* predicate on the initial state value *)
  (v : seq (E b))               (* list of elements from the initial state *)

  (n : nat)                     (* the length of this list (as a [nat]) *)
  (* The reason to [nat] rather than [size v] is that the type of v changes
     with each iteration of the fold, which confuses [Program Fixpoint] enough
     that it fails to compute the final proof term even after ten minutes. *)

  (Hn : n == size v)            (* witness that [length == size v] *)
  (Q : forall x : A, seq (E x)) (* function that can determine [v] from [b] *)
  (Hsub : subseq v (Q b))       (* a proof that [v] is a subseq of [Q b] *)

  (F : forall (b b' : A) (Rbb' : R b b'), E b -> E b')
                                (* transports element types between states *)

  (* The fold function [f] takes an intermediate state, a witness for the
     inductive predicate on that state, an element from the initial list which
     is known to be related to that state (and whose type has been transported
     to relate to that state), the list of remaining elements to be processed
     by the fold, and proof that this element and remaining list are at least
     a subsequence of the state.
         The expected result is a new state, proof that this new state relates
     to the incoming state in terms of [R] (which must be transitive), proof
     that the inductive predicate holds for this new state, and proof that the
     transported remainder [xs] is also a subsequence of the list determined
     by [Q] from the new state. *)
  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)),
         subseq (x :: xs) (Q z)
           -> { res : { z' : A | R z z' }
              | P res.1 & subseq (map (F z res.1 res.2) xs) (Q res.1) })

  (* The fold is done when [n] reaches zero *)
  {struct n} :
  (* The result is a final, inductively predicated state *)
  { b' : A | P b' } :=
  match (v, n) with
  | (y :: ys, S n') =>
      match f b Pb y ys Hsub with
      | exist2 (exist b' Rbb') Pb' Hsub' =>
          let ys' := map (F b b' Rbb') ys in
          @dep_foldl_inv A P R E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => exist P b Pb
  end.
Obligation 2.
  inversion Heq_anonymous0.
  clear Heq_anonymous.
  rewrite -H1 in Hn.
  rewrite -H0 in Hn.
  simpl in Hn.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.

Program Fixpoint dep_foldl_invE
  {errType : Type}              (* the short-circuiting error type *)
  {A : Type}                    (* the value being mutated through the fold *)
  {P : A -> Prop}               (* inductive predicate to be maintained on A *)
  {R : A -> A -> Prop}          (* a relation on A that must be preserved *)
  {E : A -> eqType}             (* type of the elements we are folding over *)
  (b : A)                       (* the initial state value *)
  (Pb : P b)                    (* predicate on the initial state value *)
  (v : seq (E b))               (* list of elements from the initial state *)

  (n : nat)                     (* the length of this list (as a [nat]) *)

  (Hn : n == size v)            (* witness that [length == size v] *)
  (Q : forall x : A, seq (E x)) (* function that can determine [v] from [b] *)
  (Hsub : subseq v (Q b))       (* a proof that [v] is a subseq of [Q b] *)

  (F : forall (b b' : A) (Rbb' : R b b'), E b -> E b')
                                (* transports element types between states *)

  (f : forall (z : A) (Pz : P z) (x : E z) (xs : seq (E z)),
         subseq (x :: xs) (Q z)
           -> errType +
              { res : { z' : A | R z z' }
              | P res.1 & subseq (map (F z res.1 res.2) xs) (Q res.1) })

  {struct n} :
  errType + { b' : A | P b' } :=
  match (v, n) with
  | (y :: ys, S n') =>
      match f b Pb y ys Hsub with
      | inl err => inl err
      | inr (exist2 (exist b' Rbb') Pb' Hsub') =>
          let ys' := map (F b b' Rbb') ys in
          @dep_foldl_invE errType A P R E b' Pb' ys' n' _ Q Hsub' F f
      end
  | _ => inr (exist P b Pb)
  end.
Obligation 2.
  inversion Heq_anonymous0.
  clear Heq_anonymous.
  rewrite -H1 -H0 in Hn.
  simpl in Hn.
  move: eqSS Hn => /= -> /eqP ->.
  by rewrite size_map.
Qed.
