Require Import Hask.Ssr.
Require Import Hask.Data.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Graph.

Variable a : eqType.
Variable b : eqType.

Record Graph := {
  vertices : seq (option a);
  edges    : seq b;
  edge_f   : b -> (option a * option a)
}.

Definition emptyGraph (f : b -> (option a * option a)) : Graph :=
  {| vertices := [::]
   ; edges    := [::]
   ; edge_f   := f
   |}.

Definition addVertex v (g : Graph) : Graph :=
  (fun vg =>
    {| vertices := if v \in vg then vg else v :: vg
     ; edges    := edges g
     ; edge_f   := edge_f g
     |})
  (vertices g).

Definition addEdge e (g : Graph) : Graph :=
  let g' :=
    (fun eg =>
      {| vertices := vertices g
       ; edges    := if e \in eg then eg else e :: eg
       ; edge_f   := edge_f g
       |})
    (edges g) in
  let: (a, z) := edge_f g' e in
  addVertex a (addVertex z g').

Definition removeEdge (x : b) g : Graph :=
  {| vertices := vertices g
   ; edges    := filter (fun y => y != x) (edges g)
   ; edge_f   := edge_f g
   |}.

Definition connections f (x : option a) g : seq b :=
  filter ((fun y : option a => y == x) \o f \o edge_f g) (edges g).

Definition outbound : option a -> Graph -> seq b := connections fst.
Definition inbound  : option a -> Graph -> seq b := connections snd.

Fixpoint tsort' fuel l (roots : seq (option a)) (k : b -> seq b) g : seq b :=
  (* The fuel represents the fact that we must only call tsort' once for
     each vertex in the graph.

     jww (2015-05-13): It would be far more satisfying to have a real proof of
     termination, since any error in choice of fuel is not propagated, making
     this function useless in the context of proof. *)
  if fuel isn't S fuel then rev l else

  if edges g isn't e :: _ then rev l else

  let: next :=
    if roots is n :: s
    then (n :: s, g)
    else
      (* Wimmer: You can break cycles of arbitrary depth with a swap. When you
         see the moves as edges in a directed graph, then the swap of two
         registers reverses the direction of the edge between these registers.
         This breaks the cycle and makes the new graph acyclic.

         jww (2015-01-30): This means I need a way to indicate swaps here,
         since effectively what I am doing now is swapping through memory. *)
      ([:: snd (edge_f g e)], foldr addEdge (removeEdge e g) (k e)) in
  if next isn't (n :: s, g') then [::] else (* always matches *)

  let outEdges := outbound n g' in
  let: (res, g'') :=
    foldl (fun acc e => let: (res, g'') := acc in
                          (e :: res, removeEdge e g''))
          ([::], g') outEdges in
  let outNodes := map (@snd _ _ \o edge_f g) outEdges in
  let s' := s ++ filter (@nilp _ \o inbound ^~ g'') outNodes in

  tsort' fuel (l ++ res) s' k g''.

(* The function [k] takes an edge, and must yield an edge whose target (as
   given by [edge_f g]) is [None]. *)
Definition topsort g (k : b -> seq b) (p : rel b) : seq b :=
  (* Identify vertices that have no incoming edge (i.e., the "in-degree" of
     these vertices is zero, meaning that no edge has such a vertex for its
     destination). *)
  let verts := undup [seq fst (edge_f g x)
                     | x <- sortBy p (edges g)] in
  let noInbound := (fun xs => [seq x <- verts | x \notin xs])
                     (map (@snd _ _ \o edge_f g) (edges g)) in
  (* +1 is added to the fuel in case None is injected as a root *)
  tsort' (size (vertices g)).+1 [::] noInbound k g.

End Graph.

Arguments emptyGraph {a b} f.
Arguments addVertex {a b} v g.
Arguments addEdge {a b} e g.
Arguments removeEdge {a b} _ g.
Arguments outbound {a b} _ g.
Arguments inbound {a b} _ g.
Arguments topsort {a b} g k p.

(* Compute *)
(*   ( addEdge (Some  1, Some  3) *)
(*   $ addEdge (Some  4, Some  5) *)
(*   $ addEdge (Some  9, Some  7) *)
(*   $ addEdge (Some 10, Some 11) *)
(*   $ addEdge (Some 11, Some 10) *)
(*   $ addEdge (Some  7, Some  1) *)
(*   $ addEdge (Some  6, Some  2) *)
(*   $ addEdge (Some  2, Some  4) *)
(*   $ addEdge (Some  5, Some  6) *)
(*   $ emptyGraph). *)

(* Compute topsort *)
(*   ( addEdge (Some  1, Some  3) *)
(*   $ addEdge (Some  4, Some  5) *)
(*   $ addEdge (Some  9, Some  7) *)
(*   $ addEdge (Some 10, Some 11) *)
(*   $ addEdge (Some 11, Some 10) *)
(*   $ addEdge (Some  7, Some  1) *)
(*   $ addEdge (Some  6, Some  2) *)
(*   $ addEdge (Some  2, Some  4) *)
(*   $ addEdge (Some  5, Some  6) *)
(*   $ emptyGraph). *)
