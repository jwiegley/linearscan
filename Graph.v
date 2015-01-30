Require Import LinearScan.Lib.

Section Topsort.

(* jww (2015-01-29): This behavior of this Graph depends on our knowing that a
   register can only appear once as the source and once as the target of any
   edge.  This needs to be verified. *)

Variable a : eqType.

Record Graph := {
  vertices : seq (option a);
  edges    : seq (option a * option a)
}.

Definition emptyGraph :=
  {| vertices := [::]
   ; edges    := [::] |}.

Definition addVertex v (g : Graph) : Graph :=
  (fun vg =>
    {| vertices := if v \in vg then vg else v :: vg
     ; edges := edges g
     |})
  (vertices g).

Definition addEdge e (g : Graph) : Graph :=
  let g' :=
    (fun eg =>
      {| vertices := vertices g
       ; edges := if e \in eg then eg else e :: eg
       |})
    (edges g) in
  addVertex (fst e) $ addVertex (snd e) $ g'.

Definition removeEdge (x : option a * option a) g :=
  {| vertices := vertices g
   ; edges    := filter (fun y => y != x) (edges g) |}.

Definition connections f (x : option a) g :=
  filter ((fun y : option a => y == x) \o f) (edges g).

Definition outbound := connections (@fst _ _).
Definition inbound  := connections (@snd _ _).

Fixpoint tsort' fuel l roots g :=
  (* The fuel represents the fact that we must only call tsort' once for
     each vertex in the graph. *)
  if fuel isn't S fuel then rev l else
  if edges g isn't (se, de) :: es then rev l else

  let: next :=
    if roots is n :: s
    then (n :: s, g)
    else ([:: de], addEdge (se, None) $
                   removeEdge (se, de) $ g) in
  if next isn't (n :: s, g') then [::] else

  let outEdges    := outbound n g' in
  let: (res, g'') := foldl (fun acc e =>
                              let: (res, g'') := acc in
                              (e :: res, removeEdge e g''))
                           ([::], g') outEdges in
  let outNodes    := map (@snd _ _) outEdges in
  let s'          := s ++ filter (@nilp _ \o inbound ^~ g'') outNodes in

  tsort' fuel (l ++ res) s' g''.

Definition topsort g :=
  let noInbound :=
      (fun xs => [seq x <- vertices g | x \notin xs])
      (map (@snd _ _) (edges g)) in
  (* +1 is added to the fuel in case None is injected as a root *)
  tsort' (size (vertices g)).+1 [::] noInbound g.

End Topsort.

Arguments emptyGraph [a].
Arguments addVertex [a] v g.
Arguments addEdge [a] e g.
Arguments removeEdge [a] _ g.
Arguments connections [a] _ _ g.
Arguments outbound [a] _ g.
Arguments inbound [a] _ g.
Arguments topsort [a] g.

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
