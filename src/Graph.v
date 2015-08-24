Require Import Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Graph.

Variable a : eqType.
Variable b : eqType.

Record Graph := {
  vertices : seq a;
  edges    : seq b;
  edge_f   : b -> a * a
}.

Definition emptyGraph (f : b -> a * a) : Graph :=
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
   ; edges    := rem x (edges g)
   ; edge_f   := edge_f g
   |}.

Lemma removeEdge_same_vertices : forall g e,
  size (vertices (removeEdge e g)) == size (vertices g).
Proof. by []. Qed.

Definition connections f (x : a) g : seq b :=
  filter ((fun y : a => y == x) \o f \o edge_f g) (edges g).

Definition outbound : a -> Graph -> seq b := connections fst.
Definition inbound  : a -> Graph -> seq b := connections snd.

Definition removeVertex (v : a) g : Graph :=
  foldr removeEdge {| vertices := rem v (vertices g)
                    ; edges    := edges g
                    ; edge_f   := edge_f g |} (outbound v g).

Lemma removeVertex_spec : forall g v,
  v \in vertices g -> size (vertices (removeVertex v g)) < size (vertices g).
Proof.
  move=> g v Hin.
  rewrite /removeVertex.
  elim: (outbound v g) => //= in Hin *.
  rewrite size_rem //.
  by case: (vertices g) => //= [*] in Hin *.
Qed.

Definition topsort (g0 : Graph) (split : b -> seq b) : seq a * seq b :=
  let fix go fuel g :=
    (* jww (2015-08-23): Proof is sorely needed to avoid this possibility. *)
    if fuel isn't S fuel then (vertices g, edges g) else
    (* Identify vertices that have no incoming edge (i.e., the "in-degree" of
       these vertices is zero). *)
    let noInbound := [seq v <- vertices g | nilp (inbound v g)] in
    if noInbound is [::]
    then if edges g isn't e :: _
         then ([::], [::])
         else go fuel (foldr addEdge (removeEdge e g) (split e))
    else
      let: (ns', es') := go fuel (foldr removeVertex g noInbound) in
      (noInbound ++ ns', flatten [seq outbound n g | n <- noInbound] ++ es') in
  go (size (vertices g0)).*2 g0.

End Graph.

Arguments emptyGraph {a b} f.
Arguments addVertex {a b} v g.
Arguments addEdge {a b} e g.
Arguments removeEdge {a b} _ g.
Arguments outbound {a b} _ g.
Arguments inbound {a b} _ g.
Arguments topsort {a b} g0 split.

Definition topologically_sorted `(g : Graph a b)
  (xs : seq a) (ys : seq b) : bool :=
  perm_eq (vertices g) xs &&
  all (fun x => let: (a, b) := edge_f g x in index a xs < index b xs) ys.

Example topsort_ex1 :
  let g :=
    ( addEdge (Some  1, Some  3)
    $ addEdge (Some  4, Some  5)
    $ addEdge (Some  9, Some  7)
    $ addEdge (Some 10, Some 11)
    $ addEdge (Some 11, Some 10)
    $ addEdge (Some  7, Some  1)
    $ addEdge (Some  6, Some  2)
    $ addEdge (Some  2, Some  4)
    $ addEdge (Some  5, Some  6)
    $ emptyGraph id) in

  let swap mx := match mx with
    | (Some x, Some y) => [:: (Some y, Some x)]
    | (Some x, None)   => [:: (Some x, None)]
    | (None,   Some y) => [:: (None,   Some y)]
    | (None,   None)   => [::]
    end in

  let: (verts, xs) := topsort g swap in
  [&& topologically_sorted g verts xs

  ,   verts ==
      [:: Just 9
      ;   Just 7
      ;   Just 1
      ;   Just 3
      ;   Just 5
      ;   Just 6
      ;   Just 2
      ;   Just 4
      ;   Just 11
      ;   Just 10 ]

  &   xs ==
      [:: (Just 9,  Just 7)
      ;   (Just 7,  Just 1)
      ;   (Just 1,  Just 3)
      ;   (Just 5,  Just 4)
      ;   (Just 5,  Just 6)
      ;   (Just 6,  Just 2)
      ;   (Just 2,  Just 4)
      ;   (Just 11, Just 10) ] ].
Proof. by []. Qed.
