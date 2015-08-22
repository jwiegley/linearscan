Require Import Lib.

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
   ; edges    := rem x (edges g)
   ; edge_f   := edge_f g
   |}.

Lemma removeEdge_same_vertices : forall g e,
  size (vertices (removeEdge e g)) == size (vertices g).
Proof. by []. Qed.

Definition connections f (x : option a) g : seq b :=
  filter ((fun y : option a => y == x) \o f \o edge_f g) (edges g).

Definition outbound : option a -> Graph -> seq b := connections fst.
Definition inbound  : option a -> Graph -> seq b := connections snd.

Definition removeVertex (v : option a) g : Graph :=
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

Definition unhandled_nodes g : nat :=
  let noInbound := [seq v <- vertices g | nilp (inbound v g)] in
  (size (vertices g)).*2 - size noInbound.

Variable spl : b -> seq b.

Definition replaceEdge e g := foldr addEdge (removeEdge e g) (spl e).

Hypothesis Hspl : forall (g : Graph) (e : b),
  e \in edges g -> unhandled_nodes (replaceEdge e g) < unhandled_nodes g.

Lemma leq_double_r : forall n m, n <= m -> n <= m.*2.
Proof.
  move=> n m H.
  rewrite -muln2.
  have ->: n = n * 1 by ordered.
  exact: leq_mul.
Qed.

Fixpoint topsort (g0 : Graph) : seq (option a) * seq b :=
  let fix go fuel g :=
    if fuel isn't S fuel then ([::],[::]) else
    (* Identify vertices that have no incoming edge (i.e., the "in-degree" of
       these vertices is zero, meaning that no edge has such a vertex for its
       destination). *)

    let noInbound := [seq v <- vertices g | nilp (inbound v g)] in

    if noInbound is [::]
    then if edges g isn't e :: _
         then ([::], [::])
         else go fuel (replaceEdge e g)
    else
      let: (ns', es') := go fuel (foldr removeVertex g noInbound) in
      (noInbound ++ ns', flatten [seq outbound n g | n <- noInbound] ++ es') in
  go (size (vertices g0)).*2 g0.
(*
Next Obligation.
  apply/leP.
  rewrite /unhandled_nodes /inbound /connections /funcomp /removeVertex.
  (* have H: n \in vertices g. *)
  (*   elim: (vertices g) => //= [v vs IHvs] in Heq_noInbound *. *)
  (*   rewrite in_cons. *)
  (*   apply/orP. *)
  (*   case: (nilp (inbound v g)) in Heq_noInbound. *)
  (*     left. *)
  (*     by inversion Heq_noInbound. *)
  (*   right. *)
  (*   exact: IHvs. *)
  (* move: (removeVertex_spec H). *)
  (* have Hcount : forall (a : eqType) f (x : option a) xs, *)
  (*     count f (rem x xs) <= count f xs. *)
  (*   move=> t f x. *)
  (*   elim=> //= [y ys IHys]. *)
  (*   case: (y == x) => /=. *)
  (*     rewrite addnC. *)
  (*     exact: leq_plus. *)
  (*   exact: leq_add2l. *)
  elim: (vertices g) => //= [v vs IHvs] in Heq_noInbound *.
  case: (nilp (inbound v g)) in Heq_noInbound.
    clear IHvs.
    inversion Heq_noInbound.
    rewrite eq_refl.
    move=> *.
    case: (outbound v g) => /= [|o os];
    case: (nilp [seq x <- edges g | snd (edge_f g x) == v]) => /=.
    - set fs := filter _ _.
      rewrite doubleS subnS subSKn.
      rewrite subSn.
        by apply/eqP; ordered.
      rewrite /fs size_filter.
      set f := (X in count X _).
      move: (count_size f vs) => H.
      exact: leq_double_r.
    - set fs := filter _ _.
      rewrite doubleS.
      apply: ltn_sub2r.
        rewrite /fs size_filter.
        set f := (X in count X _).
        move: (count_size f vs) => H.
        apply/leqW.
        exact: leq_double_r.
      by ordered.
    - case: (edges g) => /= [|e es].
    case: (v == n).
      set F := foldr _ _ _.
      case: (nilp [seq x <- edges g | snd (edge_f g x) == v]) => /=.
        set fs := filter _ _.
    
  admit.
Admitted.
Next Obligation.
  apply/leP.
  apply: Hspl.
  rewrite -Heq_anonymous.
  exact: mem_head.
Qed.
*)

End Graph.

Arguments emptyGraph {a b} f.
Arguments addVertex {a b} v g.
Arguments addEdge {a b} e g.
Arguments removeEdge {a b} _ g.
Arguments replaceEdge {a b spl} _ g.
Arguments outbound {a b} _ g.
Arguments inbound {a b} _ g.
Arguments topsort {a b} spl g0.

Definition topologically_sorted `(g : Graph a b)
  (xs : seq (option a)) (ys : seq b) : bool :=
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

  let split mx := match mx with
    | (Some x, Some y) => [:: (Some y, Some x)]
    | (Some x, None)   => [:: (Some x, None)]
    | (None,   Some y) => [:: (None,   Some y)]
    | (None,   None)   => [::]
    end in

  let: (verts, xs) := topsort split g in
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
