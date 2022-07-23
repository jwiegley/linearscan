Set Warnings "-notation-overridden".

Require Import Hask.Ltac.
Require Import LinearScan.Ssr.
(* Require Import Trace. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Graph.

Variable a : eqType.

Record Graph := {
  vertices : seq a;
  edges    : seq (a * a)
}.

Definition emptyGraph : Graph :=
  {| vertices := [::]
   ; edges    := [::] |}.

Definition addVertex v (g : Graph) : Graph :=
  (fun vg => {| vertices := if v \in vg then vg else v :: vg
              ; edges    := edges g |})
  (vertices g).

Definition addEdge e (g : Graph) : Graph :=
  (fun eg => {| vertices := vertices g
              ; edges    := if e \in eg then eg else e :: eg |})
  (edges g).

Definition graphInsert e (g : Graph) : Graph :=
  addVertex (fst e) (addVertex (snd e) (addEdge e g)).

Definition removeEdge (x : a * a) g : Graph :=
  {| vertices := vertices g
   ; edges    := rem x (edges g) |}.

Theorem removeEdge_same_vertices : forall g e,
  size (vertices (removeEdge e g)) == size (vertices g).
Proof. by []. Qed.

Definition outbound (x : a) (g : Graph) : seq (a * a) :=
  [seq e <- edges g | x == fst e].

Definition inbound (x : a) (g : Graph) : seq (a * a) :=
  [seq e <- edges g | x == snd e].

Definition removeVertex (v : a) g : Graph :=
  foldr removeEdge {| vertices := rem v (vertices g)
                    ; edges    := edges g |} (inbound v g ++ outbound v g).

Theorem removeVertex_spec : forall g v,
  v \in vertices g -> size (vertices (removeVertex v g)) < size (vertices g).
Proof.
  move=> g v Hin.
  rewrite /removeVertex.
  elim: (inbound v g ++ outbound v g) => //= in Hin *.
  rewrite size_rem //.
  by case: (vertices g) => //= [*] in Hin *.
Qed.

End Graph.

Arguments emptyGraph {a}.
Arguments addVertex {a} v g.
Arguments addEdge {a} e g.
Arguments graphInsert {a} e g.
Arguments removeVertex {a} _ g.
Arguments removeEdge {a} _ g.
Arguments outbound {a} _ g.
Arguments inbound {a} _ g.

Definition topsort {a : eqType}
  (splittable : a -> bool) (split : a -> Graph a -> Graph a)
  (g0 : Graph a) : seq a :=
  let fix go fuel (g : Graph a) :=
    if fuel isn't S fuel then vertices g else
    (* Identify vertices that have no incoming edge (i.e., the "in-degree"
       of these vertices is zero). *)
    let noInbound := [seq v <- vertices g | nilp (inbound v g)] in
    if noInbound is [::]
    then if vertices g isn't v :: vs
         then [::]
         else if [seq x <- v :: vs | splittable x] is x :: _
              then go fuel (split x g)
              else vertices g   (* jww (2015-09-02): indicate error! *)
    else noInbound ++ go fuel (foldr removeVertex g noInbound) in
  go (size (vertices g0)).*2 g0.

Arguments topsort {a} splittable split g0.

(* Definition topologically_sorted `(g : Graph a) (xs : seq a) : bool := *)
(*   [&& perm_eq (vertices g) xs *)
(*   &   all (fun x : a * a => *)
(*              let: (a, b) := x in *)
(*              if inl a \in xs *)
(*              then if inl b \in xs *)
(*                   then index (inl a) xs < index (inl b) xs *)
(*                   else index (inl a) xs > index (inr b) xs *)
(*              else if inl b \in xs *)
(*                   then index (inr a) xs < index (inl b) xs *)
(*                   else index (inr a) xs > index (inr b) xs) (edges g)]. *)

Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Example topsort_ex1 :
  let g :=
    ( graphInsert (inl  1, inl  3)
    $ graphInsert (inl  4, inl  5)
    $ graphInsert (inl  9, inl  7)
    $ graphInsert (inl 10, inl 11)
    $ graphInsert (inl 11, inl 10)
    $ graphInsert (inl  7, inl  1)
    $ graphInsert (inl  6, inl  2)
    $ graphInsert (inl  2, inl  4)
    $ graphInsert (inl  5, inl  6)
    $ emptyGraph) in

  let splittable x := match x with
    | inl _ => true
    | _ => false
    end in

  let split x g := match x with
    | inl x =>
        {| vertices := rem (inl x) $ if inr x \in vertices g
                                     then vertices g
                                     else inr x :: vertices g
         ; edges    := let f e :=
                         let: (a, b) := e in
                         if a == inl x
                         then (inr x, b)
                         else e in
                       map f (edges g) |}
    | _ => g
    end in

  let: xs := topsort splittable split g in
  [&& (* topologically_sorted g xs *)

  (* ,    *)
      vertices g == [:: inl 3; inl 9; inl 11; inl 10; inl 7
                    ;   inl 1; inl 2; inl 4; inl 5; inl 6]

  &   xs == [:: inl 9; inl 7; inl 1; inl 3
            ;   inr 11; inl 10                 (* cycle was broken at 11 *)
            ;   inr 2; inl 4; inl 5; inl 6 ]]. (* cycle broken at 2 *)
Proof. by []. Qed.
