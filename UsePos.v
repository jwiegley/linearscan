Require Import LinearScan.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
    uloc   : nat;
    regReq : bool
}.

Coercion uloc : UsePos >-> nat.

Module UsePosNotations.
Notation " (| x |) " := {| uloc := x; regReq := false |}.
Notation " (! x !) " := {| uloc := x; regReq := true |}.
End UsePosNotations.

Definition upos_lt (x y : UsePos) : bool := uloc x < uloc y.
Arguments upos_lt x y /.

Program Instance upos_lt_trans : Transitive upos_lt.
Obligation 1. exact: (ltn_trans H). Qed.

Section EqUpos.

Variables (T : eqType) (x0 : T).
Implicit Type s : UsePos.

Fixpoint equpos s1 s2 {struct s2} :=
  match s1, s2 with
  | {| uloc := u1; regReq := rr1 |},
    {| uloc := u2; regReq := rr2 |} => (u1 == u2) && (rr1 == rr2)
  end.

Lemma equposP : Equality.axiom equpos.
Proof.
  move.
  case=> [u1 rr1].
  case=> [u2 rr2] /=.
  case: (u1 =P u2) => [<-|neqx]; last by right; case.
  case: (rr1 =P rr2) => [<-|neqx]; last by right; case.
  by constructor.
Qed.

Canonical upos_eqMixin := EqMixin equposP.
Canonical upos_eqType := Eval hnf in EqType UsePos upos_eqMixin.

Lemma equposE : equpos = eq_op. Proof. by []. Qed.

Definition UsePos_eqType (A : eqType) :=
  Equality.Pack upos_eqMixin UsePos.

End EqUpos.

Lemma all_leq : forall x y xs,
  all (fun u : UsePos => y <= u) xs -> x <= y
    -> all (fun u : UsePos => x <= u) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    exact: (leq_trans H3 _).
  exact: IHzs.
Qed.

Lemma all_leq_ltn : forall x y xs,
  all (fun u : UsePos => y <= u) xs -> x < y
    -> all (fun u : UsePos => x < u) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    exact: (leq_trans H3 _).
  exact: IHzs.
Qed.

Lemma all_ltn : forall x y xs,
  all (fun u : UsePos => u < y) xs -> y <= x
    -> all (fun u : UsePos => u < x) xs.
Proof.
  move=> x y.
  elim=> [|z zs IHzs] //=.
  move/andP => [H1 H2] H3.
  apply/andP; split.
    exact: (ltn_leq_trans H1 _).
  exact: IHzs.
Qed.

Lemma NE_StronglySorted_UsePos_impl : forall xs,
  NE_StronglySorted upos_lt xs -> NE_head xs < (NE_last xs).+1.
Proof.
  intros.
  induction xs; simpl in *; auto.
  inversion H.
  apply NE_Forall_last in H3.
  exact/ltnW.
Qed.

(** When splitting a [NonEmpty UsePos] list into two sublists at a specific
    point, the result type must be able to relate the sublists to the original
    list. *)
Definition UsePosSublistsOf (before : nat)
  `(H : NE_StronglySorted upos_lt l) :=
  { p : option (NonEmpty UsePos) * option (NonEmpty UsePos)
  | let f x := x < before in match p with
    | (Some l1, Some l2) =>
        [ /\ l = NE_append l1 l2
        &    NE_last l1 < before <= NE_head l2
        ]

    | (Some l1, None) => l = l1 /\ NE_last l1 < before
    | (None, Some l2) => l = l2 /\ before <= NE_head l2
    | (None, None)    => False
    end
  }.

(** Return two sublists of [l] such that for every element in the first
    sublist, [f elem] return [true]. *)
Fixpoint usePosSpan (before : nat) `(H : NE_StronglySorted upos_lt l) :
  UsePosSublistsOf before H.
Proof.
  destruct l as [x|x xs] eqn:Heqe.
    destruct (x < before) eqn:Heqef.
      exists (Some (NE_Sing x), None).
      by split.
    exists (None, Some (NE_Sing x)).
      by split; try rewrite leqNgt Heqef.

  destruct (x < before) eqn:Heqef.
  - Case "x < before".
    destruct (usePosSpan before xs)
      as [[[l1| ] [l2| ]] Hsublists];
    try match goal with
          [ |- NE_StronglySorted _ _ ] => by inversion H
        end;
    inversion Hsublists;

    [ SCase "sublists = (Some, Some)";
      eexists (Some (NE_Cons x l1), Some l2)
    | SCase "sublists = (Some, None)";
      eexists (Some (NE_Cons x l1), None)
    | SCase "sublists = (None, Some)";
      eexists (Some (NE_Sing x), Some l2) ];
    simpl; split; f_equal; try assumption;
    intuition; constructor; assumption.

  - Case "before <= x".
    eexists (None, Some (NE_Cons x xs)).
    by split; try rewrite leqNgt Heqef.
Defined.

Lemma usePosSpan_spec (before : nat) `(H : NE_StronglySorted upos_lt l) :
  (usePosSpan before H).1 <> (None, None).
Proof. by case: (usePosSpan before H) => [[[?| ] [?| ]] ?]. Qed.
