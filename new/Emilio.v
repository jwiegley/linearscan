Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
Require Import tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NonEmpty.

  Variable T : eqType.

  Definition NonEmpty := {n : nat & n.+1.-tuple T}.

  Coercion ne_seq (l : NonEmpty) : seq T.
  Proof. by case: l=> n t; exact t. Defined.

  Coercion t_ne n (l : n.+1.-tuple T) : NonEmpty.
  Proof. by exists n. Defined.

  Definition NE_append (n1 n2 : NonEmpty) : NonEmpty.
  Proof.
    move: n1 n2=> [n1 t1] [n2 t2].
    exact: existT _ [tuple of t1 ++ t2].
  Defined.

  Definition NE_head (n : NonEmpty) : T.
  Proof. by move: n=> [n t]; exact: thead t. Defined.

  (* option NonEmpty is isomorphic to seq... *)
  Definition one_seq (l : option NonEmpty) : seq T.
  Proof. case: l=>[[n t]|]; last exact: [::]; first exact: t. Defined.

  Definition seq_one (l : seq T) : option NonEmpty.
  Proof. case: l=>[|x xs]; first exact: None; last apply: Some.
         exists (size xs). apply: in_tuple (x :: xs).
  Defined.

End NonEmpty.

Arguments NonEmpty [T].

Section ExampleSpec.

  Variable T : eqType.

  (* Check the head with f, return false if empty *)
  Definition chk_head (f : pred T) (s : seq T) : bool :=
    oapp f false (ohead s).

  (* First spec, using plain lists *)
  Definition seq_spec l l1 l2 (f : pred T) :=
    [&& l == l1 ++ l2 :> seq T
      , all f l1
      & ~~ (chk_head f l2)
    ].

  (* Second version, using option NonEmpty *)
  Definition NE_spec (l : NonEmpty) (f : pred T) (p : option NonEmpty * option NonEmpty) :=
    match p with
      | (Some l1, Some l2) =>
        [ /\ l = NE_append l1 l2
        ,    all f (ne_seq l1)
        &    ~~ f (NE_head l2)
        ]
      | (Some l1, None) => l = l1 /\ all f (ne_seq l1)
      | (None, Some l2) => l = l2 /\ ~~ f (NE_head l2)
      | (None, None)    => False
    end.

  (* Now we prove that both specifications are equal *)

  (* First directon *)
  Lemma spec_equiv1
        (l : NonEmpty) (f : pred T)
        (p : option NonEmpty * option NonEmpty) :
    NE_spec l f p ->
    seq_spec (ne_seq l) (one_seq p.1) (one_seq p.2) f.
  Proof.
    move: l p=> [nl [sl Hl]] [[[n1 [s1 H1]]|] [[n2 [s2 H2]]|]] //=.
    - case: s2 H2=> // x2 s2 H2 [[_ /eqP Hcat]] Hall.
      rewrite /thead (tnth_nth x2) /= => Hneg.
      by apply/and3P.
    - move=> [[_ /eqP Hcat]] Hall.
      by apply/and3P; rewrite cats0.
    - case: s2 H2=> // x2 s2 H2 [[_ /eqP Hcat]].
      rewrite /thead (tnth_nth x2) /= => Hneg.
      by apply/and3P.
  Qed.

  (* Second direction *)
  Lemma spec_equiv2 n (l : n.+1.-tuple T) l1 l2 (f : pred T) :
    seq_spec l l1 l2 f ->
    NE_spec (t_ne l) f (seq_one l1, seq_one l2).
  Proof.
    case: l l1 l2=> l Hl [|x1 s1] [|x2 s2] /and3P[/= /eqP Hcat Hall Hneg];
    rewrite /chk_head /= in Hneg; try split=>//.
    - by case: l Hl Hcat.
    - rewrite Hcat /t_ne in Hl *.
      have/eqP En: size s2 == n by [].
      rewrite -En /= in Hl *.
      by apply/eqP; rewrite eq_Tagged eqE /=.
    - rewrite cats0 in Hcat *.
      rewrite Hcat /t_ne in Hl *.
      have/eqP En: size s1 == n by [].
      rewrite -En /= in Hl *.
      by apply/eqP; rewrite eq_Tagged eqE /=.
    - rewrite Hcat /t_ne in Hl *.
      have/eqP En: size s1 + size (x2 :: s2) == n by rewrite -size_cat.
      rewrite -En /= in Hl *.
      by apply/eqP; rewrite eq_Tagged eqE /=.
  Qed.

End ExampleSpec.
