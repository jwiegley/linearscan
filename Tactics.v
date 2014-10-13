Ltac inv H := inversion H; subst; simpl; auto.

Ltac contra := intros top; contradiction top; clear top.

Ltac invert := intros top; inversion top; clear top.

Tactic Notation "invert" "as" simple_intropattern(pat) :=
  intros top; inversion top as pat; clear top.
