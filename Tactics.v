Ltac inv H := inversion H; subst; simpl; auto.

Ltac contra := intros top; contradiction top; clear top.