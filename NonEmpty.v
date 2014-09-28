(** ** NonEmpty lists *)

Inductive NonEmpty (a : Set) : Set :=
  | NE_Sing : a -> NonEmpty a
  | NE_Cons : a -> NonEmpty a -> NonEmpty a.

Arguments NE_Sing [_] _.
Arguments NE_Cons [_] _ _.

Fixpoint NE_to_list {a} (ne : NonEmpty a) : list a :=
  match ne with
    | NE_Sing x => cons x nil
    | NE_Cons x xs => cons x (NE_to_list xs)
  end.

Definition NE_hd {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x _ => x
  end.

Fixpoint NE_tl {a} (ne : NonEmpty a) : a :=
  match ne with
    | NE_Sing x => x
    | NE_Cons x xs => NE_tl xs
  end.

Fixpoint NE_fold_left {a b : Set} (f : a -> b -> a) (ne : NonEmpty b) (z : a) : a :=
  match ne with
    | NE_Sing x => f z x
    | NE_Cons x xs => NE_fold_left f xs (f z x)
  end.
