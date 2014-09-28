Require Import Lib.
Require Import NonEmpty.

(** ** UsePos *)

(** A "use position", or [UsePos], identifies an exact point in the
    instruction stream where a particular variable is used.  If this usage
    requires the use of a physical register, then [regReq] is [true] for that
    use position. *)

Record UsePos : Set := {
  uloc   : nat;
  regReq : bool
}.

(** ** Range *)

(** The *extent* of a [Range] is the set of use positions it ranges over,
    inclusively.

    A Range is built up from a set of use positions, and defines the inclusive
    range of those positions.  It can be extended, or split, but never shrunk.
    Also, the non-empty list of use positions is not guaranteed to be in any
    order, and overlapping use positions are accepted but only the most recent
    one "wins". *)

Record RangeDesc := {
    rbeg : nat;
    rend : nat;
    ups  : NonEmpty UsePos;

    range_nonempty : rbeg < rend         (* this comes in handy *)
}.

Inductive Range : RangeDesc -> Set :=
  | R_Sing u :
    Range {| rbeg := uloc u
           ; rend := S (uloc u)
           ; ups  := NE_Sing u
           ; range_nonempty := le_n (S (uloc u))
           |}

  | R_Cons u x : Range x -> forall (H : uloc u < rbeg x),
    Range {| rbeg := uloc u
           ; rend := rend x
           ; ups  := NE_Cons u (ups x)
           ; range_nonempty := Lt.lt_trans _ _ _ H (range_nonempty x)
           |}

  | R_Extend x b' e' : Range x ->
    Range {| rbeg := min b' (rbeg x)
           ; rend := Peano.max e' (rend x)
           ; ups  := ups x
           ; range_nonempty := min_lt_max _ _ _ _ (range_nonempty x)
           |}.

Definition rangeExtent (x : RangeDesc) := rend x - rbeg x.

Definition rangesIntersect (x y : RangeDesc) : bool :=
  if rbeg x <? rbeg y
  then rbeg y <? rend x
  else rbeg x <? rend y.

Definition rangesIntersectionPoint (x y : RangeDesc) : option nat :=
  if rangesIntersect x y
  then Some (min (rbeg x) (rbeg y))
  else None.

Definition anyRangeIntersects (is js : NonEmpty RangeDesc) : bool :=
  fold_right
    (fun r b => orb b (existsb (rangesIntersect r) (NE_to_list js)))
    false (NE_to_list is).

Fixpoint NE_fold_left {a b : Set} (f : a -> b -> a) (ne : NonEmpty b) (z : a) : a :=
  match ne with
    | NE_Sing x => f z x
    | NE_Cons x xs => NE_fold_left f xs (f z x)
  end.

Definition firstIntersectionPoint (rd1 rd2 : NonEmpty RangeDesc)
  : option nat :=
  NE_fold_left
    (fun acc rd =>
       match acc with
       | Some x => Some x
       | None =>
         NE_fold_left
           (fun acc' rd' =>
              match acc' with
              | Some x => Some x
              | None => rangesIntersectionPoint rd rd'
              end) rd2 None
       end) rd1 None.
