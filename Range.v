Require Import Lib.
Require Import NonEmpty.

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

(** ** RangeDesc *)

(** The *extent* of a [RangeDesc] is the set of use positions it ranges over,
    inclusively, plus any extensions that have been applied to the range.

    A [RangeDesc] is built up from a set of use positions, and defines the
    inclusive range of those positions.  It can be extended, or split, but
    never shrunk.  Also, the non-empty list of use positions is not guaranteed
    to be in any order, and overlapping use positions are accepted, where the
    most recent one "wins".

    Although minimally there is at least one position fixing the beginning and
    end of the range, it's possible for the range to extend before or beyond
    the first and last use positions; for example, in the case of a use
    position ranging over the scope of a loop. *)

Record RangeDesc := {
    rbeg : nat;
    rend : nat;
    ups  : NonEmpty UsePos;

    range_nonempty : rbeg < rend         (* this comes in handy *)
}.

(** ** Range *)

(** A [Range] constrains how a [RangeDesc] may be constructed, and maintains
    any invariants. *)

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

Definition getRangeDesc `(r : Range d) := d.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition rangeExtent `(Range r) := rend r - rbeg r.

Definition rangesIntersect `(Range x) `(Range y) : bool :=
  if rbeg x <? rbeg y
  then rbeg y <? rend x
  else rbeg x <? rend y.

Definition rangesIntersectionPoint `(xr : Range x) `(yr : Range y) : option nat :=
  if rangesIntersect xr yr
  then Some (min (rbeg x) (rbeg y))
  else None.
