Require Import Lib.
Require Import NonEmpty.
Require Import Hask.Alternative.

Open Scope nat_scope.

Import EqNotations.

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

Definition upos_le (x y : UsePos) := uloc x <= uloc y.
Definition upos_lt (x y : UsePos) := uloc x < uloc y.

Program Instance upos_lt_trans : Transitive upos_lt.
Obligation 1. unfold upos_lt in *. omega. Qed.

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
    rend : nat;                 (* 1 past the last use position *)
    ups  : NonEmpty UsePos;

    ups_head : rbeg <= uloc (NE_head ups);
    ups_last : uloc (NE_last ups) < rend;
    ups_sorted : NE_StronglySorted UsePos upos_lt ups;

    range_nonempty : rbeg < rend         (* this comes in handy *)
}.

(** ** Range *)

(** A [Range] constrains how a [RangeDesc] may be constructed, and maintains
    any invariants. *)

Inductive Range : RangeDesc -> Prop :=
  | R_Sing u :
    Range {| rbeg := uloc u
           ; rend := S (uloc u)
           ; ups  := NE_Sing u

           ; ups_head   := le_n (uloc u)
           ; ups_last   := lt_n_Sn (uloc u)
           ; ups_sorted := SSorted_sing _ _ u

           ; range_nonempty := le_n (S (uloc u))
           |}

  | R_Cons u x : Range x -> forall (H : uloc u < rbeg x),
    Range {| rbeg := uloc u
           ; rend := rend x
           ; ups  := NE_Cons u (ups x)

           ; ups_head   := le_n (uloc u)
           ; ups_last   := ups_last x
           ; ups_sorted := NE_StronglySorted_cons _ _ _ _
               (lt_le_trans _ _ _ H (ups_head x)) (ups_sorted x)

           ; range_nonempty := Lt.lt_trans _ _ _ H (range_nonempty x)
           |}

(*
  | R_Append l r : Range l -> Range r -> forall (H : rend l <= rbeg r),
    Range {| rbeg := rbeg l
           ; rend := rend r
           ; ups  := NE_append (ups l) (ups r)

           ; ups_head   := eq_ind_r (fun u => rbeg l ≤ uloc u)
                                    (ups_head l) NE_head_append_spec
           ; ups_last   := eq_ind_r (fun u => uloc u < rend r)
                                    (ups_last r) NE_last_append_spec
           ; ups_sorted := NE_StronglySorted_append _ _ _ _
                (lt_le_trans _ _ _ (ups_last l) (le_trans _ _ _ H (ups_head r)))
                (ups_sorted l) (ups_sorted r)

           ; range_nonempty :=
               lt_le_shuffle (range_nonempty l) H (range_nonempty r)
           |}
*)

  | R_Extend x b' e' : Range x ->
    Range {| rbeg := min b' (rbeg x)
           ; rend := Peano.max e' (rend x)
           ; ups  := ups x

           ; ups_head   := le_min _ _ _ (ups_head x)
           ; ups_last   := lt_max _ _ _ (ups_last x)
           ; ups_sorted := ups_sorted x

           ; range_nonempty := min_lt_max _ _ _ _ (range_nonempty x)
           |}.

Definition getRangeDesc `(r : Range d) := d.

Coercion getRangeDesc : Range >-> RangeDesc.

Definition rangeExtent `(Range r) := rend r - rbeg r.

Definition rangesIntersect `(Range x) `(Range y) : bool :=
  if rbeg x <? rbeg y
  then rbeg y <? rend x
  else rbeg x <? rend y.

Definition rangeIntersectionPoint `(xr : Range x) `(yr : Range y) : option nat :=
  if rangesIntersect xr yr
  then Some (min (rbeg x) (rbeg y))
  else None.

Definition findRangeUsePos `(Range r) (f : UsePos -> bool) : option UsePos :=
  let check u := if f u then Some u else None in
  let fix go us := match us with
      | NE_Sing u     => check u
      | NE_Cons u us' => check u <|> go us'
      end in
  go (ups r).

Fixpoint usePosSpan (f : UsePos -> bool) (l : NonEmpty UsePos)
  : (option (NonEmpty UsePos) * option (NonEmpty UsePos)) :=
  match l with
    | NE_Sing u =>
        if f u
        then (Some l, None)
        else (None, Some l)
    | NE_Cons u us' =>
        let (xl, xr) := usePosSpan f us' in
        if f u
        then match xl with
               | Some xl' => (Some (NE_Cons u xl'), xr)
               | None => (Some (NE_Sing u), xr)
             end
        else match xr with
               | Some xr' => (xl, Some (NE_Cons u xr'))
               | None => (xl, Some (NE_Sing u))
             end
  end.

Definition rangeSpan (f : UsePos -> bool) `(r : Range rd)
  : (option { rd1 : RangeDesc | Range rd1 } *
     option { rd2 : RangeDesc | Range rd2 }).
Proof.
  destruct rd.
  pose proof ups0 as ups1.
  apply (usePosSpan f) in ups1.
  destruct ups1.
(*
  let maybeAppend `(x : Range d) (mr : option { d : RangeDesc | Range d })
        : option { d : RangeDesc | Range d } :=
      match mr with
        | Some (exist rd' r') =>
            let res := R_Append d rd' x r' _ in
            Some (exist _ (getRangeDesc res) res)
        | None => Some (exist _ d x)
      end in
  let (xl, xr) := usePosSpan f (ups rd) in
  let xl' := match xl with
               | Some xl' => R_Extend (R_Sing x) (rbeg r) (rbeg r)
  match ups rd with
    | NE_Sing x =>
        if f x
        then (Some (exist _ rd r), None)
        else (None, Some (exist _ rd r))
    | NE_Cons x xs =>
        let (xl, xr) := rangeSpan f xs in
        if f x
        then let r' :=  in
             (maybeAppend r' xl, xr)
        else let r' := R_Extend (R_Sing x) (rend r) (rend r) in
             (xl, maybeAppend r' xr)
  end.
*)
Admitted.