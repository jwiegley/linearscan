(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import LinearScan.Allocate.
Require Import LinearScan.Lib.
Require Import LinearScan.NonEmpty.
Require Import LinearScan.Machine.

Module MyMachine <: Machine.

Definition maxReg := 32.
Extract Constant maxReg => "32".

Lemma registers_exist : (maxReg > 0).
Proof. unfold maxReg. exact: ltn0Sn. Qed.

End MyMachine.

Module Import LinearScan := MAllocate MyMachine.

Definition determineIntervals {op : Set} (ops : OpList op) : ScanStateSig :=
  let mkint (ss : ScanStateSig) (mx : option RangeSig)
            (f : forall sd, ScanState sd -> forall d, Interval d
                   -> ScanStateSig) :=
      let: (exist sd st) := ss in
      match mx with
      | Some (exist _ r) => f _ st _ (I_Sing r)
      | None => ss
      end in

  let handleVar ss mx := mkint ss mx $ fun _ st _ i =>
        packScanState (ScanState_newUnhandled st i) in

  let: (varRanges, regRanges) := processOperations ops in
  let regs := vmap (fun mr =>
                if mr is Some r
                then Some (packInterval (I_Sing r.2))
                else None) regRanges in

  let s0 := ScanState_nil in
  let s1 := ScanState_setFixedIntervals s0 regs in
  let s2 := packScanState s1 in

  foldl handleVar s2 varRanges.

Definition allocateRegisters {op : Set} (ops : OpList op) :
  (SSError + seq (AllocationInfo op))%type :=
  uncurry_sig linearScan (determineIntervals ops).

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(** Danger!  Using Int is efficient, but requires we know we won't exceed its
    bounds. *)
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant apply   => "(Prelude.$)".
Extract Inlined Constant safe_hd => "Prelude.head".
Extract Inlined Constant sumlist => "Data.List.sum".
Extract Inlined Constant lebf    => "Data.Ord.comparing".
Extract Inlined Constant insert  => "Data.List.insertBy".

Extract Inlined Constant Arith.Plus.tail_plus => "(Prelude.+)".

Extraction Implicit widen_id [ n ].
Extraction Implicit widen_fst [ n ].

Extract Inlined Constant widen_id           => "".
Extract Inlined Constant widen_fst          => "Prelude.id".
Extract Inlined Constant List.destruct_list => "LinearScan.Utils.uncons".
Extract Inlined Constant list_membership    => "Prelude.const".

(* Avoid extracting this function, which has no computational value, but Coq
   insists on ignoring its opacity. *)
Extract Inlined Constant boundedTransport =>
  "LinearScan.Utils.boundedTransport'".

Extraction Blacklist String List Vector NonEmpty.

Separate Extraction allocateRegisters NE_map.

(* Show which axioms we depend on for this development. *)
Print Assumptions allocateRegisters.

(* Print Libraries. *)