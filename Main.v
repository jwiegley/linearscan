(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.Allocate.
Require Import LinearScan.Assign.
Require Import LinearScan.Blocks.
Require Import LinearScan.Build.
Require Import LinearScan.Interval.
Require Import LinearScan.LiveSets.
Require Import LinearScan.Loops.
Require Import LinearScan.Resolve.
Require Import LinearScan.ScanState.
Require Import LinearScan.Morph.
Require Import String.

Generalizable All Variables.

Inductive FinalStage : Set :=
  | BuildingIntervalsFailed
  | AllocatingRegistersFailed.

Record ScanStateDescSet (maxReg : nat) : Set := {
    s_nextInterval : nat;

    s_intervals : Vec IntervalDesc s_nextInterval;
    s_fixedIntervals : Vec (option IntervalDesc) maxReg;

    (* The [nat] in this member indicates the beginning position of the
       interval. *)
    s_unhandled : seq (nat * nat);       (* starts after pos *)
    s_active    : seq (nat * nat);       (* ranges over pos *)
    s_inactive  : seq (nat * nat);       (* falls in lifetime hole *)
    s_handled   : seq (nat * option nat) (* ends before pos *)
}.

Definition toScanStateDescSet `(sd : ScanStateDesc maxReg) :
  ScanStateDescSet maxReg :=
  {| s_nextInterval   := nextInterval sd
   ; s_intervals      := vmap (fun x => @getIntervalDesc x.1 x.2) (intervals sd)
   ; s_fixedIntervals := vmap (fun mx =>
                                 match mx with
                                 | Some x => Some (@getIntervalDesc x.1 x.2)
                                 | None => None
                                 end)
                              (fixedIntervals sd)
   ; s_unhandled      := [seq (nat_of_ord (fst i), snd i) | i <- unhandled sd ]
   ; s_active         := [seq (nat_of_ord (fst i),
                               nat_of_ord (snd i)) | i <- active sd ]
   ; s_inactive       := [seq (nat_of_ord (fst i),
                               nat_of_ord (snd i)) | i <- inactive sd ]
   ; s_handled        := [seq (nat_of_ord (fst i),
                               option_map (fun x => nat_of_ord x) (snd i))
                         | i <- handled sd ]
   |}.

Record Details {blockType1 blockType2 : Set} (maxReg : nat) : Set := {
  reason          : option (SSError * FinalStage);
  liveSets        : IntMap BlockLiveSets;
  inputBlocks     : seq blockType1;
  allocatedBlocks : seq blockType2;
  scanStatePre    : option (ScanStateDescSet maxReg);
  scanStatePost   : option (ScanStateDescSet maxReg);
  loopState       : LoopState
}.

Definition linearScan
  `{dict : Monad m} {blockType1 blockType2 opType1 opType2 : Set}
  (maxReg : nat) (registers_exist : maxReg > 0)
  (binfo : BlockInfo blockType1 blockType2 opType1 opType2)
  (oinfo : @OpInfo maxReg m dict opType1 opType2)
  (blocks : seq blockType1) : Yoneda m (Details maxReg) := fun _ k =>
  (* order blocks and operations (including loop detection) *)
  z <-- computeBlockOrder binfo blocks ;;
  let: (loops, blocks1) := z in

  (* create intervals with live ranges *)
  let liveSets  := computeLocalLiveSets binfo oinfo blocks1 in
  let liveSets' := computeGlobalLiveSetsRecursively binfo blocks1 liveSets in

  match buildIntervals binfo oinfo blocks1 loops liveSets' with
  | inl err =>
    pure $ k $ Build_Details _ _ maxReg
      (Some (err, BuildingIntervalsFailed)) liveSets' blocks1 [::]
      None None loops
  | inr ssig =>
    (* allocate registers *)
    let opCount := (countOps binfo blocks1).+1 in
    match walkIntervals registers_exist ssig.2 opCount with
    | inl (err, ssig') =>
      pure $ k $ Build_Details _ _ maxReg
        (Some (err, AllocatingRegistersFailed)) liveSets' blocks1 [::]
        (Some (toScanStateDescSet ssig.1))
        (Some (toScanStateDescSet ssig'.1)) loops
    | inr ssig' =>
        let sd       := finalizeScanState ssig'.2 opCount.*2 in
        let allocs   := determineAllocations sd in
        let mappings := resolveDataFlow binfo allocs blocks1 liveSets' in

        (* replace virtual registers with physical registers *)
        blocks2 <--
          assignRegNum binfo oinfo allocs liveSets' mappings blocks1 ;;
        pure $ k $ Build_Details _ _ maxReg None liveSets' blocks1 blocks2
          (Some (toScanStateDescSet ssig.1))
          (Some (toScanStateDescSet sd)) loops
    end
  end.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(** Danger!  Using Int is efficient, but requires we know we won't exceed its
    bounds. *)
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "(Prelude.succ)"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (n Prelude.- 1))".

Extract Inductive String.string => "Prelude.String" ["[]" "(:)"].

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.LT" "Prelude.EQ" "Prelude.GT"].

Extract Inlined Constant safe_hd => "Prelude.head".
Extract Inlined Constant sumlist => "Data.List.sum".
(* Extract Inlined Constant lebf    => "Data.Ord.comparing". *)
(* Extract Inlined Constant insert  => "Data.List.insertBy". *)

Extract Inlined Constant Arith.Plus.tail_plus => "(Prelude.+)".

Extraction Implicit widen_id [ n ].
Extraction Implicit widen_fst [ n ].

Extract Inlined Constant widen_id           => "".
Extract Inlined Constant widen_fst          => "Prelude.id".
Extract Inlined Constant List.destruct_list => "LinearScan.Utils.uncons".
Extract Inlined Constant list_membership    => "Prelude.const".

Extract Inductive NonEmpty => "[]" ["(:[])" "(:)"].

Extraction Blacklist String List Vector NonEmpty.

Separate Extraction linearScan.

(* Show which axioms we depend on for this development. *)
Print Assumptions linearScan.

(* Print Libraries. *)