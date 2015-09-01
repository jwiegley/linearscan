(** Linear Scan Register Allocator

    The linear scan algorithm in this module is documented by the paper
    "Optimized Interval Splitting in a Linear Scan Register Allocator" by
    Christian Wimmer and Hanspeter Mӧssenbӧck:

    https://www.usenix.org/legacy/events/vee05/full_papers/p132-wimmer.pdf
*)
Require Import LinearScan.Lib.
Require Export Hask.Haskell.
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
Require Import LinearScan.Verify.

Generalizable All Variables.

Inductive FinalStage : Set :=
  | BuildingIntervalsFailed
  | AllocatingRegistersFailed.

Record ScanStateDescSet (maxReg : nat) : Set := {
    s_nextInterval : nat;

    s_intervals      : seq IntervalDesc;
    s_fixedIntervals : seq (option IntervalDesc);

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
   ; s_intervals      := map (fun x => @getIntervalDesc x.1 x.2)
                             (vec_to_seq (intervals sd))
   ; s_fixedIntervals := map (fun mx =>
                                match mx with
                                | Some x => Some (@getIntervalDesc x.1 x.2)
                                | None => None
                                end)
                             (vec_to_seq (fixedIntervals sd))
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
  reason          : option (seq SSTrace * FinalStage);
  liveSets        : IntMap BlockLiveSets;
  resolvingMoves  : IntMap (seq ResolvingMoveSet);
  inputBlocks     : seq blockType1;
  orderedBlocks   : seq blockType1;
  allocatedBlocks : (IntMap (RegStateDescSet * seq AllocError) *
                     IntMap RegStateDescSet *
                     IntMap RegStateDescSet)
                        + seq blockType2;
  scanStatePre    : option (ScanStateDescSet maxReg);
  scanStatePost   : option (ScanStateDescSet maxReg);
  loopState       : LoopState
}.

Definition linearScan
  `{dict : Monad m} {blockType1 blockType2 opType1 opType2 : Set}
  (maxReg : nat) (registers_exist : maxReg > 0)
  (binfo : BlockInfo blockType1 blockType2 opType1 opType2)
  (oinfo : @OpInfo maxReg m dict opType1 opType2)
  (useVerifier : UseVerifier) (blocks : seq blockType1) : m (Details maxReg) :=
  (* order blocks and operations (including loop detection) *)
  z <-- computeBlockOrder binfo blocks ;;
  let: (loops, blocks1) := z in

  (* create intervals with live ranges *)
  liveSets  <-- computeLocalLiveSets binfo oinfo blocks1 ;;
  liveSets' <-- computeGlobalLiveSetsRecursively binfo blocks1 liveSets ;;

  ssig <-- buildIntervals binfo oinfo blocks1 loops liveSets' ;;
  (* allocate registers *)
  let opCount := (countOps binfo blocks1).+1 in
  match walkIntervals registers_exist ssig.2 opCount.*2.+1 with
  | inl (err, ssig') =>
    pure $ Build_Details _ _ maxReg (Some (err, AllocatingRegistersFailed))
      liveSets' emptyIntMap blocks blocks1 (inr [::])
      (Some (toScanStateDescSet ssig.1))
      (Some (toScanStateDescSet ssig'.1)) loops

  | inr ssig' =>
      match finalizeScanState ssig'.2 opCount.*2 with
      | inl err =>
        pure $ Build_Details _ _ maxReg (Some (err, AllocatingRegistersFailed))
          liveSets' emptyIntMap blocks blocks1 (inr [::])
          (Some (toScanStateDescSet ssig.1))
          (Some (toScanStateDescSet ssig'.1)) loops

      | inr (exist sd _) =>
        let allocs := determineAllocations sd in
        mappings <-- resolveDataFlow binfo allocs blocks1 liveSets' ;;
        res <-- assignRegNum binfo oinfo useVerifier allocs liveSets'
                             mappings loops blocks1 ;;
        let: (moves, blocks2) := res in
        let blockInfo := match blocks2 with
          | inr xs => inr xs
          | inl vs =>
              inl (verErrors vs,
                   IntMap_map (fun x => fromRegStateDesc x.1) (verInit vs),
                   IntMap_map (fun x => fromRegStateDesc x.1) (verFinal vs))
          end in

        pure $ Build_Details _ _ maxReg None
          liveSets' moves blocks blocks1 blockInfo
          (Some (toScanStateDescSet ssig.1))
          (Some (toScanStateDescSet sd)) loops
      end
  end.

Require Import Hask.Haskell.

(* Set Extraction Conservative Types. *)

Extraction Implicit widen_id [ n ].
Extraction Implicit widen_fst [ n ].

Extract Inlined Constant widen_id  => "".
Extract Inlined Constant widen_fst => "Prelude.id".

Separate Extraction linearScan.

(* Show which axioms we depend on for this development. *)
Print Assumptions linearScan.

(* Print Libraries. *)