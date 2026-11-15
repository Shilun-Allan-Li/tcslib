# seq-zk checkpoint 1

Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.
Issued exchange pack: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
Local proof branch: `fill/seq-zk`; checkpoint commit:
`a758032d636fd410b0c4b8a1530a96d000cc467a` (not pushed).

This is checkpoint 1, not the final payload. `InteractiveProof.seqRep` is fully proved and
uses only `propext`, `Classical.choice`, and `Quot.sound`. The other four frozen targets keep
their original statements and `sorry`. Work on the next checkpoints continues.

| Target | Status |
|---|---|
| `InteractiveProof.seqRep` | Proved, checked, standard axioms |
| `InteractiveProofErr.seqRep` | Original admission remains |
| `EfficientProverProofErr.seqRep` | Original admission remains |
| `StatZK.seqRep` | Original admission remains |
| `ZK.seqRep` | Original admission remains |

## Proof and ownership

The verifier machine uses the published counted/search hosts. Perfect completeness is
pointwise on the finite original coin spaces: each final real-phase history is the original
history on its coin slices, so every phase accepts. For soundness, restricting the repeated
verifier tape to its initial original-length prefix preserves uniformity. Its phase-zero
execution agrees with the original verifier against the unchanged arbitrary prover. A base
rejection makes the aggregate conjunction false. The original negligible error therefore
works unchanged. Zero rounds and both first-mover orientations are covered; completeness
also allows zero phases, while soundness uses the frozen positive-phase premise.

Only the lead edited SequentialZK.lean, committed on fill/seq-zk, ran merged checks, and
prepared delivery. No proof branch is pushed.

| Worker | Proved work included in this checkpoint |
|---|---|
| Lead `/root`, tag `seq-zk` | `InteractiveProof.seqRep`; the nine construction/efficiency/completeness/soundness bridges listed below; approved `StatZK_iff` reader |
| `/root/zk_route`, tag `seq-zk-a` | `Normalization.lean` and `NormalizationMachine.lean` |
| `/root/efficiency`, tag `seq-zk-b` | `Efficiency.lean`, all six generic efficiency lemmas |
| `/root/soundness`, tag `seq-zk-c` | `Soundness.lean`, three execution-prefix readers and the adaptive probability bound |

The lead bridges are `Protocol.ProverBounded.seqRep`, `seqVerifier_exec_first`,
`seqRep_outV_eq`, `seqRep_exec_phase_take`, `seqRep_complete`, `seqRep_reject_of_first`,
`seqRep_sound_first`, `seqProver_efficient`, and `seqVerifier_efficient` (the latter eight
inside `Protocol`). The collector lists every stored constant, including private/generated
constants, in `evidence/logs/checkpoint1-axioms/`.

Changed sources: the owned file, its four imported helpers, and the approved reader in
`ZeroKnowledge/Defs.lean`. The module title/status and Contents list now describe the partial
proof status. The existing interactive-proof sketch agrees with the delivered proof.
No target statement, other existing declaration, or global simp attribute was weakened.

## Host and environment

The host-wide cap is **at most three Lean processes across all jobs**. Every lead and
subagent Lean/check invocation uses the issued lean-slot.sh and the default ~/.lean-slots.
The sole narrowed cache get held all three slots; subagents ran no Lake commands. Each has
its own worktree and olean tree, with packages linked read-only to the lead. APFS clones
seed only completed lead TCSlib oleans; no package tree was copied. Lead baseline and working
olean trees are separate, so the genuine base artifacts remain immutable during working
checks. Slot records and the isolation record are delivered.

Preflight: 12 CPUs, 19,327,352,832 physical-memory bytes; initial computed headroom
5,104,074,752 bytes = 4.754 GiB; disk free 229,666,520 KiB on APFS, above the 12 GiB floor.
A later diagnostic snapshot computes 6.438 GiB headroom. No E-RES shortage occurred.
All checkout/scratch paths use the disk-backed APFS volume, not a RAM disk.

Both issued packs and all 237 source hashes verified. The 76 computed Mathlib roots equal
the supplied roots. All present packages match lake-manifest.json; the four documentation
packages are ABSENT. No zero-size oleans. The first-root cache probe passed. The host archive
store already held 32,667 files / 1,595,387,830 bytes (earlier origin unknown); this session
reported no files to download and decompressed 2,107 archives. These are not claimed as new
downloads. The host ~/.elan toolchain is shared under the host addendum.

## Completed checks and remaining final checks

- Exact-base bootstrap: all 237 modules, zero errors/nonzero exits; exactly 23 admission warnings.
- All four helpers checked by their authors and again by the lead in the working tree.
- Approved Defs reader and committed owned module checked by the lead with zero errors.
- Owned module has exactly four remaining target admission warnings.
- Full stored-constant axiom census and named consumer prints completed. The proved target
  and all new helper/bridge declarations use standard axioms. The remaining targets and
  their admitted consumers correctly retain `sorryAx`.
- Base strict/coe seals with PolyExpr.eval both excluded/included completed, with native
  install/identity/instance-mask/EOF guards. SequentialZK passes all four cells. Defs has ten
  inherited diagnostics in each cell, in six declarations: `perfectZK_zeroRounds`,
  `AbortRetry.attempt_poly`, `AbortRetry.exists_retrySimulator`, `AbortRetry.statClose_retry`,
  `PerfectZKAbort.statZK`, and `negligible_inv_pow_sqrt_div`. Every raw log and attribution is
  included. Coe exclusion removes the projection-only FinDist CoeFun instance; it changes no
  baseline failure. Exact request sets and exclusions are delivered.
- Checkpoint owned canonical coe seal (PolyExpr.eval excluded): zero errors; all 1,852
  requests verified at installation and EOF. Batching 2,250 changes command grouping only,
  not coverage, native guards, proof budgets, or source bytes.
- Width: every delivered library file is <=100 columns and <=1,000 lines.
- Style lint: base and checkpoint both 92 FAIL / 101 WARN. No new FAIL. The only WARN line
  difference is an improvement: Defs now lists two missing readers instead of three,
  because StatZK gained its approved reader. Full line-set diff is included.
- git am replay in independent scratch clone reproduces the exact checkpoint commit hash
  and all six source files, using COMMITS.tsv committer metadata and disabled signing.

The final merged sweep, complete final helper/owned strict+coe seal matrix, paired controls,
and explicit-unfold scan remain final-delivery work. Prepared but unrun checkpoint seal
sources are included and are not claimed as passing checks. This checkpoint is delivered now
because the issued route calls for a whole-declaration checkpoint after InteractiveProof;
it is not a claim that final intake checks are complete. This timing judgment is disclosed
under Seyoon's instruction to work autonomously and disclose exceptions.

## Overlap and reuse

Searches before implementation are in `lead-searches.log` and each subagent's search logs.
Every overlap below is either direct reuse or a disclosed generalization; no foreign private
lemma was copied.

- `ProverBounded.seqRep`: nearest Interaction.lean:383 `ProverBounded.mono` changes the bound,
  not the protocol; the new lemma reads the repeated prover and reuses proverBounded_iff.
- `seqVerifier_exec_first`: nearest owned original `seqRep_exec_phase` (base line 287) assumes
  the honest repeated prover. The new induction covers an arbitrary unchanged prover in
  phase zero, using the published move-index readers rather than that stronger honest premise.
- `seqRep_outV_eq`: combines owned `seqVerdict_eq` (base :233) and Interaction.lean:449 outV_eq
  with the existing move count. It publishes the final-history specialization.
- `seqRep_exec_phase_take`: combines original seqRep_exec_phase, the new generic exec_snd_take,
  and core List.take_drop; it adds final-history restriction, not a duplicate phase induction.
- `seqRep_complete`: nearest graph-specific completeness arguments in
  ZeroKnowledge/ThreeColoring/ProtocolProofs.lean and GraphIsomorphism/Proofs.lean; directly
  reuses HardcoreBit/Basic.lean:110 forall_of_uprob_eq_one and :123 uprob_eq_one_of_forall,
  Adversary.lean:98 length_coinBlock and :216 ofFn_padFin_of_length.
- `seqRep_reject_of_first`: new aggregate-conjunction consequence of the first-phase reader;
  nearest original seqRep_exec_phase has the different honest-prover premise noted above.
- `seqRep_sound_first`: reuses HardcoreBit.pushesUniform_restrict/prodMap and public
  Asymptotic/ReductionSupport.lean:288 take_ofFn_castLE. GI/Proofs.lean:813
  pushesUniform_castLE is a specialization of the same restriction reader, not copied.
- `seqProver_efficient` and `seqVerifier_efficient`: construction-specific bridges directly
  reuse SeqEfficiency.phase_efficient and verifier_efficient; no machine argument is repeated.
- `StatZK_iff`: exact defining reader, analogous to Defs.lean:164 ZK_iff; added only with the
  explicit scope approval below, in its defining file.
- `encodeMsgs_eq_encWords`: exactly matches the local have in SecureComputation/Yao.lean:352,
  outside the allowed closure. It is re-derived from published encoding nil/cons readers.
  ThreeColoring/Machines.lean:911 encodeMsgs_eq_flatMap is another nearest relative.
- `normalizeMsgs` and its reader/invariants are new canonical-slot operations. Their length,
  per-message, fixed-point, and encoding bounds directly reuse decWords_encWords,
  List.take_of_length_le, and BinaryArith/Words.lean:81 length_encWords_le.
  CommitmentLemmas.lean:241 gives the same generic encoding-size bound with a larger dependency;
  no copy is used. `length_encodeMsgs_normalizeMsgs_le` specializes the directly reused bound.
- `polyTimeComputable_encWords_decWords`, `polyTimeComputable_decWords_getD`, and
  `polyTimeComputable_encode_normalizeMsgs`: directly reuse Words.lean:221 mapW,
  BinaryArith/Loops.lean:391 getW, EncodingMachines.lean:459 truncate_poly, and
  ThreeColoring/Machines.lean:159 counted emission, rather than copying hosts.
- `take_encodeMsgs` uses CommitmentLemmas.lean:233 encodeMsgs_append plus List.take_append;
  its new encoded-prefix formula had no public match in the searched closure. `takeMsgs_poly`
  directly composes this with the public drop/count machinery. `phase_poly`,
  `phase_efficient`, `verdict_poly`, and `verifier_efficient` reuse GI/Proofs.lean's
  efficient_of_polyTime and GI/EfficiencyRep.lean's message-count/coin-slice readers and the
  public bounded-index search. All per-declaration details are in seq-zk-b/searches.md.
- `exec_prefix`, `exec_fst_take`, and `exec_snd_take` are execution specializations of
  published exec_succ and core prefix_iff_eq_take, not copies of a prior execution lemma.
- `uprob_adaptive_all_le` generalizes ThreeColoring/Protocol.lean:307 `uprob_adaptive_escape` from rate 1-1/m to arbitrary nonnegative s. It
  directly reuses OneWayFunctions/Basic.lean:90 uprob_and_le_mul and Fin.snocEquiv.
  Its local cast algebra re-derives the general-type versions of private :275/:286
  challengesBefore_snoc_castSucc/last, which are specialized and private. No private lemma
  is referenced or copied; this overlap is explicitly disclosed.

## Scope requests

One explicit request: add the nine-line StatZK_iff reader in frozen
TCSlib/Cryptography/ZeroKnowledge/Defs.lean. Seyoon answered **"Approve this reader addition"**.
The exact request, answer and diff are in evidence/scope-request/. No other frozen file changed.
Seyoon later authorized best judgment on exceptions and messaging workers for shared Mac
resources; that instruction is retained in evidence/coordination/. Shared-slot coordination
with derand, sc-garble and Ladner is recorded there. No other worker's tree or process was
edited, removed or interrupted.

## Promotion and reader requests

At a shared-file window, consider moving the Strategy/BinArith encoding bridge, encoded-prefix
reader and generic exec-prefix readers beside encodeMsgs/exec in Interaction.lean; decoded
canonicalization/lookup beside the BinaryArith word-list hosts; generic repetition-machine
closure facts into a shared encoded-interaction layer; and the arbitrary-rate adaptive bound
into the probability layer. These are promotion requests, not frozen-file edits in this payload.

## Payload and replay

patches/ contains the complete format-patch series at the issue base. COMMITS.tsv includes
all author/committer metadata and the signing column; commits use commit.gpgsign=false.
src/ contains every changed/new repository file. evidence/ includes input packs, tools,
probe/seal/control preparations, raw successful and failed logs, requests, source snapshots,
subagent records and manifests. Its SHA256SUMS covers every evidence file except itself.
The top-level SHA256SUMS covers every delivered file except itself; exact path equality and
hashes are verified before the exchange commit/push. Delivery touches only inbox/fills/seq-zk/.
