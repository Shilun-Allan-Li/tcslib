# seq-zk checkpoint 2

Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.
Issued exchange pack: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
Local proof branch: `fill/seq-zk`, kept local. Complete two-commit series:
`a758032d636fd410b0c4b8a1530a96d000cc467a`,
`e978a28274fdeb545e622ae28747221088352512`.

This is checkpoint 2, not the final payload. Three complete target declarations are proved
and checked with only `propext`, `Classical.choice`, and `Quot.sound`:

| Target | Status |
|---|---|
| `InteractiveProof.seqRep` | Proved at checkpoint 1, rechecked after completeness refactor |
| `InteractiveProofErr.seqRep` | Proved: exact soundness error `s(n)^Q(n)` |
| `EfficientProverProofErr.seqRep` | Proved: efficiency, bound and every-witness completeness |
| `StatZK.seqRep` | Original admission remains; endpoint/statistical assembly in progress |
| `ZK.seqRep` | Original admission remains; advised phase reduction/assembly in progress |

All five frozen statement headers are byte-for-byte identical to the issue base
(`evidence/logs/checkpoint2-statements.log`). No other existing declaration or global simp
attribute was weakened. The remaining two targets and their affected consumers retain
`sorryAx`; they are not claimed proved. Work continues after this checkpoint.

## Proof and ownership

The repeated verifier and prover machines use published counted/search hosts. Perfect
completeness is pointwise on original coin slices. The explicit-error soundness engine first
fixes the arbitrary prover's tape, then uses only earlier verifier blocks to determine each
induced prefix. The original proof's soundness applies to the prover that hardwires that
prefix. The generic adaptive bound multiplies the conditional acceptance bounds to `s^Q`.
The binary aggregate verdict converts acceptance to rejection. This covers zero rounds,
odd rounds, either first mover and arbitrary cheating provers. The abstract error engine
also covers zero phases (error one); the frozen positive-phase hypotheses remain unchanged.
The native compiler reports an unused `hQ` in InteractiveProofErr.seqRep for this reason.
This benign warning is disclosed; it does not weaken a statement or add a style-lint WARN.

Only the lead edited SequentialZK.lean, committed on fill/seq-zk, ran merged checks and
prepared delivery. The module title/status and precise Contents list describe these three
proved results. Their existing sketches match the delivered arguments.

| Worker | Included proofs and helper ownership |
|---|---|
| Lead `/root`, `seq-zk` | All three target bodies; owned construction/specification/efficiency/completeness/soundness bridges; PrefixFolds, PrefixLaws, ProofTransfers; approved StatZK_iff |
| `/root/zk_route`, `seq-zk-a` | Normalization, NormalizationMachine, PhaseView, Statistical, ExecutionBounds |
| `/root/efficiency`, `seq-zk-b` | Efficiency, WrappedVerifier, SimulatorMachine, RealPhases, PaddedProverSpec |
| `/root/soundness`, `seq-zk-c` | Soundness, Phases, Congruence, VerifierPrefix, ErrSoundness, RepeatedVerifier, RepeatedSoundness |

There are 22 changed/new library files: the owned module, twenty helpers and the approved
Defs reader. Their source bytes are in src/. The collector records all 306 stored constants,
including generated/private constants, with their axioms. Compared with checkpoint 1,
155 new/changed axiom-set rows contain no `sorryAx`. Full new public statements and formulas
are in their docstrings; source and collector inventories identify every new declaration.
New owned bridges after checkpoint 1 are exec_boundary_lengths, seqRep_verifierSpec and
seqRep_proverSpec. Existing seqRep completeness now directly uses ProofTransfers.complete,
which in turn reuses the published ProverBounded.exists_complete interface.

The statistical infrastructure already included here supplies fixed-tape wrapped verifiers,
real/padded arbitrary-verifier endpoints, canonical malformed-output fallback, normalized
strict-PPT prefix accumulation and exact prefix bounds. It does not by itself prove either
remaining target. Additional checked future helpers (Advice, StatisticalPostprocess,
StatisticalRecursion, SuffixMachine and canonical-reader additions) are retained ONLY as
clearly labeled evidence snapshots outside this checkpoint's proof revision. Subagent
closed-file manifests distinguish them. No future helper is silently included in src/ or
this checkpoint's complete format-patch series.

## Host and environment

The host-wide cap is at most three Lean processes across all jobs. Every lead/subagent
Lean, Lake and checker command used the issued wrapper and default ~/.lean-slots, with
seq-zk/seq-zk-a/seq-zk-b/seq-zk-c tags. Lake cache commands are lead-only and hold three slots.
Each subagent has an isolated worktree/olean tree and read-only package symlink to the lead.
Only completed lead TCSlib oleans may be APFS-cloned; package trees are never copied.
The genuine baseline and current working olean trees are separate. New evidence drivers
also use a per-tree writer lock. Waiting for host slots is normal, not E-RES.

Mac preflight: 12 CPUs, 19,327,352,832 physical-memory bytes; initial computed headroom
5,104,074,752 bytes (4.754 GiB). APFS free space was 229,666,520 KiB, above the 12 GiB floor.
Subsequent logged headroom readings were above 4 GiB, including 6.438, 6.113, 6.011,
5.944 and 6.265 GiB. No E-RES shortage or RAM-disk path occurred.
Both issued packs and all 237 source hashes verified. Original 76 narrowed Mathlib roots
matched the supplied roots. All present packages match the pinned manifest; four unneeded
documentation packages are ABSENT. No zero-sized oleans, and the import-root cache probe
passed. The shared archive store already held 32,667 files / 1,595,387,830 bytes (earlier
origin unknown); the initial fetch downloaded none and decompressed 2,107 archives.
Later Advice work needs only the two additional precise Mathlib roots Fintype.Lattice and
Real.Archimedean, whose pinned oleans were already present. The lead reverified package pins
and ran a narrowed three-slot cache get: no downloads, 901 archives decompressed, exit0
at11:11:00UTC. Waiting for all three slots was normal shared contention.
The host shared toolchain/archive-store exceptions are those expressly allowed by the addendum.

## Completed checks and remaining final checks

- Exact-base bootstrap: all 237 modules, zero errors/nonzero exits, exactly 23 admissions.
- All twenty included helpers passed native module checks by their authors and the lead.
- The owned module and approved Defs reader passed merged checks. Owned has exactly two
  remaining original target admission warnings.
- Three target axiom prints are standard only. Full stored-constant census and consumer
  prints passed. No newly proved/helper/bridge declaration introduces an extra axiom.
- All five frozen statement headers match the base exactly.
- Base full strict/coe x eval-excluded/included seals completed for both preexisting changed
  files. Owned passes all four cells; Defs has ten inherited diagnostics in the same six
  declarations (listed below). New helpers are absent at the genuine base, as recorded.
- The complete stable checkpoint-1 helper/Defs matrix has also completed (twenty cells):
  all four old helper files pass every variant; Defs retains its same ten diagnostics.
- Checkpoint-2 owned canonical coe seal, eval excluded: zero diagnostics, all 1,870 native
  name/installation/instance-mask/EOF requests verified. Full request source/log retained.
- Width/size: every included library file is <=100 columns and <=1,000 lines. Owned940lines.
- Style lint: base/checkpoint both92 FAIL/101 WARN. No new FAIL; the only WARN-line change
  improves Defs missing-reader count3 to2 through the approved StatZK_iff addition.
- Independent scratch git-am replay reproduced EACH of the two exact commit hashes and all
  22 changed source files using COMMITS.tsv metadata and disabled signing.

Inherited Defs seal failures in every baseline/stable matrix cell:
perfectZK_zeroRounds; AbortRetry.attempt_poly; AbortRetry.exists_retrySimulator;
AbortRetry.statClose_retry; PerfectZKAbort.statZK; negligible_inv_pow_sqrt_div.
Every raw diagnostic and source-line/declaration attribution is retained. Excluding the
native-classified projection-only FinDist CoeFun changes no failure so far. PolyExpr.eval is
excluded in A and included in B; both strict and coe results are recorded separately.

Paired sensitivity controls completed: five unsealed probes pass; each of five sealed
negatives fails exactly once at its expected declaration, while the published-reader positive
passes. Singleton native installation/identity/instance-mask/EOF guards all verify. The tests
cover padFin and inArg in A/B, and PolyExpr.eval in B (A intentionally excludes eval).
Unrelated archived hash-sign/CostBoundedBy targets are absent from these request sets.

The final merged full sweep, final admission census, complete matrix for the newer helpers
and final owned source, and explicit-unfold scan remain FINAL-delivery work.
No prepared/unrun probe is claimed passing. Stable seals will be reused only when source,
import closure, pins and exact request sets agree byte-for-byte; otherwise they will rerun.
The issued route requests this checkpoint once the two whole declarations are proved.
Delivering it before final-only checks is a disclosed timing judgment under Seyoon's
best-judgment instruction; this report does not represent final intake completion.

## Exceptions and diagnostic integrity

Seyoon's exact autonomy/resource-coordination instruction is retained under
 evidence/coordination/2026-11-15-resource-messages.md. It authorized best judgment on
exceptions while he sleeps, with complete disclosure. No other worker's tree, process or
slot was modified or interrupted. Inter-worker messages concerned only shared resources.

Some own proof elaborations were diagnosed as pathological using preserved source,
process-chain/resource readings, read-only stack samples and/or flushed stage markers.
The lead separately authorized graceful SIGINT of only each verified own Lean child so its
wrapper could flush and release normally. These are proof-debugging exceptions, not
elapsed-time timeout commands or E-RES. Complete attempt ledgers, authorizations, raw logs,
source snapshots, corrected tentative diagnoses and lossless samples are delivered under
subagents/seq-zk-a and seq-zk-c. The complete frozen a-ledger through attempt07 is appended below.
There were eight such a-interruptions (StatisticalRecursion01, NormalizedStep01–07), plus
c’s ErrSoundness01. These are disclosed explicitly, including unsuccessful debugging attempts.
c's ErrSoundness attempt01 exited130 after619.72s, maxRSS3,831,316,480 bytes; its explicit
reader rewrite passed. StatisticalRecursion's typed rewrite also passed. NormalizedStep
remains unfinished future work, with no checked-proof claim.

Raw samples exceeding GitHub's per-file limit are represented by numbered lossless ZIP
parts, each with entry list, original SHA256/length and verified byte-for-byte extraction.
The uncompressed originals remain outside the payload; no raw bytes are omitted. No live
log was moved. CP2 copies only explicitly frozen CLOSED subagent files, hash-verifies each
against its closed-file manifest, and labels later work separately.

One invalid dependent probe was inadvertently launched after PrefixLaws failed and removed
its olean. Its import failure is not a mathematical finding; its raw log and correction note
are retained. PrefixLaws was repaired and checked before the valid standard-axiom probe02.
A summary-write attempt was denied by the filesystem sandbox and then rerun with the normal
worktree escalation. A first evidence-copy attempt assumed a different manifest path base;
it copied nothing before failing, and the corrected copy verified every source digest.
Neither affected a Lean result or the delivered source bytes.

## Remaining target obligations

StatZK.seqRep: finish the normalized one-phase comparison, typed independent phase recursion,
joint verifier-tape averaging, and exact real/SQ coin-law endpoint transport. The checked
uniform SQ machine already has CV+Q*S coins, canonical fallback and polynomial output bound.
ZK.seqRep: in addition to the shared endpoints, construct the efficient normalized-phase
plus simulated-suffix reduction; select bounded metadata as advice independently of the
negligible bound and all witnesses; apply ZK at the enlarged auxiliary bound and multiply
its negligible error by Q. The finite-supremum advice-selector and arbitrary-start suffix
machine are checked future work, not an asserted completion of this obligation.
No target or sketch has been found false; no weakening or missing-fact escalation is claimed.

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


### Additional overlap and reuse in checkpoint 2

Every relative below is direct reuse or an explicitly disclosed generalization. Raw searches
precede implementation in the lead and subagent search logs. No private proof was copied.

- exec_boundary_lengths factors the arithmetic previously local to original
  seqRep_exec_phase (issue-base SequentialZK.lean:280); it reuses owned length/count readers.
- seqRep_verifierSpec and seqRep_proverSpec instantiate each abstract field from the
  construction's published coin/round/mover/next/index/count readers, avoiding import cycles.
- PrefixFolds realStep/simStep and realPrefix/simPrefix are typed semantic counterparts of
  SimulatorMachine.phasePrefix (same helper directory). They directly use existing core
  Fin.foldl, introduce no machine/control host, and give both real and simulated families.
- PrefixLaws zero/succ/snoc readers directly reuse core Fin.foldl_zero/foldl_succ_last and
  Fin.snoc_castSucc/last. simPrefix_eq_phasePrefix directly reuses phasePrefix_succ_simulate;
  it does not repeat tape/block interpretation or a machine-efficiency proof.
- ProofTransfers.next_length_le specializes the PaddedProverSpec next field, analogous to
  owned ProverBounded.seqRep but abstract in the source protocol. The owned construction
  result is unavailable to its imported helper without a cycle. ProofTransfers.complete
  directly reuses Protocol.ProverBounded.exists_complete (InteractiveProofs.lean:249)
  with a local relation pairing the original bound and pointwise complete witness.

Additional per-declaration records are included verbatim below. Source line references
are from the revisions actually searched; their sources/checks are preserved in evidence.

### PaddedProverSpec overlap and reuse

The lead approved this construction contract, including all-natural-index/all-natural-phase
reader fields and the two direct endpoint methods. The structure has no relation or B premise.

New declarations:
- PaddedProverSpec and its nine field projections package direct source construction equations.
  The nearest related contract is seq-zk-c's public Composability.PaddedVerifierSpec at
  SequentialZK/RepeatedVerifier.lean:38. The new structure is its prover-side counterpart:
  it has no terminal-verdict field, fixes the honest prover rather than the verifier, and
  allows any cheating verifier. Its original_count is for fixed π.P and arbitrary V, the
  dual of that contract's arbitrary-P/fixed-π.V local_length field. Its boundary reader holds
  at every natural phase index, as supplied by the owned global length readers. No foreign
  equation theorem is re-proved: the owned module will instantiate each field once from
  seqProver_next, seqRep_P, seqRep_rounds_eval, seqRep_verifierFirst, proverMoveIndex_exec,
  exec_fst_length/exec_snd_length, the public count readers and the mover-period reader.
- PaddedProverSpec.real_phase directly instantiates the new public exec_real_phase
  (RealPhases.lean:~92), with no repeated execution induction or arithmetic proof.
- PaddedProverSpec.padded_phase directly instantiates the new public exec_padded_real_phase
  (RealPhases.lean:~161), using the contract's original_count at phaseVerifier V and its
  phase-boundary fields. It does not repeat any filler or phase proof.

No equivalent padded-prover contract was found in TCSlib or pinned Mathlib. Raw searches are
in padded-prover-spec-searches.log. The contract and its methods are sequential-construction
specific and should remain in this helper; no frozen-file promotion/edit is requested.


### RealPhases overlap and reuse

This helper imports no owned module. Source-only copies of author seq-zk-c's checked stable
Soundness and updated Phases modules were independently compiled in seq-zk-b's olean tree.
Hashes, provenance, and raw successful compile output are retained. Those sources were not
edited and no foreign olean was copied.

Raw searches are in real-phases-searches.log. They found no generic empty-prover suffix reader
or arbitrary-verifier real/padded sequential endpoint in TCSlib or pinned Mathlib.

New declarations:
- exec_snd_empty: nearest relative Composability.exec_prefix
  (SequentialZK/Soundness.lean:42) shows only that both earlier histories remain prefixes.
  Empty contents of all newly received prover messages require the stronger suffix statement.
  The elementary induction uses only public exec_succ, mover readers, and List append/replicate
  equations; no private lemma or proof block is copied. Its arithmetic identification uses
  the public List.length_append/length_replicate and Nat.add_sub_cancel_left readers.
- exec_real_phase: DIRECTLY REUSES the newly checked public
  Composability.exec_phase_of_moves (SequentialZK/Phases.lean:~58), with original P and the
  fixed-tape phaseVerifier V. It does not duplicate that real-phase induction. The verifier
  contract directly reuses phaseVerifier_next_phaseAux (WrappedVerifier.lean:128),
  Composability.exec_snd_take (Soundness.lean:76), and List.take_append_drop.
  Nearest source endpoint is owned Protocol.seqRep_exec_phase (base SequentialZK.lean:280),
  but that theorem couples two honest repeated parties, whereas this theorem handles an
  arbitrary cheating verifier and the zero-coin fixed-prefix wrapper. The new proof's local
  quotient/remainder equalities have the same arithmetic formulas as unexported local hmod/
  hdiv inside that owned proof; they are re-derived using public Nat.add_mul_mod_self_left,
  Nat.add_mul_div_left, Nat.mod_eq_of_lt and Nat.div_eq_of_lt. No private fact is referenced
  or copied. Index recovery and phase-start counts are supplied by the caller.
- exec_padded_real_phase: directly combines exec_real_phase and exec_snd_empty. The shifted
  filler-position remainder is proved through public Nat arithmetic readers. The exact
  number k-p uses caller-provided initial/final/local counts, rather than duplicating owned
  alternating-move count proofs. The arbitrary verifier's filler replies have no premise.

Promotion: exec_snd_empty belongs beside the interactive-execution API in Interaction.lean
at a shared-file window. The two sequential real/padded endpoint results belong in this
source-specific helper. No frozen-file edit or new host is needed.


### SimulatorMachine overlap, reuse and host record

The lead approved phasePrefix as a public mathematical semantic recursion, realized using the
published ColMachines.polyTimeComputable_loopState' host. No new control host, transition
machine, or private machine is built. PhaseView was copied as an authorized stable source;
its hash and independent compile log are retained. It was not edited; no agent-a olean copied.

Raw searches are in simulator-searches.log. Earlier Efficiency/WrappedVerifier searches cover
coin slicing, uniform output/layout combinators, and canonical prefix reencoding. No exact
normalized-prefix simulator was found in TCSlib or pinned Mathlib.

New declaration nearest relatives and reuse:
- phasePrefix / zero / succ / succ_simulate: public mathematical sequence of canonical
  normalized simulator calls, following the issued source sketch. Nearest repeated-simulator
  code is PerfectZKAbort.retry (ZeroKnowledge/Defs.lean:337) and attempt (:319): their input is
  fixed and output stops at the first success, rather than changing auxiliary prefix and
  accumulating normalized messages. S.simulate_eq, S.runAt_eq and S.runAtL readers are reused
  to match the published simulator convention exactly.
- length_phasePrefix: new exact i*k count obtained from public
  length_normalizePhaseMsgs (PhaseView.lean:~97) and List append/replicate length readers.
- length_le_of_mem_phasePrefix: new prefix bound obtained by induction from public
  length_le_of_mem_normalizePhaseMsgs (PhaseView.lean:~105) and empty fillers.
- length_encodeMsgs_phasePrefix_le: direct use of public
  CommitmentLemmas.length_encodeMsgs_le (CommitmentLemmas.lean:241), together with the two
  preceding prefix readers. No generic encoding-size proof is copied.
- encode_emptyMsgs_poly: counted emission of the fixed chunk pairEncode [] [] through public
  ColMachines.polyTimeComputable_flatMap_range (ThreeColoring/Machines.lean:~158).
  Core List.map_const' and flatMap_map identify the result with existing encodeMsgs_eq_flatMap.
  This generic encoding composition has no exact prior counterpart found by the searches.
- phasePrefix_poly: existing ColMachines.polyTimeComputable_loopState' (:101), unary arithmetic,
  GI.coinSlice_poly (GraphIsomorphism/EfficiencyRep.lean:376), agent-a's public normalized-view
  machine, phaseAux_poly, and NUPPT output/layout readers are reused. The only new invariant is
  the exact identity of the existing host's state with the encoded semantic prefix. Nearest
  concrete consumers are ThreeColoring proverRepStr_poly and PerfectZKAbort.retry_poly
  (Defs.lean:412); their fixed protocol/first-success outputs prevent direct reuse.
- exists_phaseSimulator: uses public NUPPT.ofPolyTimeUniform and its uniform/coins/activation
  readers. Nearest relative exists_retrySimulator (Defs.lean:433) uses n retries on the same
  input, whereas this simulator threads phaseAux data and emits the entire canonical view.

Promotion requests: phasePrefix and the simulator construction are source-specific and stay
in this helper. The small encode_emptyMsgs_poly composition could later move beside the shared
encoded-history machines. No frozen-file changes or scope requests are needed.


### WrappedVerifier searches, reuse and overlap

The lead approved this helper and the source-only copies of agent-a Normalization.lean and
NormalizationMachine.lean. Their provenance hashes are in wrapped-dependency-provenance.log.
Each copied source was compiled independently in seq-zk-b's olean tree. They were not edited.

Raw reuse searches are in wrapped-searches.log; additional read-only source comparison:
SecureComputation/Yao.lean:352 derives encodeMsgs=encWords locally before its decodeMsgs reader.
The new helper instead imports and reuses agent-a's public encodeMsgs_eq_encWords and
polyTimeComputable_encWords_decWords, avoiding a fresh encoding-equality proof.

New declaration overlaps:
- phaseAux, phaseAux_eq: phase-specific nested-pair data encoding; nearest construction
  LevinTransfer.liftVerifier (ZeroKnowledge/NPLemmas.lean:268) stores an original input and
  auxiliary input in a pair. This phase construction additionally stores a fixed verifier
  tape, phase index and arbitrary earlier message prefix, so the existing construction does
  not have its required interface.
- phaseAux_fields, phaseAux_z, phaseAux_tape, phaseAux_phase, phaseAux_prefix: specialized
  readers for the new encoding. They reuse public pairFstD_pairEncode/pairSndD_pairEncode,
  agent-a encodeMsgs_eq_encWords, BinArith.decWords_encWords (BinaryArith/Words.lean:116),
  and core List.length_replicate, rather than reproving a generic pair or decoder fact.
- phaseAux_length: specialized exact length, directly reusing Turing.length_pairEncode
  (TuringMachine/Encoding.lean:220). It retains the phase index in unary for later advice bounds.
- phaseVerifier, phaseVerifier_coins, phaseVerifier_next, phaseVerifier_coinLen,
  phaseVerifier_next_phaseAux: new fixed-tape, prefix-extending strategy and its readers.
  Nearest construction LevinTransfer.liftVerifier/liftVerifier_next (:268/:274) changes the
  common input and tape prefix rather than fixing an auxiliary tape and extending history.
  Neither that construction nor its statement can be reused directly.
- phaseVerifier_efficient: nearest relative LevinTransfer.liftVerifier_efficient (:295)
  and earlier SeqEfficiency.phase_poly. It uses the same existing uniform output/layout
  combinators, plus agent-a's canonical prefix reencoding and public
  CommitmentLemmas.encodeMsgs_append (:233). The imported published constituent lemmas
  are reused; no machine, private lemma, host or generic canonicalization proof is copied.

Promotion request: phaseAux and phaseVerifier are specific to this sequential-composition
construction and should stay here. A future shared fixed-tape strategy-preprocessing closure
lemma could subsume phaseVerifier_efficient and LevinTransfer.liftVerifier_efficient; no frozen
file change is needed for this delivery.

- phaseAux_poly: direct repeated use of public PolyTimeComputable.pairEncode followed by
  the new encoding equation. Nearest generic relative NUPPT.polyTimeComputable_layout
  (Randomized/Closure.lean:~180) assembles a different four-field machine layout, so the
  exact phase auxiliary encoding requires this short composition.

- phaseAux_length_le: directly applies the new phaseAux_length and public
  CommitmentLemmas.length_encodeMsgs_le (:241), then monotonicity of multiplication.
  It specializes the generic encoding bound to the new auxiliary layout; the generic
  message bound is reused rather than reproved.


## ExecutionBounds continuation

ExecutionBounds.lean is 88 lines, maximum width 94, with no admissions or simp attributes.
It imports only stable Normalization.lean; the previous four source hashes were asserted
unchanged when this report was finalized. Public searches found no existing generic message
length bound for Cryptography.exec.

New declarations and overlap:

- exec_snd_bounded derives a bound on every verifier-received message from a fixed prover
  tape's uniform next-message bound. It uses only Interaction.lean's exec_zero and exec_succ
  readers (lines 262 and 266 in the base). Related
  Games/Protocols.lean:316 execT_trace bounds concern a different oracle protocol and only message
  counts; they do not provide this statement. No private argument was copied.
- exec_snd_slice_bounded directly specializes exec_snd_bounded through the public core
  List.mem_of_mem_take and List.mem_of_mem_drop readers. It adds no list-membership lemma.
- length_encodeMsgs_exec_snd_le applies Words.lean:81 length_encWords_le through the checked
  encodeMsgs_eq_encWords bridge and exec_snd_bounded. It is execution-specific. No duplicate
  generic encoded-history bound was added; the nearest existing generic
  CommitmentLemmas.lean:241 length_encodeMsgs_le is subsumed by the Words theorem reused.

Promotion request: generic execution-message bounds belong beside the execution readers in
Interaction.lean at a future shared-file window. No frozen-file edit was made or needed.

ExecutionBounds check01 passed with one unused simp argument; the argument was removed in
its single proof block. Check02 passes with no diagnostics, RSS 1,560,723,456 bytes and
1.77 seconds compiler wall time. Both raw attempts, preimplementation searches, width/hash
ledger, diagnostic summary and own-tag slots are retained. No Lake command ran. The hybrid
outline now marks the execution-message-bound obligation resolved by this checked helper;
the separate cheating-verifier padded-phase endpoint reader remains a lead obligation.

## Prefix-hardwired prover and offset execution

After approving the proposed interface, the lead assigned a NEW helper `Phases.lean`,
importing the stable Soundness helper. The new public construction `prefixProver` fixes
an earlier received history, auxiliary input and prover tape; generated `coins` and `next`
readers expose its zero coin polynomial and append contract. The new theorem `exec_phase`
identifies any corresponding segment of the full execution, under the mover and verifier
reply hypotheses, with a run of this prefix-hardwired prover. No owned definitions are
imported or unfolded. The optional bounded verifier-congruence theorem remains a design
proposal only and has not been added.

Overlap and promotion:
- `prefixProver` is a fixed-tape/fixed-prefix strategy wrapper. The nearest owned wrapper is
  `Protocol.seqProver`, original `SequentialZK.lean:200`; the latter slices prover coins and
  drops earlier received messages, while this one fixes the original tape and prepends
  earlier received messages. It does not restate that construction. No equivalent public
  wrapper was found by the recorded searches for `hardwir`, fixed tape, prefix strategy,
  zero-coin strategies, and prover next-message append calls.
- `prefixProver_coins` and `prefixProver_next` are generated field readers of this new
  construction, not re-proved foreign readers.
- `exec_phase` shares the induction architecture of the owned honest-run
  `Protocol.seqRep_exec_phase` (`SequentialZK.lean:280` at issue base), but applies to any
  prover and any two verifier strategies under an explicit real-phase contract. It uses
  only published `exec_zero`/`exec_succ`, generated prefixProver readers, and core List
  append/drop equations. No proof block or private declaration was copied.
- The nearest other general execution comparison is public
  `LevinTransfer.exec_congr` at `ZeroKnowledge/NPLemmas.lean:88`; it compares whole runs
  from empty histories under equality on all histories. It cannot supply an execution
  segment with fixed nonempty earlier histories. It is outside the supplied bootstrap
  closure and is not imported.
- Promotion request: prefixProver and exec_phase belong beside the interactive-execution
  API in `ZeroKnowledge/Interaction.lean` at a shared-file window. The permitted helper
  retains them for this fill.

Phases check history:
- Attempt 01: exit 1 with one unresolved false-mover branch. The branch retained
  `if false = true`; adding the public Bool false-equality and if-false simplification
  closed it. Max RSS 2,147,205,120 bytes. Raw log retained.
- Attempt 02: exit 0 with 0 errors and 0 warnings, fresh olean produced. Max RSS
  2,154,381,312 bytes. Raw log retained.

Final Phases.lean: 96 lines, maximum width 94, SHA-256 `22d94a4e178f0a0f34b4fabb3609a7ca33a171a9e38cf275d8dcf0e79e33a9e2`. No admissions.

## Congruence along the reached source histories

The lead assigned a NEW `Congruence.lean` for checkpoint 2 tape nonanticipation and later
ZK. It imports only `ZeroKnowledge/Interaction.lean` and introduces the public theorem
`exec_congr_reachable`. Its hypotheses compare replies only at active positions before
`g`, on each source execution's actual received history; prover and verifier tapes may
both differ. The conclusion is equality of the complete executions after `g` moves.
It uses only published `exec_zero` and `exec_succ` readers and public Bool equalities.
No previous helper source was changed.

Overlap and promotion:
- Nearest relative: public `LevinTransfer.exec_congr`,
  `TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean:88`. That theorem permits different
  inputs but requires each party's replies to agree on **every** possible history.
  The new theorem has a weaker reached-history premise at a bounded number of moves,
  and identical common/auxiliary inputs. The published theorem cannot directly discharge
  this premise and is outside the supplied order closure. No existing proof block was
  copied; the standard induction is re-derived from the public execution readers.
- Searches for `exec_congr|exec_eq_of|next_eq_on|reachable.*exec|exec.*reachable` across
  TCSlib and for execution congruence/reachability under pinned Mathlib/Computability
  found no closer reusable theorem. Raw output is in congruence-searches.log.
- Promotion request: `exec_congr_reachable` belongs beside `exec_succ` in
  `ZeroKnowledge/Interaction.lean` in a shared-file window.

Congruence check attempt 01: exit 0 with 0 errors and 0 warnings, fresh olean produced.
Max RSS 1,549,713,408 bytes; raw log and structured result retained. The invocation used
this sub-agent's own olean tree and tag through the host-wide shared slot wrapper.

Final Congruence.lean: 68 lines, maximum width 94, SHA-256 `724fb756e96ac9f210b2a0f75dd9d403bddc2a0c226225a4ba01e9f284efcb56`; no admissions.

## Earlier verifier blocks determine the earlier transcript

The lead assigned NEW `VerifierPrefix.lean`. The public theorem
`exec_eq_of_verifier_blocks` accepts an arbitrary padded verifier, an arbitrary terminal
reply function, and a move-index recovery hypothesis on the actual source run. It proves
that agreement of verifier coin blocks below `j<q` gives equality of the full transcript
before move `2*k*j`, against the same arbitrary prover and fixed prover tape.

The zero-round case has no moves. In the positive-round case the recovered index gives
`2*received.length ≤ t+1`, excluding the terminal history `q*k` before the cutoff. The
phase index is below `j` by the public core theorem `Nat.div_lt_of_lt_mul`. Reusing
`exec_congr_reachable` and the supplied padded reply reader then identifies the runs.
The proof does not unfold any owned definition or the body of `coinBlock`; `dsimp only`
reduces the local `let idx` appearing explicitly in its own hypothesis.

Overlap and reuse:
- Directly reuses this sub-agent's published `Composability.exec_congr_reachable` in
  `SequentialZK/Congruence.lean:42`. No congruence proof is duplicated.
- The nearest owned construction reader is `Protocol.seqRep_exec_phase`, original
  `SequentialZK.lean:280`, which compares an honest phase with an original execution.
  That theorem neither handles arbitrary cheating provers nor compares two full verifier
  tapes, so it cannot give this nonanticipation statement.
- The lead's new `Protocol.seqVerifier_exec_first` handles phase zero against the original
  verifier; it also does not identify earlier transcripts for arbitrary two tapes and a
  phase cutoff. The new helper contains no copy of that proof.
- Specialized earlier transcript readers such as `GI.exec_vfirst_eq` in
  `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:90` describe history-independent
  verifier messages. Here the underlying verifier may depend on its within-phase history,
  so that interface cannot be reused. No specialized proof was copied.
- The move-index arithmetic is supplied by the lead, not re-proved from a foreign count
  function. Core `Nat.div_lt_of_lt_mul` is directly reused rather than copied.
- The statement belongs to this fill's padded-phase helper layer; no frozen-file promotion
  or reader request is required for it.

Searches for coin-block execution/prefix and verifier-tape dependencies in TCSlib and
pinned Mathlib/Computability are recorded in verifier-prefix-searches.log. No equivalent
published padded-verifier nonanticipation theorem was found. No new Mathlib root was
added, and no earlier helper was changed.

VerifierPrefix attempt 01: exit 0, 0 errors, 0 warnings, fresh olean produced. Max RSS
2,170,912,768 bytes. Exact invocation, raw log, source audit, and slot lines are included.

Final VerifierPrefix.lean: 89 lines, maximum width 94, SHA-256 `6be4e9f9c220e9ba15798dc0b61bc9a7cafc5c9ea1ec62a673de7c2d5e26c7f7`; no admissions.

## Explicit soundness error and fixed-prefix section bounds

NEW `ErrSoundness.lean` contains three checked declarations:
- `InteractiveProofErr.uprob_accept_le`: for every no-instance and prover, acceptance
  probability is at most the stated error `s(|x|)`.
- `InteractiveProofErr.sound_nonneg`: the error is nonnegative at every no-instance length.
- `Composability.prefixProver_accept_le`: when the earlier received messages and original
  prover tape are hardwired, the acceptance probability over a fresh original verifier
  tape alone is at most `s(|x|)`. The wrapper's public zero-coin reader shows that every
  local prover coin string is empty. Published output/transcript equations, `uprob_prod`,
  and `HardcoreBit.uexp_const` then remove its unused coin coordinate.

Search and overlap disclosure:
- No `InteractiveProofErr` acceptance or nonnegativity bound was found by the recorded
  TCSlib/Mathlib searches. Nearest public relative is
  `InteractiveProof.exists_uprob_accept_lt` at `ZeroKnowledge/InteractiveProofs.lean:193`.
  It returns a strict bound for an existential negligible error; it cannot provide the
  frozen arbitrary explicit-error value `s`. The new acceptance proof adapts the same
  complement-of-rejection argument, directly reusing `uprob_mono`, `uprob_not`, and the
  public soundness field. This overlap is explicit; it is not a copied private theorem.
- `sound_nonneg` directly specializes the public Mathlib order equivalence
  `sub_le_self_iff` generated at
  `Mathlib/Algebra/Order/Group/Unbundled/Basic.lean:214`, using `uprob_le_one`. No order or
  probability fact is re-proved.
- `prefixProver_accept_le` specializes the new acceptance bound to the existing public
  prefixProver wrapper. Its marginalization is direct reuse of the uniform product and
  constant-average readers. It does not re-prove the generic uniform second-projection law
  (`HardcoreBit.pushesUniform_snd`, HardcoreBit/Basic.lean:210) or the averaging statement
  `Protocol.exists_proverCoins_le` (Interaction.lean:548).
- Promotion request: the first two generic methods belong in
  `ZeroKnowledge/InteractiveProofs.lean` at a shared-file window. The prefix-specific bound
  remains in this fill's helper layer. No frozen file was edited.

Diagnosed elaboration and authorized proof-debugging exception:
- Attempt 01 started 09:37:03 UTC, acquired its slot at 09:37:08, and was running rather
  than queued. The sub-agent initially inferred a slot wait from the empty buffered output;
  the lead corrected this status, and the process snapshot confirmed the running child.
- A read-only one-second stack sample showed active `evalCalc`/`elabCalcSteps` and deep
  `isExprDefEqExpensive` recursion in the probability calculation. Mac headroom measured
  by the lead was 6.438 GiB, above the floor; this was not E-RES.
- The lead explicitly authorized a graceful interruption under Seyoon's best-judgment
  exception. Its verbatim instruction is preserved in err-soundness-debug-authorization.md.
  The exact child PID96807 and parent96799 and full Lean command were re-verified before
  SIGINT. Only that child was signaled; no wrapper or other job was touched.
- The complete attempt source, raw checker output, process inspection, interruption record,
  and stack sample are retained. Lean exited130, checker exited1, and no olean was produced.
  It ran619.72s with maxRSS3,831,316,480 bytes. This was diagnosed proof debugging, not an
  elapsed-time timeout, resource shortage, or claimed proof failure.
- Replaced only the pathological probability calc with an explicit reader-based product
  proof. Attempt02 passed with 0 errors and 0 warnings, fresh olean, runtime6.63s,
  CPU1.43s, maxRSS2,164,834,304 bytes. No previous helper source changed.

Large raw diagnostic representation:
- Raw sample size145,047,604 bytes, SHA256
  `440251c95334e50dfb92d8140690daa5315ec081bb69b6135602a9ce0187deec`.
- Deliver the lossless numbered part `err-soundness-diagnostics-01.zip`, with its entry list
  and verification log. Its sole member is the complete original err-soundness-sample.log;
  streamed decompression was SHA256-checked byte-for-byte, with the original length.
- ZIP size1,916,631 bytes. The original raw local sample remains outside the payload at
  `.lake/seq-zk-c-raw-diagnostics/err-soundness-sample.log`. The completed sample was moved
  only after verified compression; no running log was moved. No raw bytes are omitted.

Final ErrSoundness.lean: 85 lines, maximum width 94, SHA-256 `4ada2d316efd3efd4d387dde0880b9360ea66fff55581b2535081dc09ac76705`; no admissions.

## General phase-coupling extension for the simulator worker

At the lead's request, added `exec_phase_of_moves` to Phases.lean with arbitrary local
strategies, auxiliary inputs and tapes. Each supplied active-move equation reads a local
party on the reached source history with its fixed old prefix dropped. The generic
induction proves both prefix-append history decompositions. The previous `exec_phase`
statement is unchanged and now applies this theorem; its prover premise follows from
`exec_prefix`, the public List prefix append equation, and prefixProver_next. Its sketch
was synchronized. There is only one phase induction; no duplicate proof was retained.

Overlap: the new theorem generalizes this same file's prior exec_phase, whose old source
and source audit are retained as phases-before-generalization files. The new generic
induction replaces that old induction; the old API is a direct published-theorem reuse.
No foreign or private proof was copied. This belongs beside the generic interactive
execution API at a shared-file window, extending the prior promotion request.

Phase generalization check01: exit0, no errors/warnings, fresh olean, runtime4.67s,
maxRSS2,155,839,488 bytes. Dependent ErrSoundness recheck: exit0, no errors/warnings,
fresh olean, runtime2.70s, maxRSS2,165,014,528 bytes. It is the only owned helper directly
importing Phases; the simulator worker was sent the exact checked signature and source
and will recheck its new consuming helpers in its own tree. Existing API preserved.

Current Phases.lean: 142lines/max94, SHA256`dcec347fe5aaf7407861a8248809c400c4d1f8ad85b6c6195bacd4a7261d13be`.

## Full generic explicit-error repetition engine

The lead approved the PaddedVerifierSpec interface before substantial implementation.
`RepeatedVerifier.lean` supplies the public proposition-valued structure and its two
phase readers. `RepeatedSoundness.lean` supplies the actual probability engine. Neither
imports or unfolds the owned SequentialZK module, and no target statement is weakened.

New declarations and formulas:
- `PaddedVerifierSpec π ρ x q p terminal`: the nine displayed coin/round/first-mover,
  padded-next, binary-terminal, actual-index, boundary-length, original-length, and mover
  periodicity properties. Every public field has a formula docstring in Lean argument order.
- `PaddedVerifierSpec.phase_exec`: both histories of a real phase equal their fixed earlier
  histories followed by an original-verifier execution against prefixProver.
- `PaddedVerifierSpec.phase_take`: taking the p real prover slots of a final phase history
  recovers that original-verifier history. The k=0 branch is explicit.
- Private `phaseTape` and `phaseTape_block`: table coins are read through the canonical
  FunFamily.blocks equivalence and its published ofFn reader.
- Private `zeroTail`: a finite table with prescribed earlier blocks and explicit all-false
  future blocks. Private `phaseGood`: original acceptance with its induced earlier
  received history and fixed prover tape. Private `phaseGood_section` specializes the
  checked prefixProver acceptance bound. Private `phaseGood_of_test` identifies actual
  phase tests using VerifierPrefix and phase_take.
- `PaddedVerifierSpec.outV_eq`: repeated output equals its terminal function on the
  complete source transcript, through public Protocol output/transcript readers.
- `PaddedVerifierSpec.accept_le`: original explicit error s gives aggregate acceptance
  probability at most s(|x|)^q against every prover.
- `PaddedVerifierSpec.sound`: the binary aggregate verdict gives rejection probability at
  least1-s(|x|)^q. The q=0 branch is explicit. No q-positivity premise is added to this
  helper, and the frozen owned statements retain their original hypotheses.

Overlap and reuse, including every restatement/specialization:
- PaddedVerifierSpec's fields package the owned equations as caller-supplied hypotheses;
  they are not new proofs or claims that an arbitrary protocol satisfies them. Nearest
  original SequentialZK.lean readers: seqVerifier/its generated readers at236;
  seqVerdict_eq at222; seqRep_rounds_eval at261 and seqRep fields at254;
  verifierMoveIndex_eq at117 and verifierMoveIndex_exec at182; exec_fst_length at153 and
  exec_snd_length at163 with countP_moverIsV at133/countP_not_moverIsV at143;
  proverMoves_eq at127; moverIsV_two_mul_add at128. They cannot be imported into a helper
  without a cycle; the lead instantiates each field from exactly these published readers.
- phase_exec directly reuses exec_phase, including its generic induction. Its nearest
  owned relative is honest-only seqRep_exec_phase (issue-base line280); the new reader
  permits an arbitrary prover and an abstract verifier specification. Its quotient and
  remainder arithmetic directly reuses the core Nat add-multiple division/modulo readers;
  it does not copy a private lemma or add another execution induction.
- phase_take directly reuses phase_exec, exec_snd_take and the supplied length readers.
  Nearest lead checkpoint1 reader: Protocol.seqRep_exec_phase_take at owned line478
  (source queried during this work); that theorem is honest-only and unavailable to the
  abstract helper. The new reader generalizes the final-phase restriction to every prover.
- Private phaseTape is a local string alias for (FunFamily.blocks q c).symm. Nearest alias
  is public GI.blocksEquiv at GraphIsomorphism/SoundnessRep.lean:207. Private phaseTape_block
  has nearest relative public GI.coinSlice_blocksEquiv at that file:224. It is not a copy
  of the latter's entrywise proof: it directly specializes the already-imported canonical
  FunFamily.ofFn_blocks reader (Asymptotic/Adversary.lean:277), using Equiv.apply_symm_apply.
  This canonical public reader is the reused interface; no GI implementation is duplicated.
- Private zeroTail has nearest public relative extendStream at
  Pseudorandom/Functions/LazySampling.lean:196 (inside the supplied closure). extendStream
  returns a stream on all naturals and uses Classical.arbitrary beyond its prefix. The new
  finite-table leaf uses the explicitly requested all-false fallback, including truncation
  if i exceeds q; extendStream does not publish that exact fallback. Mathlib Function.extend
  (Logic/Function/Basic.lean:686) is a choice-based extension along a map, not this explicit
  total finite-prefix/truncation leaf. The two-line conditional definition is disclosed;
  no existing extension theorem or private proof was copied or re-proved.
- phaseGood is a local predicate naming the original verifier/prefixProver test, rather
  than a new iteration host. phaseGood_section directly reuses prefixProver_accept_le;
  it merely substitutes the earlier transcript of the zero-tail table as its fixed prefix.
- phaseGood_of_test directly reuses exec_eq_of_verifier_blocks and phase_take. Its only
  extra table fact reads the prescribed prefix of zeroTail; Fin casts reduce by the core
  projection equations. There is no duplicated nonanticipation or phase induction.
- outV_eq's nearest lead reader is Protocol.seqRep_outV_eq, owned line453 when queried.
  The new theorem is the abstract-spec counterpart; it directly reads supplied rounds,
  first-mover, boundary, and next equations through published Protocol readers. It cannot
  import that construction-specific owned theorem without a cycle.
- accept_le directly reuses Protocol.exists_proverCoins_le (Interaction.lean:548), the
  canonical FunFamily.blocks equivalence/readers, VerifierPrefix through the phase-test
  reader, prefixProver_accept_le through phaseGood_section, and uprob_adaptive_all_le.
  Nearest specialized repetition proof is GI.gniRep_accept_le at
  GraphIsomorphism/SoundnessRep.lean:344, with its protocol-specific 2^-n+sampling-error
  rate. It does not supply arbitrary s or this abstract padded verifier; no proof was copied.
- sound uses outV_eq, the supplied binary terminal equation, OneWay.uprob_congr,
  uprob_not, and Mathlib sub_le_sub_left directly. The nearest specialized complement
  conversion is GI.gi_rep_efficientProverProofErr at SoundnessRepGI.lean:438. Its
  protocol-specific conclusion cannot supply this generic reader. No probability
  complement or order fact was re-proved.

Promotion/readers: PaddedVerifierSpec and these abstract padded-phase readers belong in
this topic helper layer. General prerequisites already carry the earlier Interaction and
InteractiveProofs promotion requests. No frozen-file edit, scope extension, private host,
new Mathlib root, or new simp attribute was introduced.

Validation history and resource evidence:
- RepeatedVerifier01: syntax cascade from reserved capital Π; changed the bound protocol
  name to valid ρ. RepeatedVerifier02: explicit first-mover projection case split was
  needed for the index arithmetic; fixed through if_pos/if_neg on its equality. Both raw
  failures retained. RepeatedVerifier03 passed spec+phase_exec. RepeatedVerifier04 passed
  the complete phase_take extension with0errors/0warnings, actual runtime2.87s,
  maxRSS2,194,358,272. Its slot wait was10:04:53–10:15:32 UTC, normal host contention;
  not a stall or E-RES.
- RepeatedSoundness01 found one local-notation simplifier mismatch. Attempt02 fixed the
  outer block but exposed the inner occurrence's local c alias. Attempt03 normalized that
  local proposition explicitly and passed the full engine with0errors/0warnings, fresh
  olean, runtime2.41s, maxRSS2,172,452,864 bytes. All raw logs and structured results remain.
- The full engine uses explicitly typed probability intermediates and public product/
  equivalence readers; no pathological dependent calc or proof-debug interruption occurred.
- Each check used this sub-agent's own olean tree and shared wrapper/tag. Source files
  remain below1000lines and100characters. The lead owns the final merged sweep, axioms,
  seals, lint, commits and delivery.

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

## Closed a diagnostic ledger (verbatim)

# Closed own compiler-debugging ledger for checkpoint 2

This snapshot is complete through NormalizedStep attempt07. No own Lean process is active at
the snapshot boundary. Every listed interruption was separately authorized by the lead under
Seyoon’s best-judgment exception after verifying the exact own child chain. These were
diagnosed proof-elaboration investigations, never elapsed-time timeouts or E-RES reports.
No other process or slot was interrupted/edited/removed.

## StatisticalRecursion

Attempt01: own Lean3000 under wrapper2984, active CPU/Meta.isDefEq work, headroom6.113GiB.
The lead authorized SIGINT after exact source/sample/chain preservation; checker exit130,
783.64s, maxRSS3,811,213,312 bytes. A fully typed sampler/domain rewrite then passed attempt02
with 0 diagnostics in2.45s, maxRSS2,121,269,248 bytes. Source139lines, maxwidth94, SHA256
fe7d94d26ba375222245902da6ce0e71c9789d9ee98a9e68e4a063d5ada9591e.
The raw source, exact rewrite patch, authorization, process/resource records and sample are
all delivered. The native sample is losslessly packed in part001 with verified raw SHA.

## NormalizedStep closed attempts

All seven attempts below were interrupted by exact lead authorization and exited Lean130;
none is claimed checked. The mathematical/API read-only review found no known domain flaw.

| Attempt | Wall seconds | Max RSS bytes | Closed diagnosis | Authorization |
|---|---:|---:|---|---|
| 01 | 287.41 | 4226859008 | Sparse stack showed Simpa/whnf; assigning it to a particular hproduct line was tentative, not source-localized. | normalized-step-interruption-authorization.md |
| 02 | 334.22 | 4356784128 | Sparse stack showed Exact/isDefEq; no exact source line established. | normalized-step-interruption-02-authorization.md |
| 03 | 313.03 | 3860791296 | Ordinary trace markers absent in checker stdout; stage not localized. | normalized-step-interruption-03-authorization.md |
| 04 | 338.13 | 3989684224 | dbg_trace markers also absent in checker stdout; this was not evidence that proof had not begun. | normalized-step-interruption-04-authorization.md |
| 05 | 112.09 | 3356131328 | Direct-file IO markers proved module/signature/proof/fixed-point stages done; last marker test.begin brackets the hrawT declaration (type AND value). Earlier dot-reader-only attribution was overstated. | normalized-step-interruption-05-authorization.md |
| 06 | 735.60 | 5710823424 | Fully explicit statClose_iff reader still stopped within that declaration; type versus value remained unresolved. Authorized opaque-law fallback. | normalized-step-interruption-06-authorization.md |
| 07 | 342.75 | 5554405376 | Opaque generic helper independently passed; fixed and pointwise stages completed. Final explicit concrete generic-law instantiation remained pending. Authorized opacity/instance correction after lead cache. | normalized-step-interruption-07-authorization.md |

The live markers first isolate the whole hrawT declaration, not its annotated type versus
its value. Earlier guesses assigning that whole stage specifically to the dot-reader were
tentative and are explicitly corrected here. Attempt06’s explicit reader did not resolve it.
Attempt07 instead used seq-zk-c’s checked opaque generic law, but its concrete instantiation
still required further elaboration work. No target or helper statement has been weakened.

## Preservation and resource evidence

Eight own compiler-debugging interruptions are recorded here: StatisticalRecursion01 plus
NormalizedStep01–07. Other workers’ events are outside this sub-agent ledger; the lead has
their separate records. All own wrappers flushed checker output and released normally.
Resource readings stayed above the 4GiB floor; latest attempt07 headroom6.105GiB.

Native samples were created for StatisticalRecursion01 and NormalizedStep01–04; each is
delivered losslessly in numbered ZIP parts001–005, with raw SHA256, exact entry list and
verified decompression. Uncompressed originals are retained outside the payload under
/private/tmp/seq-zk-a-diagnostics/. Attempts05–07 were localized with direct-file markers;
no native samples were created for them, so none is omitted.

Exact marked source snapshots, each raw check log, preserved live marker logs, authorization
records, exact process-chain records, resource logs, and checker-stdout snapshots are included.
Checked prerequisite sources are retained in source-snapshots/ under their module paths.
StatisticalPostprocess belongs to seq-zk-c; its source hash/provenance and own dependency
check are included. No active check/marker is being copied at this snapshot boundary.

Future diagnostic changes and checks will use new attempt/file names. This closed ledger and
the files named by checkpoint2-closed-files.tsv are frozen until the lead confirms copying.

The source under evidence/drafts/StatisticalTransfer.lean is an uncompiled future assembly
draft against agreed helper APIs. It is not part of either delivered proof commit.

The closed a manifest uses a path column; b/c use relative_path. Two preliminary copy
attempts assumed the other convention and stopped before copying. The final copy checked
every digest and retained each original manifest unchanged.
