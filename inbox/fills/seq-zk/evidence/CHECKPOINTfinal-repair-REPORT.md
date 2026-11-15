# seq-zk final delivery

All five frozen `seqRep` theorems of PS10 Theorem175.1 are proved. This final report's
outcome, revision, inventory and verification sections supersede the historical checkpoint
statuses preserved in the evidence and appendices. No target statement was weakened.

Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.
Issued exchange pack: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
Final local proof revision: `d842dc8f681f6b89499129f5b64a50d0e4587935`.
Lean4.25.0; pinned Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
The `fill/seq-zk` proof branch remains local. The six unsigned proof commits, in order, are
listed with full identities/dates/signing information in `patches/COMMITS.tsv`:
`a758032d636fd410b0c4b8a1530a96d000cc467a`,
`e978a28274fdeb545e622ae28747221088352512`,
`04c253e48d9c0ebb73943f39412365cd4d8e02db`,
`5a80d36a5a4da1c2906b747dab59251fdd03836a`,
`7cecd426dddac78789c9e7fc627a7cd013d67792`,
`d842dc8f681f6b89499129f5b64a50d0e4587935`.

## Targets and resulting behavior

| Frozen declaration | Final result |
|---|---|
| `ZK.seqRep` | Proved; one uniform strict-PPT simulator, polynomial times negligible advantage |
| `StatZK.seqRep` | Proved; exact statistical error `Q(n)*δ(n)` |
| `InteractiveProof.seqRep` | Proved; perfect completeness and negligible soundness |
| `InteractiveProofErr.seqRep` | Proved; exact soundness error `s(n)^Q(n)` |
| `EfficientProverProofErr.seqRep` | Proved; efficient prover and exact soundness error `s(n)^Q(n)` |

All five statement headers are byte-for-byte identical to the issue base. The new proofs
handle either first mover, odd or zero rounds and zero phases where the frozen hypotheses
allow them. The generic explicit-error engine also covers zero phases with error1; the
original `hQ` hypothesis is retained in `InteractiveProofErr.seqRep`, with a benign native
unused-variable warning disclosed here.

The simulator validates raw phase views and normalizes them to exactly the real prover-slot
count, each message bounded by the original prover-message polynomial. Malformed views use
a canonical fallback. Empty honest-prover fillers pad phases; arbitrary cheating-verifier
filler replies remain unrestricted. Normalization fixes real phase views. One global verifier
tape and independent phase-simulator tapes yield the same uniform strict-PPT simulator before
any auxiliary-input bound or distinguisher is supplied.

For statistical ZK, randomized postprocessing, averaging and the conditional-prefix recursion
sum exactly `Q*δ`. For computational ZK, a finite polynomial metadata domain selects a common
negligible phase bound uniformly over arbitrary witnesses. Neither advice nor simulator stores
or tests the witness. The conditional real-prefix/simulated-suffix hybrid sums `Q*|ε|`; the
published polynomial-times-negligible lemma completes the result. Exact split/block and
endpoint readers identify actual real and simulator views without further error. No efficient
honest-prover or simulated-output-shape premise was introduced.

## Ownership, changed files and sketch edits

Only the lead edited SequentialZK.lean, applied the approved frozen reader, committed the local
proof branch, ran the merged final checks and prepared/pushed delivery. Helpers were split by
module; no two agents edited one helper. Each agent had a separate managed worktree and olean
tree, with packages linked read-only to the lead's pinned packages.

| Worker | Included source and proofs |
|---|---|
| Lead `/root`, `seq-zk` | All five target bodies; main specification/phase bridges; PrefixFolds, PrefixLaws, ProofTransfers, StatisticalTransfer, ComputationalTransfer; approved StatZK_iff |
| `/root/zk_route`, `seq-zk-a` | Normalization, NormalizationMachine, PhaseView, Statistical, ExecutionBounds, NormalizedStep, StatisticalRecursion, StatisticalPrefix, BoundedMetadata, RealPrefixBounds |
| `/root/efficiency`, `seq-zk-b` | Efficiency, WrappedVerifier, SimulatorMachine, RealPhases, PaddedProverSpec, SuffixMachine, ComputationalReduction, ReductionAdvantage, ComputationalPhaseBound |
| `/root/soundness`, `seq-zk-c` | Soundness, Phases, Congruence, VerifierPrefix, ErrSoundness, RepeatedVerifier, RepeatedSoundness, Advice, StatisticalPostprocess, EndpointSampling, HybridRecursion, SuffixLaws, ComputationalAdvice, ContinuationProbability, ComputationalHybrid |

There are41source files: main,39helpers and the approved Defs reader. They total7731lines;
main is990lines; every file is≤1000lines and every line≤100characters (maximum99).
`evidence/final-source-inventory.json` records every path/size/width/SHA.
`evidence/final-stored-constants.tsv` lists all414stored constants, including generated/private
ones. The complete declarations and their public equations/formulas are delivered in `src/`.
The table below is the exact file inventory. New helpers are imported precisely and listed
in the main Contents. The module title/status and all five target sketches describe the
implemented proof. New public definitions/abbreviations have readers; proofs of at least15
lines have English sketches, and long proofs have stage comments. Seven initially missing
stage-comment blocks were fixed in commit4; the later HybridRecursion block was fixed before
commit5. No new global simp attribute was added.

## New declarations

The exact202source-written new declarations are listed, with paths and lines, in
`evidence/subagents/seq-zk-b/final-review-15/new-source-declarations.tsv`.
The414stored-constant inventory additionally includes generated/private constants and retained
original declarations. The new public interfaces comprise bounded phase normalization and
readers, padded prover/verifier contracts and phase/endpoint laws, uniform simulator and
continuation machines, exact adaptive soundness, statistical postprocessing/recursion,
finite metadata/advice selection, computational phase reduction/advantage, conditional hybrid
bounds and the two ZK transfer theorems. Each full statement/docstring is in its source;
no extra axiom, admitted helper or replacement target premise was introduced.

## Verification

* Both issued packs passed native `shasum -a256 -c`; all237base source hashes matched.
  Mac preflight, toolchain/package pins, narrow-root import probe and baseline237-module
  bootstrap passed. The issued76roots were used; only Mathlib.Data.Fintype.Lattice and
  Mathlib.Data.Real.Archimedean were later added as precise direct prerequisites. Lead-only
  cache gets used the issued slot wrapper with `-k3`; no `lake build` or unfiltered cache get.
* Final owned-module recheck passed. The full276-module sweep (original237in exactly their
  supplied relative order, plus39helpers before consumers) passed with zero errors and all
  exits0. The admitted-declaration census changed exactly23→18: only the five targets above
  disappeared. All18inherited admissions are unchanged. See `logs/sweep-final-01/` and
  `logs/final-sorry-census.json` under evidence.
* Final native collector at revision d842 printed all414stored constants, all five targets,
  PerfectZK.seqRep, PerfectZKAbort.seqRep and the ThreeColoring consumers. Every axiom set is
  a subset of `{propext, Classical.choice, Quot.sound}`; no new `sorryAx`. See
  `logs/final-repair-axioms/`, `logs/final-repair-axiom-summary.json` and the TSV inventory.
* The six-commit format-patch series replayed in a clean scratch clone from the exact issue
  base. The resulting full Git tree and all41delivered source bytes matched revision d842.
  Raw commands/results: `logs/final-repair-replay.log`. Signing is explicitly recorded.
* Style lint at base and final:92FAIL/101WARN. Line-set comparison found no new FAIL. The
  sole changed WARN line improves Defs' missing-reader list from3definitions to2, removing
  StatZK. `logs/final-static-audit.json` records frozen headers, size, width and exact line sets.

### Rule10 whole-file seals and controls

All164final cells are accounted for:41owners × strict/coe × eval-excluded A/eval-included B.
The canonical coe/A variant treats projection coercions and PolyExpr.eval as notation.
Both strict and eval-included stress variants also pass every new/changed proof. Each native
probe covers the full transitive TCSlib import closure, not a handpicked subset; exact native
identity, install masks and EOF masks are verified for every request. Diagnostics count
both `error:` and `error(…)` forms. Advice has a legitimately empty TCSlib closure and zero
requests; its native zero-batch install/EOF records are checked explicitly.

160cells have zero errors. The four Defs cells each retain the same10errors in the same six
inherited declarations as the four issue-base Defs cells. The new StatZK_iff reader is clean.
The main's four issue-base cells are clean. The following inherited failures occur identically
in coe/A, coe/B, strict/A and strict/B; none is a new fill failure:

| Defs declaration | Errors per variant at base and final |
|---|---:|
| perfectZK_zeroRounds | 2 |
| AbortRetry.attempt_poly | 1 |
| AbortRetry.exists_retrySimulator | 2 |
| AbortRetry.statClose_retry | 1 |
| PerfectZKAbort.statZK | 3 |
| negligible_inv_pow_sqrt_div | 1 |

The effective final164cells consist of20exact checkpoint1reuses,120unchanged revision5native
cells and24revision6native reruns for the six owners whose import closures meet the repaired
helpers. `rule10/final-repair/selected-matrix.{json,tsv}` links every final record to its
selected native request record, raw log and guard result. The source and every TCSlib import
closure file are byte-identical between each selected native revision and final d842; pins
and exact request rows also match. Full hashes are in final-source-closure-provenance.json.
Earlier superseded failures remain delivered, with source revision and attribution, rather
than being counted as final results.

Whole-file seals found two real implicit-reader violations in revision5: acceptProb_prod in
ContinuationProbability (one error per variant), and distAdv_phaseReduction in
ReductionAdvantage (two errors per variant). Commit6 replaces those implicit reductions with
published acceptProb and Equiv/split-tape readers. Their statements are unchanged. All24cells
in affected owner/import closures were rerun at d842 and pass. Strict/coe and eval A/B introduce
no final new failing declaration or difference beyond the six inherited Defs declarations.

The ten retained native paired controls comprise five clean unsealed probes and five sealed
negative probes, each failing exactly once at the designated negative declaration while its
public-reader positive succeeds. Their complete definition-home import closures and pins are
unchanged at d842, and each sealed identity is present in final requests; reuse is certified
in `rule10/final-repair/control-reuse-provenance.json`. Raw logs, sources, request rows and
native masks are under checkpoint2 controls. padFin and inArg are exercised in A/B; eval is
exercised in B and explicitly excluded in A. Archived CostBoundedBy/hash-sign-only targets
absent from this closure are marked absent, not claimed exercised.

The final explicit-unfold scan covers all41sources. The primary native kind probe classifies
1245items:868theorem references,6owned definitions and371initially unresolved items, with
zero foreign definition items. A complete supplemental source-local review and24-target native
kind/home/projection/type-is-Prop probe resolve the remaining names, including proof-valued
specification fields, exported class-field readers and inherited own AbortRetry definitions.
`rule10/final-repair/explicit/` and `subagents/seq-zk-a/final-review-12/` preserve both initial
and supplemental classifications and sources. The merged result is897public readers,8inherited same-file definition items and340local/inline
proof items, with zero unexplained uses. No unresolved foreign-definition use is waived.

## Scope requests

One frozen-file change was requested and approved: nine lines adding `StatZK_iff` beside the
existing predicate in `TCSlib/Cryptography/ZeroKnowledge/Defs.lean`. It is an `Iff.rfl` reader
analogous to ZK_iff and changes no definition or prior theorem statement. Exact diff and
verbatim request/answer are in `evidence/scope-request/`.

Request (verbatim):

May I add the nine-line `StatZK_iff` reader in frozen `TCSlib/Cryptography/ZeroKnowledge/Defs.lean`? The exact proposed diff is at /Users/seyoonr/.codex/worktrees/seq-zk-a/tcslib-exchange/evidence/subagents/seq-zk-a/scope-StatZK-iff.patch. It exposes the existing simulator property using `Iff.rfl`, analogous to `ZK_iff`, without changing any definition or theorem statement. The issued seq-zk brief’s “Frozen files / Scope requests” rule requires Seyoon’s approval for this edit; Rule 10 prevents adding this reader in a helper. I’ll continue the independent interactive-proof work while this is pending.

Seyoon's answer (verbatim): Approve this reader addition

There were no further frozen-file edits. Frozen Games/Efficiency and all parent facades remain
unchanged. Suggested promotions below are requests for maintainer consideration; they were
implemented only within the authorized helper directory.

## Overlap and reuse

Raw lead searches and every agent's search logs are delivered. The detailed per-declaration
records in the appendices below preserve exact nearest-relative paths/lines, reuse/generalization
relationships and promotion requests, including historical alternatives and corrected attempts.
Their historical status sentences refer only to their stated checkpoint/source cutoff; the
final revision and verification above are authoritative. No foreign private lemma was copied.
The full final ComputationalTransfer addition is described here before those appendices:

* `zk_of_padded_spec` directly reuses the published ZK_iff, phaseVerifier_efficient,
  exists_phaseSimulator, exists_negligible_phase_bound, realPrefix_bounds,
  prefix_distAdv_joint_le, distAdv_view_endpoints and Negligible.polyExpr_mul. Nearest owned
  relative is `Composability/SequentialZK/StatisticalTransfer.lean:49`
  (`statZK_of_padded_spec`), whose statistical-distance contract
  cannot establish computational indistinguishability. The new assembly uses the common
  nonuniform metadata bound and computational hybrid; it copies neither selector, machine,
  prefix induction nor probability host. Nearest existing specialized hybrids are
  `ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean:549` (`exists_hybRed_ge`) and GI ZK hybrids; these have protocol-specific
  view/reduction contracts. `ZeroKnowledge/Defs.lean:602` (`PerfectZKAbort.statZK`) uses abort/retry amplification, which
  does not give this conditional-prefix composition theorem. All are searched/disclosed;
  shared public components are reused directly.
  Polynomial closure directly reuses `Asymptotic/ReductionSupport.lean:267`
  (`Negligible.polyExpr_mul`); no new negligible-times-polynomial proof is added.
* `ZK.seqRep` instantiates that generic theorem with the already published owned
  seqRep_proverSpec. The final proof adds no duplicate semantic or computational host.
* Existing NUPPT.loopState' and Fin.foldl supply the strict-PPT simulator and semantic phase
  recursion. No new repetition host was introduced. The indexed phase tables use canonical
  FunFamily block equivalences and public readers; repeated specializations are disclosed
  in each helper record rather than silently copied.

Promotion/reader requests: normalize/encode glue and uniform phase machinery belong with
future shared games support; the generic acceptance/postprocessing, conditional-family hybrid,
reindexing, finite-selector and length-indexed negligible-bound results belong in shared
probability/advice/reduction modules; padded proof-system contracts belong near InteractiveProofs.
The exact statements and nearest relatives are in the appended agent records. The only reader
needed in an existing defining file was the approved StatZK_iff. No other promotion or reader
request is needed to make this payload compile or satisfy Rule10.

## Host resources, exceptions and evidence completeness

The issued wrapper/default three-slot pool governed every Lean/lake/check command, including
all agent commands. Root tag seq-zk; agent tags seq-zk-a/b/c. Lead-only narrowed cache fetches
reserved3slots. No process belonging to another job was touched. Mac preflight/headroom,
package pins, narrowed roots, seeds and coordination records are delivered. Each olean tree
had one writer; packages were linked, never copied. Final independent seal streams used
separate APFS-cloned completed TCSlib trees under the same shared cap3. A one-second slot-free
gap replaced the earlier six-second gap after derand/sc-garble reported their Lean/cache work
complete. This is disclosed lead implementation judgment under Seyoon's best-judgment/resource
coordination authorization; it changes no proof budget, request, guard, module granularity or
resource cap. The final sweep itself is serial.

Ten pathological own Lean children were gracefully interrupted during development: eight by
a, one c ErrSoundness attempt and one root StatisticalTransfer attempt. Each had concrete
source/process/resource evidence and individual lead authorization under Seyoon's best-judgment
instruction; exact PID/parent/command was reverified before signaling the own child only. Raw
logs, stack/process samples, wrapper flush/release records and corrected clean reruns remain
included. These were not fixed timeouts or E-RES events. The a failure ultimately came from a
missing Defs import leaving NUPPT.simulate invalid in a signature; root/c source review missed
that cause. Root's StatisticalTransfer failure came from a positional argument to implicit V;
root and read-only review missed it until the named argument/typed application exposed it.
Earlier incorrect diagnostic hypotheses are retained and explicitly corrected.

Other preparation/instrumentation corrections are fully retained: missing baseline artifacts
were seeded with source/hash provenance; premature invalid dependency probes are labeled;
one source integration hash mismatch correctly rejected changed author comments; a dispatcher
missing-order-file attempt started no Lean; one JavaScript orchestration parse failure started
no subprocess. An overly strict final-order preparation assertion was corrected while preserving
original237relative order, using previously bootstrapped unchanged late dependencies with
verified source hashes/nonempty artifacts. The final static audit's initial broad simp regex
matched proof text, then was corrected to attribute declarations; no source or Lean change.

The zero-request Advice native seal passed. Its postprocessor initially rejected an empty name
set; the validator was corrected to require the explicit unique zero batch, two zero mask
records and matching install/EOF counts. All nonempty checks and native instrumentation remain
unchanged. Original tool version, trace and valid native log remain delivered. The stopped
dispatcher resumed only remaining cells; no Lean child was interrupted by this harness correction.
Progress-only aggregate attempts while checks were still running are labeled progress; the
final aggregate requires and certifies all164cells. No automatic approval review rejected an
action, no push was refused at the prior checkpoints, and no mathematical/scope exception beyond
the approved reader is claimed.

All evidence is under `evidence/`, including all raw success/failure logs, attempts, probe sources,
request manifests/rows, guards, scripts/tool versions, agent records and immutable receipts.
Append-only receipts resolve exact historical bytes to current files or preserved archives;
no old receipt is silently replaced. Large diagnostic samples are delivered losslessly as
numbered ZIP parts with entry lists, original lengths/hashes and verified extraction; no file
is omitted for size. `evidence/SHA256SUMS` covers exactly evidence files except itself; top-level
`SHA256SUMS` covers exactly every payload file except itself. Both path sets and every digest
are checked before delivery. Checkpoint1,2and3were delivered from the lead's separate delivery
worktree, only under inbox/fills/seq-zk; final delivery follows the same rule, unsigned commit,
pull-with-rebase and ordinary push. No proof branch push or PR/merge is performed.

## Exact final source inventory

| Source | Lines | Max width |
|---|---:|---:|
| `TCSlib/Cryptography/Composability/SequentialZK.lean` | 990 | 98 |
| `TCSlib/Cryptography/Composability/SequentialZK/Advice.lean` | 67 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/BoundedMetadata.lean` | 135 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalAdvice.lean` | 74 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalHybrid.lean` | 197 | 97 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalPhaseBound.lean` | 184 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean` | 271 | 99 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalTransfer.lean` | 100 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Congruence.lean` | 68 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean` | 354 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Efficiency.lean` | 306 | 99 |
| `TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean` | 269 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/ErrSoundness.lean` | 85 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ExecutionBounds.lean` | 88 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/HybridRecursion.lean` | 93 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean` | 98 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/NormalizationMachine.lean` | 97 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/NormalizedStep.lean` | 126 | 96 |
| `TCSlib/Cryptography/Composability/SequentialZK/PaddedProverSpec.lean` | 142 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean` | 168 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/Phases.lean` | 142 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean` | 103 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixLaws.lean` | 118 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ProofTransfers.lean` | 75 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/RealPhases.lean` | 207 | 95 |
| `TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean` | 101 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/ReductionAdvantage.lean` | 111 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/RepeatedSoundness.lean` | 218 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/RepeatedVerifier.lean` | 194 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean` | 351 | 97 |
| `TCSlib/Cryptography/Composability/SequentialZK/Soundness.lean` | 163 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/Statistical.lean` | 73 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalPostprocess.lean` | 60 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalPrefix.lean` | 154 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalRecursion.lean` | 139 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalTransfer.lean` | 115 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/SuffixLaws.lean` | 122 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean` | 323 | 99 |
| `TCSlib/Cryptography/Composability/SequentialZK/VerifierPrefix.lean` | 89 | 94 |
| `TCSlib/Cryptography/Composability/SequentialZK/WrappedVerifier.lean` | 207 | 96 |
| `TCSlib/Cryptography/ZeroKnowledge/Defs.lean` | 754 | 99 |

## Historical per-declaration overlap and implementation appendices

### Checkpoint3 overlap compendium (historical cutoff)

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


### Statistical checkpoint additions: overlap and reuse

The per-declaration records below supplement the earlier complete overlap list. Raw searches
precede implementation, and no private proof was copied.

- StatisticalTransfer.statZK_of_padded_spec directly combines StatZK_iff (Defs.lean:187),
  phaseVerifier_efficient (WrappedVerifier.lean:154), exists_phaseSimulator
  (SimulatorMachine.lean:~305), PaddedProverSpec.statClose_prefix, StatClose.map,
  statClose_average, and statClose_view_endpoints. Nearest earlier complete construction is
  PerfectZKAbort.statZK (Defs.lean:433ff): it retries a fixed input until success, whereas
  this proof threads bounded normalized prefixes. Its machine is reused through the public
  exists_phaseSimulator, and no retry/loop/postprocessing proof is copied. This generic
  padded-prover transfer belongs in this topic helper layer; no frozen-file promotion needed.
- NormalizedStep.normalizePhaseMsgs_viewV publishes the real fixed point originally local
  to the same file's statistical theorem; that theorem now reuses it, with one proof retained.
  It directly uses PhaseView.normalizePhaseMsgs_of_encode and ExecutionBounds.exec_snd_bounded.
- Canonical phaseVerifier_eq/phasePrefix_eq and the endpoint _eq readers are home-definition
  equations, added for literal reader compliance; no foreign equation is re-derived.


## StatisticalRecursion checked continuation

StatisticalRecursion.lean introduces no definition or host. Its sole public theorem
statClose_recursion takes caller-supplied zero and snoc equations for arbitrary real/simulated
sampler families and updates. Shared-prefix averaging replaces the final update at cost
delta; the existing randomized test-set reader transports the induction hypothesis through
the same simulated final update. Public transitivity and Fin.snocEquiv close the successor.
No Nonempty assumption on either coin type is required, because empty coin tables have
explicit inhabitants in the base case.

Nearest relatives: OneWayLemmas.lean:276 statClose_pi handles independent copies of one fixed
sampler comparison; Statistical.lean:59 statClose_chain handles a supplied full-sampler chain.
Neither is a caller-supplied state-dependent snoc recursion theorem, and neither proof was
copied. Directly reused readers are Statistical.lean:44 statClose_average,
Sampling.lean:237 StatClose.abs_uprob_sub_le_prod, Sampling.lean:167 StatClose.trans,
Sampling.lean:179,185 seed-equivalence transports, and Mathlib Fin.snocEquiv/snoc_init_self.
Promotion beside generic StatClose support is requested at a shared-file window.

The first source triggered stack-diagnosed pathological implicit sampler unification and
was interrupted only by exact lead authorization, with the raw source, sample, resource
reading, process chain and authorization preserved. The explicitly typed rewrite passed
check02 with no diagnostics in2.45s, maxRSS2,121,269,248 bytes. It is139lines, maxwidth94,
SHA256 fe7d94d26ba375222245902da6ce0e71c9789d9ee98a9e68e4a063d5ada9591e.
Its precise rewrite patch and large lossless sample ZIP part001 are delivered.

## NormalizedStep pending compiler diagnosis

NormalizedStep is not yet claimed checked. Its stronger zero-verifier API was approved by
the lead and independently reviewed as mathematically/type-consistent by seq-zk-c. The exact
phase-wrapper reader-only instantiation recipe is normalized-step-instantiation.md.

compiler-diagnosis-summary.md and the numbered authorization/process/source/marker records
retain each targeted own-process proof-debugging interruption. All were authorized by the
lead under Seyoon's best-judgment exception, never elapsed-time timeouts or E-RES, and no other
job or slot was changed. Every created native stack sample is delivered losslessly in ZIP
parts with raw SHA256, entry lists and verified extraction. Current work is localizing the
scalar test comparison declaration with robust direct-file IO markers; no false proof claim
or statement weakening is made. All diagnostic IO/trace must be removed before a final clean
source check and intake.

## Checkpoint 2 closed-evidence boundary

compiler-diagnosis-summary.md is the authoritative corrected closed ledger through
NormalizedStep attempt07. It supersedes earlier tentative source-stage descriptions in this
historical report. Eight own exact-process interruptions are recorded: StatisticalRecursion01
and NormalizedStep01–07, all separately lead-authorized proof debugging rather than timeouts
or E-RES. No own Lean is active at this boundary. NormalizedStep remains unverified; the checked
StatisticalPostprocess dependency and completed fixed-point/pointwise markers do not imply
that its full concrete instantiation passed. The next opacity/instance correction awaits the
lead's three-slot cache completion. Complete prerequisite sources and lossless native-sample
ZIP parts are included so all closed raw evidence has its sources and verification tools.


## Final normalization and statistical-prefix extension

NormalizedStep is now clean-checked with no diagnostics. Its final source hash is
07c9fed43664eeaa47b712f02b72f09addbe0ceb8dc134917cd0b33f6754e689
(101lines,maxwidth96;nativecheck10=2.22s). The compiler ledger now explicitly records the
missing ZeroKnowledge.Defs import exposed by attempt08 and corrected before09. Prior
elaboration-stage diagnoses were incomplete because invalid simulate fields in the
signature remained buffered. The corrected exact-source check is retained in full.

StatisticalPrefix is clean-checked with no diagnostics. Its final source hash is
5275167b11df6074d08df53ae24486e94ccb1149eaf5d6541e88ad9fe1727d64
(151lines,maxwidth94;nativecheck02=2.31s). PaddedProverSpec.statClose_step specializes the
zero-verifier comparison at every index and prefix using an explicit coin-length equality,
coin equivalence and public ofFn reader. PaddedProverSpec.statClose_prefix instantiates the
public sampler-recursion bound using the public zero/snoc fold readers. It assumes only
a direct prover-message cap and raw phase closeness at every auxiliary input; S need not
be uniform. Neither proof uses a target theorem or creates a host.

Nearest overlap relatives: StatisticalRecursion's generic caller-supplied family bound,
NormalizedStep's generic zero-verifier bound, PrefixLaws zero/snoc readers,
PaddedProverSpec.original_count, public StatClose.comp_equiv_left/nonneg, and Mathlib
List.ofFn_congr. StatisticalPrefix is their concrete composition, not a duplicate generic
loop or statistical law. Exact searches are statistical-prefix-searches.log.

The lead authorized APFS clones of completed helper oleans into this isolated olean tree.
Eight completed immutable prerequisite source/olean pairs were copied with provenance in
prefix-prerequisite-seed.json. Their sources are reused unchanged; no other owner file was
edited. The lead will perform final source, axioms, seals and sweep checks.

## BoundedMetadata overlap plan

Nearest existing material is ColZKMachine's finite maximizing domain with a bounded
sigma-word, plus the public padFin/ofFn_padFin_of_length codec. The new metadata type
only assembles those standard finite representations into the five actual reduction
fields. It defines no selector, maximizing principle, interpreter or machine. c's Advice
selector will consume the resulting finite nonempty type. The exact packed-size formula
is b's public reductionData_length; it is reused directly, not re-proved.


## Complete checked helper handoff

seq-zk-a proved ten helper modules: Normalization, NormalizationMachine, PhaseView,
Statistical, ExecutionBounds, StatisticalRecursion, NormalizedStep, StatisticalPrefix,
BoundedMetadata and RealPrefixBounds. All final source bytes are in source-snapshots with
owner/status/hash rows. No target or frozen file was edited. The lead alone integrates,
commits, seals, sweeps and delivers the target declarations.

At lead request, NormalizedStep11 exposed normalizePhaseMsgs_viewV without any statistical
premise. The existing comparison calls it; no second normalization proof was added. The
new final source hash is76766e13e0eff35d107c98505f932dcec17cdf20f89c5f423f7e1d64217884b5
(126lines;clean native11=2.50s). This supersedes the earlier101line clean10 source.

BoundedMetadata final03 passed2.38s,0diagnostics. It defines finite nonempty five-field
PhaseMetadata, exact raw data/length readers and exact coverage. An initially redundant
direct Mathlib.Data.Fintype.Sigma import was removed before final03; the final source
imports only ComputationalReduction and requires no new Mathlib root. Source hash
f94e6c8ff89a1674aaed5047e479856ebe3e2a1623e2d2ccdeb46f4ae6f8959b.
Its raw01failure and exact source are retained (product RHS parenthesization and a proof
where simp had already changed reflexive equalities to True);02passed,03removed the
redundant import and added the direct packed-data cover corollary.

RealPrefixBounds final02 passed2.27s,0diagnostics. Its aggregate theorem gives exact j*k
message count, the uniform B cap, and encoding length at most(j*k)*(2*B+2) for every
real prefix j≤q. It reuses the public raw coin-table inverse/block reader and endpoint,
the specification's boundary/reply readers, and ExecutionBounds. No generic word-length
estimate is duplicated. Source hash
1a50f8656f00e280506a67947a16a0583cdcc5fb9242efa3e15a3fc160f390d8.
Its raw01failure is retained; split_ifs generated both first-mover cases as well as the
active/filler cases, so02applied the same bounded/empty branch argument to all four.

The retained FullOwnHelpersAxioms.lean probe checks42public declarations across all ten
owned modules. It passed5.09s with0diagnostics and only propext,Classical.choice,Quot.sound.
It also synthesizes Fintype and Nonempty of PhaseMetadata for arbitrary five natural
bounds. The smaller MetadataAndStatisticsAxioms.lean is a prepared but unused predecessor
probe retained for completeness; the full probe is the executed evidence.

All copied dependencies preserve their owner's exact checked bytes: c StatisticalPostprocess
and final EndpointSampling, b final ComputationalReduction, and lead-completed helper
sources/oleans cloned only after completion authorization. Provenance JSON files record
source hashes/check rows. seq-zk-a ran no lake command and touched no other worker process.
There were no new compiler interruptions after the historical eight own authorized events.


## Checkpoint3 closed-evidence boundary

The lead reports CP3 proof revision04c253e48d9c0ebb73943f39412365cd4d8e02db. The first eight
seq-zk-a helper sources are part of that proof revision. BoundedMetadata and RealPrefixBounds
are fully checked future support sources OUTSIDE CP3, as is b's ComputationalReduction
dependency; all three exact sources are retained under source-snapshots for replay of the
new checks and the full axioms/Fintype probe. Their outside-CP3 status is explicit in the
checkpoint3-closed-files.tsv source_status column. No own process is active at this boundary.
After producing that receipt, every named byte is frozen until the lead confirms copying.

The preceding agent report includes explicitly labeled future BoundedMetadata and
RealPrefixBounds, outside CP3. Its source_status receipt is authoritative for that boundary.
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


## Endpoint helper overlap record (verbatim)

# EndpointSampling implementation record

Author: seq-zk-c. Assigned by lead after the checkpoint2 closed-evidence manifest was
sealed. This record and all endpoint-* files are future evidence, outside checkpoint
source e978a28274fdeb545e622ae28747221088352512. All72 files in the sealed manifest remain
byte-for-byte unchanged. The lead owns final integration, commits, frozen seals and delivery.

## Supplied interface and coordination

Read root PrefixFolds/PrefixLaws, b PaddedProverSpec/SimulatorMachine, and a
StatisticalRecursion. Coordinated the joint `(verifier tape, prefix)` domain with a and
b before coding. The lead approved generic tape block equivalences, real prefix
identification by the published padded-phase reader, and the optional joint statistical
endpoint convenience theorem. No sibling or main source was edited or checked in its
foreign tree. There is no target change or added cryptographic premise.

The stable new module is EndpointSampling.lean,269lines/max95columns, SHA256
76827a0f531b095aeccd1460ef56ad13bb13612a861f9e7af82bad9069c1c048.

It publishes:
- coinTableEquiv(hlen:m=q*c) and its block reader, for the real prover tape.
- coinBlocksEquiv(v,q,c,hlen:m=v+q*c) and its verifier-take/phase-block readers.
- statClose_reindex, for supplied endpoint equivalences and pointwise endpoint readers.
- PaddedProverSpec.realPrefix_eq_exec, for j<=q and supplied block equalities.
- PaddedProverSpec.realCoinsEquiv, with domain actual `(rho.withV V).ExecCoins` and codomain
  `V.Coins |x| x (Fin q -> pi.P.Coins |x|)`, plus tape/block readers.
- PaddedProverSpec.viewV_eq_realPrefix, the actual encoded real-view endpoint.
- simulate_eq_simPrefix, the typed simulator endpoint from the published raw split reader.
- statClose_view_endpoints, consuming joint real/simPrefix closeness and returning actual
  encoded repeated view versus SQ.simulate with exactly the same error. Its only extra
  readers are p=the original mover count, SQ coinLen=v+q*S.coinLen, and the supplied SQ
  split-tape endpoint; the lead derives them directly from existing readers.

## Search, overlap, reuse, and promotion

Raw exact searches are in endpoint-sampling-searches.log.

- coinTableEquiv is the canonical FunFamily.blocks composed with a finite-length cast.
  The nearest existing assemblies are RepeatedSoundness.accept_le (verifier blocks) and
  GI.gniTapes (graph-specific sampler blocks). Neither exports the required general
  length-cast table equivalence. The block proof directly reuses FunFamily.ofFn_blocks
  and List.ofFn_congr, rather than duplicating the GI.coinSlice_blocksEquiv entrywise proof.
  Promotion request: a named length-cast block equivalence/reader belongs in
  Asymptotic/Adversary.lean if accepted; it is frozen here.
- coinBlocksEquiv directly reuses splitCoins and ofFn_splitCoins_fst/snd from
  Asymptotic/CollectionsHelpers.lean:145ff, then FunFamily.blocks/ofFn_blocks. No sum split,
  take/drop proof, block equivalence, or entrywise window proof was reproduced.
  Its distinct combined codomain is one verifier tape and a finite table of phase tapes.
  Promotion request: combined uniform-tape layout reader in the shared sampling layer.
- statClose_reindex is only published comp_equiv_left/right followed by supplied pointwise
  function equalities. Searches found no combined endpoint-reader interface. It does not
  reproduce probability invariance or a statistical switch. Nearest public declarations
  are StatClose.comp_equiv_left/right (Sampling.lean:179/185). Promotion request to Sampling.
- realPrefix_eq_exec directly composes realPrefix_zero/succ and PaddedProverSpec.padded_phase.
  Its induction is on the number of phase updates, not a duplicated execution/phase proof.
  Nearest real endpoint is b's padded_phase; its single-phase conclusion does not identify
  the finite fold with all phases. The lemma belongs in this topic helper layer.
- realCoinsEquiv and its readers are the typed composition of coinTableEquiv,
  Protocol.withV_vCoinsEquiv/ofFn and product commutation. viewV_eq_realPrefix directly
  combines that interface with Protocol.viewV_withV and the real fold reader.
- simulate_eq_simPrefix directly reuses root simPrefix_eq_phasePrefix and the combined
  block readers; its raw endpoint is supplied by b's exists_phaseSimulator. It contains
  no second simulator recursion or reconstruction of the simulator machine.
- statClose_view_endpoints directly maps joint prefixes to canonical View encoding and
  reuses statClose_reindex plus both endpoint readers. It adds no per-phase statistical
  argument and preserves the error without a triangle/normalization loss.

No frozen source, new simp attribute, foreign-definition unfolding tactic, Lake command,
new iteration host, witness bound, target assumption, or new direct Mathlib root.
CollectionsHelpers was already inside the issued cached TCSlib closure.

## Isolated prerequisites and validation

The lead approved source-copying exact checkpoint helper sources plus b's final canonical
WrappedVerifier/SimulatorMachine public-reader additions, followed by native own checks.
endpoint-prerequisite-sources.json records all source provenance and SHA256s. Own helper
sources were retained. B's two final hashes were verified before copying. No sibling
oleans were copied.

The initial prerequisite Normalization check passed. NormalizationMachine then failed
because the initial209-module own bootstrap lacked ThreeColoring/Machines.olean. This
complete missing-import attempt is preserved, with no source edit to the prerequisite.
Using the lead's explicit existing authorization, APFS-cloned28 missing BASELINE oleans
from root's completed working tree; all source bytes were verified against both own/root
sources and exact checkpoint e978a28274fdeb545e622ae28747221088352512, all olean bytes hashed,
and no existing artifact overwritten. All SequentialZK modules were excluded from seeding.
endpoint-root-baseline-seed.json records each source/artifact hash and path.

Native own-tree checks then passed, one module at a time, in this order:
NormalizationMachine (retry02), PhaseView, WrappedVerifier, RealPhases, PaddedProverSpec,
PrefixFolds, SimulatorMachine, PrefixLaws. Each raw attempt and structured result is retained.

EndpointSampling check01 passed with0errors/0warnings, a fresh own olean,2.45s actual
runtime and maximum resident set size2,236,170,240bytes. The exact attempt source is saved.
Every Lean invocation used LEAN_SLOT_TAG=seq-zk-c, the shared lean-slot wrapper,
/usr/bin/time -l, scripts/lean_check_tree.sh and the separate seq-zk-c olean tree. There was
no interruption, timeout, sampling, or resource exception in this task.

The stable checked source/hash/API were sent to lead and a. No own Lean process remains.

Final reader-compliance amendment: at the lead's request, added full canonical
coinTableEquiv_eq, coinBlocksEquiv_eq, and realCoinsEquiv_eq, each rfl in its home module.
No existing body/reader changed. Check02 passed0diagnostics,2.66s actual runtime,
maxRSS2,237,087,744bytes. Final source/hash sent to lead and a; source remains stable.

## Uniform advice selector and opaque statistical post-processing

At the lead's request, inspected the published NUPPT closure/advice APIs and nearest
ThreeColoring finite-selector/hybrid proofs. The initial finite-kernel alternative is
unnecessary: maximizing the finitely many real suprema over arbitrary witnesses gives a
selector independent of the eventual negligible bound. The lead approved that route.
The complete design and remaining concrete obligations are recorded in
computational-advice-design.md; exact raw API searches are in advice-postprocess-searches.log.

Advice.lean introduces only exists_uniform_bound_selector: finite nonempty metadata,
arbitrary witness type, and a common nonnegative upper bound yield a metadata value whose
nonnegative uniform witness bounds also bound every metadata/witness pair. The proof
directly reuses Mathlib Finite.exists_max, le_csSup, and csSup_le. The nearest existing
ColZK.exists_hidingView_bound (ColZKMachine.lean:323) selects among finite colour/advice
triples and has a specialized commitment conclusion; it does not supply the arbitrary
witness-domain implication. No proof was copied. Promotion request: place this generic
bounded-family selector in a future shared order/probability helper. New precise imports
Mathlib.Data.Fintype.Lattice and Mathlib.Data.Real.Archimedean were approved by the lead;
both pinned olean files were already cached, and the lead owns required roots/pin/cache
updates. This agent ran no Lake command. Check01 passed with0errors/0warnings, 1.69s actual
runtime and maxRSS1,466,220,544 bytes. The slot wait from10:55:20 to10:57:10 UTC was normal
host contention, not an elapsed-time diagnosis, interruption, or resource shortage.

NormalizedStep's concrete elaboration remained slow inside the raw test bound despite
explicit public-reader arguments. The lead and a requested an opaque generic helper;
StatisticalPostprocess.lean introduces only statClose_map_fst. Its pair-indexed fixed-point
hypothesis matches a's existing proof directly. The ignored product factor is explicitly
Nonempty, necessary for the uniform-probability projection law (and automatically true
for verifier coin function spaces even with zero bits). It directly reuses StatClose.map,
statClose_iff, OneWay.uprob_congr and uprob_fst. Searches found no combined public map/fst
law. Nearest laws are those four imported public readers; no statistical switch, uniform
product, or event congruence proof was duplicated. Promotion request: this general law
belongs in Asymptotic/Sampling.lean if accepted; that file is frozen, so it stays in the
approved topic helper. Check01 passed with0errors/0warnings, 2.19s actual runtime and
maxRSS2,110,701,568 bytes. Source/API/hash sent to a and lead for independent copying and
checking. No concrete protocol or NUPPT appears in the helper, and no NormalizedStep edit,
check, sample, or interruption was performed by this agent.

Both new source files are stable. Every own Lean-running command used the shared wrapper,
seq-zk-c tag, one module, and own olean tree. Full raw checks, source hashes, searches,
structured attempt results, and refreshed source/diagnostic audits accompany this record.
No new simp attribute, frozen-file edit, scope extension, admission, or target change.

The computational suffix/hybrid sections above are labeled future evidence; they are not
part of checkpoint3src at the stated proof revision.

## Comment-final delivery boundary

The delivered proof tip is5a80d36a5a4da1c2906b747dab59251fdd03836a. The fourth commit adds
only16stage-comment lines across the owned file, SimulatorMachine and StatisticalPrefix.
A token roundtrip removes those lines and exactly restores the prior sources; statements
and proof tactics are unchanged. The prior source audit found seven long new proofs whose
sketches were present but internal comments missing; all seven were corrected before delivery.
Lead native rechecks passed for both changed helpers, StatisticalTransfer and the owned file.
The exact comment-final axiom census, style diff, width check, canonical seal and four-commit
independent replay are under checkpoint3-doc paths; earlier checkpoint3 logs remain historical.

Subagent checkpoint3receipts use04c253... as their original source boundary. The later
post-cp3-audit and simulator-doc-comments receipts supply the exact checked comment overlays.
Every receipt remains byte-identical. Additional closed computational-phase-bound and
withV-reader-fix receipts and snapshots postdate that boundary and are explicitly future
support, outside this checkpoint's30src files. ComputationalTransfer.lean under drafts is
uncompiled future final assembly, reviewed read-only with exact source hashes; it is not a
proved source in this checkpoint.

## Historical receipt resolution

Closed receipt files are kept immutable. Nine referenced metadata paths later acquired newer
versions after copy acknowledgment. Their original exact bytes are also delivered: five a
metadata files recovered from our published CP2Git payload, two c append-only result prefixes
verified by original hashes, and two c audit files deterministically regenerated by the
unchanged original script from15authenticated source snapshots and exactly48historical logs.
Both regenerated files match their original receipt SHA256exactly. The current171-file c
receipt stayed unchanged throughout. All commands/input hashes/stdout/provenance are retained.
receipt-resolution.tsv resolves every historical row to exact current or archived bytes;
no old metadata or raw diagnostic has been dropped. Primary SHA256SUMS manifests cover all
versions and the resolution map.


### Preserved implementation record: subagents/seq-zk-a/report.md

# seq-zk-a final helper report

Agent `/root/zk_route`, tag `seq-zk-a`, branch `fill/seq-zk-a`, issue base
107f1e8c218733eac12d6b9bee6fece441271317. Worktree:
`/Users/seyoonr/.codex/worktrees/seq-zk-a/tcslib-exchange`.
Own olean tree: `.lake/seq-zk-a-oleans`, seeded by the lead from completed base modules.
`.lake/packages` is a symlink to the lead's exact-pin packages and read-only to this agent.
No commits, Lake commands, frozen edits, or SequentialZK.lean edits were made by this agent.

## Checked source

- Normalization.lean: 98 lines, maximum width 94; encoding bridge, bounded slot normalizer,
  exact count, per-message length bound, canonical bounded-list fixed point, encoded-size bound.
- NormalizationMachine.lean: 97 lines, maximum width 95; polynomial-time canonical reencoding,
  total decoded lookup, and encoded bounded-slot normalization for arbitrary polynomial-time
  raw input and unary-computable slot count and bit cap.
- PhaseView.lean: 168 lines, maximum width 95; canonical view metadata/tape/encoding validator,
  fixed-point and malformed-view fallback, bounded normalized messages and polynomial-time
  validator/encoded-normalizer theorems.

All three compile without final diagnostics or admissions, and add no simp attributes.
Source hashes are recorded in final-width-and-hashes.log. The first two source files were
held byte-stable after checking so seq-zk-b could reuse them with recorded provenance.

## Overlap and reuse

### Normalization.lean

- encodeMsgs_eq_encWords exactly matches the local `have henc` inside
  SecureComputation/Yao.lean:352. That provider is outside the supplied closure; this helper
  derives the general statement from public nil/cons readers of both encodings. The same
  representation occurs in ThreeColoring/Machines.lean:912 encodeMsgs_eq_flatMap.
  Promotion request: a general Strategy/BinArith encoding bridge belongs beside
  Strategy.encodeMsgs in ZeroKnowledge/Interaction.lean during a shared-file window.
- normalizeMsgs and normalizeMsgs_eq publish a new bounded-slot operation. No existing
  normalization with this shape was found in TCSlib or Mathlib searches.
- length_normalizeMsgs specializes List.length_map and List.length_range, directly reused.
- length_le_of_mem_normalizeMsgs uses List.length_take and Nat.min_le_left; this is the same
  arithmetic as List.length_take_le, specialized to the new operation.
- normalizeMsgs_encodeMsgs reuses BinArith.decWords_encWords (Words.lean:116) and
  List.take_of_length_le. No decoder or list host is copied.
- length_encodeMsgs_normalizeMsgs_le directly specializes public Words.lean:81
  length_encWords_le to the new invariants. CommitmentLemmas.lean:241 length_encodeMsgs_le
  offers the same generic encoded-size bound but introduces larger cryptographic imports.

### NormalizationMachine.lean

- polyTimeComputable_encWords_decWords specializes Words.lean:221 polyTimeComputable_mapW
  to the identity payload and uses mapW_pairEncode at line 208. No host is copied.
- polyTimeComputable_decWords_getD composes canonicalization with Loops.lean:391
  polyTimeComputable_getW and its reader getW_pairEncode at line 375.
- polyTimeComputable_encode_normalizeMsgs uses these lookups, EncodingMachines.lean:459
  truncate_poly, and ThreeColoring/Machines.lean:159 polyTimeComputable_flatMap_range. The
  published counted-emission argument is reused. Its import is within the supplied closure
  and was confirmed with the lead. No extra size premise or new private host is introduced.
- Promotion request: the generic canonicalization and total decoded-lookup lemmas belong
  beside the BinaryArith word-list hosts at a future shared-file window.

### PhaseView.lean

- phaseViewPayload and its eq reader are a new canonical-view validator; no matching
  validator was found. normalizePhaseMsgs and its eq reader compose it with normalizeMsgs.
- phaseViewPayload_of_encode specializes Interaction.lean:302 View.encode_mk, public pair
  projection equations, and Words.lean:116 decWords_encWords. All are directly reused.
- phaseViewPayload_of_ne is the new validator's failed-branch equation, proved by if_neg.
- normalizePhaseMsgs_of_encode directly reuses Normalization.lean:76
  normalizeMsgs_encodeMsgs after the canonical payload reader.
- length_normalizePhaseMsgs, length_le_of_mem_normalizePhaseMsgs, and
  length_encodeMsgs_normalizePhaseMsgs_le directly reuse Normalization.lean:60,66,89 after
  the new definition reader. They are its three phase-view specializations.
- normalizePhaseMsgs_of_ne specializes the normalized-empty-payload formula; its list
  calculation directly reuses core getD/getElem?/take/map-constant/range equations.
- polyTimeComputable_phaseViewPayload composes the existing canonical reencoder with
  Loops.lean:426 polyTimeComputable_eqW and PolyTimePairing.lean:290
  polyTimeComputable_ite. It introduces no host or machine construction.
- polyTimeComputable_encode_normalizePhaseMsgs directly reuses
  NormalizationMachine.lean:72 after validation. No additional promotion is requested for
  these phase-specific operations.

Searches and closest relatives are recorded in searches.md, searches.log,
normalization-machine-searches.log, map-identity-search.log, phase-view-searches.log and
phase-view-ite-search.log. Searches consulted the lead's Mathlib source read-only.

## Scope and mathematical assessment

The agent discovered the missing StatZK reader and supplied scope-StatZK-iff.patch without
applying it. The lead reports Seyoon approved the addition and the lead applied it. This
agent changed no frozen file. route-assessment.md records the independent mathematical
review of the ZK/StatZK route, auxiliary bounds and edge cases. No mathematical counterexample
was found; that assessment itself is not a checked composition proof.

## Checks and evidence

Every check used LEAN_SLOT_TAG=seq-zk-a, the assigned TCSLIB_OLEANS, the issued host wrapper,
/usr/bin/time -l, and scripts/lean_check_tree.sh for one module. All raw attempts are retained.

- Normalization passed attempt 01: 0 errors, 0 warnings; RSS 1,564,000,256 bytes.
- NormalizationMachine attempt 01 had one map-identity proof error and two unused simp
  arguments. Core List.map_id' fixed the lambda identity; attempt 02 passed with 0 errors,
  0 warnings; RSS 2,213,593,088 bytes.
- PhaseView attempt 01 had one missing true-conditional simplification and one unused simp
  argument. Public if_true completed the payload proof; attempt 02 passed with 0 errors,
  0 warnings; RSS 2,224,095,232 bytes.

check-summary.json counts both error: and error(...) diagnostic forms. slots.log records
all this tag's acquisitions/releases and their timestamps; it supplies the module start/end
for the first normalization raw log, which contains only the timing report. Later raw logs
include START/END timestamps, including any normal slot wait. Axiom/seal/campaign-lint checks
are the lead's final merged-branch responsibility. No probe/check logs have been omitted.

## Statistical helper continuation

Statistical.lean adds the sole missing sampler-level shared-prefix averaging lemma
`statClose_average`. It directly reuses statClose_iff (Asymptotic/Sampling.lean:133),
StatClose.abs_uprob_sub_le (Sampling.lean:138), abs_uexp_sub_le (Sampling.lean:210), and
uprob_prod (Foundations/Probability.lean:153). This is a new packaging of those published
interfaces, not a copied averaging proof. Promotion beside StatClose in Sampling.lean is
requested at a future shared-file window.

The lead approved an explicit nonnegative error premise to cover an empty shared seed space.
statistical-api.md records the exact counterexample to the draft interface without that
premise, and explains why it is not a frozen-target flaw. Actual phase coin spaces are
nonempty and one-phase closeness also supplies nonnegativity for witnessed inputs.

No randomized postprocessing wrapper was added: StatClose.abs_uprob_sub_le_prod already
provides the exact test-set bound, and statistical-api.md gives its two-line consumer.
The new file imports only Asymptotic.Sampling, within the supplied closure; no new host,
cache root, frozen edit or simp attribute is introduced.

Statistical.lean passed wrapped check 01 with no diagnostics; peak RSS 2,110,177,280 bytes,
3.22 seconds compiler wall time, after a normal shared-slot wait. The raw log includes
START/END timestamps. statistical-searches.log retains the searches before implementation.
The final source width/hash ledger, check summary, and own-tag slot log are updated.

## Finite-chain and actual-kernel outline continuation

After fresh public TCSlib and Mathlib searches, Statistical.lean now also publishes
statClose_chain for an arbitrary same-seed family f : Nat -> Omega -> O. The proof only
uses public StatClose.refl (Sampling.lean:153) and StatClose.trans (Sampling.lean:167), with
natural-cast arithmetic. It has no sign premise on delta, including q=0. Nearest relatives
are Probability.lean:218 abs_sub_le_sum_hybrids (a scalar probability-gap theorem) and
OneWayLemmas.lean:276 statClose_pi (independent products of a fixed sampler comparison).
Neither is an arbitrary-family StatClose chain; neither argument is copied. Promotion of
this generic chain lemma beside StatClose is requested at a shared-file window.

Statistical check02 passes with no diagnostics; RSS 2,114,224,128 bytes and 3.67 seconds
compiler wall time. All check summaries, own slot records, and final source hashes are
updated. The earlier Statistical hash is superseded by final-width-and-hashes.log.

hybrid-outline.md gives a precise semantic proof plan for the actual one-phase kernels,
using b's approved phaseAux/phaseVerifier and phasePrefix simulator-fold readers. It includes
normalization's real fixed point, common paired real/simulator coin tables, shared-prefix
averaging, existing randomized suffix data processing, full chain, and endpoint coin-law
transports. It explicitly records remaining execution-reader obligations rather than
assuming them. The outline has been coordinated with seq-zk-b; it proposes no private host
or frozen edit and weakens no target. Raw extra API searches are retained in
statistical-chain-searches.log and hybrid-execution-searches.log.

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

## StatisticalRecursion checked continuation

StatisticalRecursion.lean introduces no definition or host. Its sole public theorem
statClose_recursion takes caller-supplied zero and snoc equations for arbitrary real/simulated
sampler families and updates. Shared-prefix averaging replaces the final update at cost
delta; the existing randomized test-set reader transports the induction hypothesis through
the same simulated final update. Public transitivity and Fin.snocEquiv close the successor.
No Nonempty assumption on either coin type is required, because empty coin tables have
explicit inhabitants in the base case.

Nearest relatives: OneWayLemmas.lean:276 statClose_pi handles independent copies of one fixed
sampler comparison; Statistical.lean:59 statClose_chain handles a supplied full-sampler chain.
Neither is a caller-supplied state-dependent snoc recursion theorem, and neither proof was
copied. Directly reused readers are Statistical.lean:44 statClose_average,
Sampling.lean:237 StatClose.abs_uprob_sub_le_prod, Sampling.lean:167 StatClose.trans,
Sampling.lean:179,185 seed-equivalence transports, and Mathlib Fin.snocEquiv/snoc_init_self.
Promotion beside generic StatClose support is requested at a shared-file window.

The first source triggered stack-diagnosed pathological implicit sampler unification and
was interrupted only by exact lead authorization, with the raw source, sample, resource
reading, process chain and authorization preserved. The explicitly typed rewrite passed
check02 with no diagnostics in2.45s, maxRSS2,121,269,248 bytes. It is139lines, maxwidth94,
SHA256 fe7d94d26ba375222245902da6ce0e71c9789d9ee98a9e68e4a063d5ada9591e.
Its precise rewrite patch and large lossless sample ZIP part001 are delivered.

## NormalizedStep pending compiler diagnosis

NormalizedStep is not yet claimed checked. Its stronger zero-verifier API was approved by
the lead and independently reviewed as mathematically/type-consistent by seq-zk-c. The exact
phase-wrapper reader-only instantiation recipe is normalized-step-instantiation.md.

compiler-diagnosis-summary.md and the numbered authorization/process/source/marker records
retain each targeted own-process proof-debugging interruption. All were authorized by the
lead under Seyoon's best-judgment exception, never elapsed-time timeouts or E-RES, and no other
job or slot was changed. Every created native stack sample is delivered losslessly in ZIP
parts with raw SHA256, entry lists and verified extraction. Current work is localizing the
scalar test comparison declaration with robust direct-file IO markers; no false proof claim
or statement weakening is made. All diagnostic IO/trace must be removed before a final clean
source check and intake.

## Checkpoint 2 closed-evidence boundary

compiler-diagnosis-summary.md is the authoritative corrected closed ledger through
NormalizedStep attempt07. It supersedes earlier tentative source-stage descriptions in this
historical report. Eight own exact-process interruptions are recorded: StatisticalRecursion01
and NormalizedStep01–07, all separately lead-authorized proof debugging rather than timeouts
or E-RES. No own Lean is active at this boundary. NormalizedStep remains unverified; the checked
StatisticalPostprocess dependency and completed fixed-point/pointwise markers do not imply
that its full concrete instantiation passed. The next opacity/instance correction awaits the
lead's three-slot cache completion. Complete prerequisite sources and lossless native-sample
ZIP parts are included so all closed raw evidence has its sources and verification tools.


## Final normalization and statistical-prefix extension

NormalizedStep is now clean-checked with no diagnostics. Its final source hash is
07c9fed43664eeaa47b712f02b72f09addbe0ceb8dc134917cd0b33f6754e689
(101lines,maxwidth96;nativecheck10=2.22s). The compiler ledger now explicitly records the
missing ZeroKnowledge.Defs import exposed by attempt08 and corrected before09. Prior
elaboration-stage diagnoses were incomplete because invalid simulate fields in the
signature remained buffered. The corrected exact-source check is retained in full.

StatisticalPrefix is clean-checked with no diagnostics. Its final source hash is
5275167b11df6074d08df53ae24486e94ccb1149eaf5d6541e88ad9fe1727d64
(151lines,maxwidth94;nativecheck02=2.31s). PaddedProverSpec.statClose_step specializes the
zero-verifier comparison at every index and prefix using an explicit coin-length equality,
coin equivalence and public ofFn reader. PaddedProverSpec.statClose_prefix instantiates the
public sampler-recursion bound using the public zero/snoc fold readers. It assumes only
a direct prover-message cap and raw phase closeness at every auxiliary input; S need not
be uniform. Neither proof uses a target theorem or creates a host.

Nearest overlap relatives: StatisticalRecursion's generic caller-supplied family bound,
NormalizedStep's generic zero-verifier bound, PrefixLaws zero/snoc readers,
PaddedProverSpec.original_count, public StatClose.comp_equiv_left/nonneg, and Mathlib
List.ofFn_congr. StatisticalPrefix is their concrete composition, not a duplicate generic
loop or statistical law. Exact searches are statistical-prefix-searches.log.

The lead authorized APFS clones of completed helper oleans into this isolated olean tree.
Eight completed immutable prerequisite source/olean pairs were copied with provenance in
prefix-prerequisite-seed.json. Their sources are reused unchanged; no other owner file was
edited. The lead will perform final source, axioms, seals and sweep checks.

## BoundedMetadata overlap plan

Nearest existing material is ColZKMachine's finite maximizing domain with a bounded
sigma-word, plus the public padFin/ofFn_padFin_of_length codec. The new metadata type
only assembles those standard finite representations into the five actual reduction
fields. It defines no selector, maximizing principle, interpreter or machine. c's Advice
selector will consume the resulting finite nonempty type. The exact packed-size formula
is b's public reductionData_length; it is reused directly, not re-proved.


## Complete checked helper handoff

seq-zk-a proved ten helper modules: Normalization, NormalizationMachine, PhaseView,
Statistical, ExecutionBounds, StatisticalRecursion, NormalizedStep, StatisticalPrefix,
BoundedMetadata and RealPrefixBounds. All final source bytes are in source-snapshots with
owner/status/hash rows. No target or frozen file was edited. The lead alone integrates,
commits, seals, sweeps and delivers the target declarations.

At lead request, NormalizedStep11 exposed normalizePhaseMsgs_viewV without any statistical
premise. The existing comparison calls it; no second normalization proof was added. The
new final source hash is76766e13e0eff35d107c98505f932dcec17cdf20f89c5f423f7e1d64217884b5
(126lines;clean native11=2.50s). This supersedes the earlier101line clean10 source.

BoundedMetadata final03 passed2.38s,0diagnostics. It defines finite nonempty five-field
PhaseMetadata, exact raw data/length readers and exact coverage. An initially redundant
direct Mathlib.Data.Fintype.Sigma import was removed before final03; the final source
imports only ComputationalReduction and requires no new Mathlib root. Source hash
f94e6c8ff89a1674aaed5047e479856ebe3e2a1623e2d2ccdeb46f4ae6f8959b.
Its raw01failure and exact source are retained (product RHS parenthesization and a proof
where simp had already changed reflexive equalities to True);02passed,03removed the
redundant import and added the direct packed-data cover corollary.

RealPrefixBounds final02 passed2.27s,0diagnostics. Its aggregate theorem gives exact j*k
message count, the uniform B cap, and encoding length at most(j*k)*(2*B+2) for every
real prefix j≤q. It reuses the public raw coin-table inverse/block reader and endpoint,
the specification's boundary/reply readers, and ExecutionBounds. No generic word-length
estimate is duplicated. Source hash
1a50f8656f00e280506a67947a16a0583cdcc5fb9242efa3e15a3fc160f390d8.
Its raw01failure is retained; split_ifs generated both first-mover cases as well as the
active/filler cases, so02applied the same bounded/empty branch argument to all four.

The retained FullOwnHelpersAxioms.lean probe checks42public declarations across all ten
owned modules. It passed5.09s with0diagnostics and only propext,Classical.choice,Quot.sound.
It also synthesizes Fintype and Nonempty of PhaseMetadata for arbitrary five natural
bounds. The smaller MetadataAndStatisticsAxioms.lean is a prepared but unused predecessor
probe retained for completeness; the full probe is the executed evidence.

All copied dependencies preserve their owner's exact checked bytes: c StatisticalPostprocess
and final EndpointSampling, b final ComputationalReduction, and lead-completed helper
sources/oleans cloned only after completion authorization. Provenance JSON files record
source hashes/check rows. seq-zk-a ran no lake command and touched no other worker process.
There were no new compiler interruptions after the historical eight own authorized events.


## Checkpoint3 closed-evidence boundary

The lead reports CP3 proof revision04c253e48d9c0ebb73943f39412365cd4d8e02db. The first eight
seq-zk-a helper sources are part of that proof revision. BoundedMetadata and RealPrefixBounds
are fully checked future support sources OUTSIDE CP3, as is b's ComputationalReduction
dependency; all three exact sources are retained under source-snapshots for replay of the
new checks and the full axioms/Fintype probe. Their outside-CP3 status is explicit in the
checkpoint3-closed-files.tsv source_status column. No own process is active at this boundary.
After producing that receipt, every named byte is frozen until the lead confirms copying.


### Preserved implementation record: subagents/seq-zk-c/computational-hybrid-record.md

# Computational helper record (future work after checkpoint3)

Author: seq-zk-c. The lead owns main, frozen files, final merge/checks/axioms/seals,
commits and delivery. This record concerns only c-owned helper modules and isolated native
checks. Checkpoint3 source is04c253e48d9c0ebb73943f39412365cd4d8e02db. The first10 c helpers
match that source exactly; the five helpers below are future checked source outside it.
checked-source-snapshots.json and its exact15 snapshots record this distinction.

## Checked contributions and architecture

HybridRecursion.lean:90lines, SHA5277132bb0013c9e290f17272947624e6fd33f17fb9029608d9821affe1e92da.
The public hybrid_recursion_gap_le uses arbitrary state and continuation potential, only
finite nonempty real coin type A, supplied initial/snoc family readers, and conditional
potential drift<=epsilon at every actual prefix. It concludes end-to-end difference
<=q*epsilon. It directly reuses the existing telescope, snoc equivalence, product averaging,
and abs_uexp_sub_le. No finite state/witness bound, new iteration host or new telescope.

SuffixLaws.lean:122lines, SHA4415c221a7d3273f02c22572a20f7033071a504364cb0b5dc855c35e281f3971.
phaseStep_eq_simStep reads a supplied typed block; phaseSuffix_front separates the first
update of b's existing suffix; phaseSuffix_congr_blocks depends only on its own range;
phaseSuffix_update_before ignores an overwritten earlier table coordinate. There is no
new suffix machine or duplicate execution-phase induction. This module owns no definitions.

ComputationalAdvice.lean:74lines, SHAf7a61a8277300e179d2df45c2be4261c90429d8ad7142583ef75e967ad26cffc.
exists_uniform_negligible_bound takes finite nonempty A(n), arbitrary witnesses W,
gap<=1, a validity predicate, and one negligible bound for every selected metadata function.
It chooses metadata before epsilon by the checked Advice selector and concludes one
negligible epsilon uniformly bounds every valid gap by abs(epsilon(n)). Invalid gaps are
zero only inside the proof. No machine decides validity or witness membership. No
nonnegative-gap premise, witness encoding, witness maximum attainment, or bound on W.
Old Advice source is unchanged.

ContinuationProbability.lean:320lines, SHAa5922afe075adffb6349ba1801857125ac76ec158d4bca3faa8fc5289ee03d32.
- acceptProb_prod, acceptProb_update_tuple, acceptProb_postprocess_fst expose exact opaque
  product/update/unused-factor acceptance laws from published probability readers.
- continuationProb(+_eq) is the existing suffix acceptance potential, sampling a full
  typed table of independent S tapes and using only the suffix range.
- continuationProb_bellman uses the published acceptProb_update to reseed the current
  table entry, the front-step reader to consume it, and update_before to remove it from
  all later phases. It is exactly a fresh current simulator coin and independent suffix.
- continuationProb_real directly uses a's normalizePhaseMsgs_viewV fixed point with the
  supplied padded-prover original message count and caller's uniform prover bound. It
  removes the wrapper's zero verifier tape by opaque public averaging/projection laws.
- continuationProb_sim is the matching raw S call identity from the Bellman law.
- phaseGap(+_eq) is the SINGLE shared local raw original-view/S gap through b's
  phaseContinuation, with coin product (Fin Q -> S.Coins) x Dcoins. b's
  ComputationalPhaseBound consumes this public definition/reader; no duplicate gap.
- phaseGap_eq_drift states its exact absolute potential drift under the real next phase.
Final source has the required sim proof sketch and major-step comments. Only docs changed
between passing03 and passing04; no statements, definitions or tactics changed.

ComputationalHybrid.lean:197lines, SHA07e9f3beeaca0c2d2c4d5aa4e166cda4833412ad6b9bf5b5aba62aa888fa9bb1.
prefix_distAdv_le assumes the shared phaseGap bound for each ACTUAL realPrefix before q,
plus d, numeric p count, nonnegative epsilon and honest-message bound. It concludes the
canonical real/simulated prefix view advantage<=Q(|x|)*epsilon at fixed verifier tape.
The real/sim endpoint identities and generic potential theorem do all the work.
prefix_distAdv_joint_le averages verifier tapes. distAdv_reindex directly uses public
acceptProb_comp_equiv and supplied readers. distAdv_view_endpoints equates actual encoded
repeated-view/SQ advantage with the joint typed prefix advantage, reusing stable Endpoint.
No metadata validity, finite witnesses, weakened target or extra cryptographic assumption.
The q=0 case is included by the generic telescope; no Fin0 index is fabricated.

## Coordination and source provenance

The lead approved every new helper/API before coding. c alone edited these files. a owns
NormalizedStep and RealPrefixBounds; b owns SuffixMachine, ComputationalReduction,
ReductionAdvantage and ComputationalPhaseBound; root owns main and transfers. No helper
ownership overlap or foreign-tree edit/check occurred. In particular, a supplies ALL real
normalization and prefix-size proofs, b supplies ALL machine/advice construction and
NUPPT reduction-coin transport, and c does not duplicate them.

Only stable checked source bytes were copied from b/a, then compiled in c's own tree.
Hybrid prerequisite source manifests record exact hashes. A source-copy assertion caught
b's comment-only update from0095... to32d8... before copying; c waited for b's successful
final native check, then copied32d8... unchanged. This was provenance checking, not a proof
failure. SuffixMachine, ComputationalReduction, ExecutionBounds and a's corrected
NormalizedStep all passed native own-tree prerequisite checks. No sibling olean was used.

## Search, overlap, reuse, and promotion

Raw searches are in hybrid-searches.log; earlier advice/endpoint searches remain complete.

Nearest generic hybrid: Foundations/Probability.abs_sub_le_sum_hybrids. HybridRecursion
USES it directly; only conditional-prefix averaging and the snoc reader are new. Nearest
specialized hybrid is ColSimLemmas.exists_hybRed_ge (ThreeColoring/SimulatorLemmas), whose
protocol-specific coordinate/prefix proof does not supply the conditional state-potential
contract. Promotion request: generic conditional-family hybrid in shared probability if
accepted; frozen modules were not edited.

Suffix front/block readers are consequences of b's published phaseSuffix_succ/zero and
phaseStep_eq. None existed in the searched closure. The finite-table update proof uses
canonical FunFamily.ofFn_blocks plus Equiv.apply_symm_apply, not an entrywise copy of
GI.coinSlice_blocksEquiv. This same canonical specialization also appears as a local
reader in RepeatedSoundness; it is disclosed and directly reuses the public window law.
No independent block/window arithmetic is re-proved.

ComputationalAdvice directly reuses Advice.exists_uniform_bound_selector. Nearest existing
finite selector is ColZK.exists_hidingView_bound, which cannot cover an arbitrary witness
domain. Its finite maximum proof was not copied. Promotion request: the length-indexed
logical lifting belongs with a future shared advice/reduction helper.

acceptProb_prod's nearest relative is the local hX product computation in ColZK.exists_fixSeed;
no exact public sampler-factor averaging reader was found. It directly reuses acceptProb_def,
uprob_comp_equiv and uprob_prod. acceptProb_update_tuple SPECIALIZES the existing public
acceptProb_update (Indistinguishability.lean:103), dropping Unit via acceptProb_fst; it does
not construct/re-prove a uniform update bijection. postprocess_fst uses acceptProb_bind,
the product reader and HardcoreBit.uexp_fst. Promotion requests: these generic acceptance
readers belong in shared Experiments/Indistinguishability, which are frozen here.

continuationProb/phaseGap are topic-specific semantic leaves, with canonical_eq readers.
Bellman uses published acceptProb_update and owned suffix readers; real identity uses a's
published fixed point; sim identity uses b's phaseContinuation_eq. These helpers introduce
no probability distribution host, simulator loop, or normalization proof.

The actual q*epsilon theorem directly reuses HybridRecursion, PrefixLaws, phaseGap_eq_drift,
and both suffix endpoints. Nearest specialized bounds are the ThreeColoring hybrid and
coordinatewise pair-hybrid theorems in Commitment; they do not supply this adaptive real
prefix/simulated suffix contract. No specialized proof was copied. distAdv_reindex is only
acceptProb_comp_equiv plus supplied function equalities; promotion to shared sampling is
requested. Endpoint transfer reuses stable EndpointSampling, not a second coin induction.

## Native validation and corrections

All attempts use LEAN_SLOT_TAG=seq-zk-c, the shared lean-slot.sh wrapper, /usr/bin/time -l,
scripts/lean_check_tree.sh ONE module, and c's private seq-zk-c olean tree. All Python uses
python3 -I. Every raw output, source-attempt snapshot and structured result is retained.
No interruption, timeout, sampling, resource exception or Lake command in this task.

- HybridRecursion01: rewrite could not infer a product integrand through projections.
  Supplied it explicitly to the public expectation-equivalence reader. Attempt02 passed,
  0diagnostics,2.23s,maxRSS2,116,681,728.
- SuffixLaws01: omega saw an opaque Fin.mk.val term. Exposed its concrete value by change.
  Attempt02 passed,0diagnostics,2.53s,maxRSS2,227,847,168.
- ComputationalAdvice01 passed,0diagnostics,2.17s,maxRSS2,006,581,248.
- ContinuationProbability01: implicit product/fst reader matches and update_self name;
  fixed through explicit functions and the published correct reader. Attempt02: explicit
  Fin value and bind postprocessor needed. Attempt03 passed the complete shared gap/drift
  module. Attempt04, doc-final only, passed0diagnostics,2.35s,maxRSS2,243,788,800.
- ComputationalHybrid01: after suffix_zero, an own local realView alias goal remained;
  closed it by rfl. Attempt02 passed all four complete declarations,0diagnostics,2.33s,
  maxRSS2,231,697,408. No target or premise change.

Endpoint's separate record includes its final canonical-reader check02. The old read-only
NormalizedStep diagnostic suggestions are corrected by normalized-step-diagnosis-correction.md:
the actual cause was a missing direct Defs import, found by a/root with with_reducible.
The initial closed evidence remains byte-identical, preserving the full chronological record.


### Preserved implementation record: subagents/seq-zk-b/computational-reduction-overlap.md

# Computational reduction search and overlap disclosure

Worker: seq-zk-b. Source SHA256: 32d8ef575f769772b7e8b4b309ddf55d3e52c605c0f09c7fdc98cdbec11e6bb3.

Searches are retained verbatim in computational-reduction-searches.log. No existing generic
metadata-driven normalized one-phase/simulated-suffix reduction was found. The nearest
concrete reductions are ThreeColoring/ColZKMachine.lean exists_colHidingRed (commitment
hiding with advice) and SimulatorLemmas.lean exists_hybRed_ge (commitment-coordinate hybrid).
They do not implement this sequential-protocol continuation; no proof body was copied.

Direct reuse: Complexity/Randomized/Closure.lean exists_comp, exists_seq, exists_withAdvice;
public NUPPT uniform constructor, input/layout and activation readers; WrappedVerifier
phaseAux_eq/phaseAux_poly; PhaseView normalization PT reader; SuffixMachine phaseSuffix_poly;
EncodingMachines unary arithmetic; public pair/encoded-message readers. No new host or
hand-built control machine was introduced. Raw prefix advice decodes totally, including
malformed words, without testing witness or reachability.

phaseContinuation repeats the normalized-candidate append expression of phaseStep and the
local phasePrefix_poly assembly. Its candidate is supplied externally, while phaseStep
computes it by activating S, so phaseStep_poly cannot directly instantiate this function.
The PT leaf is re-derived from the published normalization/pair/append readers, then the
published arbitrary-start/prefix suffix theorem is applied. A later extraction could share
that candidate-append PT leaf. This overlap and reuse were explicitly approved by the lead.

The uniform continuation sampler is nearest exists_phaseSimulator, but it reads arbitrary
advised metadata/current raw candidate rather than constructing a whole repetition from an
empty prefix. Both use the same published uniform constructor, not duplicated hosts.
All additions stay within the approved helper scope; no frozen source or Mathlib root changed.


### Preserved implementation record: subagents/seq-zk-b/reduction-advantage-overlap.md

# Typed reduction advantage overlap disclosure

Worker: seq-zk-b. ReductionAdvantage.lean introduces no definitions or hosts. Searches are
retained in reduction-advantage-searches.log. Nearest generic readers are
EnsembleLemmas.acceptProb_coins_equiv and coinsEquiv/take_ofFn_coinsEquiv/
drop_ofFn_coinsEquiv (Asymptotic/EnsemblesLemmas.lean:85,141,151,156). They are directly reused,
not copied. This improves the initially proposed local splitCoins/cast equivalence by using
the already published exact split/cast constructor and its two tape readers.

CommitmentLemmas.acceptProb_distinguisherL_of_runAtL handles one deterministic preprocessor
with an equal coin polynomial. ThreeColoring/ColZKMachine.distAdv_distinguisherL_reparam
handles deterministic preprocessing with a changed security parameter. Neither handles the
random continuation suffix and independent final-distinguisher tape required here. Their
standard public-reader/reindexing pattern is reused, but no proof body was copied and no
new general probability transport theorem is introduced. The new theorem applies the
existing acceptance reindexer twice and the public distAdv_def.

Canonical FunFamily.blocks.symm only regroups the simulator coin table; its implementation
is not unfolded. The raw run equation is a hypothesis supplied by exists_phaseReduction,
so the proof does not unfold any foreign reduction or machine. Only the local equivalence
e is expanded. NUPPT.distinguisherL_eq/runAt_eq/coinLen_eq and PolyExpr evaluation readers
supply all foreign computations. No validity, reachability, witness or nonemptiness premise
was added. Parent approved this exact statement and source-only integration.


### Preserved implementation record: subagents/seq-zk-b/computational-phase-bound-overlap.md

# Common phase-bound overlap and reuse disclosure

Worker: seq-zk-b. Parent approved this exact helper/API after receiving a concrete proposal.
No existing theorem was found assembling the fixed original wrapped-ZK comparison into the
common finite-metadata phase bound. Searches are in computational-phase-bound-searches.log.
Nearest relatives are c's exists_uniform_negligible_bound/exists_uniform_bound_selector,
a's PhaseMetadata bounds/cover, our advised phase reduction and typed advantage bridge,
and c's shared phaseGap reader. They are all reused directly; no selector, cover, reduction,
coin transport or probability host is copied. No public definitions or hosts are added.

The bounded-gap leaf directly reuses ColZK.distAdv_le_one from the already cached pinned
ThreeColoring/ColZKLemmas module; no duplicate generic probability lemma or new Mathlib root
is added. Local syntactic polynomials set H=Q*k*(2B+2) and
b=2*var+2*Lz+2*V.coins+2*Q+H+8. The selected metadata word has length at most b by the public
PhaseMetadata.toData_length_le/toData_eq readers. On canonical raw-prefix validity,
reductionData_encodeMsgs identifies this word with pairEncode x aux. The existing public
length_pairSndD_le reader bounds aux; no pair arithmetic is reproved.

Validity is a local proof-only predicate R x y plus canonical-prefix and j<Q facts.
The arbitrary witness y is outside the finite metadata and is neither stored nor tested.
The existing selector is applied before requesting the original negligible error. The
machine remains the already checked total advised phase reduction. The final exact cover
handles arbitrary typed bounded prefixes, without a reachability or prover-bound premise.

The first two failures concerned only local argument/name/equality elaboration. Native01
exposed implicit List.length_ofFn use, a missing Turing namespace, and dependent coin casts
from rewriting a parameter inside the distinguisher. Native02 exposed a rewrite touching
both sides of a canonical-prefix equation and the final analogous dependent distinguisher
transport. Keeping local experiments at actual decoded x.length, transporting the whole
real-valued phaseGap by congrArg, and applying the public packed-prefix reader resolves them.
No theorem statement, hclose premise, or machine construction was weakened. Exact source
snapshots and all raw failure logs are retained. Native03 passed; native04 seals a single
line wrap only, with an exact inverse-transform hash check retaining attempt03.

All foreign definitions are used through published equations/bounds. Only local aliases
are unfolded. Sibling helper sources are copied unchanged with SHA256 provenance and checked
independently in seq-zk-b's private olean tree. No sibling oleans, frozen files, main edits,
new Mathlib roots, Lake calls or Git commits are involved.


### Preserved implementation record: subagents/seq-zk-c/final-acceptprob-reader/README.md

# Final explicit acceptance-reader correction

Lead-owned canonical C_A found one foreign-definition access in
ContinuationProbability.acceptProb_prod: its initial acceptProb_def rewrite affected the
outer occurrence, while the RHS occurrence inside uexp was left for the final rfl to
unfold. The full old seal failure is preserved by the lead at
evidence/logs/final-seals-stream-2/final-coe-SealA_Cryptography_Composability_SequentialZK_ContinuationProbability.log,
reported line155. This was a reader-discipline failure, not a false theorem.

At the lead's request, c changed ONLY that short proof's last line. The final source uses
`simp only [acceptProb_def, Equiv.prodAssoc_symm_apply]`, reading both the RHS acceptance
formula and the product-association equation explicitly. No public statement, import,
other proof byte, frozen file or scope changed. The withV seed-reader correction remains
exactly as checked before. No seal/probe was run by c; lead reruns the affected20 cells.

Old source SHA4b7b7ad15dcd6ead93532c83dfe9e2b1f9750e2d5933ae359949bd7b4475db9a.
First reader-only trial SHA8d631348a0f8e346dcf6df132fa70df0572830978ee140ceb0e48f8a208f7e84
exposed one remaining ordinary native goal: product-association evaluation. Its complete
source/patch/roundtrip and raw native failure remain,2.69s actual runtime,
maxRSS2,238,791,680bytes. No interruption, timeout or resource exception.

Final source SHA91355ac3dff34e7b06e8684bf36b1c5fb363c7688a737f8f4efcf4f18246011d,
354lines/max94columns. Adding the published product-association reader closes the same
proof. Native retry02 passed0errors/0warnings,2.42s actual runtime,
maxRSS2,246,049,792bytes. All output/source/result evidence is preserved; final patch and
roundtrip-final.json verify exact forward/reverse git-apply bytes and that replacing only
that final line by the old rfl restores every old source byte, including all statements.

Both native attempts used seq-zk-c, the shared Lean slot wrapper, the private c olean tree,
/usr/bin/time -l and scripts/lean_check_tree.sh for this module alone. No Lake, dependent
sweep, seal, axiom probe, new definition, theorem or Mathlib root. All171 prior current
receipt files were verified unchanged. Source and this new evidence are closed for exact
copying into the lead's final revision6 matrix/payload.


### Preserved implementation record: subagents/seq-zk-a/final-review-12/REPORT.md

# Final explicit-reader scan: unresolved-name review

Reviewer: seq-zk-a. Final proof revision d842dc8f681f6b89499129f5b64a50d0e4587935.
Read-only review of scan1.py, scan2.py, review_explicit.py, and the final-repair/explicit
inputs/results. All41scanned source files independently match the committed revision byte
for byte (source-revision-verification.json). No Lean/lake command or source edit was made
by this reviewer. Python scripts write only this final-review-12 evidence directory.

## Completed outcome

The raw scan contains1245items:868native-resolved theorem uses,6same-module definition
uses,and371LOCAL_OR_UNRESOLVED items. Its zero-foreign count alone was incomplete evidence
until those371items were reviewed. Every one is now classified source-locally and the
nonlocal aliases are checked by the lead's completed secondary native probe:

| Supplement category | Items |
|---|---:|
|Named local hypothesis, case, lambda, obtained value, or let|322|
|Anonymous local have proof named this|2|
|Inline typed show equality proof term|15|
|Local equality combined by Eq.trans|1|
|Public theorem/equality/iff/contract readers through aliases|29|
|Additional same-module inherited AbortRetry definitions|2|
|Still unexplained|0|

Thus the merged interpretation is897public theorem/reader items,8same-module definition
items,and340local/inline proof items. No foreign definition-body unfolding was found. All
eight same-module definition occurrences are in declarations marked UNCHANGED by the
base/final touched map. No newly added/changed declaration unfolds a foreign definition
explicitly in this scan. The raw scan2 output is retained unchanged; this is a separately
reported supplement, not a silent rewrite of its results.

## Native alias confirmation

The lead ran `.lake/seq-zk-rule10/final-repair/explicit/ExplicitAliases`; the retained log
`evidence/logs/final-explicit/final-explicit-aliases.log` contains all24requested canonical
names,EXPLICIT_ALIAS_DONE24,and EXIT0,with zero error: or error( diagnostics.22names have
native kind theorem and type_is_Prop=true; the only two definitions are AbortRetry.attempt
and AbortRetry.retry,with the same Defs module home as their explicit uses.

The initial conservative warning that proof-valued class/spec fields might have definition
kind was a probe-design precaution, not an observed issue. The pinned native result
actually classifies every queried proof field as theorem-kind. native-supplement-validation
records these exact results and probe/log hashes.

## Why the scanner left valid names unresolved

1. Export aliases are absent from the probe's raw env.constants string map. `mul_zero` and
   `zero_mul` are exported from MulZeroClass at Mathlib/Algebra/GroupWithZero/Defs.lean:77
   (field declarations35,37). Their canonical names MulZeroClass.mul_zero and zero_mul are
   theorem-kind public equality readers in the native result. `not_not` is exported from
   Classical at Mathlib/Logic/Basic.lean:188; Init/Classical.lean:141 declares the theorem.
2. Receiver notation needs the local receiver type. hA.advice_eq/hS.advice_eq resolve to
   Complexity.NUPPT.Uniform.advice_eq (Randomized/PPT.lean:300). The specification methods
   h.realCoinsEquiv_fst_ofFn,d.phase_take,and d.outV_eq resolve to their published
   PaddedProverSpec/PaddedVerifierSpec theorems. The13spec-field uses are public equality
   proof projections (first,rounds_eval,next,boundary; rounds_eq,first_eq,next_eq,terminal_eq,
   period,local_length), not attempts to unfold those projections' definitions. All are
   native theorem-kind/type-is-Prop=true.
3. List.mem_singleton.mp and List.prefix_iff_eq_append.mp apply the mp direction of public
   iff theorems to local membership/prefix proofs. Canonical List lemmas and Iff.mp were
   verified natively. hpV.trans hp combines two local equality proofs using Eq.trans;
   hpV is explicitly bound by congrArg at SequentialZK.lean:669.
4. `open AbortRetry in` appears at Defs.lean:588 before the following theorem's docstring.
   scan1.py only searches tactic-local opens inside the owning declaration span, so it
   misses this legal preceding local open. At636,648,the inherited simp arguments attempt
   and retry are owned AbortRetry.attempt/retry (defined at328,346 in that same file). At642,
   firstHit_map_getD_eq is the public AbortRetry theorem declared at460. These are not
   private copies and are not foreign-definition uses.
5. The inline keyword show is not a declaration name. The15full items are13arithmetic
   equality terms proved by ring/omega and two local funext h equalities. No foreign body
   is hidden in those terms. The two local this entries come from anonymous have:= at
   Defs.lean:472 and494 before their rw uses at474 and496.

## Source-local handling of ordinary local names

For322entries the review retains the enclosing compiled declaration and direct binding
evidence (have,let,set,by_cases,intro,obtained pattern,case/lambda binder,or typed premise)
strictly before the scanned use. No blanket “starts with h” rule was used. All322had a
direct binder match under a second stricter pass. The two anonymous-have cases were
reviewed manually and explicitly overridden. The exact occurrence, full rewrite item,
source context,and local binding lines are in native-validated-review.json. The original
proposed/unlocated intermediate files remain for provenance; resolved-review and native-
validated-review explicitly resolve both initial missing binder locations.

## Tool review and requirements

scan2.py correctly keeps LOCAL_OR_UNRESOLVED separate at32–33 and reports raw foreign
items only among resolved names at37–46. It cannot itself certify zero foreign unfolding
while unknown names remain. Its equation-target handling covers generated eq_N,eq_def,
eq_unfold heads; the original explicit-items inventory remains authoritative for those
lexer records. Any native-kind continuation must preserve both diagnostic forms error:
and error( and must require successful completion/exit, as done in the root logs here.

review_explicit.py is not generic for this fill: it hard-codes hash-sign SignatureScheme
aliases,an unrelated local-head whitelist,and writes .lake/hash-sign-rule10 paths. It should
not be executed unchanged or treated as resolving the371seq-zk unknowns. The present
supplement performs the corresponding source-specific review and canonical native check,
while leaving that archived tool untouched.

This explicit scan is one part of Rule10 evidence; it does not replace strict/coe A/B
irreducibility seals or their attribution. The lead's separate native sweeps/axioms/seals
remain the authority for implicit elaboration. No source correction is requested by this
review. All files produced here are indexed by receipt.tsv and lie outside the historical
frozen CP3 and post-CP3 audit receipts.
