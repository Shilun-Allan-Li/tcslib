"""Write the final authoritative report, retaining complete historical overlap appendices."""
from pathlib import Path
import json
E=Path('evidence');S=json.loads((E/'logs/final-rule10-summary.json').read_text());assert S['completed']==164 and not S['pending']
A=json.loads((E/'logs/final-static-audit.json').read_text());assert A['files']==41
text='''# seq-zk final delivery

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
'''
text+='\n## Exact final source inventory\n\n| Source | Lines | Max width |\n|---|---:|---:|\n'
for r in json.loads((E/'final-source-inventory.json').read_text()):text+=f"| `{r['path']}` | {r['lines']} | {r['max_width']} |\n"
text+='\n## Historical per-declaration overlap and implementation appendices\n\n'
old=(E/'CHECKPOINT3-doc-REPORT.md').read_text();text+='### Checkpoint3 overlap compendium (historical cutoff)\n\n'+old[old.index('## Overlap and reuse'):]
for rel in ['subagents/seq-zk-a/report.md','subagents/seq-zk-c/computational-hybrid-record.md','subagents/seq-zk-b/computational-reduction-overlap.md','subagents/seq-zk-b/reduction-advantage-overlap.md','subagents/seq-zk-b/computational-phase-bound-overlap.md','subagents/seq-zk-c/final-acceptprob-reader/README.md','subagents/seq-zk-a/final-review-12/REPORT.md']:
 text+='\n\n### Preserved implementation record: '+rel+'\n\n'+(E/rel).read_text()
(E/'CHECKPOINTfinal-repair-REPORT.md').write_text(text)
print('Final report written:',len(text.encode()),'bytes')
