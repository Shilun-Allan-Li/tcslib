# Gate106 round3 — shared Segment and polynomial-time contracts

**DRAFT: validation is running; not issued. Not yet clear to merge: #215.**
Seyoon selected Codex. This round audits PR215, branch lean/dedup-sg1 against
complexity/arora-barak-ch3-4. Current head **d0c4a292e781b55617e05b33fdd423bb059fd735** contains the user-merged
#230 APIs; current campaign proof base **3023dc1408c3d216fc07a7cbba9ae30135b861ed**. The records pin, immutable exchange
commit/path, bundle SHA256 and exact section count belong in the finalized bundle prologue
and dispatch prompt. No value is inferred from a moving checkout.

## Previous findings and the actual revision

Verbatim findings-r2.md reports HOLD0blockers/1major/0minors/15notes, SHA256
5a8031c24faace90a0e4d5b1bc11cc0414057e21a016712485473ccdbde25d28.
Original findings.md, pack.md/pack-r2.md, dispatched prompts and bundles remain immutable.
Read resolutions.md, resolutions-r2.md and errata-r1.md. Earlier findings/probes/records
are data; this current scope and its frozen source govern the requested audit.

Round2 accepted F1's two Segment-based cut repairs and F3's six-consumer/twelve-call
SingleTape accounting. F2 requires generic polynomial-closure reconstructions to consume
published contracts; those were outside the six acknowledged adapter/dispatcher kinds.
This revision fixes16 private SAT/Hardness implementations at **6d3903f7ba3dbdee3ad233c8d908427f3324be2f** and integrates
the current campaign. Seyoon separately accepted the seventh unary-clock-host retention
kind below; no additional API is proposed. Seyoon approved
the single new Hardness import TCSlib.Complexity.ClassNP.PolyTimePrefix.

The PR still changes five Lean files: ClassNP/Tautology, Build/CounterLoop,
Robustness/SingleTape, ClassNP/SAT and CookLevin/Hardness. The first three retain their
original SG1 proof/source scope; SAT/Hardness additionally retain the two round1 cut repairs
and add the16 current private proof re-points. The original two Build.Contract.Basic
imports in Tautology/SingleTape were separately approved earlier. Public names/types,
visibility, executable definitions/tables and unrelated old proof bodies remain frozen.
The three original removed private concatenation names have their approved private bridges;
no new public declaration is introduced.

## Sixteen exact proof repairs

| Owner | Private declaration | Existing published interface |
| --- | --- | --- |
| SAT | sat_pt_pair_input | PolyTimeComputable.pairEncode with polyTimeComputable_id |
| SAT | sat_pt_mapSnd | pairMapSnd.eq_1, function equality, PolyTimeComputable.pairMapSnd |
| SAT | sat_pt_pair | PolyTimeComputable.pairEncode |
| SAT | sat_pt_append | PolyTimeComputable.append |
| SAT | sat_pt_unaryLength | polyTimeComputable_unary |
| Hardness | clNative_linear | polyTimeComputable_of_linear |
| Hardness | clNative_map | pairMapSnd.eq_1, function equality, PolyTimeComputable.pairMapSnd |
| Hardness | clNative_pair | PolyTimeComputable.pairEncode |
| Hardness | clNative_append | PolyTimeComputable.append |
| Hardness | clNative_unary | polyTimeComputable_polyUnary |
| Hardness | clA5_pt_const | polyTimeComputable_const |
| Hardness | clA5_pt_cond | polyTimeComputable_ite |
| Hardness | clA5_pt_and | polyTimeComputable_and |
| Hardness | clA5Pair_sizes | Encoding's eq_pairEncode_of_pairDecode and length_pairEncode |
| Hardness | clA5Le_native | polyTimeComputable_lenLe after reversed unary pairing |
| Hardness | clA5Drop_native | polyTimeComputable_dropPrefixByLength and PrefixByLength.drop.eq_1 |

All16 old private headers/names/order remain literal; obsolete adjacent proof descriptions
are updated to the actual public route. Exact reverse-replacement receipts recover the
entire prior source in each generation. Mapping must include the malformed-pair branch,
not merely valid encoded inputs. pairMapSnd.eq_1 and PrefixByLength.drop.eq_1 are actual
serialized public equations already present before lookup/proof use, with empty axiom
sets. No hypothetical reader or reserved eq_def elaboration alias is used.

## Audit questions

Apply policy.md, workflow.md, maintainer/WORKFLOW.md, TEMPLATE.md and the canonical ledger.
Review definitions, literal contracts, semantic reuse, inline proof fragments, cumulative
material duplication and evidence accuracy. Existing kernel proofs need no tactic-style
rewrite. A gate closes only at zero blockers/majors with minors dispositioned; Seyoon alone
merges after a current replay. This packet does not itself close the gate.

1. Reconfirm original SG1: the strict Tautology live-anchor cut, CounterLoop's joint forbidden
state/head relation and SingleTape's closed head interval. Restate Segment and its fields
before docstrings; check their zero/one/concatenation/monotonicity uses and unchanged public
CounterLoop contracts. Original pack/evidence and their source-specific seals remain supplied.
Check the exact current byte identity before adopting any older bounded execution.

2. Recheck both SAT/Hardness cut helpers using Segment.trans and segment_iff. Singleton
forbidden anchor and True head predicate must recover the literal earlier-time cut at a+b.
Include zero durations, an early anchor, coincident start/anchor and a run halted before the
bound. Distinguish impossible hypotheses from proved conclusions. The strong guard checks
seal both ordinary reached definitions before headers, with default model simps removed;
paired positive/negative identities are checked. No global seal of unchanged legacy code
is inferred from these two sections.

3. Audit every16-site re-point above, including inline facts. Restate polynomial-time
computability, total pair decoder/default behavior, unary/conditional/comparison/prefix
semantics and the work-tape/input/output conventions from source first. Inspect each
published interface's exact type and premises. Pairing must preserve the original input;
malformed maps return []; prefix removal is by the length of u(x), not its numeric binary
value; the unary comparison pairs g before f. Field bounds must cover malformed inputs.
Try at least four adversaries: empty words/zero lengths, malformed pairs, equal/reversed
unary lengths, and dropping past the end. No machine or public statement changes are licensed.

4. Challenge rule10 from actual source, not only rfl controls. Actual new sections are
sealed before complete doc/header/body. Original13 use18ordinary guards/36fresh controls;
field-size/comparison use20/40; prefix uses21/42 in its expanded import context. Model
Action.apply/Cfg.init/initCfg default simps are disabled. All intended identities pass
unsealed and fail sealed, exact multiplicities checked with corruptions rejected. Inspect
explicit simp/rw/unfold/change arguments and distinguish unchanged same-home field reads
from foreign ordinary definitions. Core/Mathlib named definitions cannot be passed as
rewrite/unfold arguments; public equations/local equalities are legitimate. Abbreviations
and projections retain the documented standard irreducibility exclusions, not an unsafe
reducibility override. Direct new-proof citations are public except same-home private
headers/matchers. No imported theorem implementation is recursively claimed re-audited.

5. Verify source and compiler accounting independently. Current nine-owner source census is
1986declarations=349public+1637private on both sides. The five-file source freeze covers
all public headers/visibility and executable chunks, plus the authorized private bridge
replacements/imports. Baseline complete compiler census is7101constants=5750private+
1351nonprivate; ALLAX/PUBLICAX cover exactly those names. Baseline selected16old roots+
25descendants use standard axioms; nine inherited Primitives constants have sorryAx.
PENDING:final current compiled comparison after the329-module replay. Do not substitute
older MSG4's7063/1349 results for current post-230 totals, or source counts for compiler
counts. Count generated/internal/private constants and classify changes by kind/owner;
verify no formerly proved constant becomes sorry-dependent.

6. Reconcile semantic debt by kind, not raw screen edges. The14 closure/comparison repairs
replace reimplementations of10 distinct public PolyTimePairing statements out26 source
declarations (at least38.5%, a pre-repair source-inclusive review item). Decoder/length and
prefix removal are the other two repairs. Their implementations retire only when #215
merges; private names remain forwarding adapters. They are not retained acknowledged
closure debt. Earlier retained named SAT34/270 and Hardness32/544 lower bounds did not
include this general family; do not subtract16 from them. The inspected fixed-bit
clFillTM/clFill_run/clNative_fill trio matches the already accepted Unit-state constant
emission instance, bringing the Hardness named lower bound to35/544 once. These are bounded
named unions, not exhaustive cleared censuses.

7. Preserve the exact six existing human acknowledgments across TCSlib: clean-module
contracts/install-emit-stop lifting; positive-release stop adapters; bank-padding adapters;
finite one-way transducers with next/emit/finish/start; the specified polynomial bridge
bound; and separately finite-family shared-bank dispatch hosts with their companion proofs.
Concrete routing tables are data. Cleanup owner/window is the maintainer, next12.2c
SAT/Hardness consolidation after activeMIG1 and before further fills in those files. No new
API is granted. The older clPlacement schedule, broaderRO1, live-prefix watches, fixed-word
PL1 and statement-specific items keep their distinct statuses. Correct the SingleTape
accounting only as six declarations/twelve calls, never seven consumers.

8. Verify the separately accepted unary-clock-host retention ruling. Its14Hardness members
are12clRepeat* declarations plus clA5Iter_native/clA5Iter_shrinking, disjoint from the prior35
named members;49/544 is the affected-declaration lower bound, not49confirmedduplicates.
The exact by-kind scope covers existing arbitrary positive clean-call unary repetition,
frame/call/run/clock/output/budget and actual-orbit polynomial wrappers anywhere in TCSlib.
Owner/window remains maintainer,next12.2c after activeMIG1 before further SAT/Hardnessfills;
shared-host design/gating/resource contract and replacement are scheduled there. No future
private host, new API/import or route is licensed. The pre-ruling independent report remains
historical; RULING.md/ruling.json contain the actual user answer.

Evaluate the remaining source comparisons honestly. clNative_image has correctness only
on f's image; published PolyTimeComputable.comp assumes a total polynomial-time second
function. Composition's on-image operational APIs are relevant and already consumed; no
exact class-level replacement or unavoidable new API is proved in the bounded assessment.
clA5Iter_native/clRepeatTM assumes an actual-orbit envelope for computed N(x); Loop,
PolyTimeBlockLoop and BinaryArith/Iterate have actual explicit premises to compare, not
licenses to infer all-word or fixed-monomial bounds from that hypothesis. The unary-clock host's acknowledgment comes from the explicit seventh ruling, not the
prior dispatcher/transducer kinds. Generic image closure remains a separate comparison. Full current source for those homes is supplied and included in the final
25-file screen. The same comparison also includes length_pair_components_le in
PolyTimeBlockLoop, a stronger published bound than clA5Pair_sizes; the current repaired
body instead uses Encoding's inverse/length facts under the current approved import set.
No claim that no published component bound exists is made; any new import still needs
a separate ruling and opaque-consumer pre-ship. Require an exact type/premise mapping for any further mechanical re-point;
otherwise report a precise residual, not a blanket clearance. No route/host/API redesign or
new debt acceptance is delegated to the auditor.

9. Verify the full current25-file source-inclusive baseline/head screen, every candidate and
cumulative canonical/receiving-file accounting. PENDING:final25metrics/dispositions.
The older9 population and completed21 generation remain historical evidence with their
actual pins; they do not substitute for25. Population expansion is separate from new head
copies. Literal declaration shortening below the60-character cutoff is not deletion of a
compiler declaration or automatic proof of debt retirement. A few CounterProg raw chunks
include trailing omit directives belonging to the next declaration; retain raw scores and
classify their actual source meaning. Inspect live-prefix/input-bound/first-halt matches
against their exact prior watch/harvest records rather than calling every baseline pair
acknowledged. No whole-library semantic absence claim is made.

10. Verify replay/source/driver fidelity. PENDING:fresh current329-module msg5 from a complete
mac4 copy at the exact current head. Current isolated launcher pins Lean4.25 -j4, nice10 and
one outer slot lock; local3 under machine5. Actual command log proves the flag for each
module. A generated API replay in a different PR was deliberately stopped after272 good
rows on discovering the template's omitted-j4 flag; that correction is recorded separately
and is not claimed as a passed run. MSG5 uses the corrected launcher from its start. Source
and snapshot checks forbid splicing; completed pipeline/static receipts must support any
final claim. Records-only later campaign commits do not alter the current proof base.

## Executions, failures and supplied evidence

- round3-closure-repairs, round3-extra-repairs and round3-prefix-repair retain all actual
full native/scoped seals, exact guards, controls, statements, raw logs, changes and manifests.
Their generation-specific limits remain explicit: initial metadata lookup failure; two
unused simp arguments removed; final full Hardness subsequently rerun; exact import closure.
- round3-integrated records actual SAT→Hardness compilation in one complete MSG4 overlay,
16new roots+7generated descendants standardAX, complete old-context9-owner census/ALLAX,
895snapshot entries unchanged and only the two overlay outputs changed. This is pre-230
dependency context, not current mac4 metadata or the fresh merged-tree replay.
- round3-current-compiled supplies the current mac4 BASE and, when finalized, completed
MSG5 HEAD census/type/CI/effective-attribute/ALLAX comparison, with every raw byte losslessly
encoded as UTF8. Full theorem values are not part of this metadata claim; executable source
chunks are separately frozen. Failed/incomplete instrumentation attempts, diagnostic samples
and corrected staged methods remain, never described as library proof failures or passes.
- round3-current-source-screen holds completed historical21 inputs/output/classifications;
round3-current-source-screen25 holds the independently captured final25 full source union,
canonical tool, lints/source/index/pair results and source-equivalence receipts. No cap,
subsample, source substitution or raw-score repair is permitted.
- evidence/current-replay-r3 supplies the actual generated/prechecked driver, corrected
isolated launcher/shim, full329order/log/static outputs, source pins and completed receipt.
- Original round1/round2 evidence/findings/receipts remain with their original source pins;
resolutions answer every finding. No historical text is retroactively rewritten.

For binary archives/raw logs, the packet includes complete reversible UTF8 encodings and
byte/hash receipts; decode as untrusted data using a trusted standard-library reader. Review
supplied scripts before executing them. If independent native checking is unavailable,
state NOT RUN; distinguish your execution from reviewed maintainer evidence. Use only the
managed wrappers/prescribed locked pipeline, pinned4.25, one Lean process/four threads/nice10
and python3 -I; never lake build/bare Lean or a partial/spliced dependency tree.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
| --- | --- | --- | --- | --- | --- |

Return definition restatements, adversarial analysis, explicit F1/F2/F3 dispositions and a
verdict with blocker/major/minor/note counts. Identify exact source/premise mappings for
additional duplication findings. Gate closure requires zero blockers/majors and minor
dispositions, plus a current replay before Seyoon merges; this packet is not a merge order.

**Deliver your findings as a downloadable file named `sg1-dedup-r3-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in your reply.
