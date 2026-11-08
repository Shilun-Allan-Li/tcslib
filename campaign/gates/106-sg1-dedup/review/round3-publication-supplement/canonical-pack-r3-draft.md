# Gate106 round3 — shared Segment and polynomial-time contracts

**Not yet clear to merge: #215 — external round3 remains open.**
Seyoon selected Codex for this round. This packet audits PR215, branch lean/dedup-sg1
against complexity/arora-barak-ch3-4. Final head **79e7c63a6bfa5f002663924f5c7d4e72db705026** contains the user-merged
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
the current campaign. The later approved pair-bound repoint at63 uses the public
Complexity.length_pair_components_le (home ClassNP/PolyTimeBlockLoop); final79 additionally repoints Tautology's
raw on-image composition directly to FinTM.exists_comp_on_image. Seyoon separately accepted
the seventh unary-clock-host retention kind below, and subsequently FE-LIVE-1 as a distinct
scheduled kind. No new public API is proposed in this PR. Seyoon approved the two precise
Hardness imports TCSlib.Complexity.ClassNP.PolyTimePrefix and
TCSlib.Complexity.ClassNP.PolyTimeBlockLoop, each with its mechanical consumer scope.

The PR still changes five Lean files: ClassNP/Tautology, Build/CounterLoop,
Robustness/SingleTape, ClassNP/SAT and CookLevin/Hardness. The original SG1 changes in the first three remain; SAT/Hardness additionally retain
the two round1 cut repairs
and add the16 current private closure/encoding re-points. Tautology's final79 raw on-image
adapter is the additional seventeenth distinct repaired proof in this round. The original two Build.Contract.Basic
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
| Hardness | clA5Pair_sizes | Complexity.length_pair_components_le (home ClassNP/PolyTimeBlockLoop), eq_pairEncode_of_pairDecode and public pair projection equations |
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

The final additional raw image-composition repair preserves the complete private
`taut_comp_on_image` header and exact2*T1+T2+2 budget, replacing its reconstruction with
`exact FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU`. SAT's matching raw adapter already
used that public theorem. This requires no new import, API, machine, statement or debt ruling.
The bounded five-touched-file sweep retains all15 candidates/inline closings and distinguishes
Hardness's class-level image wrapper from these exact raw contracts.

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
field-size/comparison use20/40; prefix uses21/42 in its expanded import context. The final actual Hardness all11-section
seal uses21guards/42fresh controls in the approved two-import context. The additional
Tautology actual section uses14guards/28fresh controls in complete MSG6 context. Model
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
replacements/imports. Complete current native compiler comparison is7101→7063constants:
5750→5712private and1351→1351nonprivate. All1351nonprivate names/full raw types/kinds/owners/
privacy/internal flags/structural CI/reflected attributes/AX sets are exact. All168 effective
owned simp rules are exact. ALLAX covers every owned constant; PUBLICAX exactly the
nonprivate subset. The +6/-44 delta is entirely private:3authored replacement pairs,
+3/-41generated auxiliaries. Ten common raw-type changes are private generated auxiliaries;
the only shared AX change drops Classical.choice from clA5Pair_sizes. All43 conservative
changed/replacement source proof roots(38private/5public) plus93descendants,136distinct
constants, have standard AX. The old native16-root markers(25BASE/7HEAD descendants) remain
literal history/subset, not the full current repair scope. Nine inherited Primitives
sorry-dependent constants remain exact; no formerly proved constant acquired sorryAx or
another nonstandard axiom. Do not substitute pre-#230 MSG4's7063/1349 counts, oldD0's7065/
1351, or source declarations for this actual final79 census.

6. Reconcile semantic debt by kind, not raw screen edges. The14 closure/comparison repairs
replace reimplementations of10 distinct public PolyTimePairing statements out26 source
declarations (at least38.5%, a pre-repair source-inclusive review item). The final joint decoded-component bound and
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
25-file screen. The final clA5Pair_sizes body NOW consumes length_pair_components_le in
PolyTimeBlockLoop through Encoding's public inverse and pair projections, including the
malformed decoder branch. Seyoon explicitly approved this single BlockLoop import and its
exact consumer; the passed actual full-Hardness seal/control checkpoint supersedes the
older inverse/length-only implementation without relabeling its historical results. Require an exact type/premise mapping for any further mechanical re-point;
otherwise report a precise residual, not a blanket clearance. No route/host/API redesign or
new debt acceptance is delegated to the auditor.

Separately verify **FE-LIVE-1**, accepted by Seyoon2026-11-08UTC, without adding it to the
seven SG1 kinds. It covers EXISTING whole-configuration fixed LIVE-stop first-entry proofs,
including singleton/predicate, positive-time initial-exclusion and inline specializations;
comparison includes BOTH completed verdicts. It excludes None-halt selection, nonabsorbing
visits, state-only absorption and future-copy permission. Owner: maintainer(Codex). Keep
staged MIG conversions in#233 before gate118; remaining instances in next12.2c after active
MIG1 and before further SAT/Hardness fills. Exact ruling-live-stop.json is supplied.

**Clear to merge: #234 — gate119 CLOSED PASS0/0/0/17; Seyoon has not merged it.**
The canonical proposed exists_first_entry_of_fixed remains on UNMERGED prerequisite#234,
source f1ca767a10551960faf36ad9c8ff17bea3a2d88c. It is not present or used in this SG1 source,
and this PR gains no dependency on it. Current closure/status/findings/dispositions and
complete closure/return-review context are supplied as records, not a new SG1 native run
or an instruction to re-audit API119. Closure does not retire FE-LIVE-1 implementation debt.
The five current Hardness members are clFirst, clBank_first, clCopy_first, clRow_first and
clCmp_first. Each actual doc-inclusive proof chunk is unchanged versus3023 and inspected
against whole-configuration fixedness, endpoint and cut. They are name-disjoint from the
prior49named affected declarations: the checked set union is54/544(9.93%), not54confirmed
copies or five new screen edges. family-accounting.json preserves both complete sets,
empty intersection, literal current hashes and semantic mappings; no watch or separate
residual is upgraded by adding these names. This remains a named lower bound across
separately dispositioned records, not a globally cleared or exhaustive copied-material census. The live ruling does not dispose
of first-None proofs or the separate generic image-closure comparison.

9. Verify the full current25-file source-inclusive baseline/head screen, every candidate and
cumulative canonical/receiving-file accounting. Actual identical BASE is adopted after exact
source/tool/population/archive/raw-receipt checks; HEAD79 is a fresh completed1110.269s run.
Eligible canonical source spans1956→1947; directed candidates2013→1995; reproduced normalized
characters646340→645729. All35delta rows are dispositioned:2new/20gone/13changed. Against
historical63 exactly4directed Tautology image spans disappear, arising from ONE replaced
implementation with its short private adapter retained; every other row/score is identical.
The two BASE-new rows are shared lenLe application/refolding89/167 and the old SingleTape
growth-phase scaffold784/1564; neither is automatic new-debt clearance. All259 term candidates
and435eligible term spans are unchanged. Full25 CLI lints retain style153→153 and campaign
0FAIL/28WARN/28INFO→same; style exit1 is inherited, not a clean lint claim.
The older9 population and completed21 generation remain historical evidence with their
actual pins; they do not substitute for25. Population expansion is separate from new head
copies. Literal declaration shortening below the60-character cutoff is not deletion of a
compiler declaration or automatic proof of debt retirement. The unmodified raw parser can include result-type suffixes after type-let initializers
and following scope/omit directives in legacy spans; retain every raw score and inspect the
actual source. These are normalized source-span characters, not necessarily pure proof
characters. A separate complete header checker handles nested defaults and top-level result-
type let assignments; no raw score is repaired or silently redefined. Inspect live-prefix/input-bound/first-halt matches
against their exact prior watch/harvest records rather than calling every baseline pair
acknowledged. No whole-library semantic absence claim is made.

10. Verify replay/source/driver fidelity as the actual complete-snapshot chain, not one
fictional final329-module run. MSG5passed329modules/0failures/static0 atD0 from a complete
MAC4 copy, retaining66inherited admissions; MSG6passed26Hardness-downstream modules/static0
at63 from a WHOLE MSG5 clone; MSG7passed2Tautology-downstream modules/static0 atfinal79 from
a WHOLE MSG6 clone. MSG6/7scopes contain0admissions; the campaign is not admission-free.
Full driver/orders/rawlogs/static/launch trace/source receipts support each exact generation.
Only the source-specific changed tails were rerun; no snapshots are composed or spliced. The actual source-pinned branch helper is archived honestly without an explicit-j4;
the isolated pinned4.25 PATH shim enforces-j4 on every effective invocation, with nice10
and one outer slot lock; local3 under machine5. The permanent campaign-helper flag fix
is separate and is never relabeled as the branch helper used in these executions. Actual command log proves the flag for each
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
Full-source SAT83/Hardness66 inherited warnings remain in raw logs; the repaired sections add
none. Zero-warning metadata probes do not imply globally warning-free source modules.
- round3-integrated records actual SAT→Hardness compilation in one complete MSG4 overlay,
16new roots+7generated descendants standardAX, complete old-context9-owner census/ALLAX,
895snapshot entries unchanged and only the two overlay outputs changed. This is pre-230
dependency context, not current mac4 metadata or the fresh merged-tree replay.
- round3-final-compiled supplies the actual final79 unfiltered census/full types/structural
CI/reflected attributes/effective simp rules/ALLAX/PUBLICAX and all43roots+93descendants.
Fresh HEAD stages pass124.07/26.46/14.62s,0errors/0warnings. The frozen MAC4 BASE is adopted
only after all71BASE/all94historical final payloads, exact probes/population/source and nine
originally fingerprinted owner oleans verify; independent reparse reproduces BASE maps exactly.
Every raw byte is lossless UTF8 gzip/Base64. No theorem proof-value equivalence is claimed.
Original round3-current-compiled D0 results and failed/stopped instrumentation stay historical;
BASE did not fingerprint every transitive binary or the Lean executable separately, so no
stronger historical attestation is invented. Current tools/artifacts are fingerprinted.
- round3-current-source-screen25-final79 is the primary CURRENT full25 source/lint/screen:
all50source inputs and archives, actual adopted BASE receipts, fresh HEAD raw output,
complete indexes/candidates,35delta dispositions, source/header/term/attribute checks,
canonical pairdiff vsBASE and63, and the15-block on-image sweep. Entire folder is supplied.
The historical21, D0full25 and63full25 generations remain separately pinned. The final
freeze/checker reads the whole historical63 and originalD0full25 folders; both complete
dependencies are supplied, without folder caps or source substitution.
- evidence/current-replay-r3, evidence/final-replay-msg6 and evidence/final-replay-msg7
supply the actual three-generation replay chain, prechecks/drivers/enforcing launchers,
complete orders/logs/static outputs and source pins. Each individual launch is attested-j4;
root-replay-lineage-pins.json rehashes the root-owned completed evidence, not a child replay.
- round3-pair-bound-applied supplies the actual final approved11-Hardness-section proof
seal/control/native checkpoint; round3-image-repoint supplies exact before/after/header,
14-definition actual-section guard,28fresh controls, metadata and all raw failures/limits.
- Original round1/round2 evidence/findings/receipts remain with their original source pins;
resolutions answer every finding. No historical text is retroactively rewritten.

All current source claims refer to immutable final79 `.lean.txt` captures in the current
full25 evidence, not the moving campaign root paths. Root-path Lean sections inherited from
prior packets are baseline/context sources; each historical generation retains its own pins.
The publication input draft retains EVERY original1539 candidate section, all40→31 lossless
aliases and all50 current plaintext source captures, and adds the complete frozen independent
peer review plus review/round3-publication-supplement/. Its exact expanded count belongs in
the finalized prologue. The canonical pack is the leading additional section; the original
candidate pack/list/receipts stay historical sections. The missing replay-generator dependency
devtools/seyoon/graph.py is supplied byte-exact, also as inert graph.py.txt in the supplement,
with source/blob/SHA256 and actual-generation-copy provenance; graph imports only os/sys.
This resolves peer PQ1 in the publication draft without altering any frozen packet/review.
The fresh external-input inventory and context-rebinding receipt distinguish current mutable
status records from older capture pins. Root still binds final adopted bytes at the final
records commit. All cited standards, originalR1/R2 findings/dispositions, complete historical
source populations, raw controls/failures, compiled encodings and decision evidence remain.
No folder listing is capped. Peer review is packet QA, not the external gate verdict.
Large metadata/archive/log sections may be represented by deterministic gzip/Base64 UTF8
substitutions: encoding-receipt.json maps EVERY original path to full raw/gzip/encoded sizes
and SHA256 with trusted roundtrip verification. Original record files remain intact. Decode
these payloads solely as untrusted data; no supplied runner need be executed for inspection.

For binary archives/raw logs, the packet includes complete reversible UTF8 encodings and
byte/hash receipts; decode as untrusted data using a trusted standard-library reader. Review
supplied scripts before executing them. If independent native checking is unavailable,
state NOT RUN; distinguish your execution from reviewed maintainer evidence. Use only the
managed wrappers/prescribed locked pipeline, pinned4.25, one Lean process/four threads/nice10
and python3 -I; never lake build/bare Lean or a partial/spliced dependency tree.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
| --- | --- | --- | --- | --- | --- |

Put definition restatements, adversarial analysis, execution/provenance limits and explicit
F1/F2/F3 dispositions in findings or note rows, followed by the verdict with
blocker/major/minor/note counts. Identify exact source/premise mappings for
additional duplication findings. Gate closure requires zero blockers/majors and minor
dispositions, plus a current replay before Seyoon merges; this packet is not a merge order.

**Deliver your findings as a downloadable file named `sg1-dedup-r3-findings.md`** (the findings
table and the verdict line, no other wrapping), and also paste its content in your reply.
