# Gate122: first-halt readers and mandatory backwards-live companions

**Prepared for Codex audit. Not yet clear to merge: #242 — external audit pending.**
Seyoon alone dispatches, rules on design/debt and merges; no audit is dispatched here.
PR https://github.com/Shilun-Allan-Li/tcslib/pull/242; branch `codex/ab34-first-halt-reuse`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8; audited HEAD `f3c8c050ef98375bc237c72bde74f83d33833374`.
Final records/exchange pins and bundle SHA/section count are supplied by the published
exchange README and complete issued prompt. Frozen private preparation wording is
historical data; this pack and STATUS.md give the current remit.

## Source scope

The primary tranche re-points ten existing deterministic first-None selectors to the unchanged public `Turing.MultiTapeTM.exists_first_halt`. Caller-specific output, positive-time, unary-length, space-count and capture packaging stays under exactly the same complete literal headers. Three of those complete proofs also replace inherited foreign definition reads with existing published readers.

Review of the same touched owners exposed three older reproofs of generic backwards liveness. WORKFLOW3 requires mechanical older reproofs found while landing to go in the same PR. The companions `timedCut_live_before`, `timedPrefix_live` and `universal_live_before` now specialize the unchanged public `MultiTapeTM.runFrom_state_ne_none_of_le`; the fixed-prefix proof supplies its live endpoint with the existing `timedPrefix_penultimate` and discharges its original strict-to-predecessor natural bound with omega. This is disclosed as a separate mandatory companion kind, not silently folded into the first-None count. No new theorem, statement, name, privacy, import, definition, public API, home, route, admission or mathematical fill.

| ID | Complete target | Owner | HEAD line | Guard heads |
|---|---|---|---:|---:|
| 9 | `enumCont_first_halt` | `TCSlib/Complexity/ClassNP/EXP.lean` | 812 | 1 |
| 16 | `b2_unary_first` | `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 1428 | 3 |
| 17 | `b2_verify_timed` | `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 2077 | 13 |
| 18 | `sat_first_halt` | `TCSlib/Complexity/ClassNP/SAT.lean` | 685 | 3 |
| 19 | `sat_call_first_halt` | `TCSlib/Complexity/ClassNP/SAT.lean` | 3748 | 1 |
| 33 | `clA5_call_first_halt` | `TCSlib/Complexity/CookLevin/Hardness.lean` | 6117 | 1 |
| 47 | `ComputesInTime.of_spaceUsed_le` | `TCSlib/Complexity/SpaceComplexity/ConfigCount.lean` | 362 | 6 |
| 54 | `clockTM_setup` | `TCSlib/Complexity/TimeHierarchy/ClockMachine.lean` | 509 | 7 |
| BLIVE1 | `timedCut_live_before` | `TCSlib/Complexity/TuringMachine/Universal.lean` | 1731 | 2 |
| BLIVE2 | `timedPrefix_live` | `TCSlib/Complexity/TuringMachine/Universal.lean` | 2227 | 3 |
| BLIVE3 | `universal_live_before` | `TCSlib/Complexity/TuringMachine/UniversalStartup.lean` | 232 | 1 |
| 85 | `timedCapture_start` | `TCSlib/Complexity/TuringMachine/Universal.lean` | 2508 | 9 |
| 86 | `universalCapture_start` | `TCSlib/Complexity/TuringMachine/UniversalStartup.lean` | 588 | 7 |

The whole named proof is in scope, including all preceding source context. `exists_first_halt` supplies an earliest halted configuration at time no later than the bound, every earlier time non-halted, and equality of the entire earliest configuration with the supplied halted endpoint. Live-start wrappers prove positive time using the published zero-step reader. Nondeterminism's selected roots apply that contract to an inner deterministic finite machine; nondeterministic and mixed-stop selectors are not converted to this family.

The backwards-live contract propagates state≠none at time t to every s≤t. It needs no positive-time premise. The fixed prefix uses the already-proved live point at `4 * bs.length + 2 * α.length + 5`, with the original `s < ... + 6` hypothesis. The complete old/new source chunks, literal headers and parameter orientation are provided.

Reader repairs retained from FH10:17 uses VirtualTag_iff/initCfg_eq/Cfg.init_inputPos;47 uses spaceUsedByTape_eq_card/mem_visitedByTapeHead_iff;54 uses existing initCfg/Cfg.init field readers, Cfg.ext and own ctrCfg/local start. ClockMachine is a mechanical colleague-file edit. A draft FYI for Seyoon is below; this agent sent no message and used no @mention.

## Preserved holds and bounded sweep

The original 17 first-halt proposals remain fully dispositioned. Ten were adopted; seven targets were restored in six complete owner files to exact BASE. Full original source, failed probes, old17/710 history and the17-plus-canonical bounded census remain supplied under the historical packet. No old proof is exempt, no new retention/debt waiver is invented, and no global family retirement or exhaustive absence is claimed.

| ID | Held target | Concrete unresolved boundary |
|---|---|---|
|50|Machines.Call.call_run|Opaque SimRel introduction/HaltRel elimination and explicit foreign definition reads.|
|51|Machines.Clean.cleanTM_run|ccfg state/output fields, opaque PB predicate and explicit foreign reads.|
|52|Machines.MARMTime.runFrom_count_eq|Guard compiles, but explicit visitedByTapeHead/core definition arguments fail the independent source boundary review.|
|58|NDClockHostRun.startup|Explicit bootCfg unfolding and final hostCfg/runCfg definitional equality.|
|82|ObliviousCandidate.clockStageCfg_captures|Literal raw/bundled configuration header requires obliviousSchedule reduction before the body; transport/header/home decision paused.|
|83|SingleTape.one_work_tape|Opaque computation predicates; possible existing iff readers identified but the whole sweep-field route is uncertified.|
|84|SingleTape.dg_all_inputs|Computation predicates, sweep-field reads, visited membership and space-used conversion remain uncertified.|

For the mandatory backwards-live companions, candidate enumeration plus inspection covers the eight actual FH owners at e0b, then the exact three-body transform to current f3c8. All 39 complete live-form/inline-containing chunks, 380 raw closing-form hits and two additional mixed-stop decomposition exclusions are supplied uncapped. Closing forms include add/decomposition/post-halt contradictions, state/Halted/isSome predicates, change/show/simp/rw/unfold/delta/dsimp, induction/contraposition and exact-only readers. Only the original three matched the generic backwards-live reproof kind in this bounded inspection. SAT/Hardness already use the public reader; replay/no-record/universal-prefix consumers already use the local wrappers. Other candidates consume supplied full-prefix liveness, first-halt cuts, one-step simulation or forward post-halt/resource facts. The two live-anchor some-qa absorption/transfer exclusions have a different contract. No wider unchanged44-context-owner sweep or global absence is claimed. Original inline enumeration commands were not retained; the saved finishing script source-verifies every preserved chunk and raw hit without inventing that provenance.

## Source, selected metadata and complete-proof boundaries

Actual current source QA checks all 1003 tracked Lean blobs: exactly eight owner files differ from BASE and exactly the two expected owners differ from historical e0b. All eight complete HEAD owners match the passed private candidate bytes. Actual canonical declfreeze runs and independent complete-chunk comparison find exactly thirteen changed declarations; every other declaration chunk is literal-exact. All thirteen complete literal headers match BASE/HEAD. Source census remains106 public and1288 private, with no names added/removed. These are source declarations, not compiled auxiliary counts.

For the two modified owners, both complete plain sources actually elaborate on a whole copy of the passed FH10 tree, with 0 errors / 0 admission warnings. Fresh metadata compares the selected new3 and existing timedCapture_start/universalCapture_start: all five full raw type Expr strings, universe lists and AX sets equal BASE. Fresh complete-prefix guards pass for these five under the whole candidate13 imported context, at scopes2/3/1/9/7. The two unchanged capture bodies are not exempted because earlier source changed: their guards were rerun with the new preceding proofs. The eight other FH roots in six complete byte-exact e0b owners retain earlier actual metadata/full-head receipts with explicit source and historical execution bindings. No postcommit Lean rerun is claimed by this binding sheet. Current153 replay compiles the relevant current source at actual HEAD.

Footprints traverse the selected root proof/type, every reached constant's type, and own ordinary helper type/value footprints. They do not traverse imported/other-local theorem proof values or foreign definition values. Full foreign type/value Expr strings are separately collected solely to bind reused controls. Ordinary foreign TCSlib definitions are sealed; projections/kernel abbreviations are excluded from the guard count but explicit foreign/Core definition arguments remain independently reviewed. Each guard witnesses irreducibility and absence of active definition simp/unfold rows after the whole target. This is a recorded boundary, not global opacity, all-public ABI, proof-value or global AX equality.

The union is 23 ordinary heads with 46 paired controls:44 previously executed pairs for 22 heads are reused only after fresh exact full type/value Expr/universe and whole-owner object identity checks; two fresh pairEncode pairs pass native kernel checking and fail sealed rfl with exactly two expected errors. It is not 44 heads and not 46 fresh pairs. Common control options disable smart unfolding and remove Cfg.init/MultiTapeTM.initCfg definition simp rows on both sides; no transparency override. Initial inadequate positive fixtures and initial five MAC8-prefix guard attempts remain historical, separately from the five current-context guards. Root17's compiled footprint has 12 heads, while its stronger source-reader guard has 13 including Cfg.init. All three companion bodies contain no explicit simp/rw/unfold/delta definition argument.

## Actual chained current replay

Actual root-run nfh13 at f3c8 passed153/153 modules,0 failed / 0 errors. Static exits0 with 153 modules / 0 mismatches / 31 admissions. Full logs locate the 31 inherited warnings in unchanged MaxCutAlgorithm 2, UniqueGames 8, TQBF 21; their complete sources are BASE/HEAD byte-exact. This is not a zero-sorry tree claim.

The input is the whole passed e0b FH10 snapshot from the historical full222 replay, copied with cp-cR; no partial-tree composition. All895 input-before/input-after hashes equal the previous passed222 output map. Current output has895 objects, exactly two expected changed hashes, and all742 objects outside the 153-module closure unchanged. Each compile deletes its old output and records fresh output. Every 153 full log and actual source chunk is supplied; the complete1003 source/blob/SHA map is independently checked. Historical222 plus current153 are a chain, not 375 unique modules or a fresh222 run at f3c8. All helper/driver sources, prospective merge bindings, static output and full maps remain portable. No Lean job was run during completion assembly.

The execution records were not an ancestor of the source branch. The existing prospective tree object was read-checked as clean and Lean-exact to the pushed source, with records source-exact MAC8. No automatic replay validity after a later source merge is inferred.

## Actual lint and sizes

Fresh BASE/HEAD lint explicitly covers all eight changed owners at actual f3c8. Style exits1/1 with 68 findings each, all inherited identities,0 new / 0 removed;44 raw source-position/count changes are preserved. Campaign check_file uses default 8bFalse, exits0/0 with 0 FAIL / 9 WARN / 9 INFO each,0 new / 0 removed;14 raw changes remain. These inherited findings are not described as clean. Complete stdout/stderr, helper/adapter/source hashes, argv/exit receipts and every identity disposition are supplied. This is not whole-TCSlib campaign lint.

Sizes are 1,345,452→1,344,168 bytes and 25,434→25,408 splitlines across eight files. Five exceed 1000 lines at each endpoint; no 600/1000 threshold is crossed. Lint/size/sourceQA runs no Lean or screen and changes no source/Git/canonical state.

## Actual full44-file screen

Both actual root-run 44-file screens pass exit0 with unchanged source/helper hashes. BASE: 2,662 filtered bodies, 2,583 directed pairs, 540,404 reproduced characters; HEAD:2,660/2,564/538,136. BASE took 1,427.50 seconds; HEAD 1,403.77 seconds. Full outputs and all result/argv/source/tool bindings are retained. BASE output SHA256 `e9815b26862cb62d4f60262e7002d984efe710410e800a7827efbf853390c583`; HEAD `0a2fb9fe1f686d1a55dd1db896b39d8191a903b81f1e436c84c6fe268009c1cd`.

All 23 actual delta rows are source-reviewed: 0 new pairs, 19 BASE-only, 4 persistent score changes, with 18 exact raw spans and every complete changed proof. Only enumCont_first_halt and universal_live_before fall below the 60-character extraction filter; both source declarations and headers remain intact. Every changed extracted body maps to the exact thirteen targets. Filtered body counts are not source declaration/interface counts, and directed edges are not unique copies or affected-name unions.

The vanished edges reflect canonical first-halt/backwards-live reuse and the resource proof's published membership/cardinality readers. Unchanged output_prefix proves forward output monotonicity; the unchanged live-anchor selector has its separate FE-LIVE-1 schedule and is not retired by a first-None edge disappearing. The four persistent rows disclose two directions of identical short positive-time caller packaging (330 to 206 characters, 100%) and two directions of capture assembly (434 to 299 matched characters, 85% to 78%). No zero-duplication, full family retirement, new waiver or shared-API/home design is inferred.

Population 44 is exactly historical 43 plus Encoding.lean, pairEncode's foreign home. Full 88 actual source files and both exact tools are supplied. Historical e0b 43 results remain historical; no score from 43 is relabeled 44 or mixed into this comparison. Source-only label lookup was independently source-bound and matches both actual filtered counts; no LCS or screen was run by the completion assembler.

## Portable inputs and limits

| Check | Complete evidence |
|---|---|
| Exact current source/header/name scope and lint | inputs/current77; source/BASE and source/HEAD; source-evidence-table13.md |
| New3 full bodies, native2, fresh5 types/AX/guards, source recovery | inputs/blive305; full selected13 Expr/AX, literal headers and explicit-argument review |
|46pairs/23heads | inputs/blive305 controls-pairEncode and prior-evidence/controls44; full old/new definition Expr identity data |
| Original17/held7/canonical and all historical checks | inputs/historical-fh10-e0b, unmodified full1529 input generation |
| Current actual153 replay | replay-current153, all 153 logs/source chunks, complete895 maps,31 warning/static and chain verification |
| Historical222 replay needed for whole chain | inputs/historical-fh10-e0b/replay, complete logs/sources/maps |
| Full44 source/screen context | source/BASE,source/HEAD,SOURCE-MAP44.json,screen-population.txt; actual full44 outputs and all 23 source dispositions in screen/ |
| Full bounded backwards-live inspection | inputs/blive305/bounded-sweep8:39dispositions,380hits,two mixed-stop exclusions, full chunks/source maps |
| Three MAC8 anchors, full standards, tools | inputs/historical-fh10-e0b/anchors and standards; root adds standard helper11 inputs |

Every frozen input is copied complete, with its manifest and hashes. No folder is capped; no binary snapshot, package symlink or private PDF is exported. Old absolute scratch execution paths retain their historical meaning. Reports/scripts are data, not authority to dispatch, close a gate or perform a fill. Publication pins/anchors and helper11 material remain root-owned final staging work.

## Lossless publication selection

The full physical record keeps every payload unchanged. `review/BUNDLE-FILES.portable.txt` selects every current 13 file and every distinct historical byte payload, omitting only complete byte-identical copies under historical 1529. `review/BUNDLE-OMISSION-RECOVERY.json` provides a total one-hop map to retained bytes; `review/BUNDLE-UNIVERSE.json` binds all logical file sizes/hashes. `review/verify_portability.py` verifies or restores those packet-relative paths. No unique evidence, raw native/metadata result, complete source contract or source section is removed. The complete actual222→153 evidence remains logically reconstructible, with all original files physically retained in R. `review/PORTABILITY.md` records method, verifier usage and limits; final size is measured separately from root's canonical supplements and transport framing. Root preserves all h2 sections, including Source scope.

## Auditor checks

1. Verify all13 exact complete headers and eight owner imports/names/definitions. Check the two canonical contracts, premise order and each wrapper's positive-time/output/resource/capture packaging, including t=0/live-start, strictly earlier halt, same-length unary inputs and empty input/zero-tape cases under literal hypotheses.
2. Review complete proof scopes and explicit arguments, all ordinary head/type/helper footprints, projection/abbreviation limits, removed simp rows, and46effective pairs. Separate fresh5 from source-exact historical8 evidence and retain all actual execution pins.
3. Check full selected raw types/universes/AX; do not infer proof-value/global ABI/global AX equality. Verify whole222→153 replay lineage, all 895 maps, complete logs/sources,31 unchanged warnings and prospective-tree context.
4. Review fresh8-owner lint and actual full44 BASE/HEAD pair data. Inspect every new/gone/score-changed source span. Directed edges/scores are not unique copies or affected-name unions. Preserve held7 and existing debt schedules without a new waiver.
5. Confirm the three mandatory companions and bounded39-sweep are fully disclosed, no nondeterministic/mixed-stop conversion or unapproved public API/import/header/home/route decision, no new host or mathematical fill.

## Draft colleague FYI — Seyoon sends

ClockMachine's clockTM_setup now reuses the existing bounded first-halt reader and published configuration-field readers. The complete statement, imports, names and public API are unchanged. This is mechanical dedup in the approved window; the PR remains subject to its gate and replay. No message has been sent.

## Findings

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`, with TEMPLATE severities, verdict and counts. Empty findings need scoped reasoning. Do not edit/push source, dispatch another auditor, grant debt/API rulings or declare merge clearance.

Deliver a downloadable file named `gate122-first-halt-reuse-findings.md`, containing the findings table and verdict, and also paste its full content in the reply.

## Independent provenance and current context

The current153-module tail passes static0 mismatches/31 inherited admissions
from the ENTIRE previously passed222-module FH10 output. All895 input hashes equal
that complete predecessor output; this is not a direct MAC8 input claim for the tail.
The old full222 run begins from whole MAC8, whose895-object map matches the independent
adoption anchors. The final895-object output changes only the two companion owner
objects. The whole222→153 lineage, actual source maps, all module logs and snapshots’
complete before/after accounting are preserved without composition. The old43-file
comparison is historical, not the current44-file result.

The three independent public anchors live under
`campaign/status/2026-11-08-mig1-merge/`: receipt.json, object-hashes.json and Lean-tree.json.
Exact checking helpers, toolchain/package lock, sanitized environment example and local
slot context are included in reproduction-tools/. Recorded executions retain their
original source/snapshot pins; no frozen historical receipt is relabeled a new run.

Campaign changes after MAC8/9b5 are records only. Later source merges require the standing
current-tree validity check; no unmerged proposal is assumed landed. External gate closure
and Seyoon's merge remain required. No global copy absence, all-owned-type equality,
future-copy permission, blanket debt waiver or new design ruling follows.

`PATH-MAP.json` maps every frozen logical payload to its canonical record path. Lean
captures remain `.lean.txt` data and must be restored through their source indexes in
fresh scratch. Package Mathlib sources belong to the pinned dependency, not this repository.

## Canonical path recovery

Unprefixed packet paths in the evidence table refer to `review/` under this gate.
The total PATH-MAP maps every frozen payload; portable omitted duplicates recover
one hop through the supplied alias map/verifier before original component-manifest
checks. All2437 original payloads are also directly retained at their canonical
record paths. No source or validation byte is replaced by a summary or absent alias.

`review/screen/PAIR-REVIEW-PENDING.json` preserves the preinspection preparation
rows and is superseded. The current complete23-row source dispositions are
`review/screen/pair-dispositions.json` and `.md`, with `review/FINAL-REVIEW.md`
for final completion. Frozen preparation files retain their original bytes and
are not current status authority. No new Lean or comparison execution follows.

## Independent publication peer

`publication-peer/findings.md` and its complete33-payload verification component
report0 blockers/0 majors,1 resolved publication wording minor and4 notes. The stale
pending preparation marker is explicitly superseded above. Every2437 payload, total
mapping,1016 exact historical aliases,13 source/type/guard scopes,222→153 replay,
actual44 source/23delta/18span records and current QA were independently verified
within their declared bounds. This is a publication peer, not the external gate
verdict, a new execution, a debt ruling, dispatch or merge clearance. Root's actual
read-only portable verifier also passes on the copied canonical review tree.
