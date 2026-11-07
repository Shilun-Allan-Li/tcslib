# R2 delivery evidence: offline reconciliation

The supplied validation is numerically and structurally consistent with the pinned producer tree.
Archive it as a **partial, superseded delivery**. This review does not recommend source adoption,
accept the unresolved seal/factoring work, or provide a maintainer replay. No delivered tool or
proof was executed; no Lean, pair search, screen, source integration or Git mutation occurred.

The imported data ref resolves to `246d81d2ce247d9e76dcc0ffbfc5080fd1d8fde5`; the full sweep was at
`0b88b8e35aff030ec962078316554dc7484adf82`, with base
`83ac315ed9e7089466bd16a32f3b71fbadc556d2` and prior delivery
`cbfdba8102e6a5d956a1fdd2be7518b490a5abac`. All four commit objects were independently read-verified.
All eleven delivered inert source snapshots equal the head's actual Git blobs. Root's separate
safe-ingest/bundle receipts remain the authority for ZIP safety, all 4,028 payload checksums and
bundle import; this review hashes the 1,800 evidence/source files it consumes against that manifest.

## Sweep and source provenance

| Supplied run | Modules | Raw/time nonzero exits | Raw errors | Static admissions = raw warnings |
| --- | ---: | ---: | ---: | ---: |
| Full sweep 2, mid tree | 641 | 0 | 0 | 149 |
| Primitives downstream sweep 3, delivered head | 223 | 0 | 0 | 61 |

Every one of the **864 attempts** has a mapped raw output and GNU-time receipt. Their payload
hashes, command/module identity, exit, RSS, start/end timing, error count and admission count agree
with the summary. Independent diagnostic scanning includes coded Lean errors and fatal-process
markers. Static admitted-declaration counts were recomputed from the claimed commit's actual source,
not copied from the supplied static receipt. Both per-module mismatch lists are empty.

The 641-entry order exactly matches `final-order-used.txt` and has zero import-order violations or
missing TCSlib dependencies. The only repository path changed between the two run commits is
Primitives. Independently deriving its transitive downstream set produces exactly the supplied
223 modules, in the same filtered order. Each of the other **418 modules** has an equal complete
reachable TCSlib source closure at mid and head; per-module closure membership, source blob IDs and
closure hashes are retained. Toolchain and package-manifest blobs are unchanged too. The effective
641-module union therefore retains 149 static admissions/raw warnings, under the producer's claimed
execution provenance.

`final-sweep-*-module-map.json`, `head-import-graph.json`, `git-source-blob-maps.json` and
`carried418-source-closures.json` retain every check. This establishes offline source/receipt
consistency. It does not independently authenticate compiler execution, input file contents at run
time, external package artifacts, or retained oleans; no compiled snapshot was supplied or replayed
by this reviewer. It is not a replay of the later maintainer tree.

## Axioms and censuses

All sixty source `#print axioms` requests have exactly one matching successful raw result. Their
names exactly cover every public source body changed from base plus the three forwarding exports,
with no missing/extra request. Every supplied axiom set is contained in `propext`,
`Classical.choice`, `Quot.sound`; the raw exit is zero. These are producer transcripts, not an
independent native axiom walk. Full coverage and all sixty results are in `axiom-crosscheck.json`.

The owned-eleven non-private compiled census is **1,234→1,205**, with **130 additions and 159
removals**; the final owner/kind/name set is exactly revision 1's. It includes the three authored
exports, the renamed derived DecidableEq instance and compiler auxiliaries; the removed set includes
the six retired rows, old instance and auxiliaries. The full delta is preserved. This census does
not supply the private/all-constant compiled population or compare compiled types/values.

The independent source-parser census distinguishes authored named declarations from compiler
constants. For the producer's sixteen files it is public **496→493**, private **1,095→768**; for
the eleven owned homes it is public **357→354**, private **1,079→752**. The public source delta is
exactly the three gated additions and six retirements. These counts use the producer's base and
population, not the later API-reader baseline or maintainer's expanded population.

## Supplied sixteen-file screens

Output hashes, successful receipts, declaration indices, label identities, proof/term kinds,
denominators, threshold/percentage arithmetic, per-file involvement counts and reproduced-character
sums reconcile:

| Scope | Declarations | Reported/parsed directional pairs | Sum of reported shared characters |
| --- | ---: | ---: | ---: |
| Producer base sixteen | 1,279 | 1,589 | 636,810 |
| Producer delivered head sixteen | 1,003 | 623 | 208,120 |

The pair-set delta is **93 head-only, 1,059 base-only**. The inexpensive declaration index was rebuilt
using only pure parsing functions from our trusted repository tool; its hash equals the tool named
in the supplied receipts. No delivered script, tiling algorithm, substring search or new pair search
was run. Consequently this verifies recorded accounting/source binding, not each claimed shared
substring or the exhaustiveness/semantic disposition of matches. The supplied sixteen-file screen
cannot replace the maintainer's twenty-five-file head screen or grant duplication-debt clearance.

## Failed and incomplete evidence remains failed

The latest Primitives seal has **17 errors, exit 1**. All seventeen diagnostics are mapped to exact
inert-source owners in `latest-seal-diagnostic-owners.json`. LoopR2 has zero errors/exit zero. The
latest strict evidence retains **seven Catalog errors, one CertShell error and three CodeSimulator
errors**; every supplied earlier/latest attempt is enumerated separately. No strict gap is waived.

The supplied thirty-eight pointwise/abstracted goals calibrate the original **nineteen** definitions:
all pass unsealed, and each has one mapped `rfl` failure sealed. An independently constructed
same-total duplicate/drop diagnostic set is rejected by per-goal multiplicity. PrimitivesR3 adds
`pairEncode` as a twentieth guard, without an additional supplied control for it. The supplied
controls therefore do not calibrate that whole expanded guard, and broader foreign-definition
coverage is not established. The report's seal/factoring and E1/E2/E3 limitations remain open;
its data must not be restated as complete interface validation.

No discrepancy was found in the reconciled numeric/log/source-provenance claims. Two reviewer
parser assumptions stopped initial offline passes (a legacy `secs=8` exit suffix and a table-label
colon); both scripts, raw failures and exact corrections are preserved as reviewer errata, not
producer failures. `receipt.json`, `MANIFEST.json` and `SHA256SUMS` freeze this bounded review.
