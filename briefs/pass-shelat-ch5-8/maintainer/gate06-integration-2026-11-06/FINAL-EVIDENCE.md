# Gate 06 final common verification

Frozen Lean source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`. Draft [PR #232](https://github.com/Shilun-Allan-Li/tcslib/pull/232)
contains 61 changed Lean paths:54 mathematical modules and 7 import/option-only facades.
All 1,108 library source files match the Git snapshot. Common checks are reconciled for the
four selected Codex statement audits; no external gate is closed by this record.

Paths below are relative to this directory unless prefixed otherwise. `FINAL-EVIDENCE-FILES.sha256`
is the companion raw-file manifest; its own hash is pinned externally with the issue bundles.
Record commits and bundle hashes are supplied by the staged READMEs and dispatch prompts to
avoid self-referential commit/hash fields. Source/records section provenance remains explicit.

## Results and precise limits

| Check | Final outcome | Evidence |
|---|---|---|
| Native source/object/direct-prerequisite reconciliation |467 modules, zero stale records after 180+2 affected checks | `evidence-run/final-native-summary.json`, `evidence-run/final-repair-seal-ready.json` |
| Full-source seals |54 valid installation/EOF harnesses; 37 source passes, 17 source failures; 138 diagnostics in 110 unchanged full header/proof blocks | `evidence-rule10-final-r1/native-seal-runs/summary.json` |
| Failure disposition |No new/changed failing block or new home-induced read identified; 62 historical keys/48 additional observation keys; all failures retained | `evidence-rule10-final-r1/failure-disposition-r1/` |
| Seal controls |All 11 verified:5 unsealed negative passes, 5 sealed sole-proof failures, 1 sealed published-reader pass | `evidence-rule10-final-r1/native-control-runs/summary.json` |
| Collector |54 owners; 1,039 term pairs contained in 55,373 closure pairs | `evidence-rule10-final-r1/{collect1.json,seal-collector-inventory.json}` |
| Actual axiom identities |2,881 unique actual identities; 2,835 standard-only/46 admitted-dependent/0 unexpected | `evidence-rule10-final-r1/{axioms-full.json,axiom-review/}` |
| Explicit source review |4,119 items; 1,555 new/touched items across 613 heads, 0 foreign-body reads/0 unresolved new/touched items | `evidence-rule10-final-r1/explicit-source-review/` |
| Fresh source scanner |142 raw C1 hits, 10 C2 show/change rows, 3 C3 equation pairs; all retained and reconciled | `evidence-rule10-final-r1/{explicit-scan-r1,explicit-scan-reconciliation-r1}/` |
| Generated-equation census |Exact 54-module/2,881-identity match; 3 retained older pairs, 0 new/touched pairs; both metadata controls verified | `evidence-rule10-final-r1/eqn-supplement-r2/{native,extracted}/` |
| Style |10 inherited findings, 0 new; each complete prong plain/check8b run rc0 | `evidence-style-final-r2/comparison.json` |
| Lexical/public-header census |sorry 511→544; 0 admit/0 axiom commands both; 816 added/7 removed/13 changed parser rows | `evidence-static-final-r1/` |
| Source-only bundles |06A125 sections, 06B129,06C171,06D185; all 610 raw sections independently verified | `source-bundle-preparation-r1/`, final source-reviews bundle review |

Native evidence reconciles earlier successful same-chat objects and 182 affected checks
(683.783 s affected time, peak RSS 3,148,873,728 bytes). It is not a second cold 467 build.
`TCSlib.lean` was not elaborated: its bytes/exports and the other six facades are verified as
import/option-only context. The setup used the original narrowed 145-root cache fetch plus a
separately probed existing pinned Simps.Basic object, making 146 direct Mathlib roots. No
unfiltered cache fetch or whole-project lake build occurred.

The 46 admitted-dependent actual names and complete axiom sets are exactly unchanged from the
initial e9 census:33 direct statement-phase admissions and 13 proved bodies with transitive
admitted dependencies. Scope growth contributes 158 of 177 census additions; these are not 177
new source declarations. Four common standard-only axiom sets change with the reviewed proof/
decoder routes. Counts and all identities are retained; this is not proof completion.

## Source failures and cleanup accounting

All 138 source diagnostics remain failed evidence. Root and independent review checked complete
raw blocks, namespace/binding/attribute contexts and 20 relevant source diffs. The coin and
probTrue migrations preserve bodies/contracts; the latter's existing Extractors failures
concern statDist/hashPair. No failing proof block or home-induced read was newly introduced.
No complete native base environment or base-source seal was rerun by this final comparison.

The conservative witness proposal 61/49 remains immutable. Exact normalization of historical
`_root_.Complexity.NUPPT.computes_iff_uprob` resolves it to 62 historical/48 additional keys,
without fuzzy matching. Both Encoding keys are historical. The 48 are the initial 35 plus 13
PolyTimeModel observations. The frozen 764-row inventory is unchanged; do not add declaration
counts blindly to row counts. Reconcile after S2 merge with other observations and fill repairs.

## Layered Rule 10 evidence

The fresh native kind catalog has 378,176 actual Name/kind/home rows. The legacy scanner's 124
TCSlib C1 hits all match the exhaustive inherited inventory. It misses 10 uses selected by
`open PrivateKeyScheme (encodeList)`; those are explicitly retained by the source supplement.
The complete source record has 134 inherited TCSlib candidates:131 debt and exactly 3 recorded
PolyExpr.eval notation items. All 18 non-TCS raw hits also occur in unchanged complete blocks.
No explicit TCSlib abbreviation item occurs. The named-open limitation is disclosed rather
than interpreted as zero. All 10 C2 rows belong to retained unchanged failures. No example,
run_cmd/run_elab or eval/check/reduce command occurs in the 54 library sources; anonymous
instances remain stored constants. Anonymous/matcher sensitivity is separately tested.

The C3 census seeds every owned TYPE and available VALUE, including opaque values; follows
referenced TCS/unknown-home TYPES and same-owner definition VALUES; and preserves each owner/
reference pair. It prunes non-TCS types only after checking the complete imported dependency
graph (4,142 modules, 15,622 direct edges). Exact per-module root Name sets match the fresh
AXIOMSID census. Native kind/home checks leave 0 unresolved metadata. Its 3 pairs remain:

| Owned root | Foreign equation reference | Disposition |
|---|---|---|
| `Complexity.BinArith.polyTimeComputable_chunkW` | `Turing.pairDecode.eq_4` | unchanged older proof; already in the 110 failures |
| private `TCSlib.Cryptography.length_decListStep_le` | `Turing.pairDecode.eq_4` | unchanged private proof, historical eqn-term row 713; separate from the 110 failures |
| `TCSlib.Cryptography.gi_statZK` | `Complexity.NUPPT.coinLen.eq_1` | unchanged older proof; already in the 110 failures |

Parent and reference homes are recorded separately (coinLen parent PPT/reference materialized
in EnsemblesLemmas). All 3 source proofs/contracts and their relevant homes are unchanged.
No pair, failure or inherited source read is filtered, waived, relabelled zero or repaired by
these records. The composite new/touched result is 0 identified violations, not an all-library
Rule 10-clean claim.

## Invalid attempts, provenance and scope

The first final C3 attempt is invalid: parser error in two Cache record updates, followed by
synthetic-sorry evaluation refusal. It produced no valid census. The retained R2 changes only
field layout, uses fresh paths, passes rc0/zero diagnostics in 3.134 s, and is fully extracted.
The earlier BPPBridge invalid harness attempts and initial 51-file survey remain historical,
not final coverage. Prepared/unrun wording in immutable proposal/static snapshots describes
those earlier stages; the native completion/extraction records above establish final outcomes.
No unsafe evaluation, failure-driven exclusions or library proof-budget changes were used.

Source/API repairs preserve public algorithms/premises, with five equivalent full-domain
Fin/coin helper reparameterizations and the reviewed equivalent decoder delegation. See
`repair-r1/` for source reviews, exact proposal/application/tool snapshots and failed attempts.
The four statement audits still assess mathematical fidelity, security strength, edge cases,
source attribution and proof sketches. Short correctness proofs remain within their scope.

S2 is separate [PR #231](https://github.com/Shilun-Allan-Li/tcslib/pull/231), clear to merge;
this frozen Gate 06 head does not incorporate or attest it. Cleanup/efficiency retain their
post-S2 order. The checked-target source-equivalence record pins the observed records target;
any later target/source advance requires a documented equivalence check or refreshed evidence.

PS10's exact tracked course PDF and primary author URLs/version limits are in
`../../gates/06-ch5-8-statements/source-manifest.md`. Goldreich PDFs/full text/pages remain
local and are not redistributed. Receiving-auditor access is not pre-attested: the issued
packs provide the PS10 copy and official links, and require exact unavailable comparisons.

**Not yet clear to merge — four external statement audits and their resolutions remain.**
