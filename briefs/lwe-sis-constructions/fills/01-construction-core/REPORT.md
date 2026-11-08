# Construction-core proof fill

Statement freeze: `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`.
Filled Lean/root: `690217cc1aaefe411158808a8b0797fd887a8abc`.
Existing draft PR [#237](https://github.com/Shilun-Allan-Li/tcslib/pull/237),
`cryptography/lwe-sis-phase1-statements` into `cryptography/lwe-sis-constructions`.
Audited dependency: `0769cba3e44c56700349f954190fc99d9e622270`, PR #236.

## Result and freeze

All 31 audited obligations are proved. The 62 source declarations retain their
order, kinds (17 definitions, 45 theorems), signatures, definition bodies,
attributes and namespaces. Exactly the 31 formerly admitted theorem bodies
changed. The eighth module, sample schedules, is unchanged. All 68 other frozen
source/policy/pin files, including root/facade exports, are unchanged. The only
added code outside proof bodies is three precise imports, listed by
`verify_freeze.py`; all were already in the own official pinned cache inventory.

| Module | Filled obligations |
|---|---:|
| Canonical modular parsers | 5 |
| LWE bit encoding | 6 |
| Direct Regev algorithms | 2 |
| Direct Regev experiments | 3 |
| SIS hash core | 6 |
| SIS collision experiment | 1 |
| Dyadic SIS profile | 8 |
| **Total** | **31** |

Root alone edited and checked the source. Two authorized internal agents supplied
read-only proof/lemma research; neither edited files, ran native/cache work,
spawned workers or committed. No external proof reviewer has been selected or
dispatched. The statement PASS and both earlier reports are preserved verbatim.

## Verification

* A fresh serial 68-module dependency sweep through `scripts/lean_check_tree.sh`
  passes in 189.926 seconds: zero errors, zero owned admission warnings, the same
  17 inherited admission warnings. The own `.lake/core-fill-final-oleans` tree
  was absent before this sweep. Root's build fallback is absent. The full
  `TCSlib.lean` root was not built.
* Final source axiom prints cover all 62 declarations; the environment walk
  covers all 263 owned constants, each with only standard axioms and no
  `sorryAx`. All previous 256 names retain their kinds and visibility. All 166
  earlier foundation constants retain their exact axiom sets.
* Seven new compiler auxiliaries are inventoried: six arithmetic/index proof
  auxiliaries and one simplifier-generated congruence theorem,
  `LWE.decisionAdvantage.congr_simp`, emitted in the Regev experiments module.
  These are public constants, not new handwritten source declarations or owner
  interface edits. The module/name distinction is retained in the raw walk.
* The comment-aware freeze comparison reports 62 to 62 declarations and exactly
  31 changed theorem bodies. It masks only theorem proofs, then compares all
  remaining code after removing the three enumerated imports. This is not an
  elaborated type-hash comparison.
* Five scoped style checks report 0 FAIL / 2 unchanged acronym heuristic WARNs
  over 18 mathematical files. No reader name, attribute or linter changed.

The 42 development checks are retained separately, including failed attempts and
an unavailable optional `Mathlib.Data.Int.Lemmas` import. That import was removed;
the final proof uses existing integer absolute-value equations and arithmetic,
without fetching a cache root. Iteration evidence is not the final verification.
The fresh sweep and final probe are the passing evidence.

All eight package revisions match the unchanged manifest and earlier isolated
package-archive attestation. The archived copies have no Git metadata, so this
is not described as fresh per-package Git revision verification. The three added
import roots are already in the previous 2,334-module official cache inventory.
No package/cache fetch, package mutation or other chat's scratch object was used.
Physical isolation and native freshness are maintainer attestations. Process
inspection remains sandbox-denied; root jobs ran serially under the approved
resource budget and their own PIDs were recorded. No process was killed.

## Reuse and duplication accounting

No new handwritten helper, machine, host or copied existing proved infrastructure
is introduced. Numeric conversion uses the existing Candidates equations; block
extraction uses Mathlib's public flatten/slicing equation; matrix reconstruction
uses `List.ofFn_mul`. Both matrix round trips have local list/index calculations
to apply that public identity. They add no duplicate decoder or reusable host.
The vector decoder uses the same public extraction API as the earlier signed SIS
decoder; it does not copy that decoder or publish a replacement block API.

The remaining proofs use public minimal-lift, matrix, finite cardinality and
probability lemmas. The Regev ideal hybrid constructs only a local translation
equivalence. No library definition is named for unfolding in simp/rw/unfold;
local let-bound expressions are reduced where needed.

## Continuing obligations and routing

N01 remains open: validation/ingestion, approved source matching and complete
frozen-primary comparison. PDF acquisition and raw extraction are recorded, but
the shared source-registry proposal remains unapplied. N02 retains scoped native
evidence, inherited warnings, relevant landing checks and the unclaimed whole
root. N03's 31 mathematical admissions are discharged here; actual-law honest
samplers, efficient machines/adapters, all-polynomial common-secret sample
quantifiers, uniform negligible message bounds, exact raw collision-output
semantics and final primitive bridges remain open.

This proves direct Regev correctness and its concrete hybrid bound, plus the SIS
collision reduction and dyadic profile facts. It does not prove an efficient
existing-API symmetric-encryption/CRH security endpoint, Regev PKE, PRG or CCA2
construction. The dyadic profile establishes no hardness; any later CRH theorem
needs its independent `SISAssumption`. No SIS–LWE or search/lattice bridge is used.

The next proof-audit input is prepared for the existing owned exchange namespace,
`lwe-sis-constructions/outbox/gates/03-construction-core-proofs-r1/`. The user
must select Codex or Claude for this new job and dispatch it. Publication uses
only the existing draft ref and private sparse publisher; it never pushes the
central/campaign ref, merges or touches the shared exchange checkout/index.
All shared-file overlap is the earlier separate export commit, unchanged here.

**Not yet clear to merge — proofs and scoped native checks pass; external proof
review, source-policy work, relevant integration checks and user approval remain.**
