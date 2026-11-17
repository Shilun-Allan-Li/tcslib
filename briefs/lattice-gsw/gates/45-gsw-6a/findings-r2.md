# Gate 45 · round 2 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-17 (`gate45-gsw-6a-r2-findings.md`).

---

# Gate 45 — GSW phase 6a, round 2

**Overall: CLEAR. PR #358: CLEAR. PR #359: CLEAR.**

G45-01–G45-03 are resolved for the combined landing. No new findings; G45-04 is unused. Round 1’s other passes are carried forward, as requested.

| Audited item | Pinned revision |
|---|---|
| Exchange | `8e09dc58baf3c6ee000dc05f4a3763cd0a78041b` |
| Campaign records | `a9d422cc4f76fbe188770405bfd264f5710947ff` |
| PR #358, unchanged | `a616adcac0760ab56b1b0a2a4869f4763843f9ab` |
| PR #359 | `d154c8830fc8ffc52671b41992e7dbef61e30959`, tree `be58919ee4e1aa52ab1f1441d5b52c41b6caa8d9` |

Open findings after the combined remediation:

| PR | Blockers | Majors | Minors | Notes | Verdict |
|---|---:|---:|---:|---:|---|
| #358 | 0 | 0 | 0 | 0 | **CLEAR** |
| #359 | 0 | 0 | 0 | 0 | **CLEAR** |
| Overall | 0 | 0 | 0 | 0 | **CLEAR** |

The G45-02 correction lands in #359. The unchanged standalone #358 still contains the original wording; its zero open-note count above reflects resolution in the combined landing.

## Round-1 findings

Lean paths below are relative to `TCSlib/Complexity/`; line numbers are at the new #359 head.

| Finding | Status | Assessment |
|---|---|---|
| **G45-01 — major, #359** | **Closed** | `BoolCircuit.eval_node_nil` moves from `CircuitComplexity/Hierarchy.lean` into `CircuitComplexity/FormulaArith/Combinators.lean:415`, preserving its full name, binders, statement and docstring. Its disclosed proof change uses `TreeDAG`’s public evaluation readers. `TreeCircuit.const_eval:432` retains its statement and becomes a proved citation through `const_eq`. It is the only removed admission. |
| **G45-02 — note, #358** | **Closed for the combined landing** | `Combinators.lean:16–18` now distinguishes unchanged computation from the five approved proof repairs. #358 itself is unchanged. |
| **G45-03 — minor, #359** | **Closed** | LE-g45 fixes the commutator convention and C9 docstring. LE-g45b fixes the remaining module and `sigma1`/`sigma2` docstrings. The one-based cycles and their zero-based translations are correctly distinguished. C16’s separate statement about one-based state indexing remains accurate. |

**G45-01’s repair is acceptable.** The moved lemma is elementary constant-gate infrastructure, independent of the hierarchy theorem. `Combinators` is an upstream shared home beside the constant constructor and its reader. `Hierarchy` still reaches it through `TreeNCAC`; imports are unchanged and there is no cycle. The new proof handles the two Boolean cases using `eval_node_true`/`eval_node_false` and the empty-list identities. The wrapper then cites this single shared result. This removes the duplicated proof obligation without changing the public contract or creating duplicate proved material.

The actual Git deltas match the supplied diffs: LE-g45 (`ad9c4fc701ed145cbc96acceefaad447398c8321`) has sole parent `73aedcdaaaffef7e69ab012d9b9195f150bae68d`, changes three files, and has +15/−14 lines. Its only executable edits are the disclosed lemma relocation/proof replacement and the `const_eval` citation; the other edits are the disclosed wording repairs. LE-g45b has sole parent LE-g45, changes two files, and has +13/−7 lines, entirely in comments and docstrings.

## Evidence verification

| Check | Result |
|---|---|
| **Pack integrity** | **12/12** outer checksums; **227/227** LE-g45 and **150/150** LE-g45b internal checksums, with exact covered file sets. Both archive hashes match. All 11 shared pack files match their copies at the records pin. The records diff reproduces with nine-character object abbreviations and the documented exclusions. Round-1 findings are filed verbatim after the disclosed preamble. |
| **Replay binding** | Each edit has **16/16** successful rebuilt modules, zero errors and **68** `sorry` warnings. Source hashes match Git; raw log hashes, recorded object hashes, output maps and state entries agree. I independently recomputed all **1,440** module closure keys at the base and both heads. Each plan correctly builds 16 and reuses 1,424; the state-check logs cover 1,440/1,440. |
| **Maps and isolation records** | Output maps have 1,471 entries and hashes `3cb140cb…` / `fa206774…`. Exactly three recorded objects change for LE-g45 and two for LE-g45b, matching their edited files. The link-count records cover all 16 rebuilt objects with count one. Supplied snapshot/parent rehash logs report zero additions, changes and omissions at the stated checkpoints. |
| **Admissions** | **97 exact**, independently recounted from the bound raw warning logs and matched to the target row map. Combinators contributes 23; the other 74 are unchanged. The 68 freshly emitted warnings plus 29 inherited admissions account for all 97. Only `const_eval` leaves round 1’s set; LE-g45b preserves LE-g45’s set. |
| **Declaration drift** | `decls2` reports only the removal and addition of `BoolCircuit.eval_node_nil` in its old and new files, with identical normalized statements. No changed statement or other declaration delta. |
| **Axioms** | **545 constants:** 383 declaration rows and 162 auxiliary rows. Exactly **102** reach `sorryAx`: the 97 targets plus the same five dependents (`toNANDForm`, `toNANDForm_eq`, `layerNAND`, `layerNAND_gates`, `layerNAND_output`). No auxiliary constant reaches it; no other nonstandard axiom appears. The moved lemma, `const_eval` and both existing Hierarchy callers use only the standard three axioms. LE-g45b’s probe logs are byte-identical to LE-g45’s. |
| **Explicit unfolds and lint** | Zero new foreign unfolds; the old `eval_node_nil` unfold is removed. All 14 remaining foreign items are inherited Hierarchy items. Campaign lint’s **25 FAIL / 390 WARN** lists are identical at the base and both heads; the two pre-existing style-lint findings are byte-identical. |
| **LE-g45b identity** | I reproduced the comment-strip comparison and its recorded output exactly: both stripped hashes match, all six code mutations are caught, and both docstring-only controls remain equal. The Main results entry correctly separates proved `const_eval` from the **17** remaining F3 targets. |

Canonical coe-A records independently checked against their collector catalogs, embedded Git source, probe/log hashes, request components, and install/EOF coverage:

| Owner | Requests, base / LE-g45 | Errors, base / LE-g45 | LE-g45b |
|---|---:|---:|---|
| Combinators | 174 / 174 | 0 / 0 | 174 requests, 0 errors; equal |
| Barrington | 119 / 119 | 0 / 0 | 119 requests, 0 errors; equal |
| Hierarchy | 355 / 355 | 2 / 2 | Source and recorded object unchanged |

The two Hierarchy errors are the disclosed `Language.InTreeSize.inSIZE` failures, identical at base and LE-g45 apart from line numbers. The moved lemma introduces no failure.

**Carry-forward is justified for this delta.** The base Combinators/Barrington canonical records match round 1. Request sets remain equal; neither variant-specific notation exclusion occurs in any of the three changed owners’ import closures, so their strict/coercion and A/B request payloads coincide. Reused tool hashes match archived copies. No definition, reader contract or control target changes. The remaining downstream source files are unchanged, and their rebuilt recorded objects remain byte-identical. Round 1’s other passes, seals and controls therefore stand; those carried checks were not freshly executed here.

## Disclosures and limits

No new undisclosed change was identified. The pre-existing Hierarchy failures and the pack’s title/count, snapshot-adoptability, historical records-wording and line-number slips are accounted for. They do not reopen a blocker or major for this repair.

I did **not** run a fresh Lean compilation. Compilation, axiom and seal conclusions use the supplied hash-bound raw runs, independently recounted and checked against Git sources, closure keys and recorded object maps.

The #360 readers, fills, external fill delivery, Gate 46, bootstrapping/circular security and [Gen09] remain outside scope. Merge order and re-replay on snapshot #6 remain maintainer merge conditions. The user dispatches and merges.
