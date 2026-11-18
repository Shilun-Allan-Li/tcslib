# Gate 50 · round 1 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-18 (`gate50-gsw-6a-fills-findings.md`).

---

# Gate 50 — GSW 6a fills, round 1

**#366: CLEAR. #368: CLEAR. Overall: CLEAR.**

Counts below are unresolved findings at the audited pins. The historical findings graded later are not counted again.

| Scope | Blockers | Majors | Minors | Notes | Verdict |
|---|---:|---:|---:|---:|---|
| #366 | 0 | 0 | 1 | 1 | CLEAR |
| #368 | 0 | 0 | 3 | 0 | CLEAR |
| Overall | 0 | 0 | 4 | 1 | CLEAR |

## Audited pins

| Material | Pin |
|---|---|
| #366 head | `597fb736e545706a058cc212243a13f6dadfeceb` |
| #366 tree / merge base | `df05652d512a702fa8e379fe3f16258f0e1d20d5` / `555f0fe1b10a20d1be72386a97c6fe7a2f39c204` |
| #368 head | `1953898b18a33ab2cd533820c5754a1aacffeb44` |
| #368 tree / base | `89952a4a153c1183e0345f88a10568a936762a7d` / `55f553715f280be36827ad86a94c93db39ec56c3` |
| Campaign records | `b1392d065d0a8f496db8e01b6bdad746bc847ffe` |
| Exchange | `b14712e545ce9a6e08d0070ef134358cc5c8d952` |
| Gate-45 freeze | `d154c8830fc8ffc52671b41992e7dbef61e30959` |

The live PR heads match these pins. Scope follows the dispatch: #360, its addendum, all fills, LE-gf1–4, both records-tip merges, LE-g50, and all of #368. The previously audited #358/#359 content, 6b statements, cleanup Stage 1, #365, snapshot adoption and merge order are excluded.

## Findings

| ID | Severity | PR · location | Finding and evidence | Proposed fix |
|---|---|---|---|---|
| **G50-01** | **minor** | #366 · `BranchingPrograms/{Defs,Eval,Barrington}.lean`; `CircuitComplexity/{NANDForm,FormulaArith/Combinators}.lean` | Documentation still describes the admitted state: module sentences at Defs:32, Eval:35 and Barrington:32; the N2/`sorryAx` sentences at NANDForm:61 and :455. Combinators:303 and :329 still say the literal readers are missing. These disagree with the proved head and published readers. Also, the new `barrington_length_pos_aux` at Barrington:613 has a formula and sketch but lacks the glue classification promised by pack question 5. These are documentation defects, not proof or statement defects. | Correct the sketches and helper classification; make the frozen statement/module-prose corrections through a recorded documentation exception. |
| **G50-02** | **minor** | #368 · `GSW/Scheme.lean`; `Encryption/PublicKey/EnsembleSecurity.lean:116` | `hybridPlant_eq` has an accurate verbal description but omits the explicit equation and glue classification requested for the reader API. The retained sketches of `decrypt_eq_decode_errorSum` and `decrypt_of_encrypts` describe the residual calculation without identifying the newly extracted public lemma. The formal statements and proofs are correct. | Add the reader equation and glue note; identify `decrypt_eq_decode_dotProduct` in the affected sketches. |
| **G50-03** | **minor** | #368 · `evidence-s8.zip`, `owner-prereqs-6b-s8/SHA256SUMS` | The manifest includes itself with the empty-file hash. That entry fails verification. All other **184 entries pass**, and the containing ZIP is independently bound by the outer manifest and the pinned records blob. Necessary evidence remains verifiable, so this is not a major binding failure. | Issue a replacement evidence archive whose manifest excludes itself, with an appended records correction and new archive hash. |
| **G50-04** | **minor** | #368 · PR description, “Gating” and replay report | The description still assigns gating to the 6b fills or a small-items gate and reports only the snapshot-7 replay. The recorded ruling instead assigns Gate 50, and the snapshot-8 replay is present and valid. | Update the description to name Gate 50 and link the snapshot-8 replay record. |
| **G50-05** | **note** | #366 · phase-1 duplication disposition and phase-2 sweep | The phase-1 review deferred U1/U2 without filing the required disposition; the later name/body sweep missed U1–U3. Disclosure and a search returning no matches did not establish acceptance or absence of semantic duplication. LE-g50 now repairs all three, so no duplicate debt remains from these items. The retained “on #6 … No duplicate was found” PR sentence describes that limited historical scan, not a clean semantic census. | Record duplication dispositions when discovered and distinguish name/body scans from statement-shape review. No further code repair is required for U1–U3. |

## Historical findings and sweep grades

These grades apply to the original defects. “Closed” means repaired in the audited head.

| Item | Audit grade | Disposition / reason |
|---|---|---|
| GF-F01 | **major**, agree | Closed by LE-gf1: both logarithm bounds cite `Nat.pow_log_le_add_one`. |
| GF-F02 | **major**, agree | Closed by LE-gf3: four owner-side promotions, two visibility promotions, fourteen private-copy deletions and qualified consumers. |
| GF-F03 | **major**, regraded from minor | The old bound is a direct instance of `Finset.sum_le_card_nsmul`. Rebuilding it from `sum_le_sum` and `sum_const` is still an inline re-derivation under the dispatched rule. Closed by LE-gf4. |
| GF-F04 | **minor**, agree | Closed by the expressly ruled, one-sentence LE-gf2 exception. |
| GF-F05 | **note** | Size accepted by GF-W3; 948 lines after the documented rewrap, below 1,000. |
| GF-F06 | **note** | Landing dependency resolved: U8 retains LE-g45’s `const_eval` proof. |
| GF-F07 | **minor**, regraded from info | The REPORT recount exceptions are factual documentation defects; the pack reconciles them. GF-F01’s duplication omission retains its separate major grade. |
| GF-F08 | **note** | The job name in NC1’s permitted module sentence is cosmetic, not a fidelity defect. |
| GF-F09 | **note** | Process weakness; the resulting code defects are graded separately. See G50-05. |
| Sweep U1 | **major** | The substitution bounds repeated the promoted list-bound argument. Closed by LE-g50’s public-lemma calls. |
| Sweep U2 | **major** | The private mapped-list bounds became instances of the new public lemmas. Closed by deletion and redirected consumers; TreeNCAC’s two seal failures also disappear. |
| Sweep U3 | **major**, not merely borderline | The orbit equality is the full-support case of the existing Mathlib cycle-on lemma. Closed by LE-g50’s citation-based proof and attribution. |

## Verification and audit conclusions

**Integrity and provenance.** All 16 outer-manifest entries and all 89 entries inside `verification-r1.zip` verify. The seven nested archives verify except G50-03. All 58 source-file hashes verify; the copied TCSlib/reference files and 70 manifest-listed records/evidence/snapshot files match their pinned git blobs. All **53 bundle sections** match their source material. I additionally retrieved the worker delivery at `60703442`: its **955-entry outer** and **939-entry evidence** manifests pass. The deterministic base and all **seven worker commits reproduce hash for hash**, and all six delivered source files match that reproduced head.

**Freeze and proofs.** Independent comparison against `d154c883` finds **zero changed declaration headers**, no changed existing definition bodies, 78 additions and the two disclosed private removals. Exactly **36 public docstring changes are sketch-only**; `layerNAND` is the sole outside-sketch change and matches LE-gf2. The named-public declaration delta against the tip is **289 ADDED / 1 REMOVED / 0 CHANGED**; the removal is `eval_node_nil` leaving `Hierarchy`, with its destination in `Combinators`. #368 adds two declarations and changes only the disclosed private proof body.

All **98 targets**, independently identified from the frozen admissions plus `const_eval`, occur uniquely in the axiom evidence. The final census contains **853 constants**, only standard axioms, **zero TRACE lines**, and no `sorryAx`. The six promoted lemmas and the structural definitions are also covered. Source review found no hidden restriction or weakening in the conjugator argument, commutator/De Morgan cases, length bound, converse/NC¹ proofs, NAND gadgets, layering invariants, carry-save reduction, comparison or modular interval sum. The fixed permutations use kernel `decide`; C10’s general conjugacy proof uses orbit matching for arbitrary five-cycles.

**API, sources and reuse.** The fifteen #360 readers have the appropriate owners, binders and equations, with no added simp attributes. The three literal readers legitimately use their owner’s well-founded equations. The six public promotions have suitable homes and formula docstrings. #368’s decryption identity holds for every stated `P`, `s`, `C`: splitting the last coordinate gives exactly the Regev residual. Its result-level source tags are supported by the supplied GSW13/BV14 passages and the module’s documented representation deviations. `hybridPlant_eq` repeats the definition’s body exactly. The Barrington reference is supported. Documentation exceptions are recorded above.

LE-gf1/3/4 and LE-g50 consume the public results they replace; LE-gf2 is limited to the ruled sentence. I found no additional unaccepted re-proof in the reviewed declarations or inline arguments. The disclosed padded-value pair uses different representation interfaces and shared public arithmetic lemmas; the negation bounds retain equality statements, rather than the promoted upper-bound statements. Neither supplies a further instance of U1–U3.

**Rule 10.** I checked **74 owner/root seal records** against reconstructed owner bytes, git blobs, insertion hashes, probe hashes, resolved names/homes, raw logs, and installation/EOF counts. The final 22-owner run has no new failures; inherited failures remain Adder 3, DAGTransform 11, Hierarchy 2 and TreeDAG 25. TreeNCAC improves **2 → 0**. The final root run verifies **14,105 requests**, rc 0, zero errors. Attempt-2 controls have six failing sealed negatives, six passing sealed positives, and passing unsealed counterparts. The explicit-unfold comparison introduces no new foreign read. #368’s seals retain Scheme **101/0** and EnsembleSecurity **1268/6**, with the same inherited failing declarations. Together with source inspection, this suffices for the in-scope changes; it does not clear the inherited failures. Carrying the controls and scan across LE-g50 is justified by its deletion/citation-only delta and renewed owner seals.

**Replay binding.** Every per-module build source hash matches the claimed git revision, and raw log hashes and state/output-map hashes reconcile:

| Evidence | Bound revision/tree | Rebuilt modules | Result |
|---|---|---:|---|
| #366 phase 2, snapshot 6 | `ccca6f80` | 564 | rc 0; state 1,445 |
| #366 snapshot 7, then #365 merge | `e4d77a5e`, `93ae671e` | 564 + 22 | rc 0; state 1,447 |
| LE-g50 | `597fb736` | 16 | rc 0; state 1,447; zero warnings |
| #368 snapshot 7 | `1953898b` | 67 | rc 0; state 1,434 |
| #368 snapshot 8 | tree `ab098201a13ad10829914bfbc6bedcbb2fe52e9e` | 67 | rc 0; state 1,434 |

The records-tip merges preserve #366’s earlier change exactly. LE-g50 changes precisely its three declared source modules and their three output hashes. All 67 #368 rebuilt objects and logs equal the snapshot-7 run. I independently reproduced the claimed merge trees and verified their Lean equality to the respective replay trees. No necessary evidence-binding gap remains. Adoption and the second PR’s combined-tree replay remain maintainer merge conditions, outside this verdict.

This audit used independent git/source checks, patch reproduction and the recorded verification evidence. I did not run Lean or independently rehash the maintainer-hosted olean files. SSH signature blocks are present on #366’s 22 first-parent commits and #368’s commit; their signatures were not cryptographically verified.
