# Chapter-1/2 retrofit epoch R1 — round-6 findings

**Gate: OPEN — 0 blockers, 1 major, 0 minors.** R5-1, R5-2 and R5-3 are repaired: the executable screen reproduces its published output exactly, and the listed 298/423 census and 6,491 lines are correct. One further strengthened correspondence remains outside the counted union: `f2_counter_count_space` reproduces **363/452 = 80.3%** of the attached private `counter_count` proof. Accounting for it gives **299/423 = 70.7%, 6,543 lines**, with strict count **283** unchanged. Epoch R1 is not retired by this audit; its gate does not arm 12.2c. RB4's independently opened window remains valid.

Audited the supplied `retrofit-r1-r6-bundle.md`, SHA-256 `2d84aef2921ce6070a14b8b319c7830cfa5161e58f0ce7eea239d00de2ffd30c`. Locations below are extracted-source line numbers. This is a documentation and debt audit: proof bodies are compared for correspondence, not rechecked for logical correctness. No Lean source was edited.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R6-1 | **major** | `audits/duplication-ledger.md` · residual fragment `f2_counter_count_space`; `Build/Catalog.lean` · lines 3222–3273; `ClassP/TimeConstructible.lean` · `counter_count`, lines 328–357 | A counted-source proof has another substantial strengthened counterpart outside the census. | The residual pass compares this target only with public sources and records an 82-character fragment against `exists_comp_partial`. Its actual predecessor is the attached private `counter_count`, already copied as Catalog's counted `f2_counter_count`. Apply the published normalization and tiling to that source: **LCS 91; shared 363 of 452 characters, 80.3%; verdict `MEMBER`**. The source induction, base configuration proof, potential calculation and increment-run rewrite are retained inside a stronger invariant that adds trajectory bounds. This is substantive proof adaptation, not merely a common arithmetic suffix. The target remains one of the ledger's 25 nonmembers. | Record this correspondence and count the target once, excluding it from strict equality. Catalog becomes **299/423 = 70.7%, 6,543 lines**; the source is already counted, so TimeConstructible stays 20/21 and 355 lines. Change the F2A remainder to 24, update the strict-exclusion explanation and acknowledgment label, and publish this named comparison in the executable evidence. The source-visibility restriction is a limitation of the screen, not an exclusion from expanded correspondence membership. Existing D-R2 acknowledgment suffices; no new approval or Lean edit is requested. |
| R6-2 | note — no findings | Round-6 dispositions · R5-1, R5-2, R5-3; `r1-public-proof-screen.py` / `.out` | All three round-5 findings are repaired on their stated scope. | Running the attached script with `--spans` against the four extracted sources exits successfully and produces a byte-identical copy of the attached `.out`. An independent longest-match/tiling implementation reproduces every printed direct and residual result; enumeration of source 60-character windows independently confirms the direct literal hit set. There are 17 eligible pairs, comprising 2 Composition and 15 Primitives pairs, and the five unmatched sources are correctly named. `f2_strip_linear` and its public source are now counted. | Close R5-1, R5-2 and R5-3. R6-1 is a further accounting omission, not a failure to reproduce the repaired script. |
| R6-3 | note — no findings | Catalog / Primitives · seven new members and physical spans | All seven additions satisfy the published numerical rule, and the resulting **listed** census reproduces. | The five added public targets reproduce 88.7–100% of their sources; `f2_strip_linear` reproduces 86.0% and `f2_counter_heads` 64.1%. Their disjoint Catalog spans total 224 lines. Independent declaration/span reconstruction gives Catalog 298/423 and 6,491 lines; Primitives 156/272 and 3,407; Composition 5/19 and 97; TimeConstructible 20/21 and 355. The strict Catalog subtotal is 283. Details and arithmetic follow. | Retain these verified subtotals, then apply R6-1. Numerical correctness for the listed union does not establish its completeness. |
| R6-4 | note — rule assessment | Ledger · member/fragment rule and sampled exclusions | The numerical rule is reproducible and acceptable as an inclusive accounting convention; it cannot certify absence of other correspondences. | Source coverage, rather than target coverage, correctly retains reused time proofs inside larger space proofs. The 60-character floor excludes short citation wrappers such as `splitSolve`, `pairDup` and `incFixed`. I accept the five additional public members, including the conservatively counted citation wrapper `pairEncodeFixed`; no member needs demotion. The direct `polyUnary`, `pairLenCheck` and `stripLast` pairs have explicit fragment dispositions under the rule. The residual `f2_cond_time` match consists of computation-interface and run-composition fragments. **The recorded fragment target I would additionally count is `f2_counter_count_space`, for the different, private-source correspondence in R6-1.** | Keep the rule as a detection/accounting convention and retain named fragment dispositions. Do not describe the 25 residual helpers as free of copied material solely from a public-source screen. |
| R6-5 | note — no further member omission from best-match selection | Screen · residual pass | Selecting the largest shared length does not hide another public-source member in this snapshot, but the output is one winning pair per helper. | I evaluated all **27 × 28 = 756** residual/source combinations. The 28 entries are the script's public declaration population. Eight additional pairs have at least 60 tiled characters; all eight are fragments, and all their targets already have a winning-pair disposition. None is a suppressed member. Their names and measurements are recorded below. | Qualify “every candidate” as the published per-helper winning candidate. Printing all qualifying pairs would make future evidence clearer, but these secondary fragments do not change the current declaration census. |
| R6-6 | note — no findings | Ledger · carried core correspondences and reconciliation | The attached core comparisons still reproduce. | Repeated all 19 whole-declaration counter comparisons and all three Composition-private comparisons: all match after normalization and helper renaming. Primitives supplies 146 surviving private counterparts: 143 whole-declaration matches and the three already recorded `splitSolve` strengthenings. Both in-file pairs match under their declared renaming. The reconstructed groups are disjoint; F2A has 306 declarations and A2 has 45. Historical deleted originals and unattached Loop/Wrappers provenance remain carried at the prior audit's evidence level. | Carry these closures. Do not reopen their approved cleanup schedules. |
| R6-7 | note — no findings | Ledger acknowledgment table; plan · D-R2, D-R3, RB4; documentation-only attestation | The acknowledgment label matches the submitted census, and existing approvals remain adequate. Historical source equality is an attestation here. | The table labels the Catalog family 298, names D-R2 and the 12.2c window, and retains RB4's H3/relocation scope and A-S1-close window. R6-1 adds accounting of existing material inside that family. The packet contains current sources and the round-5 report, but no round-5 source blobs or intervening patch, so byte identity to round 5 is not independently established by this packet. Later ch7/zone changes and their separate gates are not re-audited here. | Update the family label to 299 with R6-1. Carry the documentation-only attestation and prior source/freeze closures without presenting them as fresh diff or kernel checks. |

**Reproduction.** Extracted all eleven attachments without modifying their contents. Ran:

```text
python3 -I audits/evidence/retrofit/r1-public-proof-screen.py . --spans
```

The complete output matches the attached `r1-public-proof-screen.out` byte for byte (SHA-256 `f9327ca20056d2a99ce86c3f2000b5c51b0f0231c86e57538543c8996b524961`). Independently masked nested comments while preserving line positions, enumerated declarations, computed physical spans, and reconstructed the member union. For string comparisons, an independent longest-match implementation with automatic junk filtering disabled reproduced the script's greedy block selection and totals.

The literal direct hits are exactly the round-5 set: Composition `id` 776 and `const` 273; Primitives `prepend` 62, `pairFst` 75, `pairSnd` 75, `pairConcat` 75, `pairLenCheck` 91 and `stripLast` 121. The unmatched sources are Composition `ifEq`/`comp` and Primitives `splitSolveWith`/`unaryToken`/`appendBit`. The published normalization retains the initial `by`: hence its short `splitSolve` citation is 29 characters rather than the previous report's 27. This does not affect any classification.

**The seven additions.** Fractions below are the published screen's shared length divided by its normalized source length. Public source names in this table begin `computesFunInTime_` unless written in full.

| Source | Catalog target | Shared / source | Catalog inclusive span | Lines |
|---|---|---:|---:|---:|
| Primitives · `stripLast` | `f2_strip_linear` | 1,625 / 1,890 = 86.0% | 4495–4558 | 64 |
| TimeConstructible · `timeConstructible_id` | `f2_counter_heads` | 666 / 1,039 = 64.1% | 3275–3319 | 45 |
| Primitives · `prepend` | `computesFunInTime_prepend_spaceUsed` | 138 / 147 = 93.9% | 3809–3830 | 22 |
| Primitives · `pairEncodeFixed` | `computesFunInTime_pairEncodeFixed_spaceUsed` | 91 / 91 = 100% | 3963–3978 | 16 |
| Primitives · `pairFst` | `computesFunInTime_pairFst_spaceUsed` | 143 / 161 = 88.8% | 3980–4005 | 26 |
| Primitives · `pairSnd` | `computesFunInTime_pairSnd_spaceUsed` | 143 / 161 = 88.8% | 4007–4030 | 24 |
| Primitives · `pairConcat` | `computesFunInTime_pairConcat_spaceUsed` | 141 / 159 = 88.7% | 4052–4078 | 27 |

The two earlier Composition targets occupy 44 and 21 Catalog lines. The six new Primitives source spans are `stripLast` 2800–2880 (81 lines), `prepend` 2086–2101 (16), `pairEncodeFixed` 2182–2198 (17), `pairFst` 2200–2217 (18), `pairSnd` 2219–2236 (18), and `pairConcat` 2251–2272 (22). Thus the five non-strip source spans sum to 91. The four advertised reference measurements all reproduce.

**Why R6-1 is a member.** `counter_count` at TimeConstructible lines 333–357 proves an existential time bound and final counting configuration by induction on the input prefix length. `f2_counter_count_space` at Catalog lines 3228–3273 retains those conclusions and adds a bound on every work-head position up to that time. Its proof retains:

1. The induction and base-time witness, followed by the complete configuration-extensionality proof.
2. The induction-hypothesis unpacking, extended by the trajectory hypothesis.
3. The increment-time witness and the identical potential calculation using `counterInc_potential` and `counterInc_bits`.
4. The run-addition/increment rewrite. The original preparatory reassociation is unnecessary because the target writes the time in the reassociated form directly.

The added branches establish the new trajectory conjunct. They do not erase the retained proof correspondence. After the script's consistent `f2_` renaming, the six greedy tiles have lengths:

```text
91 + 80 + 78 + 54 + 31 + 29 = 363
363 / 452 × 100 = 80.309734...% → 80.3%
363 ≥ 60 and 363 ≥ 452 / 2 = 226
```

Both the published algorithm and the independent implementation return `MEMBER`. This comparison is also available entirely within Catalog, since `f2_counter_count` is a verified normalized copy of the same source. Its original and the target's predecessor are already members; only `f2_counter_count_space` must be added. A targeted check of all 27 residual helpers against all 19 private TimeConstructible declarations found no other member under this rule.

This is the requested reassessment of a **named recorded fragment target**, not a demand for an unrestricted repository-wide similarity search. The six-percent public-source match is incidental to the stronger private-source correspondence. The ledger must record both dispositions without treating the former as evidence against the latter.

**Fragment and citation checks.** The direct fragments are `polyUnary` 119/255, `pairLenCheck` 305/1,391 and `stripLast` 221/1,890. The `polyUnary` target retains parts of the witness split but assembles stronger time/space obligations; the numerical fragment verdict is accurate. `pairLenCheck` retains, among other pieces, the 91-character power-bound suffix. The direct `stripLast` match retains quadratic weakening, while its substantive linear proof is correctly accounted separately in `f2_strip_linear`. Short citation wrappers remain below the absolute floor: `splitSolve` shares 29 characters, `pairDup` 35 and `incFixed` 37. No reverse reclassification is required.

The residual winner `f2_cond_time` shares 135/450 characters with `bufferedCompTM_computesInTime`: these are the computation-interface conversion and run-composition fragments. Its conditional branch selection and controller bound are different. The winning fragment disposition is reasonable.

The following additional residual pairs meet the shared-length floor but lose to the printed best match. None meets half-source coverage:

| Catalog target | Secondary source | Shared / source |
|---|---|---:|
| `f2_counter_heads` | Primitives · `computesFunInTime_appendBit` | 66 / 417 |
| `f2_strip_linear` | Primitives · `computesFunInTime_polyBits` | 61 / 636 |
| `f2_strip_linear` | Primitives · `computesFunInTime_pairMapSnd` | 93 / 414 |
| `f2_strip_linear` | Primitives · `computesFunInTime_pairLenCheck` | 271 / 1,391 |
| `f2_cond_time` | Composition · `exists_comp_partial` | 119 / 1,254 |
| `f2_cond_time` | Composition · `exists_cond` | 134 / 903 |
| `f2_cond_ledger` | Composition · `bufferedCompTM_computesInTime` | 87 / 450 |
| `f2_cond_ledger` | TimeConstructible · `timeConstructible_id` | 82 / 1,039 |

**Census reconstruction.** Fresh counts give Catalog 423 = 384 private + 39 public, Primitives 272 = 254 + 18, Composition 19 = 11 + 8, and TimeConstructible 21 = 19 + 2. The submitted Catalog union reconstructs as follows:

| Catalog partition | Members | Inclusive member lines |
|---|---:|---:|
| Primitives-sourced private counterparts | 150 | 3,249 |
| Loop-sourced | 95 | 2,200 |
| Wrappers-sourced | 17 | 297 |
| In-file originals | 2 | 30 |
| In-file copies | 2 | 30 |
| Composition private copies | 3 | 51 |
| Counter block | 20 | 345 |
| Strengthened public counterparts | 7 | 180 |
| Public-proof adaptations | 2 | 109 |
| **Submitted union** | **298** | **6,491** |
| R6-1: private counter-proof strengthening | **+1** | **+52** |
| **Union after the required correction** | **299** | **6,543** |

The Loop span includes the 22-line docstring/closure-note block preceding `f2_loopHost_contracts`. The four historical Primitives originals absent from the current source are `catalogPair_inverse`, `splitCount_firstHalt`, `splitFind_none` and `splitPrepare_first`; their surviving Catalog targets remain counted under the established rule. No group overlaps another.

The arithmetic, including the submitted figures and required correction, is:

```text
Catalog submitted:
150 + 95 + 17 + 2 + 2 + 3 + 20 + 7 + 2 = 298
291 + 7 = 298
64 + 45 + 22 + 16 + 26 + 24 + 27 = 224
6,267 + 224 = 6,491
100 × 298 / 423 = 70.449172...% → 70.4%
298 − 14 strengthened counterparts/adaptations − 1 counter near-copy = 283

Primitives:
146 surviving private originals + 6 public originals + 4 relocation copies = 156
16 + 17 + 18 + 18 + 22 = 91
3,162 + 73 + 81 + 91 = 3,407
100 × 156 / 272 = 57.352941...% → 57.4%

Unchanged source-side rows:
Composition: 3 private + 2 public = 5; 51 + 46 = 97 lines
100 × 5 / 19 = 26.315789...% → 26.3%
TimeConstructible: 19 private + 1 public = 20; 315 + 40 = 355 lines
100 × 20 / 21 = 95.238095...% → 95.2%

R6-1 correction:
298 + 1 = 299
6,491 + 52 = 6,543
100 × 299 / 423 = 70.685579...% → 70.7%
299 − 15 strengthened counterparts/adaptations − 1 counter near-copy = 283
100 × 283 / 423 = 66.903073...% → 66.9%

F2A submitted:
306 = 150 + 94 + 10 + 3 + 20 + 2 + 2 adaptations + 25 nonmembers
F2A corrected:
306 = 150 + 94 + 10 + 3 + 20 + 2 + 3 adaptations/strengthenings + 24 nonmembers
A2 unchanged:
45 = 2 internal copies + 1 Loop copy + 42 nonmembers
Catalog corrected by delivery:
299 = 282 F2A + 3 A2 + 7 earlier redirect + 7 public counterparts
```

**Disposition.** Close the three round-5 findings and accept the reproducible screen and listed spans. Carry the established source, deletion, freeze and debt-acknowledgment closures. **Do not certify ledger completeness or close epoch R1 yet:** add the explicitly identified `counter_count` → `f2_counter_count_space` correspondence and synchronize the census, evidence and labels. This audit finds one major accounting defect and no Lean correctness defect.
