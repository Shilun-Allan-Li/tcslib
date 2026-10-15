# Chapter-1/2 retrofit epoch R1 — round-7 findings

**Gate: OPEN — 0 blockers, 1 major, 1 minor.** R6-1 is repaired. The attached script reproduces its published output byte for byte, and Catalog's **318/423 = 75.2%, 7,539 lines, strict 283** is correct. However, three additional **source-side** members are printed as `MEMBER` in that very output and omitted from the ledger's counted union: Composition's `controlCfg_run`, and Loop's `emCall_right_run` and `exists_emitLoopTM`. Counting both sides gives **Composition 6/19 = 31.6%, 109 lines**, and **Loop 110/212 = 51.9%, 2,994 lines**. Catalog does not increase again. I accept the explicitly stated in-file near-duplicate convention, subject to the labeling correction below. Epoch R1 remains open; this audit does not arm 12.2c. RB4's independently opened window is unchanged.

Audited `retrofit-r1-r7-bundle.md`, SHA-256 `cf7ff7fe7095c3a58f1040640e9f3c8788faeed73e54cf3e3e1367873acded6e`. Locations and spans below refer to extracted attachments. This is a documentation/debt audit: proof bodies are compared for correspondence, not rechecked for logical correctness. No Lean source was edited and no Lean build was run.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R7-1 | **major** | `audits/duplication-ledger.md` · Composition/Loop rows and six-new-sources claim; screen · pass 3 | The Catalog additions are complete for the published screen, but their source-side membership is undercounted. | Pass 3 prints **35 like-kind member pairs over 19 Catalog targets and 24 distinct source declarations**. Fifteen sources were already counted; **nine**, not six, are new. The missing three are `controlCfg_run` → `a2_mapSetup_run` (**128/166 = 77.1%**, 12 source lines), `emCall_right_run` → the same target (**125/172 = 72.7%**, 12 lines), and `exists_emitLoopTM` → `exists_loopTM_spaceUsed` (**1,231/2,278 = 54.0%**, 128 lines). All satisfy the adopted numerical rule and appear explicitly as `MEMBER`; none belongs to the listed old source families. A target's highest-coverage counterpart does not replace its other qualifying counterparts. | Form the source union from **every** like-kind `MEMBER` pair, deduplicated per file. Add these three sources, change “6 new sources” to **9** (Primitives 1, Loop 6, Wrappers 1, Composition 1), and synchronize the ledger, pack and plan. Composition becomes **6/19, 31.6%, 109 lines**; Loop becomes **110/212, 51.9%, 2,994 lines**. Catalog remains **318/423, 7,539 lines, strict 283**. Existing D-R2 acknowledgment covers this accounting correction; no new permission or Lean change is needed. |
| R7-2 | **minor** | `r1-public-proof-screen.py` · `proof`, population filter, pass 3b; pack/ledger · coverage labels | “Every declaration” and “109 in-file near-duplicates, thirteen above 90%” need extraction/kind qualifications. The concrete omissions do not add another member in this snapshot. | The five source files have **553 declarations**, not 530. The script admits 530 after body extraction and length filtering. Its `proof` function only recognizes a top-level `:=`; it returns empty for **nine equation-style definitions and three inductives**, including `counterInc`, `loopDebit` and `emCallLo`. I separately extracted their equation/constructor bodies and screened them, and also checked the three similarly omitted Catalog inductives: **no additional pair reaches 60 shared characters**. Pass 3b has no kind guard: its 109 pairs include `f2_cond_ledger`/`f2_timedReadyCfg` and `a2_loop_prepare`/`f2_loopReady`, which pass 3 properly treats as proof/term restatements. Thus it has **107 like-kind pairs over 62 targets, twelve above 90%, plus two restatements**, one above 90%. | Handle equation-style/constructor bodies or state the extractor's exact scope and retain the supplementary negative result. Label 530 as the extracted-body population. Label pass 3b's 109 as raw pairs, with the two restatements identified, or apply the same kind guard. This is an evidence-description/parser limitation, not another demonstrated census omission. |
| R7-3 | note — no findings | Round-6 disposition · R6-1; screen · passes 1–3 | R6-1 is closed, and all 19 advertised additional Catalog members satisfy the rule. | Independently recomputed `counter_count` → `f2_counter_count_space`: **363/452 = 80.3%**, tiles 91 + 80 + 78 + 54 + 31 + 29, Catalog span **3222–3273 = 52 lines**. Pass 3 starts from the correctly repaired 299-member union. All 19 additions reproduce; their 996 lines are itemized below. Pass 1 has exactly **19** direct pairs, including the newly eligible Loop and Wrappers rows; its Loop member is already among the 19 pass-3 additions and is counted only once. | Close R6-1 and retain these target-side results. No target demotion is required. |
| R7-4 | note — no findings | Script/output · reproduction; ledger · Catalog census and spans | The executable evidence reproduces, and the listed Catalog arithmetic is correct. | Ran the attached script with `--spans`; all **1,345 output lines** match the attached `.out` byte for byte. An independent implementation reproduces all **1,083** pass-3 qualifying pairs and their verdicts, and all **109** printed in-file scores. Independent declaration/span reconstruction gives **299 + 19 = 318**, **6,543 + 996 = 7,539**, and the submitted F2A/A2/public partition. | Retain the verified Catalog census and strict subtotal. Correct the source-side union under R7-1. |
| R7-5 | note — convention accepted | Ledger · in-file convention; pass 3b; sampled fragment/restatement exclusions | Recording in-file near-duplicates without adding them to this expressly scoped census is acceptable. It is not a claim that those constructions contain no shared material. | The paired routine definitions have real operational differences: transfer erases the source during its return sweep, whereas copy preserves it. Their 99.8% directional textual score does not make their complete bodies identical. None of the 109 listed pairs has an identical normalized body. The two Catalog exact-copy pairs and all 13 H3 exact copies independently check under their declared renaming and remain counted. Near-duplicates are explicitly recorded and assigned to 12.2c, rather than omitted from the debt docket. Kind-mismatched restatements need the R7-2 qualification. | Retain the convention and the factoring docket; make its exception explicit wherever the primary membership rule is summarized. I do **not** require extra Catalog members merely because of these in-file near matches. Prior statement/fill audits alone are not evidence of absence of duplication. |
| R7-6 | note — no findings | Attached originals; ledger · acknowledgment/disposition table; documentation-only attestation | Existing correspondence closures and acknowledgment remain adequate. Historical byte identity is carried as an attestation. | Fresh whole-declaration comparisons reproduce **143** Primitives twins plus the three recorded strengthenings, **85** Loop twins plus its two strengthenings, **17** Wrappers twins, **3** Composition twins and **19** counter twins. The label **“Catalog's 318 expanded members”**, D-R2 and the 12.2c window agree with the verified target census; D-R3/RB4 dispositions remain explicit. The packet contains no round-6 source blobs or intervening diff, so equality to that earlier state is not independently established here. | Carry the prior deletion, freeze and acknowledgment closures at their established evidence level. No additional approval is requested. Do not certify overall ledger completeness until R7-1 is repaired. |

**Reproduction and population.** Extracted all thirteen attachments, then ran from the extracted root:

```text
python3 -I audits/evidence/retrofit/r1-public-proof-screen.py . --spans
```

The reproduced output's SHA-256 is `79dc6611fbb43350ad7ac5352fd4a049188553aba1d3ae81ce819091952fe49c`, identical to the attached output. Independently enumerated declarations with nested comments masked while retaining physical line positions. The independent tiler repeatedly uses the longest common block, with first-position tie-breaking and automatic junk filtering disabled, and masks the selected block on both sides.

| File | All declarations | Private / public | Bodies admitted by pass 3 |
|---|---:|---:|---:|
| Catalog | 423 | 384 / 39 | Target population: 423 − 299 = 124 |
| Primitives | 272 | 254 / 18 | 258 |
| Loop | 212 | 204 / 8 | 205 |
| Wrappers | 29 | 19 / 10 | 29 |
| Composition | 19 | 11 / 8 | 19 |
| TimeConstructible | 21 | 19 / 2 | 19 |
| **Five source files** | **553** | **507 / 46** | **530** |

The exact 25-character prefilter is lossless **for the extracted strings**: every common tile of length at least 25 contains a shared 25-character substring. Among 124 × 530 = **65,720** possible pairs, **4,265** survive that prefilter. The **1,083** qualifying pairs cover 58 targets and split into **35 member pairs + 1,041 fragments + 7 kind-mismatched restatements**. All printed verdicts agree with independent recomputation; no additional qualifying pair is suppressed. The 19 member targets leave **124 − 19 = 105** Catalog nonmembers under the stated convention.

The supplementary extraction check covered these twelve source bodies: Primitives' `CatalogPolyControl`, `catalogPolyCost`, `SplitBodyState`, `EmitterP2State`; TimeConstructible's `counterInc`, `counterCarry`; Loop's `loopDebit`, `loopBorrowPos`, `loopValue`, `loopWrite`, `emCallLo`, `emCallHi`. It also checked Catalog's `SweepPhase`, `FlagPhase`, `a2_MapState` against the source population. No added comparison reached 60 shared characters. The other eleven filtered source bodies are genuinely shorter than 25 under the published normalization. These checks resolve the concrete omission risk for the attached snapshot, but do not make the published extractor generally exhaustive.

**The nineteen Catalog additions.** The counterpart column gives the highest-coverage like-kind source; other member counterparts remain recorded in the complete output and must contribute to source-side accounting too. Spans include attached docstrings/closure notes through the final code line.

| Catalog target | Source counterpart | Shared / source | Catalog span | Lines |
|---|---|---:|---:|---:|
| `f2_exists_loopFind_space` | Loop · `exists_loopFindTM` | 899/919 = 97.8% | 7934–8032 | 99 |
| `f2_cond_time` | Wrappers · `computesFunInTime_cond` | 633/688 = 92.0% | 9868–9894 | 27 |
| `f2_rewind_heads` | Primitives · `catalogRewind` | 395/435 = 90.8% | 9931–9959 | 29 |
| `f2_cond_ledger` | Wrappers · `timed_start` | 754/1073 = 70.3% | 10084–10146 | 63 |
| `a2_map_block` | Primitives · `extract_block` | 355/675 = 52.6% | 4755–4791 | 37 |
| `a2_map_suffix` | Loop · `emLoop_run_prefix` | 68/129 = 52.7% | 4793–4845 | 53 |
| `a2_map_backB` | Loop · `emLoop_run_prefix` | 68/129 = 52.7% | 4847–4881 | 35 |
| `a2_map_backA` | Loop · `emLoop_run_prefix` | 68/129 = 52.7% | 4883–4916 | 34 |
| `a2_map_parse` | Primitives · `extract_run` | 1035/1908 = 54.2% | 4999–5071 | 73 |
| `a2_map_setup` | Loop · `loopFuel_init` | 214/422 = 50.7% | 5073–5098 | 26 |
| `a2_mapVirtual_run` | Loop · `emLoop_run_prefix` | 72/129 = 55.8% | 5150–5165 | 16 |
| `a2_mapSetup_stationary` | Primitives · `emitterP2_control` | 66/83 = 79.5% | 5173–5185 | 13 |
| `a2_mapSetup_run` | Loop · `emLoop_run_prefix` | 110/129 = 85.3% | 5201–5211 | 11 |
| `a2_mapSetup_heads` | Loop · `emLoop_run_prefix` | 73/129 = 56.6% | 5251–5258 | 8 |
| `a2_call_run` | Loop · `loopHost_halt_return` | 279/508 = 54.9% | 10376–10396 | 21 |
| `a2_loop_prepare` | Loop · `loopHost_prepare` | 1162/1339 = 86.8% | 10420–10506 | 87 |
| `a2_loop_round` | Loop · `loopHost_round` | 1059/2114 = 50.1% | 10531–10631 | 101 |
| `computesFunInTime_pairLenCheck_spaceUsed` | Primitives · `computesFunInTime_pairFst` | 115/161 = 71.4% | 4129–4214 | 86 |
| `exists_loopTM_spaceUsed` | Loop · `exists_loopCfgTM` | 141/165 = 85.5% | 10700–10876 | 177 |
| **Total** | **4 F2A + 13 A2 + 2 public** | | | **996** |

The five flagged low-coverage best matches against `emLoop_run_prefix` are `a2_map_suffix`, `a2_map_backB`, `a2_map_backA`, `a2_mapVirtual_run` and `a2_mapSetup_heads`. Their shared induction/rewrite idioms satisfy the deliberately inclusive rule. This establishes accounting membership, not historical authorship or a claim of verbatim copying. I retain all five.

**The missing source-side members.**

| Source member omitted from counted union | Catalog target already counted | Shared / source | Source span | Additional lines |
|---|---|---:|---:|---:|
| Composition · `controlCfg_run` | `a2_mapSetup_run` | 128/166 = 77.1% | 574–585 | 12 |
| Loop · `emCall_right_run` | `a2_mapSetup_run` | 125/172 = 72.7% | 3342–3353 | 12 |
| Loop · `exists_emitLoopTM` | `exists_loopTM_spaceUsed` | 1231/2278 = 54.0% | 5270–5397 | 128 |

The first two retain the run-length induction, zero case, successor rewrite, restriction of the live-prefix hypothesis and final run-step rewrite. Their tiles are **79 + 49 = 128** and **79 + 46 = 125**. They are common lockstep proof idioms, but excluding them while counting the weaker `emLoop_run_prefix` matches would violate the adopted numerical convention. The emitting-loop match includes the fuel/debit-orbit setup, success condition, round/startup assembly and computation/budget calculations; the 24 independently reproduced tiles total 1,231. Neither public visibility nor being a secondary match is an exclusion from the rule.

**Census and spans.** The disjoint Catalog blocks reconstruct as follows:

| Catalog partition | Members | Lines |
|---|---:|---:|
| Primitives-sourced private counterparts | 150 | 3,249 |
| Loop-sourced historical counterparts | 95 | 2,200 |
| Wrappers-sourced counterparts | 17 | 297 |
| In-file originals and exact copies | 4 | 60 |
| Composition private copies | 3 | 51 |
| Counter block | 20 | 345 |
| Seven earlier public counterparts | 7 | 180 |
| Three earlier adaptations, including R6-1 | 3 | 161 |
| Nineteen additions in this round | 19 | 996 |
| **Total** | **318** | **7,539** |

```text
New target lines:
F2A: 99 + 27 + 29 + 63 = 218
A2: 37 + 53 + 35 + 34 + 73 + 26 + 16 + 13 + 11 + 8 + 21 + 87 + 101 = 515
Public: 86 + 177 = 263
218 + 515 + 263 = 996

Catalog:
299 + 19 = 318
6,543 + 996 = 7,539
100 × 318 / 423 = 75.1773...% → 75.2%
306 F2A = 150 + 94 + 10 + 3 + 20 + 2 + 7 adaptations + 20 nonmembers
45 A2 = 2 internal copies + 1 Loop copy + 13 adaptations + 29 nonmembers
318 = 286 F2A + 16 A2 + 7 redirect + 9 public
34 exclusions = 5 old strengthenings + 7 earlier public + 3 earlier adaptations + 19 new
318 − 34 − 1 counter near-copy = 283
100 × 283 / 423 = 66.9031...% → 66.9%

Source-side correction:
24 member-pair sources − 15 already-counted sources = 9 new sources
9 = 1 Primitives + 6 Loop + 1 Wrappers + 1 Composition
Composition: 5 + 1 = 6; 97 + 12 = 109 lines
Loop: 108 + 2 = 110
Loop exact old spans: 2,009 + 73 + 504 = 2,586
Loop listed additions: 12 + 82 + 76 + 98 = 268
Loop omitted additions: 12 + 128 = 140
Loop corrected spans: 2,586 + 268 + 140 = 2,994
```

The 504-line H3 subtotal replaces the ledger's expressly approximate `≈512` with an exact measurement; the thirteen members are unchanged. Corrected file totals are:

| File | Submitted members | Members after R7-1 | Fraction after correction | Member lines after correction |
|---|---:|---:|---:|---:|
| Catalog | 318 | 318/423 | 75.2% | 7,539 |
| Primitives | 157 | 157/272 | 57.7% | 3,415 |
| Loop | 108 | **110/212** | **51.9%** | **2,994** |
| Wrappers | 18 | 18/29 | 62.1% | 337 |
| TimeConstructible | 20 | 20/21 | 95.2% | 355 |
| Composition | 5 | **6/19** | **31.6%** | **109** |

**Sampled exclusions and convention.** `a2_loop_prepare` shares **139/140 = 99.3%** with the term `loopReady`, but it is a proof that spells out a configuration, so that pair is correctly excluded; the proof counterpart `loopHost_prepare` supplies membership at 86.8%. The same distinction also matters for `f2_cond_ledger`: **103/140 = 73.6%** against the term `timedReadyCfg` is a restatement, while **754/1073 = 70.3%** against the proof `timed_start` is counted. Thus the kind rule affects two above-half comparisons, not only the one highlighted in the pack.

For fragment samples, `f2_poly_step`/`splitPoly_loop_end` shares **61/739 = 8.3%**, and `f2_space_of_time`/`loop_live_prefix` shares **61/156 = 39.1%**; these are partial induction or halted-prefix reasoning, not half-source reuse. The direct `polyUnary` pair remains **119/255 = 46.7%**, and the short `splitSolve` citation remains below the 60-character floor. No sampled fragment or restatement requires an additional target member. The 109 in-file raw scores reproduce, with the two kind exceptions identified in R7-2; after distinguishing them, the explicit count-exact/record-near convention is acceptable for this ledger and its acknowledged cleanup docket.

**Disposition.** Close R6-1; carry R5-1/2/3 and the prior audit closures. Accept the 19 new Catalog members, their spans, the 318/423 census, the strict subtotal and the in-file convention. The three named source-side omissions are the remaining major: the output records their correspondences, but the cumulative member union does not count them. All other published candidates have their member, fragment or restatement disposition in the referenced evidence; historical deleted originals and prior agent provenance are carried at the attached round-6 report's evidence level. Repair R7-1 and the R7-2 evidence descriptions before presenting this as a complete exhaustive census. No Lean correctness defect or new debt approval request is raised.
