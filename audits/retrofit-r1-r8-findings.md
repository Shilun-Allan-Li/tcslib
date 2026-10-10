# Chapter-1/2 retrofit epoch R1 — round-8 findings

**Gate: CLOSED — PASS, 0 blockers, 0 majors, 1 minor.** R7-1 is closed. The attached screen reproduces its `.out` byte for byte. Independent enumeration and tiling reproduce **537 like-kind MEMBER pairs**, every generated source-side addition, and all six file totals. **No omission within the stated rule and snapshot population was found; no generator bug was found.** Epoch R1 is retired and its gate condition for 12.2c is satisfied. Existing independent prerequisites for that refactor remain in force.

Audited the supplied snapshot identified as commit `29445b79`, exclusively from `retrofit-r1-r8-bundle.md`, SHA-256 `347f20e5ffd0f367bf57d7c39cd47e75661d121c6893c421897171ed8bc82158`. Later Catalog additions are excluded. This is a correspondence/accounting audit, not a recheck of Lean proof correctness. No Lean source was edited and no Lean build was run.

The user's **2026-10-10 amended severity rule** governs this report. D-R2 acknowledges the Catalog family and names the 12.2c resolution. The remaining description defect is therefore minor: it changes no membership, crosses no further file's one-fifth threshold, exposes no family outside that acknowledgment, and supplies no evidence that the named resolution cannot work.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R8-1 | **minor** | `audits/duplication-ledger.md` · pass-3 population paragraph, standing in-file paragraph, final near-duplicate note | R7-2's corrected description is present, but superseded descriptions remain elsewhere in the same ledger. | Lines 123–124 still call the source population “530 declarations”; the actual population is **553**, of which **542** have normalized extracted bodies of at least 25 characters. Lines 168–176 still describe all **109** printed pairs as in-file near-duplicates, with thirteen above 90%; the corrected classification is **107 like-kind pairs over 62 targets, twelve at least 90%, plus two kind-mismatched restatements**. The final near-duplicate note still lists the H3 `_init` pair as uncounted, whereas the Loop row and pass 4 correctly count `emLoopHost_init` through its cross-file correspondence. None affects the generated census. | Synchronize these passages with the corrected pass-4/R7-2 paragraph. Label 109 as the raw printed total if retained. Say that an in-file near-match alone adds no member, while `emLoopHost_init` qualifies independently through Catalog. No new acknowledgment or gate hold is required. |
| R8-2 | note — R7-1 closed | `r1-public-proof-screen.py` · pass 4, lines 197–228 | The hand-assembled source union has been replaced correctly, with no in-scope omission found. | The pass visits all **423** Catalog declarations and all five source files, rejects kind mismatches, applies the stated tiling thresholds, and adds every qualifying source to its file's set. The independent implementation finds **537** qualifying pairs and exactly the same per-file extra-name lists. All three R7-1 sources are present: `controlCfg_run`, `emCall_right_run`, `exists_emitLoopTM`. Target membership reconstructed directly from all qualifying pairs plus the historical base is **318**, equal to the script's pass-3-derived target union. | Close R7-1; retain pass 4 as the census generator. |
| R8-3 | note — no findings | Screen · historical sets; ledger · acknowledged families | The historical sets implement the accepted surviving families. | Reconstructed **150 Primitives = 146 surviving private twins + 4 relocation copies**, **104 Loop = 86 private twins + 1 `a2_loop_halted_run` twin + 4 relocation originals + 13 H3 copies**, **17 Wrappers = 10 `f2_` + 7 `catalog_` twins**, **20 TimeConstructible = 19 counter twins + `timeConstructible_id`**, and **3 Composition twins**. Normalized whole-declaration comparisons recover the recorded five strengthened counterparts, the exact twins, all thirteen H3 copies, and the four available Loop/Primitives relocation pairs. Catalog retains the historical copies whose originals were deleted. | Retain the historical sets. The absent Hardness source and older deletion history remain carried from the accepted prior audit; neither enlarges this round's screened population. |
| R8-4 | note — no findings | Screen/output · execution; ledger · census rows | The executable output and quoted totals agree exactly. | Ran the unmodified attached script with `--spans`: **132,785 bytes, 1,395 lines**, byte-identical to the attached `.out`. Independent reconstruction gives Catalog **318/423**, Primitives **173/272**, Loop **117/212**, Wrappers **19/29**, Composition **6/19**, and TimeConstructible **20/21**. Summing the generated members' spans gives every quoted line total, including Loop's exact **504-line** H3 subtotal. | Retain the counts, fractions and line totals shown below. |
| R8-5 | note — no findings | The 24 additional source members | Their additions satisfy the stated directional rule, including both previously uncounted H3 near-copies. | Re-tiled a qualifying counterpart for **all 24**, using a second longest-match implementation; every tile-length sequence agrees. Inspected the six source/target pairs below directly, spanning all three affected files, both declaration kinds, the two H3 cases, and a source just above 50% coverage. Independently checked all 24 physical intervals: **375 + 159 + 18 = 552** additional lines. | Retain all 24 additions. These are membership findings under the adopted numerical convention, not assertions that every pair is a verbatim copy or evidence of its authorship. |
| R8-6 | note — extraction repair verified | Screen · `proof`, population filter and pass 3b | R7-2's concrete extraction and kind-classification defects are repaired; only the stale prose in R8-1 remains. | Independent comment masking and body extraction agree on all **976 declarations = 423 + 553**. Equation-style definitions and inductive bodies are now included. The eleven short source bodies cannot reach the 60-character membership floor. Pass 3b labels the two restatements explicitly; it still prints **109 raw rows**, of which **107** are like-kind. The in-file convention remains the one accepted in R7. | Close the extraction/classification portion of R7-2 and carry its residual wording correction as R8-1. |

**Reproduction.** Extracted all thirteen attachments without modifying their contents and ran, from the extracted root:

```text
python3 -I audits/evidence/retrofit/r1-public-proof-screen.py . --spans
```

The reproduced and attached output share SHA-256:

```text
ce587e77252e62a184e98c9cfa414211f23029883dc2ddc541e4963d2a95d403
```

**Rule and generator check.** The independent scan uses the prescribed source-identifier renaming and whitespace/comment removal, then repeatedly takes the longest common unmarked substring, breaking ties by its earliest source position. It retains tiles of at least 25 characters and applies both conditions: shared length at least 60, and twice the shared length at least the normalized source-body length. The independent longest-substring implementation uses a suffix automaton; the 24 selected correspondences were also re-tiled with `SequenceMatcher`, with automatic junk filtering disabled.

There are **423 × 553 = 233,919** possible cross-file pairs, **141,289** of the same kind. **20,508** survive the exact 25-character substring prefilter, and **537** satisfy membership. The prefilter is lossless for this rule: a qualifying tiling contains a tile of length at least 25, hence a shared substring of length 25. A body shorter than 25 cannot provide such a tile. Sets remove repeated occurrences of the same source name within a file; the generator retains every qualifying source, including secondary matches to an already-counted Catalog declaration.

The target construction is also complete: the **299** historical/priorly counted Catalog members union the targets of all **537** member pairs yields **318**, with exactly the **19** additions accepted in R7. Pass 3's selection of a highest-coverage like-kind match does not lose a target: its candidate rows already meet the absolute floor, so whenever one reaches half-source coverage, the highest-coverage row also does.

**Historical correspondence check.** The 146 surviving Primitives twins split into **143 normalized-identical declarations + 3 strengthened counterparts** (`splitSolve_of_body`, `splitSolve_source`, `splitSolve_closed`). Loop's 86 private `f2_` twins split into **84 identical + 2 strengthened** (`loopHost_prepare`, `loopHost_contracts`); the separately named `loop_halted_run` twin gives **87**, with **85** strict twins. Wrappers' seventeen, Composition's three, and the nineteen private counter twins are normalized-identical. The thirteen H3 declarations agree under one consistent `loopHost`-family renaming, with `loopCall` shared. The two Catalog in-file exact-copy pairs also agree. Thus the name-based historical rules reproduce the accepted membership distinctions, rather than accidentally treating the five strengthenings as exact copies.

**Directly inspected re-tilings.** Tile sizes below are normalized Unicode-character counts in the order selected. All six targets are in `Build/Catalog.lean`; source intervals include the attached docstring or attribute through the final code line.

| Source member | Catalog counterpart | Tile sizes and shared total | Shared / source | Source interval |
|---|---|---|---:|---|
| Primitives · `emitterP2StateDecidableEq` | `f2_splitBodyStateDecidableEq` | 128 + 58 + 57 + 56 + 55 + 54 = **408** | 408/726 = **56.2%** | 5491–5507, **17 lines** |
| Primitives · `emitterToken_double` | `f2_scanCopy_suffix` | 98 + 87 + 45 + 44 + 41 + 33 + 32 + 25 = **405** | 405/803 = **50.4%** | 6169–6196, **28 lines** |
| Primitives · `mapCfg` | `f2_lenCfg` | 37 + 31 + 27 = **95** | 95/160 = **59.4%** | 2332–2341, **10 lines** |
| Loop · `emLoopHost_init` | `f2_loopHost_init` | 65 + 30 = **95** | 95/106 = **89.6%** | 4506–4513, **8 lines** |
| Loop · `emLoopHost_anchor_return` | `f2_loopHost_anchor_return` | 692 + 216 + 27 = **935** | 935/961 = **97.3%** | 5090–5130, **41 lines** |
| Wrappers · `captureCfg` | `f2_loopBodyCfg` | 48 + 29 + 27 + 25 = **129** | 129/227 = **56.8%** | 118–135, **18 lines** |

The first pair repeats the constructor-case equality-instance construction; both declarations are classified as terms by the stated rule. The second shares the input-read, zero-tape step and head-motion proof fragments, and **810 ≥ 803** verifies its close threshold crossing without rounding. The configuration pairs share the input-position and selected-tape projections while implementing different remaining fields. The H3 initialization shares the initialization rewrites; the anchor-return pair shares the live-prefix, release, stop-step and padded-source argument. These differences do not disqualify a pair under the adopted partial-coverage rule.

**Verified census.** “Added by pairs” means distinct sources outside the historical set, not the number of qualifying pairs.

| File | Historical base | Added by pairs | Members / declarations | Fraction | Member lines |
|---|---:|---:|---:|---:|---:|
| `Build/Catalog.lean` | 299 prior members | 19 targets | **318/423** | **75.2%** | **7,539** |
| `Build/Primitives.lean` | 150 | 23 | **173/272** | **63.6%** | **3,790** |
| `Build/Loop.lean` | 104 | 13 | **117/212** | **55.2%** | **3,153** |
| `Build/Wrappers.lean` | 17 | 2 | **19/29** | **65.5%** | **355** |
| `TuringMachine/Composition.lean` | 3 | 3 | **6/19** | **31.6%** | **109** |
| `ClassP/TimeConstructible.lean` | 20 | 0 | **20/21** | **95.2%** | **355** |

Relative to the corrected R7 census, the new source increments are **173 − 157 = 16**, **117 − 110 = 7**, and **19 − 18 = 1**, totaling **24**. Their lines give **3,415 + 375 = 3,790**, **2,994 + 159 = 3,153**, and **337 + 18 = 355**. Each affected file was already above one fifth. Catalog's accepted strict subtotal remains **318 − 34 strengthened counterparts/adaptations − 1 counter near-copy = 283**, or **66.9%**.

The completeness conclusion is restricted to the supplied six files, the stated historical sets, and the specified extracted-body/tiling rule. Other files, later additions, and adaptations below the tile threshold are outside this audit. The packet's assertion of byte identity to the previous round remains an attestation: the earlier source blobs and intervening diff are not attached. Prior freeze, deletion and acknowledgment closures are carried at their established evidence level.
