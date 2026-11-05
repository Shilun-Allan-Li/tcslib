# Four space facts out of `Machines/ARMWidth` (PR #181, an API gate): resolutions

**Gate, round 1:** the API gate of PR #181 (`lean/logspace-move` at `50adf098`). Pack `pack.md`.
**Ruled (user, 2026-11-04):** `logSpace_le_succ` moves to `SpaceComplexity/Basic` before H's brief
issues (instead of a fifth `ARMWidth` import into `Hierarchy`, or a new LS-1 copy), and with it
`LOGSPACE_subset_PSPACE`, `SPACE_succ_pow_subset_PSPACE` (to `SpaceClasses`) and
`logSpace_le_of_le_mul_two_pow` (to `Basic`). Bundle SHA-256
`29d886fbc4dc744c213d2a6e1645de8487e15461990aff3b08293a989aa23d16` (93 sections), the Lean at
`50adf098dc94d2d4fed3eb6c46c0263c502fd975`, the records at `bf117a80`. **Staged (2026-11-04); dispatched
(user, 2026-11-04).** **Findings** (`findings.md`, verbatim, SHA-256
`cf95cf1912bb4f90c16d34ef1c89756d91de4554408df982deeac152ce941eb2`; received 2026-11-04): **OPEN, 0
blockers, 1 major, 1 minor, 6 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | LS-1 is not fully retired: `narm_decides` (`Machines/NARMProof`) and `narm_logspace_ptm` (`Machines/NARMLogspace`) still re-derive `logSpace n ≤ n + 1` inline, outside the acknowledged scope. | **True; fixed in round 2** (`1d1247a3`, head `5de52d9a`). Both proofs now cite `logSpace_le_succ`; the two files are Hydroxyi's, and the re-point is a mechanical ARM dedup edit (standing exception, FYI). The two elaborate with 0 diagnostics against `oleans-lsm1` (`evidence/round2/elab/`). The freeze shows exactly those two body changes (`round2/freeze/`). The screen population adds `NARMLogspace` (15 files, `round2/screen/`). A search of the round-2 head (`round2/ls1-search/`) finds the fact stated only in `Basic`. The three remaining hits are different facts: `BPLInP`'s bit-length bound, and the polylog bounds of `ImplicitPoly` and `PreimageHost`. The ledger's LS-1 entry records the corrected scope; **LS-1 is retired when #181 merges.** |
| 2 | minor | `screen-base.status` names `wt-edis` at `2219912d`, not the pack's `711f5444`. | **True; documented and re-run.** `2219912d` is a local pre-ship commit of E-D's overlay on that tree, and all 14 population blobs are equal at the two commits (`round2/screen/round1-base-provenance.txt`). Round 2's base screen runs on a frozen export of `711f5444` itself. |
| 3 | note | Bundle and declared changes authenticated. | Agreed. |
| 4 | note | No weakening; boundary cases checked. | Agreed; the positivity hypothesis `1 ≤ s` and the padded bounds are kept. |
| 5 | note | Homes, imports, consumers and the all-ref search check out. | Agreed. |
| 6 | note | The rule-10 probes support the scoped claims; the linear probe seals only `logSpace`. | Agreed; the pack's wording keeps that scope. |
| 7 | note | Screen and lint reproduce, subject to 1–2. | Agreed; see 1 and 2. |
| 8 | note | The execution evidence is consistent, but supplied rather than re-executed. | Agreed. |

**The replay:** `replay-lsm1.sh` (`evidence/merged-tree/`), 137 modules from `oleans-leqc3`,
pinning the four blobs; precheck passed. **Passed** (user, 2026-11-04): 137 of 137 at `50adf098`,
0 failed, static-equal; snapshot `oleans-lsm1`.

**Merge state. #181: not yet clear to merge** (2026-11-04): the replay passed; it waits for gate 89.

**Round 2 staged (2026-11-04):** `pack-r2.md`, at #181's head `5de52d9a` (the fix `1d1247a3`). Bundle
SHA-256 `88447a4c6de8012e3ed0c5eecddff6fd23c391c727af5bd730257b93b81397e6` (114 sections), the
records at `a47a9a90`. **Dispatched (user, 2026-11-04).**
- **The screen:** 15 files, base a `git archive` export of `711f5444`. 87 → 87 declarations,
  23 → 23 pairs, none new or gone.
- **The replay:** `replay-lsm2` (137 modules from `oleans-leqc3`, six blobs pinned) **passed** (user,
  2026-11-04): 137 of 137 at `5de52d9a`, 0 failed, static-equal (40, all pre-existing); snapshot
  `oleans-lsm2` (`evidence/round2/merged-tree/`).

**Round 2** (`pack-r2.md`, head `5de52d9a`). **Findings** (`findings-r2.md`, verbatim, SHA-256
`0affabd012805818bcc0bbaab77153a0c9a538e474caf04e185b2f4f2636c557`; received 2026-11-04): **OPEN, 0
blockers, 1 major, 0 minors, 7 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | LS-1 is still not retired. `ImplicitPoly`'s `hWle` and `PreimageHost`'s inner `.trans` step each re-prove the logarithm's form of `logSpace m ≤ m + 1`; round 2's search had classed them as different polylogarithmic facts. | **True; fixed in round 3** (`8d41671c`, head `b8add1ac`). Both steps cite `logSpace_le_succ` through `logSpace_eq`, and both files elaborate with 0 diagnostics against `oleans-lsm2` (`evidence/round3/elab/`). `ImplicitPoly` is Hydroxyi's, an ARM-program file, so its re-point is the standing mechanical dedup exception (FYI); `PreimageHost` is the campaign's. The freeze shows exactly the two authorized bodies changed (`round3/freeze/`). A new search classifies every `Nat.log_le_self` use and every `logSpace`-by-successor statement (`round3/ls1-search/classification.md`): the fact is proved once, in `Basic`, and cited at eight sites. The screen covers 17 files with the two added (`round3/screen/`): 124 → 124 declarations, 23 → 23 pairs, none new or gone. The ledger records the corrected scope. |
| 2–8 | note | Provenance, the round-2 replacements, the baseline rerun, screen and lint reproduction, homes, meaning and execution evidence. | Agreed. On note 4, `NARMLogspace`'s missing `Main definitions` heading predates #181; it is in the deferred docstring cleanup. On note 8, `replay-lsm2` passed (above) but is superseded by round 3's `replay-lsm3`. |

**Round 3 staged (2026-11-04):** `pack-r3.md`, at #181's head `b8add1ac`. Bundle SHA-256
`763bee495a3bb520a2d0447b411c310f3d656e406966593c0338984820d509ec` (140 sections), the records at
`04d2123a`. **Dispatched (user, 2026-11-04).** **`replay-lsm3` passed** (user, 2026-11-04): 137 of 137 at
`b8add1ac`, 0 failed, static-equal (40, all pre-existing); snapshot `oleans-lsm3`
(`evidence/round3/merged-tree/`), 137 modules from `oleans-leqc3`, eight blobs pinned.

**Round 3** (`pack-r3.md`, head `b8add1ac`). **Findings** (`findings-r3.md`, verbatim, SHA-256
`f553fc4ae21427ebdae589320951b77a508f778b13d1abd6488cca5ea88b84e0`; received 2026-11-04): **OPEN, 0
blockers, 1 major, 0 minors, 7 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | LS-1 is still not retired. `ARMProof`'s `arm_decides` proves `hLn : Ls ≤ n + 1` inline, with `Ls := logSpace n`, by unfolding `logSpace` and `Nat.log_lt_self`. Round 3's search (by `Nat.log_le_self`) and its screen missed it. | **True; fixed in round 4** (`a7c2a655`): `have hLn : Ls ≤ n + 1 := by rw [hLs]; exact logSpace_le_succ n` (Hydroxyi's file, a mechanical dedup re-point, FYI). Round 4's search (`evidence/round4/ls1-search/`) covers every code line that touches `logSpace`'s definition (unfolds, rewrite and simp lists, `logSpace_eq`, local aliases) and every Mathlib upper bound of `Nat.log` (`log_le_self`, `log_lt_self`, `log_lt_of_lt_pow` and four more): 91 lines in 60 declarations, each classified. LS-1 is proved once, in `Basic`, and cited at nine sites. A binary-length sweep (189 lines) found three more families; the user ruled on each (2026-11-04). **LS-2**, `logSpace n ≤ Nat.size n + 1` and its converse: "Fix in #181 now". `logSpace_le_size_succ` moves verbatim from `ISCountMath` to `Basic`. `BPLInP`'s two inline copies, `SpaceAmplifyPoly`'s `logSpace_le_ell` and `ISCountGenCorrect`'s private `size_le_logSpace` now cite it or `length_bits_le_log` (`fe4bdb67`, `227d92ee`). In the same round, `ExpBFS/Run`'s `setup_run` cites its own file's `lgv_le_succ` (`252bbcb8`). **LS-3**, `|bits n| = Nat.log 2 n + 1`, three private copies, one in E-D's in-flight file: ledgered for the dedup window. **BL-1**, the binary length's elementary bounds re-derived from `Nat.size`: ledgered for the dedup window. The seven files round 4 changes elaborate with 0 diagnostics (`round4/elab/`), and the freeze shows exactly the intended changes (`round4/freeze/`). The screen covers 24 files (`round4/screen/`): 232 → 232 declarations, 63 → 63 pairs, none new or gone. The ledger's LS-1 entry records the third correction, and LS-2, LS-3 and BL-1 have entries of their own. |
| 2–7 | note | Provenance and freeze, the round-3 replacements, the screen and lint, the homes, meaning, and execution evidence. | Agreed. On note 3, round 4 classifies every candidate pattern, not only the listed hits. |
| 8 | note | A replay certifying the repaired final head remains outstanding; #182 must then replay its combined closure. | Agreed. `replay-lsm4` is written (`round4/merged-tree/`): 137 modules from `oleans-leqc3`, 14 blobs pinned, the same closure as round 3's. Its precheck passed at `227d92ee`. #182 then takes one merged-tree replay from round 4's snapshot (`oleans-lsm4`), as ruled. |

**Round 4 staged (2026-11-04):** `pack-r4.md`, at #181's head `227d92ee`. Bundle SHA-256
`72810cba1ccb4857a4e4a5e9a371bdf97eb93e18ae1da233e8c1b415c0149232` (212 sections), the records at `51d6cd83`. **Dispatched (user, 2026-11-04).** **`replay-lsm4` passed** (user, 2026-11-04): 137 of 137 at
`227d92ee`, 0 failed, static-equal (40, all pre-existing); snapshot `oleans-lsm4`
(`evidence/round4/merged-tree/`).

**Round 4** (`pack-r4.md`, head `227d92ee`). **Findings** (`findings-r4.md`, verbatim, SHA-256
`b242a75c8026385bd46579bbf6a01ce662dfc7c273fdf58b3562b352f23f7ed1`; received 2026-11-04): **OPEN, 0
blockers, 1 major, 3 minors, 5 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | BL-1's named scope misses further copies (`Codec/Layout`'s `wP_le`, `PathHard`'s `two_pow_ell_le` and `ell_mono`, `RandomWalkPad`'s `padDegree_le`, `PrimeFind:317–318`, `TQBFHardParams`' `wP_le`); with `Layout`'s `wP_le`, `Layout` reaches 2/9, past one fifth. | **True. Ruled (user, 2026-11-04): "Re-point now in #181."** Round 5 (`d789d6db`, `98912ab2`) re-points every BL-1 site whose file can reach a canonical lemma, adding no import. `two_pow_bits_le` moves from `Codec/Layout` to `Machines/Bin`, and `Codec/Word` publishes `wP_eq`, so `Layout`'s `wP_le` cites `length_bits_le_self` without reading `Word`'s definition (rule 10). `TQBFHardParams`' restatement of `Codec.wP_le` is removed. Fifteen sites are re-pointed: five to `two_pow_bits_le`, seven to `length_bits_le_self` (`Layout`'s `wP_le` among them, and `PrimeFind:204`, found by round 5's classification), and one each to `length_bits_le`, `length_bits_mono` and `record_pos_lt`. `Layout` now has no member. The binary-length sweep at the head classifies all 127 groups (`evidence/round5/ls1-search/bitsweep-classes.md`). The residual, 13 groups, is ledgered with a reason each: colleague-owned `CircuitComplexity`, `Machines/Bin` above the file's layer, no reachable lemma, or E-D's in-flight `NTimeDiagonalizer`. E-D's landing re-points `qy_call_bound`; the file's other four members cannot reach `Machines/Bin` and go to the dedup window. One of these, `qy_ones_ge` (iv), is new in round 5's sweep; **acknowledged into BL-1's residual (user, 2026-11-04)**, asked on the premise that E-D's landing would re-point it. Corrected the same day: the file does not reach `Machines/Bin`, so like three of its four companions it goes to the dedup window. |
| 2 | minor | LS-3's census is inaccurate; the converse's "proved once" overlooks LS-3's halves. | **Fixed** in the ledger and the classification: `Constructible` 1/28, `QuasiPolyHierarchy` 1/25, `NTimeDiagonalizer` 2/236; four occurrences, the inline one included; one public converse lemma, with LS-3's halves the only other proofs. |
| 3 | minor | The searches' coverage claim is too strong; the sweep does not reproduce (189/132 against 191/133). | **Fixed:** the classification describes both searches as candidate enumeration with inspection. `bitsweep.sh` no longer uses `\b`, which macOS's `git grep` had dropped, and now reproduces the auditor's 191 rows at round 4's head (`evidence/round5/ls1-search/`). |
| 4 | minor | The screen's population lists `ISCountGenCorrect` twice; the body lengths omitted `by`. | **Fixed:** round 5's population has 33 distinct files. The screen's own lengths, `by` included, are `logSpace_le_ell` 144 → 57 and `size_le_logSpace` 59 → 63 (round 4). |
| 5–9 | note | Provenance and the change table, the move and re-points, retirement and the name search, lint and elaboration, the replay. | Agreed. On note 9, `replay-lsm4` passed (above) but no longer certifies the PR; round 5's `replay-lsm5` replaces it. |

**Round 5 staged (2026-11-04):** `pack-r5.md`, at #181's head `98912ab2`. Bundle SHA-256
`cbe627e2bd21840c9e95569cbec884853a948e51dde6929b2104aae5bdb46161` (345 sections), the records at `72fed536`.
`replay-lsm5` is written (209 modules from `oleans-leqc3`, 25 blobs pinned; precheck passed); not yet run.
**Dispatched (user, 2026-11-04).** `replay-lsm5` deferred by the user until after a relocation.

**Round 5** (`pack-r5.md`, head `98912ab2`). **Findings** (`findings-r5.md`, verbatim, SHA-256
`ea99d908e6176a3ace4c23ed7d5d844a2bda4fc8b4c3c477fe1d117b3da0d282`; received 2026-11-04): **OPEN, 0
blockers, 2 majors, 1 minor, 7 notes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | BL-1's residual omits four declarations in three files: `QueryReshape`'s `query_index_bound` (sweep group 90; (v) in its positive branch), `UniformSample`'s `le_two_pow_size_pred` (group 62; (v)), and `CookLevin/Hardness`'s `clCount_width` ((i), by binary induction) and `clElapsed_width` ((iii), through it). | **True** (checked: the four bodies, unchanged since `711f5444`; `QueryReshape` and `UniformSample` reach `Machines/Bin`, `Hardness` reaches `TuringMachine/Encoding` but not `Bin`). **Ruled (user, 2026-11-04): acknowledge, with BL-1's scope by kind.** No Lean change. BL-1's acknowledged scope is now every re-derivation of its kinds anywhere in TCSlib, whether or not a sweep lists it, so a member found later is an accounting minor. The four join the dedup window (12.2c), whose named home below both layers (beside `Turing.length_bits_le_self`) re-points them once. Classification corrected (`evidence/round5-resolution/`): groups 62 and 90 are BL-1 (v) members; the two `Hardness` declarations were outside the sweep's patterns. |
| 2 | major | `Codec/Word`'s `bitsVal_lt_two_pow` is an exact copy of `Machines/Bin`'s, outside LS-3, BL-1 and CL-1. | **True** (checked: identical statement, both by induction on the word; `Word` imports `Bin`). **Ruled (user, 2026-11-04): acknowledged into BL-1 as kind (vi)**, the word-value bound `bitsVal w < 2 ^ |w|`, for the dedup window; there `Word`'s copy is removed and its users resolve to `Bin`'s through `open LogProg`. Census: `Word` 1/47. On `Bin`'s 5/15: its five members are the family's canonical statements, the targets of the re-points, not copies; recorded here as the one-fifth review item. |
| 3 | minor | Group 57 (`SpaceAmplifyPoly`'s `logSpace_le_ell`) is classed "a stronger bound" through a short-name key shared with `PathHard`'s; the pack says two merges where `227d92ee..98912ab2` has one. | **Fixed in the records:** `evidence/round5-resolution/bitclasses.py` keys the recurring name by file and declaration (`logSpace_le_ell` is the only named group in two files); group 57 is a citation (citations 62 → 63, "a stronger bound" 2 → 1). The range has one merge, `b0f95123`, which changes no Lean; `pack-r5.md` stays as dispatched. |
| 4–9 | note | Provenance and freeze, the move and replacements, the round-4 repairs, the name search, the screen, lint. | Agreed. On note 8, the screen's population is unchanged: the acknowledged members carry no proof edit. |
| 10 | note | The audited head lacks a completed merged-tree replay; the chain identifies round 4's commit plus working-tree changes. | Agreed. `replay-lsm5` (209 modules, 25 blobs pinned at `98912ab2`) was started by the user on 2026-11-04 and is monitored; it builds every changed file at the head from `oleans-leqc3`, which supersedes the chain as the head's certificate. Then #182 and #184 take their merged-tree replays, in that order. |

**Gate 89 closes (round 5, 2026-11-04):** 0 blockers; the two majors are debt majors, closed by
the user's acknowledgment (TEMPLATE, failure mode 5, as gates 18 and 54); the minor is fixed in
the records. **#181 is clear to merge once `replay-lsm5` passes.**
