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
