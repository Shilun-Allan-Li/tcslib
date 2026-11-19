# Gate 56 · merged-tree verification of the four foundation PRs against the records tip · r1

**Result:** the merge of `iO/phase-a-base` (#374 + #378 + #384 + #380) with the records tip is clean, and its replay
is clean. The seals are **not** as expected: coe-A finds Rule-10 errors in three #378 owners besides the known three in
`CoinSampling/Efficiency`.
- **Replay:** 37 modules rebuilt, all rc 0 with 0 errors; 1,430 reused. All 15 foundation paths and their downstream
  (root `TCSlib`, both `audits/*/Checks`) are among the 37. Their output is empty: no warning, no `sorry`.
- **State check:** OK over all 1,467 modules.
- **Admissions:** 0 in the 15 foundation files. The merge's census, **207 in 50**, is byte-identical to the records
  tip's.
- **Axioms:** 280 stored constants of the 10 foundation owners (the 4 facades store none). Every one uses only
  `propext`, `Classical.choice` and `Quot.sound`. The `sorry` control reports `sorryAx`.
- **Seals (canonical coe-A, 10 owners):**
  - **0** on 6 owners: `Subexponential`, `Realization`, `Closeness`, `CoinSampling/Basic`, `Asymptotic` and
    `Contract`.
  - `CoinSampling/Efficiency` **3**: exactly the known DL-70 lines 208, 215 and 222.
  - **Not disclosed anywhere, 8 more errors in 5 declarations of #378:**
    - `Buckets` **1** (`ofEquiv_dec`);
    - `Instances` **1** (`zmod_dec`);
    - `Transfer` **6** (`close_draw_bind`, `close_drawD_bind`, `outputsSubset_drawD`).
  - **Each fix is one line, through readers that already exist.** A sealed probe of each fixed owner gives 0 (§6).
- **Lint:** FAIL and WARN counts are unchanged against the records tip. The delta is INFO lines only. `style_lint`
  gives 0 findings on the 14 changed `TCSlib/` files and no line over 100 characters.

In-house, by a maintainer sub-agent, 2026-11-19, 03:30–04:15 UTC. Static checks used git and `python3 -I`. Lean ran
only through `scripts/lean_check_tree.sh` (the recipe's `runner.py`) and the archived seal runner `runner_full.py`
(`lean -DmaxErrors=0`, no `-o`). One process ran at a time, gated at fewer than 3 Lean processes on the host; the
readings before each start were 0–2 and there were no waits. The disk guard was 2,000 MB; free disk never fell below
6,000 MB. No `lake build`, no `lake exe cache get`.

Evidence is in `verification-r1.zip`; its SHA-256 is in `verification-SHA256SUMS`, and its inner `SHA256SUMS` lists
every file but itself. Read `PROVENANCE.txt` first. Paths below are inside the ZIP.

| Pin | Value |
|---|---|
| #374 `foundations/subexp` | `cbce64d1c135c710b7c036968ed9d4f21414aa72`, 1 commit on `a2bf4bac` |
| #378 `foundations/coin-sampling` | `3473adda66d9c61c51ba640ed4c701e5cde0b6b1`, 10 commits on #374 |
| #384 `foundations/coin-contract` | `40e12f64293833056e311ab7aaf5a62fb3006353`, 4 commits on #378 (one is the merge `21f549c2` of #378's readers) |
| #380 `foundations/realization` | `cdc0934f36365533d410607d0664a0570ae92679`, 1 commit on #374 |
| `iO/phase-a-base` | `5382668bc9cc496355c83e7b77909d9647e089b3`, `TCSlib` tree `9dcf16477970d330a6202fad6ca2fd1e0e6d5405`. Every one of its 15 changed paths is blob-equal to the PR head that owns it (`merge/phase-a-composition.txt`) |
| Merge base with the records | `a2bf4bac0d545fce1fcb4014ef12b44f9651a658` (`TCSlib` tree `849ee945…`, Lean-equal to olean snapshot #10) |
| Records tip | `53e430b68cbe22416312a4f80bbc3426c71cf86d`, `TCSlib` tree `745bf4b494b6581a5666ef9ca0a6e735a68ddcef`. This is the same Lean as Gate 54's replayed tip `88362926` |
| Merge tree | `git merge-tree --write-tree 53e430b6 5382668b` = **`4d0347941c394f6fe1ed88ec067814bcfc1fb6f9`**: clean, one output line. `TCSlib` tree **`6a724839672002fcf75c0c36e79564cbea62d0ba`** |
| Scratch commit | `ed165e99431951c466668f0b235edd12b457b3cb` = commit-tree of that tree, with parents `53e430b6` and `5382668b` (`merge/scratch-commit.txt`). **On no ref, never pushed** |

## 1. The merge (`merge/mergecheck.txt`)

- **Records side:** since `a2bf4bac` the records branch changed 12 Lean paths:
  - the GSW 6b statements and U12/U13 (8 new `GSW/*` modules and the `GSW` facade);
  - the `LWE` facade, `LWE/BitEncoding` and the new `LWE/Ratio`.
- **Foundation side:** `iO/phase-a-base` changes 15 paths:
  - 11 new modules: `Foundations/Subexponential`, `Asymptotic/Realization`, `Games/Closeness` and 8 `CoinSampling/*`
    files (the facade included);
  - the `Foundations`, `Asymptotic` and `Games` facades;
  - the import line in root `TCSlib.lean`.
- **The two sets are disjoint.**
  - Against the tip, the merge differs in exactly the 15 foundation paths.
  - Against `iO/phase-a-base`, it differs in exactly the 12 records paths.
  - Against the base, it changes 27 paths and nothing else.
- **Unchanged at base, tip, `iO/phase-a-base` and merge:** `lean-toolchain`, `lake-manifest.json` and `lakefile.lean`.
- **Root `TCSlib.lean`** is the `iO/phase-a-base` blob `2fd3a3db…`; the records side leaves it unchanged.

## 2. The start tree (`replay/startcheck/`, `replay/cand-*.out`)

**Choice.** The start tree is the #384/#387 landing's accepted tree `$SP/land-384-387/replay2`. Its state is at that
landing's check head `2291280b`, which is #387 `18dd79c1` merged with `bff0567b` and so contains `5382668b`.

| Candidate | Modules to build for `ed165e99` |
|---|---|
| `replay2` | 22 |
| `replay393b` | 18 |
| Gate 54's tree (S2-A applied) | 819 |

`replay2` was taken (the brief's first choice).

**Before the copy:**
- `stateplan check` over its own full order (1,469 modules) with its recorded state (`state.json` SHA-256 `ac3aa3ff…`):
  **RESULT OK, bad 0**.
- The map rehash (`mapnoml.py`) gives 1,500 entries, SHA-256 `b70c5677…`.

**The copy.** `cp -al` into `$SP/g56/olean-replay-g56`. The start tree was never written to: its rehash after the run
is byte-identical (`replay2-map-after.tsv`), and `lean_check_tree.sh` unlinks every olean before writing it.

## 3. The replay (`replay/`)

**Plan.** `fullorder` at the scratch commit gives **1,467 modules** (roots: `TCSlib` and both `audits/*/Checks`).
`stateplan plan` (import-closure keys, the tool unmodified) gives **22 to build** and 1,445 reused:
- **The records side's GSW 6b modules:** `Branching` and `DecryptFormula`, and downstream `Bootstrap`, `Circular`,
  `Leveled`, `LeveledSecurity`, `PolyRatio`, `Asymptotic` and the `GSW`, `Homomorphic` and `AdvancedEncryption`
  facades.
- **#387's EF-D1 edits, which are in the start state but not in the merge:** `LWE/BitNoise` and its downstream in
  `LWE`/`Pseudorandom` and `SIS`.
- Root `TCSlib` and `audits/garg-ch1-3/Checks`.

**Forced additions.** The brief asks for a rebuild of the foundation modules and everything downstream of them.
`downstream.py` over the 15 changed paths (`seeds-phaseA.txt`) gives 17 modules: the 15, root `TCSlib` and both
`Checks`. 15 of these were not in the plan, so the queue is **37** (`queue-g56.txt`). `tools/g56/run-replay.sh` ran
it with the recipe's `runner.py`, unmodified, one module per call, slot-gated and disk-guarded.

| Check | Result |
|---|---|
| `permod` (`replay/permod.*`) | 37 modules; rc≠0 **0**; `error:` 0; `error(` 0; log/record mismatches none; 03:41:31–03:45:37 UTC |
| **The 15 foundation modules and root `TCSlib`** | rc 0, **empty output** (no warning, no `sorry`) |
| `sorry` warnings | 15, all in the records side's admitted GSW 6b targets: `Bootstrap` 5, `PolyRatio` 3, `Leveled` 2, `LeveledSecurity` 2, `Asymptotic` 2, `Circular` 1. This equals the records-side census of §4 |
| Other warnings | 5, in `Pseudorandom/Generators/LWE/Flat`: the `simps` linter on a source unchanged since `a2bf4bac` (the landing r2b records the same 5) |
| `audits/garg-ch1-3/Checks` | rc 0, no `sorryAx`. Log byte-identical to Gate 54's |
| `audits/pass-shelat/Checks` | rc 0. One `sorryAx` line, on the admitted `Complexity.NUPPT.decides_of_decidesWithAdviceInTime`. Log byte-identical to Gate 54's |
| `stateplan update` | 37 taken, none refused |
| `stateplan check` over the 1,467-module order | **RESULT OK, bad 0** (`replay/statecheck.*`) |
| Rebuilt oleans vs the start tree (`rebuilt-vs-before.txt`) | **32 byte-identical**, including all 15 foundation modules. The 5 that differ are expected: `LWE/BitNoise`, `LWE` and `SIS` (now the records tip's sources, without #387); `GSW/Branching` `aa01dfa1…` and `DecryptFormula` `8f73be82…` (the U12/U13 fills). The last two equal the objects recorded by Gate 53 and Gate 54. All 37 are now at link count 1 |
| Output map (`replay/output-map.tsv`, no Mathlib) | 1,500 entries, SHA-256 `8d9584891213c1472789ffe50d2476c9d932452827450c2e3325de523f41959d`. Against the start map: 1,495 equal and 5 changed. 33 entries are outside the merge's order: 31 `PFR/*` dependency oleans, plus #387's `LWE/Efficient` and `SIS/Efficient`, which are stale here. They are not in the order and the state check does not use them |
| Cross-check against Gate 54's merged tree (`keycmp-g54.txt`) | Every module whose import-closure key is equal at `ed165e99` and at Gate 54's `62c27942` has a byte-equal olean (648 such modules). **RESULT OK** |

## 4. Admissions (`admissions/`, `sorryscan.py` over each full order)

| Tree | Census |
|---|---|
| `iO/phase-a-base` `5382668b` (1,458 modules) | `TOTAL 192 in 44 modules; native_decide 0; axiom 0`, the base's census |
| Records tip `53e430b6` (1,456) | **207 in 50**: the base's 192/44 plus the GSW 6b 15/6 |
| Merge `ed165e99` (1,467) | **207 in 50**, byte-identical to the records tip's |
| The 15 foundation files | **0**. The token scan finds no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `unsafe`, `implemented_by` or `extern`. The only `set_option`s are the three standard header lines |

## 5. Axioms (`axioms/`)

**The probe** is `G56Probe/AxiomsG56.lean`. It is the #384/#387 landing's `AxiomsHead` with the module list replaced
by the 14 foundation modules. It runs `Lean.collectAxioms` on every constant that each module stores, plus a `sorry`
control. It ran in the merge worktree on the replay tree: rc 0, 62 s.

| Module | Stored constants |
|---|---|
| `Foundations/Subexponential` | 26 |
| `Asymptotic/Realization` | 14 |
| `Games/Closeness` | 24 |
| `CoinSampling/Basic` | 66 |
| `CoinSampling/Buckets` | 21 |
| `CoinSampling/Transfer` | 13 |
| `CoinSampling/Asymptotic` | 10 |
| `CoinSampling/Instances` | 16 |
| `CoinSampling/Efficiency` | 50 (= the landing r2b's census) |
| `CoinSampling/Contract` | 40 (= the landing r2b's census) |
| The four facades | 0 |
| **Total** | **280** (249 declarations, 31 auxiliary) |

- **Axiom sets:**
  - `[Classical.choice, Quot.sound, propext]`: 238 constants;
  - `[Quot.sound, propext]`: 11;
  - `[propext]`: 17;
  - `[Classical.choice]`: 1;
  - none: 13.
- **Non-standard:** 0.
- **Control:** `CONTROL g56SorryControl [sorryAx]`.
- **The full list,** one row per constant with its PR, is `checks/decls-by-module.tsv`.

## 6. Seals on the merged tree (`seal/found/`)

**Method.** Canonical **coe-A** of the 10 foundation owners. The facades have no declarations to seal.
- **Script:** `tools/g56/sealg56.sh`, which is Gate 54's `sealg54.sh` re-pointed to this worktree and tree
  (`tools/g56/sealg56.sh` vs `tools/used/sealg54.sh`: 4 changed lines).
- **Pipeline:** the collector; `mkseals_coe.py` with the archived Gate 06/10 instrumenter (`SEAL_CHUNK=1000`); the
  gated `runner_full.py` (`lean -DmaxErrors=0`, no `-o`). All tools are byte-identical to Gate 54's copies under
  `tools/used/`.
- **Collector:** rc 0.

| Owner | Requests | coe-A errors | Error lines (source line: declaration) |
|---|---:|---:|---|
| `Foundations/Subexponential` | 2 | **0** | |
| `Asymptotic/Realization` | 1,021 | **0** | |
| `Games/Closeness` | 58 | **0** | |
| `CoinSampling/Basic` | 33 | **0** | |
| `CoinSampling/Buckets` | 47 | **1** | 194: `ofEquiv_dec` (`rfl` through `CoinSampler.congr`, a `Basic` definition) |
| `CoinSampling/Transfer` | 97 | **6** | 108–109: `close_draw_bind`; 126, 131: `close_drawD_bind` (both introduce or apply `ProbComp.Close`, a `Games/Closeness` definition, as a function); 153 (×2): `outputsSubset_drawD` (introduces `OracleComp.OutputsSubset` as a function) |
| `CoinSampling/Asymptotic` | 701 | **0** | |
| `CoinSampling/Instances` | 61 | **1** | 61: `zmod_dec` (`rfl` through `CoinSampler.congr`) |
| `CoinSampling/Efficiency` | 1,055 | **3** | 208, 215, 222: `binArith_lt/sub/mod_pairEncode`, the known DL-70 debt (the landing r2b recorded `src:208/215/222`, the same lines) |
| `CoinSampling/Contract` | 1,063 | **0** | (the landing r2b gave 0 with the same request count) |

**What differs from the expected state.** The expected state was 0 everywhere except `Efficiency`'s 3 errors. That
holds for `Efficiency` (exactly the 3 known errors) and for six other owners.
- **The difference:** 8 errors in `Buckets`, `Instances` and `Transfer`. No record discloses them.
  - The #378 report and PR body seal only `Efficiency`.
  - The landing sealed only `Efficiency` and `Contract`.
- **Same kind as DL-70.** Each one reads a definition of another file instead of its published reader:
  - `CoinSampler.congr` instead of `CoinSampler.congr_dec`;
  - `ProbComp.Close` instead of `ProbComp.close_iff`;
  - `OracleComp.OutputsSubset` instead of `OracleComp.outputsSubset_iff`.

  All three readers are in #378 itself.

**Fix probe** (`seal/fixprobe/`). Each sealed source was copied with proof-only edits (`edits.txt`, `*.diff`):
- `ofEquiv_dec := by rw [ofEquiv, CoinSampler.congr_dec, bucket_dec]`;
- `zmod_dec := by rw [zmod, congr_dec, bucket_dec]`;
- `close_draw_bind` and `close_drawD_bind` through `(ProbComp.close_iff _ _ _).2 fun g hg => …` (and `.1` at the one
  application);
- `outputsSubset_drawD` through `(OracleComp.outputsSubset_iff _ _).2 fun P hP => …`.

**Result: all three re-run sealed with rc 0 and 0 errors** (`fixprobe/runs/`). Together with the originals' errors
this is a paired control: the seal detects these reads, and the existing readers clear them. These are probe edits
only. No PR branch was changed.

## 7. Lint (`lint/`)

**`campaign_style_lint --check8b`**, merge worktree vs records-tip worktree. The scripts are identical at both.

| Subtree | Records tip | Merge |
|---|---|---|
| `TCSlib/Complexity` | 25 FAIL / 390 WARN | 25 / 390 |
| `TCSlib/Cryptography` | 92 / 103 | 92 / 103 |
| `TCSlib/InformationTheory` | 5 / 2 | 5 / 2 |

The Cryptography delta (`delta-TCSlib_Cryptography.txt`, 19 lines) is INFO only:
- the 11 new files' size and declaration lines;
- the line counts of the `Asymptotic`, `Foundations` and `Games` facades;
- the file total, 540 → 551.

**`style_lint`:**
- The 14 changed `TCSlib/` files: **0 findings** (`style-merged-15.txt`).
- `TCSlib.lean`: 6 findings, identical at the records tip (`style-tip-TCSlib.lean.txt`). They are pre-existing, and
  the added import line does not cause them.
- Width: 0 lines over 100 code points in the 15 files.

## 8. Staging checks (`checks/`; git objects and `python3 -I` only)

| File | What it shows |
|---|---|
| `commits.txt` | Every commit of the four PRs and of `iO/phase-a-base` carries an SSH signature and the two trailer lines. Each has one parent, except the merges `21f549c2` (#384), `5ed465f6` and `5382668b` |
| `promotion-stmtcmp.txt` | The 9 helpers promoted by `f96ae32e` (#384) have, whitespace-normalised and with the namespace prefix removed, **the same statements as their originals**: EF-H11's `samplesEfficiently_comap` (`71acf81c`; its decls2 row is also at `4e787bc23` on the exchange branch) and EF-D1's `drawSamplable_restrict`, `natToList_two_pow`, `polyTimeComputable_twoPowWord`, `seedModulusWord` with `_eq`, `_eq_cons`, `listToNat_`, `length_` (`bd4c6f2d` on `land/ef-d1-lattice-families`). **9/9 EQUAL** |
| `pr378-reuse-claims.txt` | PR #378's body lists `OneWay.statClose_pi` and `Nat.count_modEq_card` as reused. Neither name occurs in the 15 files; the implementation report says both were "not needed" (pack S-2) |
| `decls-by-module.tsv` | The 280 constants of §5 by PR and module, with their axioms |
| `pr/` | The four PR bodies and REST metadata, read-only, at staging |

## 9. Clean-up

- **Kept:**
  - the replay tree `$SP/g56/olean-replay-g56` (hard links to `replay2`, plus its 37 rebuilt oleans). It is a
    candidate olean state for the merge while the records tip's Lean stays at `745bf4b4`;
  - the worktrees `$SP/g56/mwt` (merge, with the probe packages) and `$SP/g56/tipwt` (records tip, for the lint), for
    the round's follow-ups.
- **Untouched:** `replay2` (map identical before and after) and `$SP/olean-snapshot*`.
- **The scratch commit `ed165e99`** is an unreferenced object, never pushed.
