# Gate 56 · merged-tree verification of the four foundation PRs against the records tip · r1 (restaged)

**Result:** the merge of the new `iO/phase-a-base` with the records tip is clean, and its replay is clean.
- **Replay:** 17 modules rebuilt, all rc 0 with 0 errors and **empty output**. They are the 15 foundation modules,
  root `TCSlib` and the two `audits/*/Checks`. 1,450 modules are reused.
- **State check:** OK over all 1,467 modules.
- **Admissions:** 0 in the foundation files. The merge's census, 207 in 50, is byte-identical to the records tip's.
- **Axioms:** 281 stored constants, all standard; the `sorry` control reports `sorryAx`.
- **Seals (canonical coe-A, all 10 owners):** **0 everywhere except `CoinSampling/Efficiency`, which has exactly its 3
  DL-70 errors**.
- **Paired controls** for the four readers used: ALL_OK.
- **decls2 of the fix:** 0 added, 0 changed, 0 removed.
- **Lint:** FAIL and WARN counts unchanged; INFO lines only.

**Why "restaged".** The draft r1 of this gate (records `057fe893`, `0cd8a194`, superseded) found 8 Rule-10 errors in
#378: `Buckets` 1, `Instances` 1, `Transfer` 6. Seyoon ruled Q-G56-1 (A): fix first, then gate (records `1b18206f`).
The maintainer then landed the fix and re-ran the whole verification on the new heads (§1–§8). The draft's S-1
evidence is kept under `draft-r1/` in the ZIP.

In-house, by a maintainer sub-agent, 2026-11-19, 04:15–04:50 UTC.
- **Static checks** used git and `python3 -I`.
- **Lean ran** only through:
  - `scripts/lean_check_tree.sh` (the recipe's `runner.py`);
  - the archived seal runner `runner_full.py` (`lean -DmaxErrors=0`, no `-o`);
  - two direct `lean -DmaxErrors=0` control runs, with no `-o`.
- **Limits:** one process at a time, gated at fewer than 3 Lean processes on the host (readings 0–2, no waits); disk
  guard 2,000 MB (free disk stayed above 5,800 MB).
- **Never run:** `lake build`, `lake exe cache get`.

Evidence is in `verification-r1.zip`; its SHA-256 is in `verification-SHA256SUMS`, and its inner `SHA256SUMS` lists
every file but itself. Read `PROVENANCE.txt` first. Paths below are inside the ZIP.

| Pin | Value |
|---|---|
| #374 `foundations/subexp` | `cbce64d1c135c710b7c036968ed9d4f21414aa72` (unchanged), 1 commit on `a2bf4bac` |
| #378 `foundations/coin-sampling` | **`2bf61a2eed72d3aad1de95134be8f89da9424af7`**: 11 commits on #374. The new commit is LE-g56-s1, on `3473adda` |
| #384 `foundations/coin-contract` | **`5b17523b3360572ef266c44c7da8633d7f651280`**: 5 commits on #378. The new one is the `--no-ff` merge of `2bf61a2e` into `40e12f64`. `Contract.lean` is unchanged |
| #380 `foundations/realization` | `cdc0934f36365533d410607d0664a0570ae92679` (unchanged), 1 commit on #374 |
| `iO/phase-a-base` | **`686bf03f25faafb5e3db20899be25e427b82099c`**: the `--no-ff` merge of `5b17523b` into `5382668b`. `TCSlib` tree `279bae0c0a927c8aa847f47e47493adb47cec118`. Each of its 15 changed paths is blob-equal to the PR head that owns it (`merge/phase-a-composition.txt`) |
| Superseded heads | #378 `3473adda`, #384 `40e12f64`, `iO/phase-a-base` `5382668b`. All three new heads are fast-forwards of these; nothing was force-pushed |
| Merge base with the records | `a2bf4bac0d545fce1fcb4014ef12b44f9651a658` (`TCSlib` tree `849ee945…`) |
| Records tip | `1b18206f5d3fee9214bfaa0fff74262836b67f48`, `TCSlib` tree `745bf4b494b6581a5666ef9ca0a6e735a68ddcef`. Its Lean is unchanged since `53e430b6` (0 paths under `TCSlib/`, `TCSlib.lean`, `audits/`, `scripts/`, toolchain, manifest or lakefile) |
| Merge tree | `git merge-tree --write-tree 1b18206f 686bf03f` = **`91d43e1f0320618c1986cd88c2cf0d1c1d4bf44e`**: clean, one output line. `TCSlib` tree **`e4c027393d1c59a30f312623aba5a3369386eeb1`** |
| Scratch commit | `ef93fdb1a31cf0523c49a05407b45f2ccb09148e` = commit-tree of that tree, with parents `1b18206f` and `686bf03f` (`merge/scratch-commit.txt`). **On no ref, never pushed** |

## 1. The fix (LE-g56-s1) and the merges

**`2bf61a2e`** on #378 is one SSH-signed commit, staged by explicit path, with the two trailer lines. It touches 3
files (+10/−6). It is proof-only.

| Declaration | Old proof | New proof |
|---|---|---|
| `Buckets.ofEquiv_dec` | `rfl` through `CoinSampler.congr` | `by rw [ofEquiv, CoinSampler.congr_dec, bucket_dec]` |
| `Instances.CoinSampler.zmod_dec` | `rfl` through `CoinSampler.congr` | `by rw [zmod, congr_dec, bucket_dec]` |
| `Transfer.CoinSampler.close_draw_bind` | a λ on `ProbComp.Close` | `(ProbComp.close_iff _ _ _).2 fun g hg => …` |
| `Transfer.CoinSampler.close_drawD_bind` | a λ on `ProbComp.Close`, and an application of a `Close` proof | `(ProbComp.close_iff _ _ _).2 fun g hg => …` and `(ProbComp.close_iff _ _ _).1 (…) g hg` |
| `Transfer.CoinSampler.outputsSubset_drawD` | a λ on `OutputsSubset` | `(OracleComp.outputsSubset_iff _ _).2 fun P hP => …` |

- **These are the draft's fix-probe edits** (`draft-r1/seal/fixprobe/edits.txt`), applied to the sources.
- **No statement, signature, import or definition changed.**
- **decls2** (the pinned `decls2.py`, SHA-256 `fa81981a…`) gives **0 rows** both for `2bf61a2e` against `3473adda`
  over the 3 files and for `686bf03f` against `5382668b` over all 14 foundation `TCSlib` files (`checks/decls2-*.tsv`).
- **One new stored constant,** `CoinSampling.ofEquiv.eq_1` (`Buckets`): the equation lemma that Lean generates for
  `rw [ofEquiv]`. It is auto-generated, not public API, and its axioms are standard (§5).
- **Before the commit,** a dev check of the 3 modules (`runner_full.py`, no `-o`) gave rc 0, 0 errors and 0 warnings
  (`r2-dev/`).
- **The merges.** `5b17523b` (#384) and `686bf03f` (`iO/phase-a-base`) are SSH-signed `--no-ff` merges with the two
  trailer lines. Each changes exactly the same 3 files against its first parent.
- **The pushes** were plain `git push` to `foundations/coin-sampling`, `foundations/coin-contract` and
  `iO/phase-a-base`: fast-forwards, each accepted on the first attempt. `git ls-remote` then showed the three new heads
  (`push-*.log`).
- **`checks/commits.txt`:** all 39 commits of the four PRs and of `iO/phase-a-base` carry an SSH signature and the two
  trailers.

## 2. The merge (`merge/mergecheck.txt`)

- **Records side:** since `a2bf4bac` the records branch changed 12 Lean paths (GSW 6b, U12/U13, `LWE/BitEncoding`,
  `LWE/Ratio`).
- **Foundation side:** `iO/phase-a-base` changes 15 paths.
- **The two sets are disjoint.**
  - Against the tip, the merge differs in exactly the 15 foundation paths.
  - Against `686bf03f`, it differs in exactly the 12 records paths.
  - Against the draft's merge `ed165e99`, it differs in exactly `Buckets`, `Instances` and `Transfer`.
- **Unchanged at the base, the tip, `iO/phase-a-base` and the merge:** `lean-toolchain`, `lake-manifest.json` and
  `lakefile.lean`.

## 3. The start tree and the replay (`replay/`)

**Start tree:** the draft's accepted replay tree `$SP/g56/olean-replay-g56`. Its state is at `ed165e99`, and it was
itself a `cp -al` of the #384/#387 landing's state-checked `replay2`.
- **Before the copy:** `stateplan check` over its 1,467-module order with its recorded state gave **RESULT OK, bad 0**.
  Its map rehash: 1,500 entries, `8d958489…`.
- **The copy:** `cp -al` into `$SP/g56/olean-replay-g56r2`. The start tree was never written to: its rehash afterwards
  is byte-identical (`startcheck/g56-map-after.tsv`).

**Plan.** `fullorder` at `ef93fdb1` gives 1,467 modules, byte-identical to the draft's order.
- **`stateplan plan`:** 8 to build (`Buckets`, `Transfer`, `CoinSampling/Asymptotic`, `Instances`, `Efficiency`,
  `Contract`, the `CoinSampling` facade, root `TCSlib`) and 1,459 reused.
- **Forced, as in the draft:** the 15 foundation modules and their downstream (`downstream.py`), 17 in all. These
  contain the plan's 8.
- **The queue** is 17 modules (`queue-g56.txt`), run by `tools/g56/run-replay-r2.sh` with the recipe's `runner.py`,
  unmodified.

| Check | Result |
|---|---|
| `permod` | 17 modules; rc≠0 **0**; `error:` 0; `error(` 0; `sorry` 0; **warnings 0**; log/record mismatches none (04:28–04:29 UTC) |
| Module output | Empty for the 15 foundation modules and root `TCSlib`. The two `Checks` logs are byte-identical to the draft's (garg: no `sorryAx`; pass-shelat: the one known `sorryAx` on the admitted `decides_of_decidesWithAdviceInTime`) |
| `stateplan update` | 17 taken, none refused |
| `stateplan check` | **RESULT OK, bad 0** over 1,467 modules |
| Rebuilt oleans vs the start tree | **14 byte-identical**. The 3 that differ are exactly `Buckets`, `Instances` and `Transfer`; their downstream (`Efficiency`, `Contract`, the facade, root, both `Checks`) is byte-identical. All 17 are at link count 1 |
| Output map | 1,500 entries, SHA-256 `af74631b99ca3048f5ee2c0dfa22e3fff7efe8a72906077ac3ab7fb65e3637ac`. Against the start tree: 1,497 equal, 3 changed |
| Key cross-checks (`keycmp-r1.txt`, `keycmp-g54.txt`) | Against the draft's merge `ed165e99`: all 1,459 modules with matching inputs have byte-equal oleans. Against Gate 54's `62c27942`: also no exception. Both **RESULT OK** |

## 4. Admissions (`admissions/`)

| Tree | Census |
|---|---|
| `iO/phase-a-base` `686bf03f` (1,458) | 192 in 44, the base's |
| Records tip `1b18206f` (1,456) | **207 in 50**, byte-identical to the draft's tip census |
| Merge `ef93fdb1` (1,467) | **207 in 50**, byte-identical to the tip's |
| The 15 foundation files | **0**. No `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `unsafe`, `implemented_by` or `extern`; only the three standard `set_option` lines |

## 5. Axioms (`axioms/`)

**The probe** `G56Probe/AxiomsG56.lean` (unchanged from the draft) ran on the new tree: rc 0.

| Module | Stored constants |
|---|---|
| `Subexponential` | 26 |
| `Realization` | 14 |
| `Closeness` | 24 |
| `Basic` | 66 |
| `Buckets` | 22 (+1, `ofEquiv.eq_1`) |
| `Transfer` | 13 |
| `CoinSampling/Asymptotic` | 10 |
| `Instances` | 16 |
| `Efficiency` | 50 |
| `Contract` | 40 |
| The four facades | 0 |
| **Total** | **281** |

- **Non-standard axioms:** 0. Every constant uses only a subset of `propext`, `Classical.choice` and `Quot.sound`.
- **Against the draft:** no constant's axiom set changed.
- **Control:** `CONTROL g56SorryControl [sorryAx]`.
- **The full list** is `checks/decls-by-module.tsv`.

## 6. Seals on the merged tree (`seal/found/`)

**Method.** Canonical **coe-A** of the 10 foundation owners.
- **Script:** `tools/g56/sealg56r2.sh`, the draft's `sealg56.sh` re-pointed to the new tree (4 changed lines).
- **Pipeline:** the collector; `mkseals_coe.py` with the archived Gate 06/10 instrumenter (`SEAL_CHUNK=1000`); the
  gated `runner_full.py`.
- **Collector:** rc 0. Request counts are identical to the draft's.

| Owner | Requests | coe-A errors |
|---|---:|---:|
| `Foundations/Subexponential` | 2 | **0** |
| `Asymptotic/Realization` | 1,021 | **0** |
| `Games/Closeness` | 58 | **0** |
| `CoinSampling/Basic` | 33 | **0** |
| `CoinSampling/Buckets` | 47 | **0** (draft: 1) |
| `CoinSampling/Transfer` | 97 | **0** (draft: 6) |
| `CoinSampling/Asymptotic` | 701 | **0** |
| `CoinSampling/Instances` | 61 | **0** (draft: 1) |
| `CoinSampling/Efficiency` | 1,055 | **3**: source lines 208, 215 and 222 (`binArith_lt/sub/mod_pairEncode`), exactly the DL-70 debt, and the same lines as the draft and the landing r2b |
| `CoinSampling/Contract` | 1,063 | **0** |

**Paired controls** (`ctl/`). They cover the four readers that the fix uses: `CoinSampler.congr_dec`, `bucket_dec`,
`ProbComp.close_iff` and `OracleComp.outputsSubset_iff`.
- **The files:** `Sealed.lean` is `Unsealed.lean` plus `attribute [local irreducible]` on the four definitions
  (`CoinSampler.congr`, `bucket`, `ProbComp.Close`, `OracleComp.OutputsSubset`). Each has four NEG examples (the
  direct read) and four POS examples (through the reader).
- **Sealed:** rc 1 with **exactly 4 errors, one at each NEG** (lines 17, 21, 29 and 34). Every POS passes.
- **Unsealed:** rc 0, 0 errors.
- **Result: ALL_OK.** Each reader is the published route, and the seal detects the direct read.

## 7. Lint (`lint/`)

**`campaign_style_lint --check8b`** at the merge, against the tip. The scripts and `TCSlib` are unchanged since the
draft's tip worktree.

| Subtree | Records tip | Merge |
|---|---|---|
| `TCSlib/Complexity` | 25 FAIL / 390 WARN | 25 / 390 |
| `TCSlib/Cryptography` | 92 / 103 | 92 / 103 |
| `TCSlib/InformationTheory` | 5 / 2 | 5 / 2 |

The Cryptography delta is INFO only (19 lines). It is the draft's delta with the new line counts of `Buckets` (242),
`Instances` (174) and `Transfer` (175).

**`style_lint`:**
- the 14 `TCSlib/` files: **0 findings**;
- `TCSlib.lean`: 6 pre-existing findings, identical at the tip;
- width: 0 lines over 100 code points.

## 8. Staging checks (`checks/`)

| File | What it shows |
|---|---|
| `commits.txt` | 39 commits, all SSH-signed with the two trailers. Merges: `21f549c2`, `5b17523b` (#384); `5ed465f6`, `5382668b`, `686bf03f` (`iO/phase-a-base`) |
| `decls2-378-LE-g56-s1.tsv`, `decls2-iobase-686bf03f-vs-5382668b.tsv` | 0 rows each |
| `promotion-stmtcmp.txt` | The 9 promoted helpers in `Contract.lean` at `5b17523b` (the same blob as `40e12f64`) equal their originals: **9/9 EQUAL** |
| `pr378-reuse-claims.txt` | `OneWay.statClose_pi` and `Nat.count_modEq_card` occur 0 times (pack S-2) |
| `decls-by-module.tsv` | The 281 constants by PR and module |
| `pr/` | The four PR bodies and REST metadata at restaging. #378's and #384's bodies do not yet mention LE-g56-s1 (pack S-3) |

**`draft-r1/`** holds the superseded draft's S-1 evidence:
- the seal table and error map;
- the failing owners' seal logs;
- the fix probe (sources, edits, diffs, runs).

## 9. Clean-up

- **Kept:**
  - the new replay tree `$SP/g56/olean-replay-g56r2`: hard links plus its 17 rebuilt oleans, and the candidate state
    for the merge;
  - the draft's tree `olean-replay-g56`, untouched by this run;
  - the worktrees `$SP/g56/mwt` (now at `ef93fdb1`, with the probe packages), `tipwt` and `wt378` (the branch work;
    detached, at `2bf61a2e`).
- **Untouched:** `replay2`, `$SP/olean-snapshot*`, the records branch, and the #374 and #380 branches.
- **The scratch commits** `ed165e99` and `ef93fdb1` are unreferenced objects, never pushed.
