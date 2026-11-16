# Integration cross-build: records tip × #341 × #340 (2026-11-16)

**Result: B builds cleanly.** 783/783 rebuilt modules have rc 0 with 0 errors (both `error:` and `error(`), through root
`TCSlib` and both `audits/*/Checks`. The state check and the whole-tree check are OK. The axioms hold as required, the
admissions go 198 → 195 as expected, and no module changed by #331, #339 or #338 alters any Rule 10 owner's closure. This
meets the integration condition of #341 and, pending Gate 44, of #340.

Maintainer job. Detailed provenance: `PROVENANCE.txt` inside `int-x-341-340-evidence.zip`.

## Inputs

| Item | Commit | Notes |
|---|---|---|
| Records tip T | `ee11f2a69deb4baf1491437f41098b393149bb2b` | Contains #331, #339 and #338. Its `TCSlib`, `TCSlib.lean`, `audits`, `scripts` and lake files are the same objects as int-x-331-339-338's cross-built tree `7d47e675512c478ad840f9bc85ad352800193674`. |
| #341 (sc-yao) | `355a0288d56290e8c984228cbc1824187029e456` | Merge base `f9fda8fe8d11fc68c233df2979a86d356ddfe1ab`; 70 files (68 added, 2 modified). |
| #340 (pair-bdh, T1) | `916afc25c21f5e52b4b01958186ad55d2f615fd1` | Merge base `9e7a96481785d6cac4dea3b2e990c49ac278b060` (the #331 head); 1 file, `Pairing/Assumptions.lean`. |

Both heads equal `origin refs/pull/N/head`, at the start and at the end of the job. During the job the records branch gained
13 records-only commits (`ee11f2a6` → `c32ca857`), one of which records Gate 42 round 2 as CLEAR. None of them changes
`TCSlib`, `TCSlib.lean`, `audits`, `scripts` or the lake files.

## Method

The method is int-x-331-339-338's, and its tools are reused unmodified. The #340 seals use pair-bdh's seal tools (LE-gate40's)
verbatim.
- New tools: `diffcheck2.py` (the landing diff check as one script), `sealrel2.py` (seal relevance), `mkprobe41.py` and
  `axsum41.py` (the axioms probe and its summary), `sealcmp41.py` (comparison with the in-house seals), and `restore_x41.sh`.
  `restore_x41.sh` is `restore_x3.sh` with only the order path changed.
- The disk watcher also had a pause guard: below 1000 MB free it would stop this job's own process group. It never fired; the
  lowest free space seen was 1465 MB.

Steps:
1. **Preflight.** The `$SP/dl-oleans` snapshot is 1230 files with SHA-256
   `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, the required value.
2. **Merges.** In a new sparse worktree, I created the local branch `int/x-341-340` at T and ran `git merge --no-ff` twice.
   Both merges were clean. The commits are unsigned, dated 2026-11-16T00:00:00Z and never pushed.
3. **Build.** I built incrementally from the snapshot base `eff2dcd0` by import-closure keys (`stateplan.py`).
   - Order: the closure of root `TCSlib`, `audits/garg-ch1-3/Checks` and `audits/pass-shelat/Checks` at B, 1421 modules. As
     a set it equals `downorder.py`'s order against `eff2dcd0`.
   - Plan: 783 modules to build (the same 561 snapshot oleans as X, plus 222 new) and 638 reused.
   - The 561 snapshot oleans were backed up and hash-verified. I added the Mathlib overlay and built NthRootLemmas
     (`c0a9cff0…`, as before).
   - Modules were built one at a time through `scripts/lean_check_tree.sh`. Then came the state check, the whole-tree check,
     the census, and the reference and log comparisons.
4. **Axioms.** One probe at B through `runner_full.py` (`lean -DmaxErrors=0`, no `-o`). It reuses the earlier DepTrace
   `#admitted` unmodified on 71 names, plus a per-module closure census over 85 owners.
5. **Seals.** Canonical coe A and coe B on `Pairing/Assumptions` only (see Seal relevance).
6. **Restore.** I restored the backup, deleted the new oleans and the overlay, and ran `restoreplan --delete`. Then I took a
   fresh snapshot and ran a second, independent check.

## Merges

| | Commit | Tree |
|---|---|---|
| A = T × #341 | `ae1d48fa6a8df2940a264082cbe602e557bfe6eb` | `c6faa7c567fefbe95693e6f3e5202b8b9f8b393b` |
| B = A × #340 | `ac6f0a1c8b8fb8a80c9c87c5524bad5ec70769db` | `4433cec3a2f40087fa65eddc7f545ed2e5239cef` |

The local branch `int/x-341-340` is kept at B. It has no upstream.

- **Diff check.** `git diff T B -- TCSlib TCSlib.lean audits` has 71 files. It equals exactly the union of the two PRs' diffs
  against their merge bases (70 + 1 files, disjoint):
  - paths, statuses, modes and new blobs all match;
  - the old blobs at T equal those at each merge base;
  - every file of B is blob-equal to its PR head.

  Nothing outside `TCSlib/`, `TCSlib.lean` and `audits/` changes.
- **Reverse order.** T × #340 × #341, done with `git merge-tree` and unreferenced scratch commits, is clean at each step and
  gives tree `4433cec3…`. That is the same tree as B. Each forward merge also equals its `git merge-tree` result.
- **Name clash.** #341 adds 739 public names; #340 adds none (its 10 new declarations are private). The intersection is empty.
  The only duplicate names are the same 12 pre-existing `GraphTheory/Core` duplicates at T and B.

## Build of B

- **Runner:** rc 0. **783/783 rc 0; `error:` 0; `error(` 0; the substring "error" 0.** Every log hash equals its record.
- **Totals:** 57 sorry warnings (X's 60 minus Yao's 2 and T1) and 419 warnings; 6714 s of module time (20:49–22:41 UTC);
  maximum RSS 4.58 GB.
- **The 71 PR modules**, plus root `TCSlib`, the `SecureComputation` hub, `YaoReal` and both `audits/*/Checks`: all rc 0, 0
  errors in both forms and 0 sorry. The only warning is the known `BobIO.lean:218` "try 'simp' instead of 'simpa'", as at
  sc-yao's M′. `Pairing/Assumptions` has 0 warnings.
- **State check** (`stateplan check` over the 1421-module order): **RESULT OK**.
- **Whole-tree check** (`treecheck_ml`): every module is rc 0 at the B source, every olean equals its record, and there are no
  missing or stray oleans and no empty directories: **RESULT OK**. The tree holds 4799 files, none of them zero bytes.
- **References:**
  - All 783 rebuilt oleans are byte-identical, in source and olean, to a record from an earlier committed build.
    #341's 70 modules match sc-yao's integration-tip build of M or M′. `Pairing/Assumptions` matches pair-bdh's in-house build.
    Every other module matches X's build.
  - Two modules, `YaoReal` and the `SecureComputation` hub, have a reference with the same source but a different olean. Those
    references are the builds without sc-yao (X, X1 and others). Both modules are byte-identical to sc-yao's M and M′, as
    expected, since their closures contain the Yao modules. The sc-yao integration-tip recorded the same pair.
  - `logcheck`: 783 OK-REF.

## Axioms on B

The probe ran with rc 0, 0 errors and 0 warnings. `axsum41.py` gives **RESULT OK**.
- **Yao (#341).** `yaoProtocol_hbcSecure`, `yaoHybrid_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators`,
  `yaoSeed_good_whp`, `RunWithHost.acc_poly`, the ten `otProtocol_*` and `HybridProtocol.hbcSecure_compose` all depend on
  `[propext, Classical.choice, Quot.sound]`, with no direct `sorryAx` user in any closure.
  - The Yao and `acc_poly` closures (21457 / 20479 / 9172 / 20202 / 17757 / 4610) equal sc-yao M′'s.
  - `otProtocol_simulators`, `_polyTime`, `_hbcSecure` and `hbcSecure_compose` (16652 / 7298 / 16742 / 17721) equal M's.
- **T1 (#340).** `bdhAssumption_of_dbdhAssumption` is **standard** now: `[propext, Classical.choice, Quot.sound]`, with
  closure 17296 and no `sorryAx` user. At X it had `sorryAx`, with closure 9582.
- **`bb1_sidSecure`.** It depends on `[propext, sorryAx, Classical.choice, Quot.sound]`, and its closure's direct `sorryAx`
  users are **exactly T2, T3 and T4**. T2, T3 and T4 are each the only direct user in their own closures.
- **GSW.** All 35 targets are still standard with 0 `sorryAx` users. This is a full check, not a spot check.
- **Unchanged rows.** Every GSW, pairing-standard, T2–T4 and `bb1_sidSecure` row, including the closure sizes, is identical to
  int-x-331-339-338's. The only changed row is T1's.
- **Owner census.** 83 of the 85 owners have no direct `sorryAx` user in their union closures. These include
  `Pairing/Assumptions` (at X it had [T1]), `Yao`, `Uniform` and all 67 helpers. As at X, `BonehBoyenMachine` reaches [T4] and
  `BonehBoyenSecurity` reaches [T2, T3, T4].

## Admissions (int-x census method, `tipcensus.py`)

- **T `ee11f2a6`: 198**, identical per module to int-x-331-339-338's census of X.
- **B `ac6f0a1c`: 195 = 198 − 2 − 1**, which is the expected value.
  - #341 removes 2: `SecureComputation/Yao` 2 → 0. Its 68 new modules have 0.
  - #340 removes 1: `Pairing/Assumptions` 1 → 0.

  No other module changes. No set disagrees. The same 34 modules outside root `TCSlib`'s closure have no record. There is no
  difference to explain.

## Seal relevance

`git diff 2da7e0f3 ee11f2a6 --name-only -- TCSlib` gives 19 modules: 12 from #331, 5 from #339 and 2 from #338. Root
`TCSlib.lean` also changes, but no owner imports the root. I computed each owner's import closure at B, at its PR head and,
for #341, at sc-yao's M′ `061ad60c`.

- **#341** (70 Rule 10 owners: `Yao`, `Circuits/Uniform`, the hub `Yao/HybridProof` and its 67 helpers; 262 modules in the
  union of their closures):
  - **None of the 19 lies in any owner's closure.**
  - Each closure at B equals the closure at the #341 head and at M′, in module set and in every source blob (70/70 and 70/70).
  - So the earlier seal evidence carries over unchanged: Phase 2 and the integration-tip seals on M and M′.
- **#340** (owner `Pairing/Assumptions`, closure 58 modules):
  - **One** of the 18 relevant modules lies in its closure: **`Pairing/Group` (#331)**. Its blob (`b6464ece`) is the same at
    B, at the #340 head and at the #331 head.
  - The whole closure at B equals the closure at the #340 head, in module set and in every source blob.
  - So nothing under the owner changed. Because the brief asks for seals whenever such a module is in the closure, I ran the
    canonical seals on this owner only:

| Seal (`-DmaxErrors=0`) | Requests | rc | `error:` | `error(` | Install / EOF | Failing declarations |
|---|---|---|---|---|---|---|
| coe A (canonical) | 894 | 0 | 0 | 0 | yes / yes | none |
| coe B (`SEAL_EVAL=1`) | 895 | 0 | 0 | 0 | yes / yes | none |

  The collector's source and log, both probe sources, both seal logs and both summary rows are byte-identical to pair-bdh's
  in-house coe A/B at `916afc25`. The records differ only in `rev`.

## Restore

`$SP/dl-oleans` is back to snapshot `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`:
- 0 backup hash failures; 561 oleans restored; 222 new oleans and the Mathlib overlay deleted;
- `restoreplan --delete`: extra 0, changed 0, missing 0;
- **SNAPSHOT EQUAL**, with 1230 files and 0 empty directories;
- a fresh recheck snapshot is also equal, and `restoreplan` without `--delete` again gives 0 / 0 / 0.

I then removed the backup and the scratch worktree; the probe and seal sources had already been removed from it. The branch is
kept. `dl-oleans-2` and the other worktrees were not touched.

## Anomalies

None affecting the result.
1. **Records branch moved.** It gained 13 records-only commits during the job. No code path changed.
2. **Seal run despite an unchanged closure.** The literal seal-relevance test for #340 is positive (`Pairing/Group`), although
   that module is unchanged relative to the #340 head. The seals were run as instructed, and they reproduce the in-house
   result.

## Files

- `int-x-341-340-evidence.zip`, SHA-256 `b65ded6582c597e13c54ddd6bd2c3398c4dbe20a2e9f0881b71d6e6d6f2e6209`. It contains 1246
  files plus its own `SHA256SUMS` (SHA-256 `611cc75c0a63db8a4b106c5c776e13d900ca5e2e52c447331dd089fd84dc70db`), under
  `int-x-341-340/`:
  - `PROVENANCE.txt`;
  - `landing/` and `checks/`;
  - `order-b/`, `order-tip/`, `state/` and `plan-b/`;
  - `tree/` and `build-mathlib-extra/`;
  - `build-b/`, with every module log;
  - `records/`, `tree-final/` and `refs/`;
  - `admissions/` and `axioms/`;
  - `seal-relevance/`, `seals-340/` and `restore/`;
  - `tools-used/` and the run scripts.

  It was verified from a fresh extract: 1246/1246 OK, with an exact path set.
- `SHA256SUMS` covers the files of this directory.
