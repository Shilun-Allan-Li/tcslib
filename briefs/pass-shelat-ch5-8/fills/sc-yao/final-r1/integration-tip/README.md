# sc-yao (#341) · integration build on the records tip

**Result for M: clean.** The landing head `e9b03c43` merged into the current records tip builds with 0 errors in both
forms through root `TCSlib` and both `Checks`. The whole-order state check passes. `yaoProtocol_hbcSecure` now uses only
the standard three axioms. Sorry warnings go from 229 at the tip to 227. The Yao seals are byte-identical to Phase 2's.

**Result for M' (Gate 42 landing edits, head `355a0288`): clean.**
- The 20 affected modules rebuild with rc 0 and 0 errors in both forms; the state check passes.
- `RunWithHost.acc_poly`'s new body elaborates, so no fallback body was needed. Its axioms are standard.
- All four RunWithHost seals give 0 errors.

**`dl-oleans-2`** was restored to snapshot `457ba704…`: SNAPSHOT EQUAL; extra 0, changed 0, missing 0.

The records branch gained 10 records-only commits during the job (`f22e0f67` → `c5eb7cf4`, and origin `f6f295a6`).
`TCSlib`, `TCSlib.lean`, `audits`, `scripts` and the lake files are unchanged across them, so M's code is still "current
tip + #341".

Date: 2026-11-16 UTC. Working directory: `$SP/dl-review/sc-yao-r1/int-tip/`, where `$SP` is this session's scratchpad.
All of it is in `integration-tip-evidence.zip` under `int-tip/`: SHA-256
`4d24501bca1d67a8cf8905448acb77b161a61a45e8d38f72f14dea2fca95d6d8`, 989 entries. `SHA256SUMS` lists every entry, then
the zip itself. Verified from a fresh extract: all 989 entries OK, with an exact path set.

## Inputs
- **Records tip** `T` = `f22e0f6798815b9263893e61928b4f16452f74ee`. Its `TCSlib`, `TCSlib.lean`, `audits`, `scripts`
  and lake files are the same git objects as in `201bf57a` (#324 merged) and in the int-x cross-built tree `199ea4c6`
  (`merge/merge-facts.txt`). `7d532e20` (#327) and `201bf57a` are ancestors of `T`.
- **#341 landing head** `H` = `e9b03c437aca251846430ff23b40ee5ff3d3347a`, built and reviewed in Phase 2 on `f9fda8fe`.
  `merge-base(T, H)` = `f9fda8fe`.
- **Olean tree** `$SP/dl-oleans-2` only. The other job's `$SP/dl-oleans` was not touched.

## Scratch merge M
- `git merge --no-ff --no-gpg-sign` of `H` into `T`, on the local branch `int/sc-yao-tip`, in a new sparse worktree
  (`$SP/wt-int-sc-yao-tip`; non-cone `/*`, without `briefs/`, `dataset/`, `blueprint/` and `dep_graph.json`).
  Author and committer dates are fixed at 2026-11-16T00:00:00Z. Nothing was pushed.
- **M** = `e327a5f284c043493e1b405b282e9abc5e002b61`, tree `741bafe2ce706adbf697ab893bf4bc28e7eb1d7d`, parents `T`, `H`.
  `git merge-tree --write-tree T H` gives the same tree, with rc 0.
- `git diff --raw --no-abbrev 201bf57a M -- TCSlib TCSlib.lean audits` is byte-identical to the same diff for
  `f9fda8fe e9b03c43`: 70 paths (68 added, 2 modified), with the same modes and old and new blobs. Over the whole tree, M
  differs from `T` in exactly these 70 paths (`merge/`).

## Build (step 4)
- **Method:** Phase 2's, with unmodified copies of its tools (`tools/`). `downorder.py` against the snapshot base
  `eff2dcd0` gives changed 250, downstream 772 and order 1410. `stateplan.py init` over the snapshot keys 1199 modules,
  and `state/state-init.json` is byte-equal to Phase 2's. `stateplan.py plan` at M gives 772 to build (561 snapshot
  modules with a changed closure key plus 211 new) and 638 to reuse. The queue equals `down.txt` and includes root
  `TCSlib`, `audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`.
- **Backup:** the 561 snapshot oleans were hard-linked into `$SP/dl-sctip-backup`; all 561 hashes were checked against
  the snapshot. The 211 new modules are listed in `tree/new-oleans.txt`.
- **Mathlib overlay:** `mloverlay.sh` (3346 symlinks) and NthRootLemmas via `mathlibextra.sh`. Mathlib is `029db123`;
  the olean is `c0a9cff0…`, as in Phase 2 and int-x. It is the only one of the 377 Mathlib roots missing from the shared
  build.
- **Runner:** `scripts/lean_check_tree.sh` (byte-equal to the repository's) through `tools/runner.py`, one Lean process,
  with `TCSLIB_OLEANS=$SP/dl-oleans-2`. No lake command and no cache get were used.
- **Result:** 772/772 rc 0. `error:` 0, `error(` 0, combined 0, and no log contains the substring "error"
  (`build-m/permod.out`, `per-module.tsv`). Every log hash equals its record.
  - Runtime: 6721 s of module time, from 17:03:09 to 18:55:11 UTC. Peak RSS was 4.30 GB.
  - Disk: the lowest free space seen was 1538 MB (`build-m/df.log`). At about 17:46 another job took about 770 MB.
  - Sorry warnings: 89. This is X1's 91 minus `Yao.lean`'s 2.
  - sc-yao's 70 modules all give rc 0, 0 errors and 0 `sorry`. The only warning is in `BobIO`: line 211,
    an unnecessary `simpa`, as in Phase 2.
  - `ComposeSecurity` (#324) and `SequentialZK` (#327) both give 0 `sorry`.
- **References** (`refunion2.py` against Phase 2's `build-head` and int-x's `records-final`): all 772 oleans are
  byte-identical, in both source and olean, to at least one reference.
  - Two modules have a same-source reference with a different olean: `YaoReal` and the hub `SecureComputation`. In both
    cases that reference is int-x's X1, which does not contain sc-yao. Both are SAME as Phase 2. This is expected, since
    their import closures differ from X1's.
- **Closure keys against Phase 2:** 1327 of the 1356 common modules have equal keys. These include `Yao`,
  `Yao/HybridProof`, all 68 helpers, `Uniform` and `audits/garg-ch1-3/Checks`. Only the 29 #327/#324-affected modules
  differ: `YaoReal`, `ComposeSecurity`, the hub, the ZK/Composability modules, root `TCSlib` and
  `audits/pass-shelat/Checks` (`checks/closure-keys-vs-phase2.txt`).
- **State check:** `stateplan.py update` took all 772 modules. `stateplan.py check` at M over the 1410-module order gives
  1410/1410 OK, RESULT OK (`build-m/statecheck.txt`).

## Axioms (step 5)
The probes were `AxiomsLand` (Phase 2's, byte-identical) and `AxiomsTipExtra`, which covers every `otProtocol_*` result
plus `#admitted` traces and uses AxiomsLand's elaborator verbatim. Both ran through `runner_full.py` (rc 0, 0 errors).
Summaries are in `axioms-summary-*.txt`; the diff against Phase 2 is in `axioms-vs-phase2.diff`.

| Constant (`TCSlib.Cryptography.SecureComputation.`…) | Axioms on M | Phase 2 |
|---|---|---|
| `yaoProtocol_hbcSecure` | propext, Classical.choice, Quot.sound | + sorryAx (through `hbcSecure_compose`) |
| `yaoHybrid_hbcSecure` | propext, Classical.choice, Quot.sound | same |
| `yaoHybrid_polyTime` | propext, Classical.choice, Quot.sound | same |
| `yaoHybrid_simulators` | propext, Classical.choice, Quot.sound | same |
| `yaoSeed_good_whp` | propext, Classical.choice, Quot.sound | same |
| `HybridProtocol.hbcSecure_compose` | propext, Classical.choice, Quot.sound | + sorryAx |
| `otProtocol_P`, `_V`, `_rounds`, `_verifierFirst`, `_isOT`, `_outV`, `_outP`, `_simulators`, `_polyTime`, `_hbcSecure` | propext, Classical.choice, Quot.sound | `_polyTime`, `_simulators` same (others not probed) |

- **`#admitted`:** no closure has a direct `sorryAx` user.
  - `yaoProtocol_hbcSecure` has 21453 constants (20865 in Phase 2, which had 1 admitted constant,
    `hbcSecure_compose`).
  - `hbcSecure_compose` has 17721, the same as int-x X1.
  - `yaoHybrid_polyTime` has 9168, `yaoHybrid_simulators` 20202, `yaoHybrid_hbcSecure` 20475 and `yaoSeed_good_whp`
    17757, all as in Phase 2.
  - The `otProtocol_*` results have 16652, 7298 and 16742 (`_simulators`, `_polyTime`, `_hbcSecure`).
- **Owners census:** 1492 stored constants, 0 nonstandard, 27 simp lemmas, 11 instances. The 1492 `AX` rows and the
  `#check @…FakeSimulator.Data.make` output are identical to Phase 2's. The rest of the AxiomsLand log differs from
  Phase 2's only in the two `sorryAx` lines above.

## Admissions (step 6)
The int-x method: `tipcensus.py`, with each module's `declaration uses 'sorry'` count taken from rc-0 records with the
module's source. The record sets are M's build and int-x's `records-final` (`admissions/`).
- **Tip** (`201bf57a`, whose Lean is `T`'s): 229. Per module, this is identical to int-x's X1 census.
- **M:** 227 over 1410 modules with a record. The only change is `SecureComputation/Yao` 2 → 0. The 68 new modules all
  have 0, and no module was removed.
- The same 34 modules outside root `TCSlib`'s closure have no record at either revision. There are no disagreeing
  records.

## Rule 10 supplement: Yao seals (step 7)
- **Method:** Phase 2's `CollectLand` collector was rerun on M with `-DmaxErrors=0`. Its log is byte-identical to
  Phase 2's (CAT-COUNT 3991, one projection-coercion instance, `FinDist.instCoeFunForallReal`).
- **Generation:** `mkseals_sy.py` with the archived Gate 06/10 harness, coe variant (`SEAL_COE_FILE`) and
  `SEAL_CHUNK=2000`. A is the default; B uses `SEAL_EVAL=1`.
  - This gives 3046 requests for A and 3047 for B. Both probe files are byte-identical to Phase 2's run probes, and
    their records differ only in `rev` and `probe_module`.
- **Runs:** `runner_full.py` (`lean -DmaxErrors=0`, no `-o`); summaries from `sealsum.py` with Phase 2's
  `touched-head.json`, since `Yao.lean` has the same blob `47d4c268` at `H` and at M.

| Seal | Requests | rc | `error:` | `error(` | Declarations | Phase 2 |
|---|---|---|---|---|---|---|
| coe A | 3046 | 0 | 0 | 0 | none | 0 |
| coe B | 3047 | 1 | 24 | 0 | 9: `yaoCoins_eval`, `yaoHybrid`, `yaoHybrid_answersB_getD`, `yaoHybrid_callA`, `yaoHybrid_callB`, `yaoHybrid_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoSeed_good_whp` | 24 in the same 9 |

- Install and EOF records are present in both logs. After the probe directory is renamed (`ScYaoSeal_coe` →
  `ScYaoTipSeal_coe`), both logs are byte-identical to Phase 2's, so the error positions and messages are identical
  (`seal-compare-phase2.txt`).
- There is no difference to explain. `Yao.lean`'s entire import closure is unchanged by #327 and #324: `Yao.lean` does
  not import `ComposeSecurity`, and only `YaoReal` does. Phase 2's attribution (`PolyExpr.eval` conversions or cascades)
  therefore carries over unchanged.

## Space (step 2)
Phase 2's `seal-runs`, `seals-coe`, `seals-strict`, `probe-sources-run`, `control-runs`, `controls-coe` and
`controls-strict` held 437 files, about 400 MB. Every one is in the committed `review-evidence.zip` (`d3f7c3da…`): the
same path under `phase2/`, the same SHA-256 in the zip entry and the same SHA-256 in `evidence-SHA256SUMS`. There were
no symlinks or special files. The directories were then deleted (`space/zipcover.txt`, `space/deleted.txt`).

## M' — Gate 42 landing edits (coordinator extension)
- **Head:** `355a0288d56290e8c984228cbc1824187029e456`, three commits on `e9b03c43`:
  - `26f0b77b` LE-reuse-2;
  - `3e99eb80` LE-refs;
  - `355a0288` LE-steps.

  Each carries an SSH signature header. The signatures are not verifiable here, because no `allowedSignersFile` is
  configured. In total, 9 files change, with 69 insertions and 3 deletions, and there are no import changes.
- **Scratch merge:** `git merge --no-ff --no-gpg-sign` of `355a0288` into `T`, on the local branch `int/sc-yao-tip-le`, in
  a second sparse worktree with the same dates.
  - **M'** = `061ad60cdc485e6248eeadfc2de165a227f7cd99`, tree `84c5381ba7188069f296f899efff9104f9b9bbe0`.
    `merge-tree` gives the same tree.
  - `git diff --raw 201bf57a M'` over the Lean paths equals `git diff --raw f9fda8fe 355a0288` (70 paths).
  - `git diff --raw M M'` over the whole tree equals `git diff --raw e9b03c43 355a0288` (9 paths)
    (`mprime/merge/merge-facts.txt`).
- **Build:** done on top of M's built state; nothing was restored in between.
  - The order at M' is byte-equal to M's (1410 modules). `stateplan.py plan` against M's updated state gives 20 to
    build and 1390 to reuse. The 20 are the 9 edited helpers and their downstream: `AliceProgram`, `DescriptionDecoder`,
    `GarbledRun`, `BobProgram`, `FakeSimulator`, `SelectedStepSecurity`, `GateHybridSecurity`, the hub
    `Yao/HybridProof`, `Yao`, `YaoReal`, the `SecureComputation` hub and root `TCSlib`. `audits/*/Checks` keep their
    keys.
  - All 20 are in M's queue (4 in the snapshot backup and 16 in `new-oleans.txt`), so the restore covers them.
  - **Result:** 20/20 rc 0. `error:` 0, `error(` 0 and substring 0. There are 0 `sorry` and 1 warning, the
    unnecessary `simpa` in `BobIO`, now at line 218 (moved from line 211), as expected.
  - 159 s of module time, 19:05:49–19:08:28 UTC, peak RSS 4.31 GB. `Yao.lean` is 1195 lines.
  - **State check:** `update` took all 20, and `check` at M' gives 1410/1410 OK, RESULT OK
    (`mprime/build/statecheck.txt`).
  - **Admissions:** `tipcensus.py` at M' gives 227, the same as M in every module.
- **Axioms** (`AxiomsLand` unmodified, plus `AxiomsLE`; rc 0, 0 errors):
  - `yaoProtocol_hbcSecure`, `yaoHybrid_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators` and `yaoSeed_good_whp`
    use propext, Classical.choice and Quot.sound. No closure has a direct `sorryAx` user.
  - Closures: `yaoHybrid_polyTime` 9172, `yaoHybrid_hbcSecure` 20479 and `yaoProtocol_hbcSecure` 21457, each 4 more
    than at M (the reused `MajLoop.acc_poly` chain). `yaoHybrid_simulators` (20202) and `yaoSeed_good_whp` (17757) are
    unchanged.
  - `YaoHybridProof.RunWithHost.acc_poly` uses propext, Classical.choice and Quot.sound, and its closure (4610) has no
    `sorryAx` user. `Complexity.StateLoop.MajLoop.acc_poly` uses the same three.
  - The `#check` output of `acc_poly`, `MajLoop.acc_poly`, `RunWithHost.acc_eq` and `MajLoop.acc_eq` confirms that the
    statement is unchanged and that the two readers state the same predicate.
  - The owners census is unchanged: 1492 stored constants, all standard, with the same `AX` rows as M
    (`mprime/axioms-vs-M.diff`).
- **Seals on `Yao/HybridProof/RunWithHost.lean`:** `CollectLand` was rerun at M' (CAT-COUNT 3991; coe names unchanged).
  Seals were made with `mkseals_sy.py` as above and run with `-DmaxErrors=0`.

| Variant | Requests | rc | `error:` | `error(` | Install / EOF |
|---|---|---|---|---|---|
| coe A (canonical) | 844 | 0 | 0 | 0 | yes / yes |
| strict A | 844 | 0 | 0 | 0 | yes / yes |
| coe B | 845 | 0 | 0 | 0 | yes / yes |
| strict B | 845 | 0 | 0 | 0 | yes / yes |

  - Phase 2's coe A on this file at `e9b03c43` also had 844 requests and 0 errors.
  - The coe and strict probes are byte-identical, because no projection-coercion instance is in this file's closure.
  - `Complexity.StateLoop.MajLoop.acc` is a sealed row in all four variants. The new body reaches it only through the
    readers `acc_eq` and `MajLoop.acc_eq`, and it passes under the seal. `RunWithHost.acc` is the file's own definition,
    so it is outside the sealed import closure by design.
- **Fallbacks:** neither of the two fallback bodies in `26f0b77b`'s message was tried, because the committed body
  elaborates. Nothing was committed.

## Restore (step 8)
`tools/restore-tree.sh` is Phase 2's `restore-tree.sh` with only the backup directory, the evidence directory and the
order path changed (`tools/restore-tree.phase2.sh`). It was run after M' (`restore/restore-log.txt`).
- **Backup:** hash failures 0. Of the 561 backed-up oleans, 40 were restored from the backup. The other 521 rebuilt
  oleans were already byte-identical to the snapshot.
- **Deletions:** the 211 new oleans were deleted, each hash logged. The Mathlib overlay was deleted: 3346 symlinks and
  NthRootLemmas.
- **Snapshot:** `tree/snapshot-post.txt` has 1230 files, 0 empty directories and SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, byte-equal to `tree/snapshot-pre.txt`
  (**SNAPSHOT EQUAL**). `restoreplan.py` reports extra 0, changed 0 and missing 0 (`restore/plan/`).
- **Independent recheck:** a fresh snapshot (`restore/snapshot-recheck.txt`) is equal to the pre-snapshot, and
  `restoreplan.py` again reports extra 0, changed 0 and missing 0 (`restore/verify-plan/`). There are no symlinks, no
  `Mathlib/` and no empty directories (`restore/restore-verify.out`).
- The script's own `tee restore/restore.out` could not open its file, because `restore/` is created by the script. This
  is the same quirk int-x recorded; the lines are in `restore-log.txt` and `restore-verify.out`.
- **Cleanup** (`cleanup.txt`): the backup, the probe directories, both scratch worktrees and the temporary extracts were
  removed. The local branches `int/sc-yao-tip` (M) and `int/sc-yao-tip-le` (M') are kept; neither has an upstream, and
  nothing was pushed. No commit was made on `/home/user/tcslib`.
  - A first combined cleanup command was refused by the built-in safety check on variable-expanded `rm` targets, and
    nothing in it ran. The removals were then made with literal paths, the form the check names as safe.

## Layout of the zip (`int-tip/`)
- `merge/`, `mprime/merge/`: merge facts and raw diffs.
- `order-m/`, `plan-m/`, `state/`, `tree/`: inputs, state and snapshots.
- `build-mathlib-extra/`: the Mathlib overlay and NthRootLemmas.
- `build-m/`: per-module records, logs, `permod`, the state check, `refunion` and `df.log`.
- `checks/`: closure keys against Phase 2.
- `probe-src/`, `probe-runs/`, `axioms-*`: axiom probes.
- `admissions/`: the sorry census.
- `seals-coe/`, `seal-runs/`, `seal-sum-*`, `seal-compare-phase2.txt`: Yao seals.
- `mprime/`: M' order, plan, state, build, probes, census and RunWithHost seals.
- `restore/`, `space/`, `cleanup.txt`: restore, space and cleanup records.
- `tools/` with `run-build-m.sh`, `tip-probes.sh`, `mprime/*.sh` and `diskwatch.sh`: every script that was run.
  - New scripts: `zipcover.py`, `axsum.py`, `mkevidence.py`, and the probes `AxiomsTipExtra.lean` and `AxiomsLE.lean`.
  - Everything else is an unmodified copy of Phase 2's tools.
