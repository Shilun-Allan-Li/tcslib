# Olean rebase of `dl-oleans-2`, then the first snapshot advance (merge of #341)

**Result.** The snapshot now sits at the merge of #341, and later jobs recompile only a PR's closure.
- `dl-oleans-2` was rebuilt from its old base `eff2dcd0` (snapshot `457ba704…`) to the records tip T, by import-closure keys.
  - It became the single snapshot directory `$SP/olean-snapshot`, as the olean snapshot procedure
    (`olean-snapshot-procedure.md`) requires.
- That snapshot was then advanced to the merge of #341, `a6d01b1b`, with the procedure itself: a `cp -al` copy,
  #341's closure rebuilt in the copy, then adopted.
- All builds had rc 0 with 0 errors, and the state checks are OK.
- Each snapshot rehashes 0 extra / 0 changed / 0 missing against its map.

The ruling is Seyoon's (2026-11-16, decision log, "rebase the olean snapshots"), followed by the procedure adopted the
same day. The work ran on 2026-11-16 and 2026-11-17 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. All records are in
`olean-rebase-evidence.zip`, and `SHA256SUMS` lists it and every entry.

## Current snapshot (the one jobs use)

| | |
|---|---|
| Directory | `$SP/olean-snapshot` (use it as `TCSLIB_OLEANS`, through a `cp -al` copy only) |
| T | `a6d01b1bd1a92e2ac0be9999689467fea7e4e77b` (Merge pull request #341) |
| Object map | `$SP/olean-snapshot.map-a6d01b1b.tsv`, SHA-256 **`954934494925e1c32d2fca23fe3250e5ae838f63b57a71ff0ad54c7ff039c111`** |
| Files manifest | `$SP/olean-snapshot.files-a6d01b1b.txt` (`snapshot.py` form), SHA-256 `73916186cd17031321e03634d2d9c2aed83646c96e6e29c56f0a434f0dbfd9d0` |
| Content | 1452 `.olean`: 1421 TCSlib/audits modules (the closure of root `TCSlib` and both `audits/*/Checks`) plus 31 PFR; no `.ilean`, no symlinks, no Mathlib overlay |

The register and the exact job recipe are in `../snapshots.md`. The forwarding note for the old tree name is
`$SP/dl-oleans-2.BASE.txt`.

## 1. Preflight
- **The tree** `$SP/dl-oleans-2` had 1230 files and snapshot SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, as required. It was byte-equal to DW-5's
  `snapshot-post.txt`.
- **Idle.** No process referenced the tree. `$SP/dl-oleans` was never touched; its running cross-build was left alone.
- **T.** `git fetch origin cryptography/pass-shelat-ch2-4` by name gave **T =
  `cd6070091380f2270568af850e3dda1081ca802e`**.
  - `git diff 7d47e675… T -- TCSlib TCSlib.lean audits lakefile.lean lake-manifest.json lean-toolchain` is empty
    (rc 0), so T's Lean equals the cross-built tree.
- **Worktree.** `$SP/wt-rebase2` was detached at T. It was sparse: non-cone `/*`, without `briefs/`, `dataset/`,
  `blueprint/`, `dep_graph.json` and the PDF. Its `.lake/packages` was symlinked to the repo's.

## 2. Rebase build at T (`olean-rebase-2/`)
The method is DW-5's, run with unmodified copies of its tools (`tools-used/`).
- **Order.**
  - `downorder.py` against `eff2dcd0` gives changed 192, down 715 and order 1353.
  - `closurecheck.py` shows the order is exactly the closure of root `TCSlib`, `audits/garg-ch1-3/Checks` and
    `audits/pass-shelat/Checks`: 0 missing and 0 extra.
  - All 1199 snapshot modules are in it.
- **State.** `stateplan.py init` at `eff2dcd0` keys 1199 modules; the result is byte-equal to DW-5's `state-init.json`.
- **Plan.** **715 to build** (561 snapshot oleans and 154 new) and **638 reused**.
- **Mathlib.** The overlay (3346 symlinks) plus NthRootLemmas (olean `c0a9cff0…`), the only missing Mathlib root.
- **Build.** `runner.py` through `scripts/lean_check_tree.sh`, one Lean process at a time.
  - **715/715 rc 0.** `error:` 0, `error(` 0, combined 0, and the substring "error" 0 (`build/per-module.tsv`).
  - Sorry warnings: 60, out of 421 warnings.
  - Time: 5823 s of module time, 22:04:12–23:41:16 UTC. Max RSS was 4.56 GB. `DetMod` took 1425 s.
- **State check.** `update` took 715 modules, and `check` over the 1353-module order gives **1353/1353 OK, RESULT OK**.
- **Snapshot at T.**
  - The overlay was removed (`restore/overlay-removal.txt`), leaving no empty directories.
  - `snapshot.py` gives 1384 files, SHA-256 `658bcbac…`.
  - restoreplan against it gives 0/0/0.
  - `basecheck.py`: an `init` at T over the new manifest equals the checked state for all 1353 modules (key and olean),
    **RESULT OK**.
  - Against the old snapshot, 1192 files are identical, 38 rebuilt oleans changed, 154 were added and none removed. PFR
    is identical.
- **Snapshot directory.** `dl-oleans-2` was renamed to `$SP/olean-snapshot`.
  - Map `olean-snapshot.map-cd607009.tsv`, SHA-256 **`73fac35ee25818653bdee00cf1a4d3b521ec1bdf4be4682109091502b7b57f84`**.
  - The rehash gave 0/0/0.
  - After the container restart (about 23:57 UTC) it was rehashed again: **0/0/0**.

## 3. Advance to `a6d01b1b` by the procedure (`olean-advance-a6d01b1b/`)
- **Tips.** `a6d01b1b` is the merge of #341.
  - `git diff c6faa7c5 a6d01b1b` over the Lean paths is empty.
  - The later records tips `3df1a658` and `42c445d3` are Lean-equal to it.
- **Copy.** `cp -al $SP/olean-snapshot $SP/olean-replay-a6d01b1b` gave 1384 files, all hard links.
- **Order.**
  - `downorder.py` against T gives changed 70, down 145 and order 1420.
  - That order omits `audits/garg-ch1-3/Checks`, which is not downstream of #341. The new `fullorder.py` gives the
    full closure, 1421 modules.
  - The plan over the full order gives **145 to build** (77 existing and 68 new) and **1276 reused**. This is the same
    build set as the downstream order.
- **Build.** The overlay and NthRootLemmas were added in the output only.
  - **145/145 rc 0**, with 0/0 errors and 0 "error" substrings. Sorry warnings: 21.
  - Time: 860 s, 00:06:28–00:20:49 UTC. Max RSS was 4.54 GB.
  - `update` took 145 modules, and `check` over the full order gives **1421/1421 OK**.
- **No write-through.**
  - All 145 rebuilt oleans have link count 1 (`checks/rebuilt-linkcount.txt`).
  - After the replay, `$SP/olean-snapshot` rehashed 0/0/0 against its T map (`checks/base-after-replay.out`).
- **Adopt.**
  - The overlay was removed from the output.
  - The map is `olean-snapshot.map-a6d01b1b.tsv`: 1452 entries, SHA-256 `95493449…`.
  - `basecheck.py` at `a6d01b1b` gives RESULT OK, over 1421 modules.
  - Against T: 1380 identical, 4 changed, 68 added and 0 removed. 73 of the 77 rebuilt existing modules came out
    byte-identical.
  - The T snapshot's oleans were deleted and the output renamed to `$SP/olean-snapshot`, at 00:21:51 UTC. The rehash
    gave **0/0/0** (restoreplan agrees).
- **The interrupted first attempt** is in `olean-advance-a6d01b1b-interrupted/`.
  - The container restart stopped it at 144/145, all rc 0, during `audits/pass-shelat/Checks`.
  - Its output was discarded unread, and the advance was redone from scratch with the same plan.

## Disk
- Free on `/`: **2311 MB** at the start (22:02 UTC). The lowest point was 2219 MB during the rebase build, and 3005 MB
  during the advance.
- **3137 MB** after cleanup. Other jobs' activity also moves this figure.
- No backup copy was made. The old snapshot's manifest is kept as
  `$SP/dl-oleans-2.snapshot-457ba704….txt` (also in the zip, `snapshots/`).

## Instructions for future job briefs
> Olean tree: never build in place. `cp -al $SP/olean-snapshot $SP/olean-replay-<job>` and pass that copy as
> `TCSLIB_OLEANS`. The base is T = `a6d01b1bd1a92e2ac0be9999689467fea7e4e77b`, map SHA-256 `95493449…c111`. Use
> `stateplan.py init <repo> <T> $SP/olean-snapshot.files-a6d01b1b.txt` and `downorder.py <repo> <rev> <T>`, and plan
> over `fullorder.py`. Follow `maintainer/snapshots.md` § Job recipe. Do not restore: discard the copy, or adopt it on
> merge.

Always check `snapshots.md` for the current row before citing T.

## Disclosures
- **Stale-file deletion.**
  - In the first advance attempt, my explicit loop to pre-delete the queued modules' `.olean`/`.ilean` in the copy was
    blocked by a tool safety check (`rm` on variable paths). It did not run, and was not worked around.
  - The deletion the procedure requires is done by `scripts/lean_check_tree.sh` itself. It runs
    `rm -f "$OL/$rel.olean"` before each compile.
  - No `.ilean` exists in any snapshot.
  - The evidence that no stale file survived and nothing was written through is the link counts, the state check and
    the base rehash above.
- **Changed restore target.** The old restore tools (`restore-tree.sh`, hard-link backups) do not apply any more.
  `dl-oleans-2` no longer exists as a name. Any brief that still cites it, or `457ba704…`, is stale.
- **Not committed.** Nothing was committed, pushed or `git add`ed. `$SP/dl-oleans` was not touched; it is left for the coordinator to retire.
- **The procedure document** cites `.ilean` and an object map. `snapmap.py` maps `.ilean` too, if one ever appears.

## Layout of `olean-rebase-evidence.zip`
- `olean-rebase-2/`: the rebase to T.
  - `tree/`, `order/`, `state/`, `plan/`, `build/` (per-module logs and `results.jsonl`), `build-mathlib-extra/`,
    `restore/`, `checks/`.
  - `tools-used/`: DW-5's tools unmodified, plus `run-build-rebase.sh`, `diskwatch-rebase.sh`, `closurecheck.py`,
    `basecheck.py` and `snapmap.py`.
- `olean-advance-a6d01b1b/`: the advance.
  - The same layout, plus `fullorder.py`, `run-build-advance.sh` and `diskwatch-advance.sh`.
- `olean-advance-a6d01b1b-interrupted/`: the stopped attempt and `INTERRUPTED.txt`.
- `snapshots/`: the old manifest (`457ba704…`), the maps and manifests for `cd607009` and `a6d01b1b`, and
  `dl-oleans-2.BASE.txt`.
