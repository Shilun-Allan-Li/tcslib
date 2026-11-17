# Olean snapshots

This is the register for `olean-snapshot-procedure.md`, the procedure beside this file. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

- **Snapshot directory:** `$SP/olean-snapshot`.
  - It is the olean root that `scripts/lean_check_tree.sh` reads as `TCSLIB_OLEANS`. It holds `TCSlib.olean`,
    `TCSlib/`, `audits/` and `PFR/`.
  - It holds every module of the closure of root `TCSlib` and both `audits/*/Checks`, as `.olean` only.
    `lean_check_tree.sh` writes no `.ilean`.
  - It has no Mathlib overlay, no symlinks and no other files.
- **Object map:** `$SP/olean-snapshot.map-<T8>.tsv`, one line `module<TAB>sha256` per file (`tools/snapmap.py`).
- **Files manifest:** `$SP/olean-snapshot.files-<T8>.txt`, in `snapshot.py` form. `stateplan.py init` and `restoreplan.py`
  read this one.

## Entries

| # | T (records commit) | Map SHA-256 | Modules (files) | Date (UTC) | Status |
|---|---|---|---|---|---|
| 0 | `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` (old base) | none: snapshot manifest `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` | 1199 (1230) | before 2026-11-16 | retired; manifest kept as `$SP/dl-oleans-2.snapshot-457ba704….txt` |
| 1 | `cd6070091380f2270568af850e3dda1081ca802e` | `73fac35ee25818653bdee00cf1a4d3b521ec1bdf4be4682109091502b7b57f84` | 1353 (1384) | 2026-11-16 23:42 | superseded; oleans deleted at adoption of #2; map and manifest kept |
| 2 | `a6d01b1bd1a92e2ac0be9999689467fea7e4e77b` (merge of #341) | `954934494925e1c32d2fca23fe3250e5ae838f63b57a71ff0ad54c7ff039c111` | 1421 (1452) | 2026-11-17 00:21 | superseded; oleans deleted at adoption of #3; map and manifest kept |
| 3 | `cf7d28f7159b46033e8b8ae170954f9575e5d145` (merge of #351) | `e9dfbfddfd6ca253f9fd5ee6c3efe868f8614083794312c89d32032564fea53d` | 1422 (1453) | 2026-11-17 03:02 | superseded; oleans deleted at adoption of #4; map and manifest kept; evidence `olean-snapshot-3-adopt/` |
| 4 | `463f224414ab7615e54104be353bfcda9dfceda7` (merge of #352) | `6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7` | 1422 (1453) | 2026-11-17 | superseded; oleans deleted at adoption of #5; evidence `olean-snapshot-4-adopt/` |
| 5 | `3f540c22360c869069a0fba684e23ce6f3cb20db` (merges of #340, #346) | `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9` | 1427 (1458) | 2026-11-17 | superseded; oleans deleted at adoption of #6; map and manifest kept; evidence `olean-snapshot-5-adopt/` |
| 6 | `8060f6b767da9e43d1c1f6d32c55b97758b80bd8` (merge of #357) | `0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf` | 1432 (1463) | 2026-11-17 | superseded; oleans deleted at adoption of #7; map and manifest kept; evidence `olean-snapshot-6-adopt/` |
| 7 | `a1fa7b652f0c235b54fc067e09b669e983daaf71` (merge of #355, with #347; Lean = TS2 `13fc8060`) | `5105c5149901c5c4375083c1f6ad998b70c909905e4fbf430c9e96117a0f7300` | 1434 (1465) | 2026-11-17 | superseded; oleans deleted at adoption of #8; map and manifest kept; evidence `olean-snapshot-7-adopt/` |
| 8 | `2dd2e60ed0cdd4681a7bd12fe4a86825e98db664` (merge of #365; Lean = `9710ac7d`, #7's T × `5eaddd17`) | `286777672d4e61f1be0ba98fca72b01d8cd9aa281eb811d100d7fe499679c49c` | 1434 (1465) | 2026-11-17 | **current**; evidence `olean-snapshot-8-adopt/` |

- **#1** was built from #0 by closure keys (`dl-oleans-2`): 715 modules built, 638 reused.
  - Every module had rc 0, with 0 `error:` and 0 `error(`.
  - The state check gave 1353/1353 OK. The rehash gave 0 extra / 0 changed / 0 missing, before and after the
    container restart.
  - Its files manifest has SHA-256 `658bcbac…`.
- **#2** is #1 advanced by this procedure.
  - The output was a `cp -al` copy of #1. #341's closure was rebuilt: 145 modules built, 1276 reused.
  - Every module had rc 0, with 0/0 errors. The state check gave 1421/1421 OK over the full closure.
  - #1 rehashed 0/0/0 after the replay, so nothing was written through.
  - The output was adopted by renaming, and it rehashes 0/0/0.
  - Its files manifest has SHA-256 `73916186…`.
- The records tip `42c445d337dbde65826f762b2230481a093fd8a7` (2026-11-17) is Lean-equal to #2.
- Evidence: `olean-rebase-dl-oleans-2/`.

## Job recipe (replay on the current snapshot)

The tools are in `olean-rebase-dl-oleans-2/olean-rebase-evidence.zip`, under `olean-advance-a6d01b1b/tools-used/`. Run
them with `python3 -I` and `PATH=$HOME/.elan/bin:$PATH`. `R` is the repo, `T` the current entry, `REV` the PR head or its
`git merge-tree --write-tree` tree, and `W` a worktree or export at `REV` with `.lake/packages` symlinked to the repo's.

1. **Copy.** `cp -al $SP/olean-snapshot $OUT`, where `$OUT=$SP/olean-replay-<job>`. The copy costs almost no disk.
2. **Overlay, in `$OUT` only.**
   - `mloverlay.sh $OUT`, then `mathlibextra.sh $OUT Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas <log>`.
     The olean must be `c0a9cff0…`.
   - Never add the overlay to the snapshot.
3. **Plan.**
   - `stateplan.py init $R $T $SP/olean-snapshot.files-<T8>.txt state.json`.
   - `downorder.py $R $REV $T order` gives the PR's downstream.
   - `fullorder.py $R $REV full-order.txt` gives the closure of root and both Checks.
   - `stateplan.py plan $R $REV full-order.txt state.json plan` gives `plan/queue.txt`.
4. **Build.**
   - `runner.py $W plan/queue.txt $OUT <logdir>` runs one Lean process per module through `lean_check_tree.sh`
     with `TCSLIB_OLEANS=$OUT`.
   - The checker removes each module's stale `.olean` before compiling it, which unlinks the hard link. No `.ilean`
     exists.
   - Never write into an existing file of `$OUT` in place (`cp` over it, `>`); unlink it first.
5. **Accept.**
   - `permod.py` must give rc 0 and 0 `error:`/`error(` for every module.
   - `stateplan.py update`, then `check` over `full-order.txt`, must give `RESULT OK`.
   - Every rebuilt `.olean` must have link count 1.
   - `snapmap.py verify $SP/olean-snapshot <current map>` must still give 0/0/0.
   - Seals, axiom probes and controls run against `$OUT`.
6. **Adopt, on merge,** when the procedure's step-3 diff is empty. Otherwise discard `$OUT`.
   - Remove `$OUT/Mathlib`.
   - Run `snapmap.py make $OUT $SP/olean-snapshot.map-<new8>.tsv` and
     `snapshot.py $OUT $SP/olean-snapshot.files-<new8>.txt`.
   - The `basecheck.py` of an `init` at the new T against the checked state must give `RESULT OK`.
   - Delete `$SP/olean-snapshot`, then `mv $OUT $SP/olean-snapshot`.
   - Run `snapmap.py verify` and require 0/0/0.
   - Add the row above.
