# Olean snapshot #11: adoption at the #377 merge (2026-11-18)

- **New T:** `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (merge of #377, `land/gsw-6b-statements`, head
  `e8553378636dc896f36fc2a5ab23c8336dbfcecb` (LE-g46b), into `cryptography/pass-shelat-ch2-4` at `f9467816`).
  - **Lean change since #10's T `cf6a2266`:** #376 (merge `d6dee3d0`) and #377. That is 13 Lean paths: 9 new GSW/LWE
    modules, `GSW.lean`, `LWE.lean` and `LWE/BitEncoding.lean` modified, plus one records-only file
    (`replay/lean-diff-T10-M.txt`).
  - **Prospective tree:** `git merge-tree --write-tree f9467816 e8553378` = `845bdc98…`, the merge commit's own tree.
    The merge and the head have the same `TCSlib` tree `949dfd63`. `TCSlib.lean`, `audits`, `scripts`, `lakefile.lean`,
    `lean-toolchain` and `lake-manifest.json` are blob-equal too (`replay/R.txt`).
  - **Step-3 diff** (`*.lean`, `lean-toolchain`, `lake-manifest.json`, `lakefile.lean`) of the merge against the head:
    **one path, `briefs/io-components/sampler-bridge/Skeleton.lean`** (`step3-diff.txt`).
    - It is a records file. Records commit `04fb2e38` added it on the first-parent side; it is not in #377.
    - It lies outside the `TCSlib` lean_lib, outside the replay's export paths and outside `fullorder.py`'s closure
      (`TCSlib`, `TCSlib.lean`, `audits`). It is one of many records-only `.lean` files under `briefs/`.
    - The same diff over the replay's export paths (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, `lakefile.lean`,
      `lean-toolchain`, `lake-manifest.json`) is **empty** (`step3-diff-export-paths.txt`).
    - The full order at T equals the replay's byte for byte, and the replay's checked state gives RESULT OK at T.
      So the step-3 condition holds for every built path.
  - **Later commits:** at the swap the branch tip was `9b92d4ff`; at the end of the job it was `39f5651b`. Both are
    records only. The step-3 diff from T to `39f5651b` is empty (`tip-since-T-diff.txt`).
- **Source:** LE-g46b's audited replay `$SP/olean-replay-6b-stmt-g46b` of `e8553378`. It is a `cp -al` of
  `olean-replay-6b-stmt-g46` (LE-g46, `7563734a`, map `65ca0263…`), which goes back through `olean-replay-6b-stmt` and
  `olean-replay-6b-o2` to snapshot #10. LE-g46b rebuilt 6 modules and reused 1450 (`replay/plan.out`).
  - LE-g46b's checks: 6 modules with rc 0, 0 `error:`/`error(` (`replay/permod.out`). The export was blob-exact, 1608
    files (`replay/export.txt`). Link check: 6 rebuilt oleans at link count 1 (`replay/linkcheck-end.txt`). State
    check at `e8553378`: 1456 OK (`replay/statecheck-end.out`). #10 rehashed 0/0/0 (`replay/snap-verify-end.txt`).
  - **Before adoption** the tree rehashed against its recorded no-`Mathlib/` map (`e7bb03b4…`): 1487 files,
    0 extra / 0 changed / 0 missing, no symlink outside `Mathlib/`, 3346 `Mathlib/` symlinks, NthRootLemmas `c0a9cff0…`
    (`replay-verify.out`).
  - Its checked state is LE-g46b's `state.json`, SHA-256 `5313731b…`. Over the 1456-module order at T (`29e7fbee…`,
    `fullorder.py`, byte-equal to LE-g46b's `full-order.txt`) it gives RESULT OK at T and at `e8553378`
    (`replay-statecheck.out`).
- **Snapshot #10 at retirement:** 0/0/0 against `84d88738…` (`v10-final/`).
- **Adoption:**
  - The `Mathlib/` overlay was removed: 3346 symlinks and the overlay NthRootLemmas olean. That olean had link count 4;
    its other links are the superseded trees.
  - Map `olean-snapshot.map-bff0567b.tsv`, SHA-256 `e7bb03b4ba71a4d8f280b2fc62400b4d7cbda2b7a46c18ba9fe1cb6a488867d0`,
    byte-equal to LE-g46b's output map. 1487 entries: TCSlib 1454, audits 2, PFR 31.
    - Against #10: 9 modules are new (the 9 new source files) and 4 differ (`Homomorphic`, `GSW`, `LWE`,
      `LWE/BitEncoding`) (`map-vs-s10.out`).
  - Files manifest SHA-256 `463c88696a64539341b8f79da270d69c35c5be167f01b30d521fc0e9be4b0b13`, 1487 files.
- **basecheck:** init at `bff0567b` (1456 modules; `state-init-bff0567b.json.gz`, JSON `3f86c2a5…`) against the
  replay's checked state: **RESULT OK** (`basecheck.out`). Build revs over the order: 1428 at `cf6a2266`, 14 at `04ba2446`,
  5 at `680be9fa`, 3 at `7563734a`, 6 at `e8553378`.
- **Swap:**
  - Before the overlay removal, before the swap and before the deletions, a `/proc` scan found no process using the
    trees (`procscan-pre-*.txt`, `tools/procscan.sh`). The one `lean` process running each time was the S2-A D2 job,
    on `$SP/s2a-d2/tree`.
  - #10's directory was **renamed to `$SP/olean-snapshot-10`**, not deleted (see below). The replay tree was moved to
    `$SP/olean-snapshot` (`swap.txt`).
  - The rehash gave **0/0/0** (`v11/`). The files manifest recomputed after the move is byte-equal. A `stateplan check`
    of the new snapshot at T against the init state gave 1456/1456 OK (`v11-statecheck.out`). #10 at its new path still
    rehashes 0/0/0 (`v10-retired/`).
  - #10's map and files manifest are kept in `$SP`. Command output is in `outputs.txt`.
- **#10's oleans kept, a deviation from procedure step 3's "delete":**
  - Link census, `tools/linkcensus.py` (`replay/linkcensus-s10.txt`, `replay/s10-only-holders.txt`): every one of #10's
    1478 oleans has link count > 1, so deleting them would free 0 bytes. 1459 are inodes of the new snapshot.
  - The other 19 (`TCSlib`, the GSW/Regev/LWE modules #376/#377 rebuilt) are held by the live S2-A trees.
    `olean-base-s2a` holds all 19; `olean-replay-s2a-d1` and `$SP/s2a-d2/tree` hold 15 of them.
  - The S2-A D2 job's `tools/rehash.sh` also rehashes `$SP/olean-snapshot` against #10's map `84d88738…`. After this
    swap that path holds #11. The job's #10 rehash should point at `$SP/olean-snapshot-10`.
  - Delete `$SP/olean-snapshot-10` once S2-A D2 no longer needs it.
- **Superseded trees deleted** after a clean `/proc` scan (`procscan-pre-delete.txt`, `deleted-trees.txt`):
  `olean-replay-6b-o2`, `olean-replay-6b-stmt` and `olean-replay-6b-stmt-g46`.
  - Their evidence is recorded: maps in `$SP/g6b-p2/output-map` and `$SP/le-g46-work`, and the committed LE-g46/LE-g46b
    evidence zips.
  - None is adoptable: #377's merge contains #376. Their link census is in `replay/linkcensus-superseded.txt`.
  - #11 rehashed 0/0/0 afterwards (`v11-after-delete/`).
  - Replay trees left: `olean-replay-s2a-d1` (S2-A, in use, untouched) and `olean-snapshot-10`.
- Free disk: 4717 MB before, 4741 MB after (`df.txt`; `df -m`). No `lake`, no `lean`, no cache get. Nothing committed.
