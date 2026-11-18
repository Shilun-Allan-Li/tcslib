# Olean snapshot #9: adoption at the #366 merge (2026-11-18)

- **New T:** `523a00a62b8ab5a6b4310f670d55ab99d4d8c5fb` (merge of #366, `land/gsw-6a-fills`, head
  `bae0d84d35bedd876bcbd7af80c0a333db766237`, into `cryptography/pass-shelat-ch2-4`).
  - **Prospective tree:** the head's tree `fbba5d383d28edf509b68b30199ca276940033ca`. #8's T `2dd2e60e` is an ancestor of
    the head, and `git merge-tree --write-tree 2dd2e60e bae0d84d` gives that tree. LE-g50d recorded the same for the
    then tip (`68718aeb…`, Lean-equal to `fbba5d38`).
  - **Step-3 diff** of the merge against that tree (`*.lean`, `lean-toolchain`, `lake-manifest.json`, `lakefile.lean`):
    empty (`step3-diff.txt`). From #8's T to the merge, 23 Lean files change (13 new, 10 modified, all in
    `Complexity/BranchingPrograms`, `Complexity/CircuitComplexity` and the two root imports).
  - **Later commits:** at the swap the branch tip was `2bff71775d5039e2e23f48b316d6d69b962e03dc`. Between T and that tip is
    the #368 merge `cf6a2266`, whose Lean change is exactly #368's two files (`tip-since-T-diff.txt`). The next commit is
    records only. #368 is replayed on this snapshot and adopted as #10 (`olean-snapshot-10-adopt/`).
- **Source:** LE-g50d's replay `olean-replay-6a-land9` of #366 at `bae0d84d`, a `cp -al` of `olean-replay-6a-land8`
  (itself a `cp -al` of `olean-replay-6a-land7`, #366 replayed on #7 + #365), with 20 modules rebuilt
  (`briefs/lattice-gsw/phase6/fills-final-r1/le-g50d-evidence.zip`, `4e5908fe…`).
  - Before adoption it rehashed against its recorded no-`Mathlib/` map (`9bb4a0d093a7…`, the copy in the job's work
    directory, byte-equal to the one in the evidence zip): 1478 files, 0 extra / 0 changed / 0 missing, no symlink outside
    `Mathlib/`, 3346 `Mathlib/` symlinks, NthRootLemmas `c0a9cff0…` (`replay-verify.out`, `tools/replayverify.py`).
  - Its checked state (after `stateplan update` at `bae0d84d`; SHA-256 of the JSON `70e3678a…`, equal to the copy in the
    evidence zip) over the 1447-module order (`4fe4abda…`; `fullorder.py` at T, byte-equal to LE-g50d's): RESULT OK at T
    and at `bae0d84d` (`replay-statecheck.out`).
- **Snapshot #8 at retirement:** 0/0/0 against `28677767…` (`v8-final/`).
- **Adoption:**
  - The `Mathlib/` overlay was removed (3346 symlinks and the overlay NthRootLemmas olean, as at #8).
  - Map `olean-snapshot.map-523a00a6.tsv`, SHA-256 `9bb4a0d093a772f4fd809289ea14e576b445d206016dc1aab26c55065996e838`.
    It is byte-equal to the audited land9 map. It has 1478 entries: TCSlib 1445, audits 2, PFR 31. Against #8's map, 13
    modules are new (the 13 new source files) and 10 differ (`TCSlib`, `ComputationalModels`, `CircuitComplexity` and 7
    of its modules).
  - Files manifest SHA-256 `7dd26a7665cf95a8ec7ec333a460ac6fe7905bc3f2c87283b7aff26b9eefe6f7`, 1478 files.
- **basecheck:** init at `523a00a6` (1447 modules; `state-init-523a00a6.json.gz`, JSON `bac9f656…`) against the replay's
  checked state: RESULT OK (`basecheck.out`). Build revs over the order: 871 at `a1fa7b65`, 535 at `e4d77a5e`, 21 at
  `93ae671e`, 20 at `bae0d84d`.
- **Swap:**
  - Before the overlay removal and before the swap no `lean` process was running, and a `/proc` scan found no process
    using either tree (`procscan-pre-*.txt`, `tools/procscan.sh`).
  - #8's directory was deleted; the other replay trees keep their hard links. land9 was moved to `$SP/olean-snapshot`.
  - The rehash gave 0/0/0 (`v9/`). The files manifest recomputed after the move is byte-equal. A `stateplan check` of the
    new snapshot at T against the init state gave 1447/1447 OK (`v9-statecheck.out`).
  - #8's map and files manifest are kept in `$SP`. Command output is in `outputs.txt`.
  - After the swap `olean-replay-6a-land7` (map `11d9fbfd…`) and `olean-replay-6b-prereq9` (map `3316e252…`) still
    rehash 0/0/0 (`land7-after-swap.out`, `prereq9-after-swap.out`).
- Free disk was about 7.6 GB before and after (`df -m`). No `lake`, no `lean`, nothing committed.
- **Superseded:** `olean-replay-6a-land7` (#366 at `93ae671e`) is no longer adoptable. `olean-replay-6b-prereq9` (#368,
  built on #8 without #366) re-replays on #9; see `olean-snapshot-10-adopt/`.
