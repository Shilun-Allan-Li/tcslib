# Olean snapshot #7: adoption at the #355 merge (2026-11-17)

- **New T:** `a1fa7b652f0c235b54fc067e09b669e983daaf71` (merge of #355 into `cryptography/pass-shelat-ch2-4`; #347 is
  its ancestor).
  - **Step-3 diff** of the merge against TS2 `13fc8060d5b8d08a8f9e80244242118acaa679e2` (`*.lean`, `lean-toolchain`,
    `lake-manifest.json`; `lakefile.lean` included): empty (`step3-diff.txt`).
  - **Later commits:** at the swap the branch tip was `cbdcc0b29a18aae254dd23790066d6f070866bf6`. All 12 commits since
    T are records only, and the same diff from T to that tip is empty (`tip-since-T-diff.txt`).
- **Source:** Stage 1's re-replay `olean-replay-cs1-s6` of TS2 on snapshot #6 (`cleanup-stage1/final-r1/phase2-s6.md`).
  - Before adoption it rehashed against its recorded no-`Mathlib/` map (`5105c514…`, the copy in the job's work directory,
    byte-equal to the one in its evidence zip): 1465 files, 0 extra / 0 changed / 0 missing, no symlink outside
    `Mathlib/`, 3346 `Mathlib/` symlinks, NthRootLemmas `c0a9cff0…` (`replay-verify.out`, `tools/replayverify.py`).
  - Its checked state (`plan/state-after-update-13fc8060`, SHA-256 of the JSON `5cba938b…`, equal to the copy in the
    evidence zip) at TS2 over the 1434-module order (`f4a44ece…`): RESULT OK (`replay-statecheck.out`).
- **Snapshot #6 at retirement:** 0/0/0 against `0858dccb…` (`v6-final/`).
- **Adoption:**
  - The `Mathlib/` overlay was removed (3346 symlinks and the overlay NthRootLemmas olean, as at #6).
  - Map `olean-snapshot.map-a1fa7b65.tsv`, SHA-256 `5105c5149901c5c4375083c1f6ad998b70c909905e4fbf430c9e96117a0f7300`.
    It is byte-equal to the audited cs1-s6 map. It has 1465 entries: TCSlib 1432, audits 2, PFR 31.
  - Files manifest SHA-256 `4bdd94df083f9cf95b2c1cab008ad123acb6f763f4d8cb8ea0891b3555ce1de2`, 1465 files.
- **basecheck:** init at `a1fa7b65` (1434 modules; `state-init-a1fa7b65.json.gz`) against the replay's checked state:
  RESULT OK (`basecheck.out`). Build revs over the order: 873 at `8060f6b7`, 561 at `13fc8060`.
- **Swap:**
  - Before the swap no `lean` process was running, and a `/proc` scan found no process using either tree
    (`procscan-pre-*.txt`, `tools/procscan.sh`).
  - #6's directory was deleted; the other replay trees keep their hard links. cs1-s6 was moved to `$SP/olean-snapshot`.
  - The rehash gave 0/0/0 (`v7/`). The files manifest recomputed after the move is byte-equal. A `stateplan check` of the
    new snapshot at T against the init state gave 1434/1434 OK (`v7-statecheck.out`).
  - #6's map and files manifest are kept in `$SP`. Command output is in `outputs.txt`.
- Free disk was about 8.2 GB before and after (`df -m`). No `lake`, no `lean`, nothing committed.
- **Not adoptable as-is any more** (built on #6 without Stage 1): `olean-replay-6a-o1-s6`, `-6a-stmt-s6`,
  `-6a-stmt-g45b`, `-6a-readers`, `-6a-fill12`, `-6a-fill86`, `-6a-land`. Each re-replays on #7 before merge-time
  adoption. Of these, only `-6a-o1-s6`, `-6a-stmt-s6`, `-6a-stmt-g45b` and `-6a-land` still exist under `$SP`.
- **Still adoptable:** `olean-replay-grpfix` (#365) is a `cp -al` of cs1-s6, which is #7's tree. It can be adopted at #365's
  merge if that merge's Lean equals tip × `5eaddd17`. Otherwise it re-replays.
