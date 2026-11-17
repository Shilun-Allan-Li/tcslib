# Olean snapshot #8: adoption at the #365 merge (2026-11-17)

- **New T:** `2dd2e60ed0cdd4681a7bd12fe4a86825e98db664` (merge of #365, `fix/pairing-group-dedup`, head
  `5eaddd171bceccee917929e7f319ff9202994c59`, into `cryptography/pass-shelat-ch2-4`).
  - **Prospective tree:** `git merge-tree --write-tree a1fa7b652f0c235b54fc067e09b669e983daaf71 5eaddd17…` (snapshot #7's
    T × #365's head) gives `9710ac7d02e95c73cf7ae7715713aa8defcda526`, which is the head's own tree (#7's T is an ancestor
    of the head).
  - **Step-3 diff** of the merge against that tree (`*.lean`, `lean-toolchain`, `lake-manifest.json`; `lakefile.lean`
    included): empty (`step3-diff.txt`). From #7's T to the merge, the only Lean change is
    `TCSlib/Cryptography/Pairing/Group.lean`.
  - **Later commits:** at the swap the branch tip was `5e693e1ee756465ab7017e5ec61ecbd799dfb3d2`. Both commits since T
    (`555f0fe1…`, `5e693e1e…`) are records only (`briefs/`, `LatticeCryptographyPlan.md`, `PairingCryptographyPlan.md`).
    The same diff from T to that tip is empty (`tip-since-T-diff.txt`).
- **Source:** #365's replay `olean-replay-grpfix`, a `cp -al` of `olean-replay-cs1-s6` (#7's tree), with 22 modules
  rebuilt at the head (`briefs/pairings/fixes/group-dedup/report.md`; evidence zip `48d787d4…`).
  - Before adoption it rehashed against its recorded no-`Mathlib/` map (`286777672d4e…`, the copy in the job's work
    directory, byte-equal to the one in the evidence zip): 1465 files, 0 extra / 0 changed / 0 missing, no symlink outside
    `Mathlib/`, 3346 `Mathlib/` symlinks, NthRootLemmas `c0a9cff0…` (`replay-verify.out`, `tools/replayverify.py`).
  - Its checked state (run 2, after `stateplan update` at `5eaddd17`; SHA-256 of the JSON `c0209023…`, equal to the copy
    in the evidence zip) over the 1434-module order (`f4a44ece…`, the same order as at #7): RESULT OK at T and at
    `5eaddd17` (`replay-statecheck.out`).
- **Snapshot #7 at retirement:** 0/0/0 against `5105c514…` (`v7-final/`).
- **Adoption:**
  - The `Mathlib/` overlay was removed (3346 symlinks and the overlay NthRootLemmas olean, as at #7).
  - Map `olean-snapshot.map-2dd2e60e.tsv`, SHA-256 `286777672d4e61f1be0ba98fca72b01d8cd9aa281eb811d100d7fe499679c49c`.
    It is byte-equal to the audited grpfix map. It has 1465 entries: TCSlib 1432, audits 2, PFR 31. Against #7's map only
    `TCSlib/Cryptography/Pairing/Group` differs.
  - Files manifest SHA-256 `597e410e33ed6d634024870d2928dacbc077578143b58d71b6ddbecee0c3c047`, 1465 files.
- **basecheck:** init at `2dd2e60e` (1434 modules; `state-init-2dd2e60e.json.gz`) against the replay's checked state:
  RESULT OK (`basecheck.out`). Build revs over the order: 873 at `8060f6b7`, 539 at `13fc8060`, 22 at `5eaddd17`.
- **Swap:**
  - Before the overlay removal and before the swap no `lean` process was running, and a `/proc` scan found no process
    using either tree (`procscan-pre-*.txt`, `tools/procscan.sh`).
  - #7's directory was deleted; the other replay trees keep their hard links. grpfix was moved to `$SP/olean-snapshot`.
  - The rehash gave 0/0/0 (`v8/`). The files manifest recomputed after the move is byte-equal. A `stateplan check` of the
    new snapshot at T against the init state gave 1434/1434 OK (`v8-statecheck.out`).
  - #7's map and files manifest are kept in `$SP`. Command output is in `outputs.txt`.
  - After the swap `olean-replay-6a-land7` still rehashes 0/0/0 against its map `11d9fbfd…` (`land7-after-swap.out`).
- Free disk was about 8.3 GB before and after (`df -m`). No `lake`, no `lean`, nothing committed.
- **Still adoptable:** `olean-replay-6a-land7` (#366, head `93ae671e`, merge tree `c8ba8961`, map `11d9fbfd…`) was
  re-replayed on #7 + #365 and contains #365's change. It can be adopted at a #366 merge whose Lean equals `c8ba8961`.
  Otherwise it re-replays.
- **Not adoptable as-is:** `olean-replay-6b-prereq` (#368) was built on #7 without #365. It re-replays on #8 before
  merge-time adoption.
