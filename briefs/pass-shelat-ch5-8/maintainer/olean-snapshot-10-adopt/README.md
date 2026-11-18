# Olean snapshot #10: adoption at the #368 merge (2026-11-18)

- **New T:** `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62` (merge of #368, `land/gsw-6b-owner-prereqs`, head
  `052e2b05fa947ce0f46024e928a5f7083e23b8dc`, into `cryptography/pass-shelat-ch2-4` at snapshot #9's T `523a00a6`).
  - **The Lean change is #368's.** From #9's T to the merge it is exactly `GSW/Scheme.lean` and
    `Encryption/PublicKey/EnsembleSecurity.lean` (`replay/lean-diff-T9-R.txt`). The diff is byte-equal to the net change
    `55f55371..052e2b05` (`1953898b` + LE-g50e against #368's base), SHA-256 `9cedbc91…` for both; pre- and post-image blobs
    agree file by file (`replay/pr368-diff-check.txt`).
  - **Prospective tree:** `git merge-tree --write-tree 523a00a6 052e2b05` = `d52cf05bb20c08b6547468d1bd489f1cf0d2e442`,
    clean. This is the merge commit's own tree (`replay/R.txt`).
  - **Step-3 diff** of the merge against that tree (`*.lean`, `lean-toolchain`, `lake-manifest.json`, `lakefile.lean`):
    empty (`step3-diff.txt`).
  - **Later commits:** at the swap the branch tip was `ef80ec966befa3d85fcaa74766d3563f2a0d791e`. Both commits since T
    (`2bff7177…`, `ef80ec96…`) are records only. The same diff from T to that tip is empty (`tip-since-T-diff.txt`).
- **Source: a fresh replay of #368's merge on #9,** `$SP/olean-replay-s10`, by #368's recipe (LE-g50e's
  `run-build-g50e.sh` with only the work directory and output tree re-pointed: `tools/run-build-s10.sh`). Evidence in
  `replay/`.
  - **Export:** `git archive` of `d52cf05b` (`TCSlib`, `TCSlib.lean`, `audits`, manifests, `scripts`): 1599 files,
    0/0/0 blob for blob (`export.txt`).
  - **Tree:** `cp -al` of snapshot #9, with the `Mathlib/` overlay (3346 symlinks) and NthRootLemmas `c0a9cff0…` (lean
    rc 0; `mathlibextra.log`).
  - **Plan:** init at `523a00a6` (byte-equal to #9's init state), full order 1447 (`4fe4abda…`, the same as at #9).
    2 changed files, 67 downstream modules: build 67, reuse 1380. The build set equals LE-g50e's.
  - **Build:** the plan's queue (imports first), one module per `runner.py` call, with the slot gate before each module
    (0 Lean processes at every reading, 0 waits). **67 modules: rc≠0 0, `error:` 0, `error(` 0, sorry 0.** The 1
    warning is the existing unused simp argument in `MAC/FromPRF.lean:129`. All 67 logs are byte-equal to LE-g50e's.
  - **State:** `stateplan update` took 67 modules. `check` over 1447 modules gives **RESULT OK** at `d52cf05b`, at
    `cf6a2266`, and again at the end.
  - **Links:** the 67 rebuilt oleans have link count 1; the 1380 reused ones are #9's inodes; no `.ilean`, no symlink
    outside `Mathlib/`.
  - **Snapshot #9:** rehash **0/0/0** before the build, after it and at the end (map `9bb4a0d0…`).
  - **Admissions:** **192 in 44 modules** at `d52cf05b`, the same at `523a00a6`, and per module equal to LE-g50e's and
    LE-g50d's census (`admissions-R.txt`).
  - **Axioms:** LE-g50e's probe source (`d04b62e6…`), unchanged. **Its log is byte-equal to LE-g50e's** (`290a49d5…`).
    7 constants checked, all within `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`.
  - **Output map** (Mathlib excluded): 1478 entries, `84d88738…`. Against #9 only `Scheme` and `EnsembleSecurity`
    differ; the rebuilt root `TCSlib` olean is byte-equal to #9's. Of the 67 rebuilt oleans, 66 are byte-equal to
    `olean-replay-6b-prereq9`'s; `TCSlib` differs because #9 contains #366.
- **Snapshot #9 at retirement:** 0/0/0 against `9bb4a0d0…` (`v9-final/`).
- **Adoption:**
  - Before adoption the replay tree rehashed against its output map: 1478 files, 0/0/0, 3346 `Mathlib/` symlinks,
    NthRootLemmas `c0a9cff0…` (`replay-verify.out`). Its checked state (`248dc4ce…`) gives RESULT OK at T
    (`replay-statecheck.out`).
  - The `Mathlib/` overlay was removed (3346 symlinks and the overlay NthRootLemmas olean).
  - Map `olean-snapshot.map-cf6a2266.tsv`, SHA-256 `84d88738ab015961eb01b4442da851c24862f46f855f9e25da63f92117e72771`,
    byte-equal to the replay's output map. 1478 entries: TCSlib 1445, audits 2, PFR 31.
  - Files manifest SHA-256 `86c6e90d11c43a1e0eec5c6dd6239dcf2b31f481e6c9a01ab334ede7e3de7d93`, 1478 files.
- **basecheck:** init at `cf6a2266` (1447 modules; `state-init-cf6a2266.json.gz`, JSON `78029ec4…`) against the replay's
  checked state: RESULT OK (`basecheck.out`). Build revs over the order: 1380 at `523a00a6`, 67 at `d52cf05b`.
- **Swap:**
  - Before the overlay removal and before the swap no `lean` process was running, and a `/proc` scan found no process
    using either tree (`procscan-pre-*.txt`, `tools/procscan.sh`).
  - #9's directory was deleted. The replay tree was moved to `$SP/olean-snapshot`.
  - The rehash gave 0/0/0 (`v10/`). The files manifest recomputed after the move is byte-equal. A `stateplan check` of
    the new snapshot at T against the init state gave 1447/1447 OK (`v10-statecheck.out`).
  - #9's map and files manifest are kept in `$SP`. Command output is in `outputs.txt`.
- **Superseded trees deleted** after a clean `/proc` scan (`procscan-pre-delete.txt`, `deleted-trees.txt`):
  `olean-replay-6a-land7` and `olean-replay-6b-prereq9`. #10 rehashed 0/0/0 afterwards. No replay tree remains besides
  the snapshot.
- Free disk: 7517 MB before the deletions, 7965 MB after (`df.txt`). Never `lake build`, no cache get; one Lean process
  at a time (69 in all: the NthRootLemmas compile, 67 modules and the axiom probe). Nothing committed.
