# EF-D1 `ef-d1-lattice-families` · final r1 · phase 2: merged-tree replay on olean snapshot #11

**Verdict: PASS.** The replay ran on the merge of `iO/phase-a-base` with the records tip, which is
Lean-equal to `bff0567b`.
- **Build.** 20/20 modules rc 0, with 0 `error:`/`error(` and 0 `sorry`. This includes the root
  `TCSlib` and both `audits/*/Checks` (closes EFD1-F05).
- **Axioms.** All 157 stored constants of the two new owners are within `propext`,
  `Classical.choice` and `Quot.sound`. A `sorry` control is flagged.
- **Seals.** Canonical coe-A seal on both new owners: 0 errors. Paired controls ALL_OK.
- **Lint.** Unchanged apart from the disclosed `LWE.lean` facade line.
- **Snapshot #11** rehashes 0/0/0 before, after the build and at the end.

The landing branch `land/ef-d1-lattice-families` (`bd4c6f2d826b2fb91c02d720d8bd6b60c2a3795e`) is
pushed and open as **draft PR #387**, with base `iO/phase-a-base`.

Run on 2026-11-18, 10:22–10:45 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `ef-d1-final-r1-evidence.zip`, beside this file. It holds `PROVENANCE.txt` and an
  inner `SHA256SUMS` that does not list itself. The zip's own SHA-256 is in
  `evidence-SHA256SUMS`.
- **Builds.** No `lake build`, no cache get.
  - This job ran **one Lean process at a time**: the recipe's `runner.py`/`runner_full.py` are
    sequential. S2-A D2 shared the host.
  - The host never had more than 2 `lean` processes at once (S2-A's plus this job's): the slot
    counts are logged at the start of each phase.
- **Not touched:**
  - the snapshot, which was read and hard-linked only;
  - `$SP/olean-snapshot-10`;
  - other agents' replay directories.

  Only this job's own PIDs were waited on; none was killed.

## P2-0 Inputs

- **Records tip.** `origin/cryptography/pass-shelat-ch2-4` = `64d51439885eb02b3be442b29b2a4197984dae2d`.
  - `git diff --name-only bff0567b 64d51439` over `TCSlib`, `TCSlib.lean`, `audits`, the lake files
    and `lean-toolchain` is empty, so the tip is Lean-equal to snapshot #11's T.
  - The coordinator later committed this folder's work in progress as `d9b07900`, which is
    records-only.
- **Snapshot #11.** `$SP/olean-snapshot`.
  - Map `olean-snapshot.map-bff0567b.tsv` = `e7bb03b4…867d0`, the register's value.
  - Files manifest `olean-snapshot.files-bff0567b.txt` = `463c8869…0b13`.
- **Recipe tools.** `olean-advance-a6d01b1b/tools-used/` from `olean-rebase-evidence.zip`
  (`b662b7da…`), extracted fresh and byte-identical to the copies used before. They were used
  unmodified: `runner.py`, `runner_full.py`, `stateplan.py`, `downorder.py`, `fullorder.py`,
  `permod.py`, `snapmap.py`, `mloverlay.sh`, `mathlibextra.sh`, `seal/review/{mkcollect,
  mkseals_coe,sealsum}.py` and the archived gate-10 builders.
- **New tools** (in `tools/` of the evidence):
  - `repro.sh` (phase-1 `git am` reproduction);
  - `recount_seals.py` and `recount_controls.py` (phase-1 recounts, re-used on this run's
    controls);
  - `rule10.sh` (this driver).

## P2-1 Scratch merge and check head (scratch only, never pushed)

- **The merge.** Made in a sparse detached worktree at `5ed465f6`, with
  `git -c commit.gpgsign=false merge --no-ff bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`. The merge
  was clean.
  - It gives `9067223f66244b67de264abc00b090296bf2d0a1`, with **tree
    `1a55e8aac645cab79de85749a17299e077c8cd62`**: the 6b fills staging tree, and equal to
    `git merge-tree --write-tree 5ed465f6 bff0567b`.
  - Against `bff0567b`, the merge changes exactly the iO base's 15 Lean paths: #374, #378, the
    contract and #380, with their facades and the root's import line.
  - The merge commit's date is a fixed `12:00Z`, which is ahead of the host clock. It affects only
    the lint export's mtimes.
- **Check head.** Unsigned cherry-picks of the 4 worker commits onto the merge give
  `e3fc2ce29436efeb3870f883f8a8e40cb9292c0f`, **tree `8135ba1ae02fd3b90c8e57798edda9c8200cb0d0`**.
  - This equals `git merge-tree --write-tree 876b1cc0 bff0567b`.
  - Against the merge, it changes exactly the 3 delivery files (+1081).

## P2-2 Replay (snapshots.md job recipe)

- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-efd1` (1487 files, all hard links).
  - `mloverlay.sh` made 3346 Mathlib symlinks.
  - `mathlibextra.sh` built `NthRootLemmas` with rc 0; its olean is **`c0a9cff0…`**.
- **Tree.** `git archive` of the check head (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake
  files, `lean-toolchain`; 1621 files), with `.lake/packages` symlinked. The three delivery sources
  in the export equal the head's and the delivered `src/` (`114f5112…`, `e9f7d368…`,
  `18c09d86…`).
- **Plan.**
  - `stateplan init` at `bff0567b`: 1456 modules.
  - `downorder.py`: changed 18, down 20.
  - `fullorder.py`: 1469, with roots `TCSlib` and both `Checks`.
  - `stateplan plan`: **20 to build, 1449 reused.** The 20 are the 15 iO paths, the 3 delivery
    modules, root `TCSlib`, `audits/garg-ch1-3/Checks` and `audits/pass-shelat/Checks`.
- **Build.** 10:25:09–10:28:02.
  - **20/20 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, `sorry` 0, warnings 0.
  - `permod.py` finds no log/record mismatch.
  - Peak maxrss: 4.59 GB (root `TCSlib`).
  - `LWE/Efficient` took 2.8 s and `SIS/Efficient` 2.3 s.

## P2-3 Accept (recipe step 5)

- `stateplan update`: 20 modules, none left out.
- `check` over the full order: **1469/1469, RESULT OK**.
- **Link count 1** for all 20 rebuilt oleans. Every other file is a hard link to the snapshot.
- **Snapshot #11** `snapmap.py verify`: **0/0/0**, 1487 files, no symlinks.
  - It was checked before the copy, after the build and at the end.
- `$SP/olean-replay-efd1` is kept for the PR's gate.

## P2-4 Axioms, probes and the SR1 demonstration

Every probe ran through `runner_full.py`: `lean -DmaxErrors=0`, with no `-o`, so nothing was written
to the tree.

- **`AxiomsHead`** (the recipe's `AxiomProbe.r2.lean` with the owner list replaced, plus a `sorry`
  control): rc 0. It covers **157 stored constants of `LWE.Efficient` and `SIS.Efficient`**: 125
  named and 32 auxiliary.

  | Axiom set | Constants |
  |---|---|
  | `[Classical.choice, Quot.sound, propext]` | 120 |
  | `[Quot.sound, propext]` | 23 |
  | `[propext]` | 11 |
  | `[]` | 3 |

  - **0 non-standard.**
  - The control `efd1SorryControl` reports `[sorryAx]`, and its `sorry` warning is the only one.
  - The worker's 119 public constants are a subset. The extra rows are structure auxiliaries
    (`mk.injEq`, `rec`, …) and generated equations.
- **`SmokeHead`** (D1-P2 on the merged tree, with #377's `LWE.Family.RatioBounded` present): rc 0,
  0 errors.
  - `fun F h D => h D` type-checks for `LWE.DLWEAssumption F.toFamily` and for
    `SIS.SISAssumption F.toFamily`.
  - `F.toFamily.RatioBounded B p` elaborates for an `LWE.EfficientFamily`.
  - `#print axioms` for both `dyadicExample`s is `[propext, Classical.choice, Quot.sound]` (D1-P3).
- **`SR1Demo`** (EF-D1-SR1, extended beyond the worker's two direct applications). With
  `bitNoise centeredNoise` locally irreducible, as any consumer's canonical seal makes them, each
  attempt fails exactly once, and nothing else errors:
  - **S1** direct `bitNoise_sample t f c`: type mismatch.
  - **S2** `rw [bitNoise_sample]`: pattern not found.
  - **S3** `simp only [bitNoise_sample]`: no progress.
  - **S4** the cast round trip through `bitNoise_sample t f (cast _ c)`: unsolved goal.
  - **S5** `rw [centeredNoise_sample]`: pattern not found.

  The two proposed readers, stated unsealed (the owner-file form), **pass by `rfl`** (P1, P2).
  So the readers are the minimal fix, and the hypothesis cannot be removed without a change to
  `LWE/BitNoise.lean`.

## P2-5 Rule 10

- **Collector.** `mkcollect.py` with owners `LWE.Efficient` and `SIS.Efficient`. `CollectHead`:
  rc 0, 0 errors.
- **Canonical coe-A seal.** `mkseals_coe.py`, A variant, recipe tool unmodified.

  | Owner | Requests | Terms | Excluded terms | Stored constants |
  |---|---|---|---|---|
  | `LWE.Efficient` | 3,012 | 41 | 17 | 108 |
  | `SIS.Efficient` | 3,046 | 20 | 11 | 49 |

  - **Attempt 1** (one harness command per owner) aborted with rc −6, "Stack overflow detected",
    before any declaration was checked. This is the known harness limit that `mkseals_coe.py`'s
    docstring records at 2,921 rows. It is kept in `rule10/attempt1/`.
  - **Attempt 2,** with `SEAL_CHUNK=1000` (the precedent setting): 4 harness parts per owner.
    - **`LWE.Efficient`: rc 0, 0 errors**, every part with install and end records (366 s).
    - **`SIS.Efficient`: rc 0, 0 errors**, every part with install and end records (401 s).
    - The end records give `verified = requested` in every part: LWE 1000/1000/1000/12, SIS
      1000/1000/1000/46.
  - **Why the request counts are higher than the worker's.** The worker's candidate set (1,269 and
    1,294) is a different enumeration of the same closure. The recipe collector requests every
    ordinary TCSlib definition in the owner's transitive closure, matchers included, and excludes
    only `PolyExpr.eval` and the `FinDist` coercion. So this seal is the stricter of the two.
- **Paired controls.** The delivered control files were re-run on this tree. Recounted per example
  span with phase 1's `recount_controls.py`:
  - **LWE:** 14 NEG and 14 POS. Sealed, each NEG fails exactly once and no POS fails; unsealed, 0
    errors.
  - **SIS:** 5 and 5, likewise.
  - **ALL_OK**, with 0 stray errors.
- **Explicit-unfold scan.** I did not re-run it. The delivered scan (0 foreign) is over the same
  bytes: the sources are bound above.

## P2-6 Lint

- `campaign_style_lint.py TCSlib/Cryptography --check8b`, on exports of the scratch merge and the
  check head:
  - merge: **92 FAIL / 103 WARN over 551 files**;
  - check head: **93 / 103 over 553**.
- **The line-set diff** is exactly one new line,
  `FAIL TCSlib/Cryptography/LWE.lean facade does not import child module
  TCSlib.Cryptography.LWE.Efficient`. This is the brief's sanctioned C8 line, which landing edit
  LE-efd1-imp removes. There is no other new FAIL or WARN, and none disappears.
- `style_lint.py` on the 3 files: **0 findings**.

## P2-7 Landing branch

- **The branch.** `land/ef-d1-lattice-families`, from `iO/phase-a-base`
  (`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`), in a sparse worktree.
  `git cherry-pick -S` of the 4 worker commits applied cleanly. Author (Claude) and author dates are
  kept, and the messages are kept verbatim with the worker's trailers, as in earlier landings.

  | # | Commit | Subject |
  |---|---|---|
  | 1 | `56e4fe429e1e24631a27450f95d11f2bea9ace11` | `LWE.EfficientFamily` |
  | 2 | `1a8580c713100abc4dc15aa05ae5817f1dea4711` | `SIS.EfficientFamily` and the facade line |
  | 3 | `bdea9ba0302dcaa587ded4eb8a9e36d0e5791a44` | reuse `onesW` |
  | 4 | `bd4c6f2d826b2fb91c02d720d8bd6b60c2a3795e` | `PolyExpr.eval` readers; reuse `count_ofFn` |

- **Checks:**
  - `git range-diff 5ed465f6..876b1cc0 5ed465f6..bd4c6f2d`: **4/4 `=`**.
  - The landing head's tree `43512202…` **equals the worker head's tree**.
  - `git merge-tree --write-tree bd4c6f2d bff0567b` = **`8135ba1a…`, the replayed check-head
    tree**, so this phase's results apply to the landing head's merge with the records tip.
  - `git diff --stat 5ed465f6 bd4c6f2d`: the 3 files, +1081, with no path outside them.
  - **Signatures.** All 4 commits carry a `gpgsig`. Each is an ed25519 signature by
    `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the key of the records commits (for
    example `64d51439` and `d9b07900`). It was read from the signature blob with `sigfp.py`
    (`git verify-commit` needs an allowed-signers file that this host lacks).
- **Pushed** as `land/ef-d1-lattice-families`; `git ls-remote` gives `bd4c6f2d…`. Draft **PR #387**
  was opened against `iO/phase-a-base`.
- **No maintainer commit** is on the branch. The `LWE.lean` import (LE-efd1-imp) cannot be applied
  on this base: `iO/phase-a-base` does not contain #377's `LWE.lean`. See `review.md`, *Landing*.

## P2-8 State after the run

- **Kept:**
  - `$SP/olean-replay-efd1` (1487 + 13 new oleans, the NthRootLemmas overlay and 3346 Mathlib
    symlinks), for the gate;
  - the landing worktree `$SP/efd1/p2/landwt`;
  - the scratch merge worktree `$SP/efd1/p2/mergewt` (scratch commits `9067223f`, `e3fc2ce2`; never
    pushed).
- **Raw seal sources are not in the zip.** They are 2.7 MB each and regenerable by `mkseals_coe.py`
  from the collector log, which is in the zip. Their SHA-256 are in
  `rule10/omitted-SHA256SUMS`.
