# EF-H11 `ef-h11-sharing-bgw` · final r1 · phase 2: merged-tree replay on olean snapshot #11

**Verdict: PASS, except EFH11-F01.** The replay ran on a scratch merge of `iO/phase-a-base` with the records
tip (Lean-equal to `bff0567b`), plus the worker's 6 commits.

- **Build.** 23/23 modules rc 0, with 0 `error:`/`error(` and 0 `sorry`. This includes the root `TCSlib`
  and both `audits/*/Checks`, which closes I6.
- **Axioms.** All 217 stored constants of the three new owners are within `propext`,
  `Classical.choice` and `Quot.sound`. A `sorry` control is flagged.
- **Canonical coe-A seal.**
  - `ShamirEfficient` and `BGW/Efficient`: **0 errors**.
  - `SecretSharing/Efficient`: **5 errors**, exactly the W1 lines `:115`, `:116`, `:122`, `:132` and
    `:143`. That is **F01, a major**.
- **Paired controls.** All OK.
- **Lint.** Unchanged.
- **Landing-edit variant.** The worker's W1+W2 patches, as a scratch commit: 13/13 rc 0, and coe-A at
  **0 errors** on all three new owners and on `Defs`. `Sharing` and `Protocol` keep exactly their
  pre-existing failures (I1).
- **Snapshot #11** rehashes 0/0/0 before, after the builds and at the end.

**No landing branch was created and no PR was opened**, because F01 is a major (see `review.md`,
*Landing (held)*).

Run on 2026-11-18, 10:46–11:20 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence.** `ef-h11-final-r1-evidence.zip`, beside this file, under `phase2/`, `probe-src/` and
  `tools/`.
- **Builds.** No `lake build`, no cache get.
  - **One Lean process at a time:** the recipe's `runner.py` and `runner_full.py` are sequential, and
    `mathlibextra.sh` was run alone.
  - The host never had more than 2 `lean` processes: this job's one plus S2-A D2's. The counts are
    logged at each phase start.
- **Not touched:** the snapshot (read and hard-linked only), `$SP/olean-snapshot-10`, and the other
  replay directories (`olean-replay-efd1`, `olean-replay-s2a-*`). No PID was killed.
- **Disk incident (recorded).** A second full worktree checkout ran the disk down to 1.6 GB free.
  - The failed checkout was removed at once.
  - Both scratch worktrees were then made sparse (`TCSlib`, `audits`, `scripts`, lake files), which
    restored 3.9 GB.
  - No other job's file was touched.

## P2-0 Inputs

- **Records tip.** `origin/cryptography/pass-shelat-ch2-4` was `7bd94e24…` at the start and
  `744441c3a538be2df525b4216b71ff8dbfce6cf5` at the end, after the EF-D1 records.
  - `git diff --name-only bff0567b 744441c3` over `TCSlib`, `TCSlib.lean`, `audits`, the lake files and
    `lean-toolchain` is empty.
- **Snapshot #11.** `$SP/olean-snapshot`.
  - Map `olean-snapshot.map-bff0567b.tsv` = `e7bb03b4…867d0`, the register's value.
  - Files manifest `olean-snapshot.files-bff0567b.txt` = `463c8869…0b13`.
  - `snapmap.py verify`: 1487 files, 0/0/0, RESULT OK.
- **Recipe tools.** `olean-advance-a6d01b1b/tools-used/`, from `olean-rebase-evidence.zip`
  (`b662b7da…`), extracted fresh into `$SP/efh11-final/recipe/` and used unmodified:
  - `runner.py`, `runner_full.py`, `stateplan.py`, `downorder.py`, `fullorder.py`, `permod.py`,
    `snapmap.py`, `mloverlay.sh`, `mathlibextra.sh`;
  - `seal/AxiomProbe.r2.lean`;
  - `seal/review/{mkcollect,mkseals_coe,sealsum}.py`, `NmCollect.template.lean`, and the archived
    gate-10 builders.
- **New tools** (in `tools/`):
  - `run-build.sh` (the driver);
  - `mkctl_efh11.py` (the paired controls);
  - `hygiene.py` (phase 1).

## P2-1 Scratch merge and check head (scratch only, never pushed)

- **The merge.**
  - Made in a detached worktree at `5ed465f6`, with
    `git -c commit.gpgsign=false merge --no-ff bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`. It was clean.
  - It gives `35441152063ab6cbd803b0510aed79005a2b0cba`, with **tree
    `1a55e8aac645cab79de85749a17299e077c8cd62`**. That equals `git merge-tree --write-tree 5ed465f6
    bff0567b`, and is the same tree as EF-D1's phase-2 merge.
- **The check head.** Unsigned cherry-picks of the 6 worker commits give
  `361777bccf036fc91f361fd8a0838c31be97245a`, with **tree `c7e32e85005b0678063d62ac2d85bed923e4b395`**.
  - That equals `git merge-tree --write-tree edacd3c9 bff0567b`.
  - It changes exactly the 5 delivery files against the merge (+1761).
  - The 3 new sources equal the delivered `src/`: `ad53c9ab…`, `374b82fd…`, `0facb22c…`.

## P2-2 Replay (snapshots.md job recipe)

- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-efh11` (1487 files, all hard links).
  - `mloverlay.sh` made 3346 Mathlib symlinks.
  - `mathlibextra.sh` built NthRootLemmas with rc 0; its olean is **`c0a9cff0…`**.
- **Plan.**
  - `stateplan init` at `bff0567b`: 1456 modules.
  - `downorder.py`: changed 20, down 23.
  - `fullorder.py`: 1470, with roots `TCSlib` and both `Checks`.
  - `stateplan plan`: **23 to build, 1447 reused.** The 23 are the iO base's 14 changed modules, the
    3 new modules, the facades `SecretSharing`, `MPC/BGW` and `MPC`, root `TCSlib`, and both `Checks`.
- **Build** (10:49:17–10:52:23).
  - **23/23 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, `sorry` 0, warnings 0.
  - `permod.py`: no log/record mismatch.
  - Peak maxrss: 4.59 GB, in `audits/pass-shelat/Checks` (117 s).
  - The new modules took 2.2 s (`Efficient`), 4.0 s (`ShamirEfficient`) and 2.4 s (`BGW/Efficient`).

## P2-3 Accept (recipe step 5)

- `stateplan update`: 23 modules, none left out.
- `check` over the full order: **1470/1470, RESULT OK**. It was repeated after the LE build and at the
  end.
- **Link count 1** for all 23 rebuilt oleans.
- **Snapshot #11** `snapmap.py verify`: **0/0/0** before the copy, after the build and at the end.
- `$SP/olean-replay-efh11` is kept for the landing replay.

## P2-4 Axioms

**`AxiomsHead`** is the recipe's `AxiomProbe.r2.lean` with the owner list replaced by the three new
modules, plus `efh11SorryControl`. It ran through `runner_full.py` (`-DmaxErrors=0`, no `-o`) with rc 0
and 0 errors. Its one `sorry` warning is the control's.

| Axiom set | Constants |
|---|---|
| `[Classical.choice, Quot.sound, propext]` | 129 |
| `[Quot.sound, propext]` | 57 |
| `[propext]` | 31 |

- **217 stored constants:** 189 `DECL` and 28 `AUX`, split `Efficient` 105, `ShamirEfficient` 99 and
  `BGW/Efficient` 13, as the collector's `MODULE … stored` lines confirm. **0 non-standard.**
- The worker's 187 named constants are a subset (0 missing). The extra `DECL` rows are the two
  generated `match_1_1` matchers; the rest are auxiliaries.
- `CONTROL efh11SorryControl [sorryAx]`.

## P2-5 Rule 10

- **Collector.** `mkcollect.py` with the 3 owners (`CollectHead`): rc 0, 1651 `CAT` rows.
- **Canonical coe-A seal.** `mkseals_coe.py`, A variant, recipe tool unmodified, with `SEAL_CHUNK=1000`
  (the precedent setting): 2 harness parts per owner. Every part has its install and end records.

  | Owner | Requests | Terms | Excluded | Stored | Result |
  |---|---|---|---|---|---|
  | `SecretSharing.Efficient` | 1,121 | 27 | 8 | 105 | **rc 1, 5 errors**: src `:115` "Function expected", `:116` "No goals", `:122`, `:132`, `:143` "`introN` failed". These are exactly `restrict_reconstruct_of_eqOn`, `restrict_localReconstruct`, `restrict_correct` and `restrict_perfectPrivacy` (**F01**). They equal the worker's gate-04 failure set. |
  | `SecretSharing.ShamirEfficient` | 1,144 | 57 | 17 | 99 | **rc 0, 0 errors** |
  | `MPC.BGW.Efficient` | 1,185 | 23 | 6 | 13 | **rc 0, 0 errors** |

  The request counts are about 50 times the worker's (20, 40 and 17). The recipe collector requests
  every ordinary TCSlib definition in the owner's closure, so this is the stricter seal (cf. EF-D1).
- **Paired controls** (`mkctl_efh11.py`).
  - `CtlS_X` is the owner's coe-A seal file with the control block after the owner's closing `end`,
    before the EOF verification. `CtlU_X` is the owner source with the same block, unsealed.
  - Expected: each NEG fails exactly once sealed and passes unsealed; every POS passes in both.

  | Owner | NEG (foreign read by `rfl`/`Iff.rfl`) | POS (published reader) | Sealed | Unsealed |
  |---|---|---|---|---|
  | A `Efficient` | A1 `threshold … .Auth ↔ k ≤ card` (`Iff.rfl`); A2 `encWords [] = []` (`rfl`) | `threshold_auth`; `encWords_nil` | 7 errors = F01's 5 + NEG lines 777 and 781, once each | 0 |
  | B `ShamirEfficient` | B1 `resWord a = bits a.val`; B2 `π.encode = ⟨…⟩` | `resWord_eq`; `encode_eq` | 2 errors = NEG lines 1191 and 1194 | 0 |
  | C `BGW/Efficient` | C1 `resWord a = bits a.val` | `resWord_eq`; C2 owned `shamirResharer` read by `rfl` | 1 error = NEG line 462 | 0 |

  **ALL_OK**, with 0 stray errors.
  - **Attempt 1 for C** had a naming error in my control text (unqualified `SecretSharing.addModW`,
    `Turing.pairFstD`). Its 11 "unknown identifier" errors occurred sealed and unsealed alike, so it
    tested nothing. It is kept in `phase2/seal-runs/attempt1-C/` and `phase2/ctl/ctl_C.attempt1.txt`.
    Attempt 2 is the row above.
- **Explicit-unfold scan.** Not re-run. The worker's scan (0 hits) is over the same bytes, and the
  sources are bound above. F01's reads are `intro` and application, not `unfold`; the seal is the check
  that catches them.

## P2-6 Landing-edit variant (scratch `a299c19e`, never pushed)

- **The commit.** The worker's `W1-defs-readers.patch` and `W2-readers.patch` (`git apply`), plus
  `W1-efficient-after-readers.diff` and `W2-bgw-mul-agreement.diff` (`patch`), all verbatim, applied
  on the check head.
  - It gives `a299c19e52f569a33072ac43563384b89591c97e`, with tree `89a2d96b…`: 5 files, +38/−6.
  - The diff is `phase2/le-variant.diff`.
- **Replay.** On `cp -al $SP/olean-replay-efh11 $SP/olean-replay-efh11-le`, `stateplan plan` gives
  13 to build: `Defs`, `Efficient`, `Shamir`, `Sharing`, `ShamirEfficient`, `Vector`, `SecretSharing`,
  `Protocol`, `Privacy`, `BGW/Efficient`, `BGW`, `MPC` and `TCSlib`.
  - **13/13 rc 0**, 0 errors, 0 `sorry`.
  - `check`: 1470/1470 OK. Link count 1.
  - `olean-replay-efh11` is unchanged: its state check is still OK.
- **coe-A seals** (`CollectLE` with 6 owners):

  | Owner | Requests | Result |
  |---|---|---|
  | `SecretSharing.Efficient` | 1,121 | **0 errors** (F01 closed) |
  | `SecretSharing.ShamirEfficient` | 1,144 | 0 |
  | `MPC.BGW.Efficient` (with `recombineRaw_bgwEval_mul`) | 1,185 | **0** (F02 closed) |
  | `SecretSharing.Defs` | 0 (imports Mathlib only) | 0 |
  | `SecretSharing.Sharing` | 13 | 2 errors, src `:64`, `:151` |
  | `MPC.BGW.Protocol` | 27 | 11 errors, src `:98`, `:135–138`, `:142`, `:158–163` |

- **The `Sharing`/`Protocol` errors are pre-existing.** The same two owners sealed at the check head
  **without** the LE (`CollectBase`) give the same 2 and 11 errors at src `:64`, `:147` and `:94`,
  `:131–134`, `:138`, `:154–159`. Every line after the 4-line reader insertion is shifted by +4, so
  the LE adds and removes none. This is I1.

## P2-7 Lint

`campaign_style_lint.py TCSlib/Cryptography --check8b`, on exports of the scratch merge and the check
head:
- merge: **92 FAIL / 103 WARN over 551 files**;
- check head: **92 / 103 over 554**;
- **the FAIL/WARN line sets are identical.**

The INFO diff is the 3 new files (including "`ShamirEfficient.lean` 965 lines > target 600") and the
two facades' line counts. `style_lint.py` on the 3 new files: **0 findings**.

## P2-8 State after the run

- **Kept for the landing:**
  - `$SP/olean-replay-efh11` (the check-head replay);
  - `$SP/olean-replay-efh11-le` (the LE variant);
  - the sparse scratch worktrees `$SP/efh11-final/p2/wt` (`361777bc`) and `$SP/efh11-final/p2/wtle`
    (`a299c19e`), both detached, holding never-pushed scratch commits;
  - `$SP/efh11-final/deliv/` (the extracted delivery).
- **Removed:**
  - the phase-1 `git am` worktree (`$SP/efh11-final/amwt`);
  - the 72 MB lint exports;
  - the failed second checkout.
- **Nothing was committed or pushed.** These records are uncommitted in the records checkout.
