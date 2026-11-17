# bb1-sim-statements · phase 2b: #352 re-replay on olean snapshot #3

**Verdict: PASS. #352 (`land/bb1-sim-group`, head `92dea4f8126747ea7e816984349b9dbb789f0065`) is clear to merge.**
- The replay rebuilt 12 modules. Each has rc 0 with 0 `error:` and 0 `error(`.
- The state check gives 1422/1422 OK, and all 12 rebuilt oleans have link count 1.
- Snapshot #3 rehashes 0/0/0 before, during and after the replay.
- Admissions against the tip are +0.
- The three helpers use only the standard axioms. The `Group` census is 82 constants, 0 non-standard.
- Rule 10:
  - The seals (strict and coe, A and B) give 0 errors on `Pairing/Group` and on the carrier `Assumptions`.
  - The controls are ALL_OK in both harnesses, and the explicit-unfold scan finds 0 foreign items.
  - Every seal probe, control probe, sealsum row and control verdict is byte-identical to phase 2's R2 (§ R2b-4).
- Lint is unchanged against the tip.

Run on 2026-11-17, 03:04–03:23 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `bb1-sim-statements-r1-phase2b-evidence.zip`, under `bb1-sim-statements-r1-phase2b/`. It has
  `PROVENANCE.txt`, `SHA256SUMS` and this file, and its own SHA-256 is in `evidence-SHA256SUMS`.
- **Not done:** nothing was committed, pushed or `git add`ed, and no PR was touched.
- **Builds:** there was no `lake build` and no cache get. This job ran one Lean process at a time.
- **#346's job:** its directories (`$SP/p346`, `$SP/olean-replay-346`, `$SP/olean-replay-346b`) and processes were not
  touched.

## R2b-0 Inputs
- **Records tip** (`git fetch`; `origin/cryptography/pass-shelat-ch2-4` = `HEAD`):
  `c0752b2e6442ca4985644195acc5d25cf83d85d0`.
  - Its Lean paths equal snapshot #3's T `cf7d28f7159b46033e8b8ae170954f9575e5d145`, the #351 merge. `git diff` over
    `*.lean`, `lean-toolchain`, `lake-manifest.json`, `lakefile.lean` and `scripts` lists nothing.
- **REV** = `git merge-tree --write-tree origin/cryptography/pass-shelat-ch2-4 92dea4f8…` =
  **`3029d8c36c00fd3a4ce27e864a2b43b46309d27f`**. The merge is clean (rc 0, no conflicts).
  - `git diff c0752b2e 3029d8c3`, over all paths, is exactly `TCSlib/Cryptography/Pairing/Group.lean | 27 +`.
  - That is the three helpers (`pow_val_add`, `pow_val_neg`, `pow_val_bijective_of_ne_one`) and their three docstring
    lines.
  - `Group.lean` at REV is blob `54e63b26`, the same blob as at the head. It has SHA-256 `59c605e1…6213` and 331 lines,
    which is phase 2's pin.
- **Snapshot #3:** `$SP/olean-snapshot`.
  - Map `olean-snapshot.map-cf7d28f7.tsv` has SHA-256 `e9dfbfdd…a53d`.
  - Files manifest `olean-snapshot.files-cf7d28f7.txt` has SHA-256 `1e9a3ba7…5733`.
- **Tools:**
  - `olean-rebase-evidence.zip` (SHA-256 `b662b7da…37ae`) → `olean-advance-a6d01b1b/tools-used/`, extracted into a fresh
    directory. It is identical to `$SP/snaptools3`.
  - The seal tools are phase 2's `tools/seal`, byte-identical, with the worker's `rule10_b.sh` and `mkctl_bb1s.py`.
  - The new scripts are `run-build.sh` and `rule10_352.sh`. They are phase 2's scripts with this job's paths, REV and tip.

## R2b-1 Replay (snapshots.md job recipe)
- **Export:** `git archive` of REV, restricted to `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, `lakefile.lean`,
  `lean-toolchain` and `lake-manifest.json`, with `.lake/packages` symlinked.
  - `exportcheck.py` gives 1574/1574 blobs, 0/0/0.
- **Copy and overlay:**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-352`.
  - `mloverlay.sh` made 3346 symlinks.
  - `mathlibextra.sh` built NthRootLemmas with rc 0, and its olean is **`c0a9cff0…`**.
- **Plan:**
  - `stateplan init` at `cf7d28f7` gives 1422 modules.
  - `downorder.py` gives changed 1 (`Group`) and down 12.
  - `fullorder.py` gives 1422 modules, the roots being `TCSlib`, `audits/garg-ch1-3/Checks` and `audits/pass-shelat/Checks`.
  - `stateplan plan` gives **12 to build and 1410 reused**.
  - **The queue equals `down.txt` as a set, and equals R2's `plan/queue.txt` byte for byte.** Those 12 are:
    - `Group`, `Assumptions`, `Operations` and the `Pairing` facade;
    - `Joux` and the `KeyExchange` facade;
    - `BonehBoyen`, `BonehBoyenMachine` and `BonehBoyenSecurity`;
    - the `IdentityBased` and `AdvancedEncryption` facades;
    - root `TCSlib`.
  - Neither `audits/*/Checks` is in `Group`'s downstream, as in R2.
- **Build** (`runner.py` through `scripts/lean_check_tree.sh`, `TCSLIB_OLEANS=$SP/olean-replay-352`, 03:07:14–03:07:45):
  - **12/12 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, and there were no log/record mismatches (`permod.py`).
  - There are 4 warnings, all `sorry`: `Assumptions` 1, `BonehBoyenMachine` 1 and `BonehBoyenSecurity` 2.

## R2b-2 Accept (recipe step 5)
- `stateplan update` took 12 modules, with none left out.
- `check` over the full order gives **1422/1422 OK, RESULT OK**. It held again at the end.
- **All 12 rebuilt oleans have link count 1**, with object hash equal to the record. The other 1441 files are hard links
  to the snapshot.
- **Snapshot #3** `snapmap.py verify` gives **0 extra / 0 changed / 0 missing**, with no symlinks and 1453 files. It ran
  before the copy, after the build and at the end.
- **Warnings** (`warncmp.py`): **12/12 SAME** as a build log of the same source.
  - 10 match phase 2 R1, which is snapshot #3's own build.
  - `Group` and `Operations` match R2.

## R2b-3 Admissions and axioms
- **Admissions** (`admdelta.py` against the tip): **+0**. Every rebuilt module has delta 0.
  - `Group` has no tip build record in these baselines. Its head count is 0.
- **Source census** (`git grep -c -w -E 'sorry|admit'` over `TCSlib`, `TCSlib.lean` and `audits`): the tip has 794
  tokens in 77 files, and REV has the same.
  - The per-file lists are identical.
  - The same method reproduces phase 2's 792 at `176cfd4a` byte for byte. The +2 since then is `Relational`, from #351.
- **Axioms** (phase 2's `AxiomsGroup` probe, unchanged, run against the replay):
  - `pow_val_add`, `pow_val_neg` and `pow_val_bijective_of_ne_one` use **`[propext, Classical.choice, Quot.sound]`**.
  - The `Group` census is **82 constants with 0 non-standard**.
  - `natCast_inj_of_lt` is absent, and no `*natCast_inj_of_lt` constant exists in the closure.
  - The probe log is byte-identical to R2's.

## R2b-4 Rule 10 (`rule10_352.sh`: touched, collect, seals, scan)
- **Method:**
  - `touched.json` is computed against the tip `c0752b2e`: 3 ADDED and 39 UNCHANGED, identical to R2.
  - The collector log is byte-identical to R2's.
  - All four variants were run in full: strict A/B and coe A/B, each with paired controls.
- **Seals** (requests: strict A / strict B / coe A / coe B):

  | Owner | Requests | rc | Errors | Install / EOF records |
  |---|---|---|---|---|
  | `Pairing/Group` | 567/568/567/568 | 0 | 0 | present in all four |
  | Carrier `Assumptions` | 644/645/643/644 | 0 | 0 | present in all four |

  - **The request name sets equal both R2's and the phase-2 base's** (`176cfd4a`) in all eight owner and variant pairs.
  - Strict A minus coe A: `Group` none, `Assumptions` `FinDist.instCoeFunForallReal`.
- **Controls:** **34 sealed negatives per harness**. The breakdown is `Assumptions` 12 (A) and 13 (B), and `Group` 4 (A)
  and 5 (B).
  - The 8 sealed control probes fail with rc 1 and exactly the expected errors.
  - The 8 unsealed probes give rc 0 with 0 errors, and 0 positives fail.
  - **ALL_OK in strict and in coe.**
- **Explicit-unfold scan** of `Group.lean`: 56 items (41 THEOREM, 15 LOCAL_OR_UNRESOLVED), **0 foreign**.
- **Identity with R2** (`comparisons-vs-r2.txt`). The following are byte-identical to R2:
  - all 8 seal probe sources and all 16 control sources;
  - the four sealsum TSVs and both `ctlcheck` logs;
  - the scan `items-head.json` and `explicit-head.json`.

  The request sets are therefore provably identical to R2's. All variants were run anyway.

## R2b-5 Lint (tip against REV, each from its own export)
- **`campaign_style_lint.py TCSlib/Cryptography --check8b`:** both give 92 FAIL / 104 WARN over 519 files, and the
  **FAIL/WARN line sets are identical**.
  - The only changed line is `Group.lean`'s INFO size line, which goes from 304 lines and 24 public declarations to 331 and 27.
- **`style_lint.py Group.lean`:** 0 findings.
- **`sk15`:** none at REV or at the tip.

## Replay output (kept)
- **`$SP/olean-replay-352`** (REV `3029d8c36c00fd3a4ce27e864a2b43b46309d27f`):
  - 1453 TCSlib/audits/PFR oleans, of which 12 were rebuilt with link count 1 and the rest are hard links to snapshot #3.
  - It also holds the `Mathlib/` overlay (3346 symlinks plus the NthRootLemmas olean).
  - The state check over the full closure (1422) is OK.
  - Disk: 6993 MB free at the start, 6767 MB at the end.
- **Adopt on merge** (recipe step 6) if `git diff --name-only <merge> 3029d8c36c00fd3a4ce27e864a2b43b46309d27f --
  '*.lean' lean-toolchain lake-manifest.json` is empty.
  - That holds if #352 merges onto a branch whose Lean still equals `cf7d28f7`.
  - If #346 merges first, the replay is not adoptable, because `BonehBoyenMachine` is shared downstream. Re-replay
    instead, which costs about 17 modules.
  - Remove `Mathlib/` at adoption.
- The export worktrees `$SP/bb1p2b/wt-rev` and `wt-tip` are scratch and can be deleted.

**Clear to merge**
