# bb1-sim-statements · maintainer delivery review (r1), phase 2: merged-tree Lean replays

**Verdict.**
- **`land/bb1-sim-games`** (`dfacac35`): **PASS**. It is ready for its PR.
- **`land/bb1-sim-group`** (`92dea4f8`, with LE-grp1): **PASS**. It is ready for its PR, which merges after the Games PR
  and a 12-module re-replay on the new snapshot (§ P2-8).
- Phase 2 found 0 blockers, 0 majors, 0 minors and 3 new infos (BS-F11–BS-F13).
- BS-F03, BS-F04 and BS-F05 are closed. BS-F06 is reconfirmed as pre-existing at the tip.
- Every check in `PHASE2-PLAN.txt` P2-0 to P2-7 holds:

  | Check | Games head | Group head |
  |---|---|---|
  | Range-diff (landing commits against the reproduced series) | 2/2 `=` | 1/1 `=`, plus LE-grp1 |
  | Rebuilt modules | 181 | 12 |
  | Every rebuilt module | rc 0, 0 `error:`/`error(` | the same |
  | Admissions against the tip | +2, exactly the two targets | +0 |
  | Axioms and census | as expected | as expected |
  | Seals (strict A/B, coe A/B) | as expected; strict `dist_apply` failure identical at the tip | as expected, 0 errors |
  | Controls | ALL_OK | ALL_OK |
  | Explicit-unfold scan | 0 foreign | 0 foreign |
  | Lint | no new FAIL/WARN | no new FAIL/WARN |

  The cross-build of tip × #346 × both heads gives rc 0 and admissions −1 +2.
- The snapshot rehashed 0/0/0 four times: before the replays, after R1, after R2, and at the end.

Run on 2026-11-17, 01:55–02:55 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `bb1-sim-statements-r1-phase2-evidence.zip`, under `bb1-sim-statements-r1-phase2/`. It has
  `PROVENANCE.txt` and `SHA256SUMS`, and its own SHA-256 is in `evidence-SHA256SUMS`.
- **Not done:** nothing was committed, pushed or `git add`ed, no PR was opened, and the landing branches stay local.
- **Builds:** there was no `lake build` and no cache get, and this job ran one Lean process at a time.
- **#346's job:** its directories (`$SP/p346`, `$SP/olean-replay-346`) and processes were not touched.

## P2-0 Tip and snapshot
- `git fetch` gave the records tip **`f472accd5e000a53d0fbe02b5414435429ce4a70`** ("Records: bb1-sim landing branches
  built; phase 2 started").
  - It is records-only since `7486e401`.
  - It has the same `TCSlib/`, `TCSlib.lean`, `audits/`, `scripts/`, lakefile, toolchain and manifest as:
    - `7486e401`;
    - the landing parent `176cfd4a42ac3300d9b84f9045f7abcd0f52ef13`;
    - snapshot #2's T `a6d01b1b`.

    In each case 0 files differ, so `landing/` did not need to be redone.
  - The landing branches sit on `176cfd4a`, an ancestor of the tip.
  - `merge-tree` of the current tip with each head (`787cd003`, `b293ebff`) is Lean-equal to that head's own tree.
- **Snapshot #2** (`$SP/olean-snapshot`) was rehashed with `snapmap.py verify` against map `95493449…c111`.
  - Each run had 1452 files and gave **0 extra / 0 changed / 0 missing**, with no symlinks and no empty directories.
  - It ran before R1, after R1, after R2, and after the P2-7 discard (`snapshot/`).
  - The snapshot was never written to, and was read only as the source of `cp -al`.

## P2-1 Landing branches
- **Range-diffs** (`landing/p2-1-landing.txt`):
  - `bdcadd85..d742bf02` against `176cfd4a..land/bb1-sim-games` gives **2/2 `=`**: `912a343e`→`02000ad4` and
    `d742bf02`→`dfacac35`.
  - `bdcadd85..fc9cf2f5` against `176cfd4a..land/bb1-sim-group` gives **1/1 `=`** (`fc9cf2f5`→`2cca41bc`), and
    `> 2: 92dea4f8` is LE-grp1, the only other commit.
- **Trees** (`landing/p2-1-trees.txt`):
  - The games head's tree is `c6d3bed3`. It equals `merge-tree 176cfd4a × d742bf02`, and it is Lean-equal to phase 1's
    `fe093214`: 0 Lean/lake paths differ. The 5 paths that do differ are the records files the tip gained since `7486e401`.
  - `land/bb1-sim-group~1` has tree `8740ccb6`, which is Lean-equal to `dd8d3efc` in the same way.
- **LE-grp1:**
  - Its hunks are byte-identical to `landing/LE-grp1-proposed.diff`, and its diff is −7 lines in `Group.lean` only.
  - `Group.lean` at the group head has SHA-256 `59c605e1…6213` and 331 lines, which is the pin.
- **Insertion checks against the tip** (`176cfd4a`; phase 1's `insertion_check.py`; `landing/insertion-check-vs-tip.txt`):
  - **PASS** for `Probability` (anchors 48 and 403; the head and `~1` both pass), `Games.lean` (9 and 42),
    `Group.lean` at `~1` (62 and 232), and `Group.lean` at the LE-grp1 head (62 and 232).
  - The LE-grp1 head also passes its five controls (ALL_OK). Removing the blocks restores the tip byte for byte.
  - `Relational.lean` is absent at the tip.
- **Export check** (`landing/export-check.txt`):
  - The three Games files at the head equal the delivery's `src/games-relational/` byte for byte.
  - `Group.lean` at the head differs from `src/group-helpers/` by exactly the LE-grp1 lines, and `~1` equals `src/` byte for byte.
- **`natCast_inj_of_lt`:**
  - At the group head, no Lean or blueprint file names it (`git grep` rc 1 over `TCSlib`, `TCSlib.lean`, `audits` and
    `blueprint`), and neither does any Lean file at the games head.
  - The only hits are records Markdown, which is history: the decision-log rows, the issued brief and `review.md`.
  - The R2 probe confirms that no constant of that name exists in `Group`'s import closure (§ P2-5).
- **Signatures** (`landing/signatures.txt`, `tools/sigkey.py`):
  - All four landing commits carry an SSHSIG with key `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`. That is the key
    of the records commits `176cfd4a` and `7486e401`.
  - The series commits are unsigned.
  - This is key identity only, not a cryptographic check (BS-F12).

## P2-2 Replay R1, the Games PR
- **Recipe:**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-bb1sim-games`.
  - The overlay (`mloverlay.sh`: 3346 symlinks) and `mathlibextra.sh` NthRootLemmas, whose olean is `c0a9cff0…`.
  - `stateplan init`: 1421 modules at `a6d01b1b`.
  - `downorder.py`: changed 3, down 181.
  - `fullorder.py`: 1422 modules, the roots being `TCSlib` and both Checks.
  - `stateplan plan`: **181 to build, 1241 reused**.
  - The worktree is a `git archive` export of `dfacac35`. `exportcheck.py` gives 1574/1574 blobs, 0/0/0.
- **The queue equals `landing/down-games-pr-merged.txt` as a set** (181).
  - It is `Probability` and its downstream: the 150 modules of the issued DOWN-PROBABILITY and the 27 `Yao/HybridProof` modules.
  - It also has `Relational`, root `TCSlib`, **`audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`** (BS-F04 and
    BS-F05 are closed).
- **Build** (`runner.py` through `scripts/lean_check_tree.sh`, 01:58:26–02:16:44, 1099 s of module time, max RSS 4.4 GB):
  - **181/181 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, and there were no log/record mismatches (`permod.py`).
  - 17 warnings, of which 6 are `sorry`.
- **Accept:**
  - `stateplan update` took 181 modules, and `check` over the full order gives **1422/1422 OK, RESULT OK**. It held again
    at the end.
  - **All 181 rebuilt oleans have link count 1**, with object hash equal to the record. The other 1272 files stay hard links.
- **Warnings** (`r1-games/checks/warnings-vs-snapshot-build.tsv`): **181/181 SAME.**
  - Each module's warning lines equal the log of a build of the same source:
    - 173 against the snapshot's own build logs (advance 33, rebase 140);
    - 5 unchanged `Games/*` modules against the worker's bootstrap at `bdcadd85` (same source; snapshot #0 reused them,
      so the rebase evidence has no log);
    - `Probability`, `Relational` and the facade against the worker's series-1 head sweep (same source).
  - **`Relational` has exactly 2 `sorry` warnings**, at 85:8 (`expect_simulate_rel`) and 124:8 (`expect_sample_rel`).
  - `Probability` has 0.
- **Admissions** (`admissions/r1-delta.txt`, `admdelta.py`): against the tip, **+2**. Both are `Relational`, the two
  targets, and every other rebuilt module has delta 0. The source token census agrees: the tip has 792 `sorry`/`admit`
  tokens in 76 files, and the games head 794 in 77, the only change being `Relational.lean` +2.
- **Name resolution, BS-F03** (`probes/games/runs/mods/Bb1sProbe_ResolveGames.log`, attempt 2):
  - `Forgery` rebuilt with rc 0 and no warnings.
  - The value of `ETTGame.abs_ettAcc_rej_sub_le`, the theorem that calls the averaging bound at `Forgery.lean:545`, uses
    exactly one `*abs_expect_sub_le_expect`: `_private.…Forgery.0.…ETTGame.abs_expect_sub_le_expect`, the private
    copy, not the public lemma.
  - The import closure holds exactly two declarations of the name: that private copy and
    `TCSlib.Cryptography.Games.ProbComp.abs_expect_sub_le_expect`.
  - The two types are alpha-equivalent (`==`), and the binders are `c f g h hb`. Only the type binder is named
    differently, `α` against `β`.
  - With `open TCSlib.Cryptography.Games ProbComp`, `resolveGlobalConst` gives exactly one constant, the public lemma,
    and the no-overload form gives no ambiguity error.
  - Inside `namespace …ETTGame` with Forgery's own `open` line, the bare name resolves to the public lemma only. Outside
    `Forgery.lean` the private copy is invisible, which is the situation after the Stage 2 deletion.
  - Forgery's call shape `abs_expect_sub_le_expect (h := h) c hb` elaborates there.
  - BS-F03 is closed: the re-point is safe.

## P2-3 Axioms (R1; probe importing the facade `TCSlib.Cryptography.Games`)
- **`#print axioms`:**
  - `abs_expect_sub_le_expect` uses `[propext, Classical.choice, Quot.sound]`.
  - `expect_simulate_rel`, `prob_simulate_rel` and `expect_sample_rel` use those plus `sorryAx`.
- **Census:**
  - `Probability` has 57 stored constants, with 0 non-standard axioms.
  - `Relational` has 3, all with `sorryAx` (the three lemmas).
  - Together that is **60 constants, non-standard only in those three**, as the worker found.
- **Trace:**
  - `expect_simulate_rel` reaches only itself (closure 5009), and `expect_sample_rel` reaches only itself (5364).
  - `prob_simulate_rel` reaches exactly `expect_simulate_rel` (5012).
  - `abs_expect_sub_le_expect` reaches none (10759).
- The StmtDump types equal the delivered headers.

## P2-4 Rule 10 on R1
- **Method:**
  - The worker's `rule10_stmt.sh`, adapted to `tools/rule10_bb1s.sh`: an export worktree, the R1 output as the tree,
    and `touched.json` against the tip.
  - The archived Gate 06/10 harness.
  - Whole-file probes with `-DmaxErrors=0`, with install and EOF records.
- **Seals.** The table gives the requests per variant (strict A / strict B / coe A / coe B), with the base taken at the
  tip from the snapshot (see "Base seals" below):

  | Owner | Head | Base (tip) | Errors |
  |---|---|---|---|
  | `Probability` | 36/36/35/35 | 36/36/35/35 | coe A/B 0; strict A/B 1 each, `ProbComp.dist_apply` |
  | `Relational` | 53/53/52/52 | new file | 0 in all four |

  - The strict `dist_apply` failure is identical at the tip, so it is **pre-existing (BS-F06, DW-10/Stage 2), not new**.
  - The request name sets of `Probability` equal the tip's in all four variants, and the sealsum rows are identical.
  - Strict A minus coe A is exactly `FinDist.instCoeFunForallReal`, for both owners.
  - Every probe has install and EOF records.
- **Controls** (`mkctl_bb1s.py`, the covering subset; 8 probes per harness):
  - 6 sealed negatives per harness (the `expect` and `AllOutputs` rows), each failing exactly once.
  - 0 positives fail, and the unsealed probes give 0 errors.
  - **ALL_OK in strict and in coe.**
- **Explicit-unfold scan** of `Games.lean`, `Probability.lean` and `Relational.lean`: 101 items (85 THEOREM,
  14 LOCAL_OR_UNRESOLVED, 2 OWNED_DEFINITION), **0 foreign**.
- **Base seals** (`rule10/base`): at the tip, from a `cp -al` copy of the snapshot plus the overlay. It was read only by
  the probes and deleted afterwards.
  - `Probability` 36/36/35/35, with the same `dist_apply` failure in strict A/B.
  - `Group` 567/568/567/568, 0 errors.
  - `Assumptions` 644/645/643/644, 0 errors.

## P2-5 Replay R2, the group PR (LE-grp1 applied)
- **Recipe** as for R1: `$SP/olean-replay-bb1sim-group`, export `92dea4f8` (1573/1573 blobs, 0/0/0), and its own
  NthRootLemmas (`c0a9cff0…`).
  - The plan is **12 to build, 1409 reused**, exactly `landing/closures.txt`'s 12, because #346 has not merged.
  - Those 12 are `Group`, `Assumptions`, `Operations`, the `Pairing` facade, `Joux`, the `KeyExchange` facade,
    `BonehBoyen`, `BonehBoyenMachine`, `BonehBoyenSecurity`, the `IdentityBased` and `AdvancedEncryption` facades, and
    root `TCSlib`.
- **Build** (02:39:32–02:40:01): **12/12 rc 0**, with 0/0 errors.
  - The state check gives **1421/1421 OK**, and it held again at the end.
  - **All 12 rebuilt oleans have link count 1.**
  - Warnings: 11 SAME and `Group` NEWSRC with 0.
  - The `sorry` warnings are unchanged: `Assumptions` 1, `BonehBoyenMachine` 1 and `BonehBoyenSecurity` 2.
  - **Admissions delta 0** against the tip, and the source census is 792 = 792.
- **Axioms** (`probes/group`):
  - `pow_val_add`, `pow_val_neg` and `pow_val_bijective_of_ne_one` use `[propext, Classical.choice, Quot.sound]`.
  - The **`Group` census is 82 constants with 0 non-standard**. That is the worker's 83 minus `natCast_inj_of_lt`.
  - `natCast_inj_of_lt` is absent, and no constant `*natCast_inj_of_lt` exists in the closure.
- **Seals** (requests: strict A / strict B / coe A / coe B):

  | Owner | Requests | Errors |
  |---|---|---|
  | `Group` | 567/568/567/568 | 0 |
  | Carrier `Assumptions` | 644/645/643/644 | 0 |

  - **The request name sets equal the tip's** in all eight owner and variant pairs. LE-grp1 removes a theorem and
    changes no request.
  - Strict A minus coe A: `Group` none, `Assumptions` `FinDist.instCoeFunForallReal`.
  - Every probe has install and EOF records.
- **Controls:** **34/34 sealed negatives per harness**. The breakdown is `Assumptions` 12 (A) and 13 (B), and `Group`
  4 (A) and 5 (B).
  - Each fails exactly once, 0 positives fail, and the unsealed probes give 0 errors.
  - **ALL_OK in strict and in coe.**
- **Scan** of `Group.lean`: 56 items (41 THEOREM, 15 LOCAL_OR_UNRESOLVED), **0 foreign**. The worker's 59 included the
  dropped helper.

## P2-6 Lint (tip against each head; each run from its own export; `lint/`)
- **`campaign_style_lint.py TCSlib/Cryptography --check8b`:**
  - The tip gives 92 FAIL / 104 WARN over 518 files.
  - The games head gives 92 / 104 over 519, and the group head 92 / 104 over 518.
  - **The FAIL/WARN line sets are identical** to the tip's. Only the INFO size lines of the changed files change
    (`Games.lean` 64→67, `Probability` 409→423, `Relational` new at 134, `Group` 304→331).
  - Phase 1's 92/103 over 450 was at the issue base.
- **`style_lint.py`** on the 4 changed files: 0 findings.
- **`sk15`:** none at either head (or at the tip).

## P2-7 Cross-build (recommended; done)
- **Tree.** `git` 2.43's `merge-tree --write-tree` takes commits only, so the four-way tree was formed as follows
  (`p2-7/merge-trees.txt`):
  - `merge-tree 176cfd4a × 89a18a82` gives `ca0fad79`, Lean-equal to phase 1's `ac9e7958`.
  - `merge-tree` of the two landing heads gives `31c1b497`.
  - A 3-way `read-tree -m 176cfd4a ca0fad79 31c1b497` into a temporary index gives 0 unmerged entries. `write-tree`
    then gives **`66fdaf9566a6bd6c1a3786fe8e796ee3c26d4d0d`**.
  - Without LE-grp1 the same steps give `752fb43c`, which is Lean-equal to phase 1's `21c1aa45`.
  - `66fdaf95` differs from `21c1aa45` only by LE-grp1 (−7 lines).
- **Build.** The cross-build ran in a further `cp -al` of the R1 output, with R1's checked state.
  - The plan rebuilt only **18 modules**, the #346 closure and the `Group` closure, with 1409 reused.
  - **18/18 rc 0** and 0/0 errors.
  - The state check gives **1427/1427 OK**, and all 18 rebuilt oleans have link count 1.
- **Admissions against the tip:**
  - **−1** at `BonehBoyenMachine` (T4, #346).
  - **+2** at `Relational`, carried in the reused R1 olean.
  - The net is **+1**, as expected; the source census is 792 → 793.
- **Trace:**
  - `bb1_sidSecure` reaches exactly `bb1_sim_random` and `bb1_sim_real`.
  - `exists_bb1_distinguisher` reaches none.
  - The three `Relational` traces are as in P2-3, and `pow_val_bijective_of_ne_one` reaches none.
- The output and its export were **discarded** after their evidence was recorded, and the snapshot then rehashed 0/0/0.

## P2-8 Merge order and adoption (for the maintainer; nothing merged here)
1. **Merge the Games PR first.** It has the largest rebuild, 181 modules.
   - On merge, run `git diff --name-only <merge> c6d3bed311a83f217428576b08065b5743003ec1 -- '*.lean' lean-toolchain
     lake-manifest.json`. The tree `c6d3bed3` is Lean-equal to `merge-tree f472accd × dfacac35` = `787cd003`.
   - If the diff is empty, adopt `$SP/olean-replay-bb1sim-games` (recipe step 6), and add `snapshots.md` row #3.
2. **Then re-replay #346 and the group PR on the new snapshot.**
   - `BonehBoyen*` lies in both `Probability`'s downstream and theirs, so their current replay outputs
     (`olean-replay-346`, `olean-replay-bb1sim-group`) will not be adoptable after the Games merge. Their prospective trees
     change in the Games files.
   - Each re-replay rebuilds only its own closure: 12 modules for the group PR, or 17 if #346 has merged.
   - Expect the same results. P2-7 already built all four together with rc 0.
3. Cleanup Stage 1's `Games.lean` insertions merge cleanly with series 1 (phase 1, BS-F09).

## Findings (phase 2)
| # | Severity | Finding | Disposition |
|---|---|---|---|
| BS-F03 | info, closed | Resolution probe: the Forgery call uses the private copy now. After the Stage 2 deletion the bare name resolves to the public lemma uniquely, with alpha-equivalent types and the same value binders. | None. |
| BS-F04, BS-F05 | info, closed | Both `audits/*/Checks` and the 27 `Yao/HybridProof` modules rebuilt rc 0 at the merged tree (R1, 181 modules). | Fix the pack template (BS-F04) at the next issue. |
| BS-F06 | info, pre-existing (reconfirmed) | Strict A/B of `Probability` fail once at `ProbComp.dist_apply`, identically at the tip (request sets equal). Coe passes. | DW-10 / Stage 2. Not new. |
| BS-F11 | info | The cherry-picked commit `2cca41bc` keeps the worker's message: "four proved helpers … and `natCast_inj_of_lt` … Mathlib states none of them in a directly usable form". LE-grp1 (`92dea4f8`) in the same PR removes that helper, the message's claim is wrong for it (BS-F01), and the range-diff requires verbatim messages. | State it in the group PR body: "LE-grp1 drops the fourth helper (BS-F01); Mathlib's `CharP.natCast_injOn_Iio` is used instead". No rewrite. |
| BS-F12 | info, process | Trailers and signatures.<br>• The two Games picks and the group pick carry the worker session's `Claude-Session` trailer (`…VTjgrz…`) and no maintainer trailer. LE-grp1 carries this session's (`…VTiuDcj…`). This is consistent with #346's landed picks.<br>• All four commits are SSH-signed with the records key `SHA256:32dP45eS…` (BS-F08: an account-wide platform key).<br>• `ssh-keygen` is not installed and the configured `.pub` is empty, so the signatures were identified by key, not verified. | None. GitHub's verification on push is the check. |
| BS-F13 | info, my evidence | My first `ResolveGames` probe failed at elaboration (5 errors): it called `ConstantInfo.getUsedConstants`, which this Lean lacks. Attempt 2 uses `getUsedConstantsAsSet`, as the axioms probe does, and passes. Attempt 1 is kept (`probes/games/attempt1/`). | None. This is a defect of the probe, not of the module. |

## Replay outputs (kept; they become snapshots on merge)
- **`$SP/olean-replay-bb1sim-games`** (R1, REV `dfacac35`, prospective tree `c6d3bed3`):
  - 1454 files: 1453 TCSlib/audits/PFR oleans plus NthRootLemmas, and 3346 Mathlib overlay symlinks.
  - 181 rebuilt oleans, each with link count 1; the rest are hard links to the snapshot.
  - The state check over the full closure (1422) is OK.
  - Remove `Mathlib/` at adoption.
- **`$SP/olean-replay-bb1sim-group`** (R2, REV `92dea4f8`, tree `863b2926`):
  - 1453 files and 3346 symlinks.
  - 12 rebuilt oleans with link count 1.
  - The state check over 1421 is OK.
  - Adoptable only if it merges before the Games PR; otherwise re-replay (P2-8).
- **Disk:** 7530 MB free at the start, 6948 MB at the lowest point and about 6989 MB at the end. The export worktrees
  (`$SP/bb1p2/wt-*`) are scratch and can be deleted.

**Phase 2 done: both landing branches pass and are ready for their draft PRs. Order: Games PR first, then re-replay the
group PR (12 modules) before it merges.**
