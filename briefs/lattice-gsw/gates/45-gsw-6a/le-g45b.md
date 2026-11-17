# Gate 45 · landing edit LE-g45b: docstring follow-up to LE-g45 (one-based cycle notation; `const_eval` no longer a target)

**Verdict: PASS, pushed.** `land/gsw-6a-statements` (PR #359) is now
**`d154c8830fc8ffc52671b41992e7dbef61e30959`** (parent `ad9c4fc701ed145cbc96acceefaad447398c8321`, LE-g45), a
fast-forward. Its tree is **`be58919ee4e1aa52ab1f1441d5b52c41b6caa8d9`**.
- **The edit:** 2 files, +13/−7, comments and docstrings only.
  - **`Barrington.lean`:** the last loose "0-based" phrasings now match LE-g45's wording.
  - **`Combinators.lean`:** `## Main results` moves `const_eval` out of the "(F3; targets)" entry.
- **Code identity:** the comment-stripped code of both files is byte-identical to the parent. Each file has 3 mutation
  controls, all caught, and 1 negative control, which stays equal.
- **Replay:** 16/16 modules rebuilt with rc 0 and 0 errors.
  - The `sorry` warnings are unchanged: 14 modules SAME, and the 2 edited files equal LE-g45's after a +3 line shift.
  - The state check gives **1440/1440 OK**. The 16 rebuilt oleans have link count 1.
  - The parent tree `olean-replay-6a-stmt-g45` rehashes **0/0/0** at the start, after the build and at the end.
- **Admissions 97**, unchanged. The exact-target check gives `RESULT EXACT`, and the admitted (file, name) set equals
  LE-g45's.
- **Axioms:** both probe logs (`AxiomsStmt`, `AxiomsG45`) are byte-identical to LE-g45's, and so is `axtrace`.
- **coe-A seals:**
  - `Barrington`: 119 requests, 0 errors.
  - `Combinators`: 174 requests, 0 errors.
  - The request sets and errors equal LE-g45's.
- Lint shows no new FAIL or WARN.
- **New replay tree:** `$SP/olean-replay-6a-stmt-g45b`. Its output map (Mathlib excluded) has 1471 entries and SHA-256
  **`fa2067748de73f7fd1d0645ed17e5a5163f365a9556a2155d37910f5817d904c`**.
- The PR description is updated.

Run on 2026-11-17, about 11:29–11:45 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`;
the job's directory is `$SP/le-g45b-work`.
- **Evidence:** `le-g45b-evidence.zip`, beside this file. It holds `PROVENANCE.txt`, `SHA256SUMS` (150 files) and
  `tools/TOOLS.txt`. Its SHA-256 is `9f41e81b1023e0d4eb87fbd5a4c45fd09822e134395451c8773e3c2c4053db38`; the zip does
  not contain this file.
- **Diff:** `le-g45b.diff.txt` = `git diff ad9c4fc7 d154c883`, SHA-256
  `68f623288815b5dab8b80d897082bc36a3b1514aeede8e4e26213fb1513ffdf4`.
- **Builds:** no `lake build` and no cache get. One Lean process of this job ran at a time. Before each of the 21 Lean
  processes, the job read the host's slot count: it saw 0 `lean` processes every time and never had to wait.
- **Records:** nothing was committed to the records branch. This file, the diff and the zip are left uncommitted.

## The edit (`git diff --numstat`: Barrington 8/5, Combinators 5/2)
- **Occurrences found.** Every "0-based", "zero-based", "one-based" and "1-based" in the five `BranchingPrograms/` files
  at `ad9c4fc7` is in `Barrington.lean`:
  - `:23`, `:109` and `:117` said "`(12345)`, `(13542)`, 0-based" or "Bar89's `(12345)`, 0-based". These are fixed.
  - `:43–44` and `:340` are LE-g45's corrected wording. They are unchanged.
  - `:456` is C16's "BV14 reads coordinate `1` of a 1-based state". This describes BV14's state indexing and is accurate,
    so it is unchanged.
- **`Barrington.lean:23–24`** (module docstring, Main definitions) now reads: "`sigma1`, `sigma2` — Lemma 3's
  five-cycles `(12345)`, `(13542)` in Bar89's one-based cycle notation, implemented in zero-based form as
  `(0 1 2 3 4)`, `(0 2 4 3 1)`."
- **`:110–112`, the `sigma1` docstring**, now reads: "Bar89's `(12345)` in its one-based cycle notation, whose zero-based
  form `(0 1 2 3 4)` is what the code implements: the five-cycle `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0`, …". The rest of the
  docstring is as before.
- **`:119–121`, the `sigma2` docstring**, is changed the same way, with `(13542)` and `(0 2 4 3 1)`. The check:
  1→0, 3→2, 5→4, 4→3, 2→1.
- **`Combinators.lean`, `## Main results`:**
  - A new entry after the `balanced` readers: "`const_eval` — the constant formula evaluates to its constant (F3);
    proved from `BoolCircuit.eval_node_nil` (an empty gate is a constant), which moved here from `Hierarchy.lean`."
  - The F3 entry now reads: "`xor3_eval`, `maj3_eval`, the other value lemmas of the fan-in-2 gadgets, and the depth and
    fan-in lemmas of every gadget (F3; targets)."
  - That entry is exactly the remaining 17 F3 targets:
    - `depth_const` and `maxFanin_const`;
    - `and2`, `or2`, `xor2`, `xor3` and `maj3`, each with its value, depth and fan-in lemma.
  - The module docstring has no separate list of homed lemmas, so `eval_node_nil` is named inside the `const_eval`
    entry.
- **Line lengths:** every new line is at most 98 characters. One draft line reached 100 and was rewrapped before the
  commit.
- **File sizes:** `Barrington` grows 465 → 468 lines, and `Combinators` grows 633 → 636 lines (the G6A-F06 size watch,
  still under 800).
- **Tooling:** the edits were made by `tools/edit.py`, which asserts that each old string occurs exactly once.

## Code identity (comment-stripping comparison)
- **Method:** `tools/commentstrip45b.py`, which is Gate 44's LE-g44 `commentstrip.py` extended.
  - It removes `--` line comments and nested `/- … -/` block comments, which covers `/--` and `/-!`.
  - It keeps string literals, and char literals as well.
  - Then it compares the stripped texts byte for byte.
- **Runs:** it was run on the parent against the worktree before the commit, and on `ad9c4fc7` against `d154c883`
  (`run/checks/commentstrip.txt`). Both give `RESULT OK`.

| File | Stripped SHA-256 (both revisions) | Comment characters | Code characters |
|---|---|---|---|
| `Barrington.lean` | `69e55110e6749bd08c48725052db4249445e9cf077d20d47376d6d162323d305` | 16854 → 17123 | 8278 = 8278 |
| `Combinators.lean` | `8c8cb4c5725c493b5d4ef29f819679575fa60da051369791b5101a58bd6a8150` | 15995 → 16231 | 14876 = 14876 |

- **Mutation controls** were applied to the new file, stripped, and compared with the stripped parent. All six give
  DIFFER, so all are caught:
  - **M1:** one space after the first code `:=`.
  - **M2:** one code token changed.
    - In `Barrington`, `sigma1`'s body `List.formPerm [0, 1, 2, 3, 4]` becomes `[0, 1, 2, 4, 3]`.
    - In `Combinators`, `TreeCircuit.const`'s body `.node b []` becomes `.node (!b) []`.
  - **M3:** a code line is commented out with `-- `.
    - In `Barrington`, this is `theorem sigma1_eq … := rfl`.
    - In `Combinators`, this is `const_eval`'s proof line.
- **Negative control N1:** one word inside a docstring was changed. It gives EQUAL in both files, as required.

## Commit and push
- **Worktree:** a sparse worktree of the two files at `$SP/le-g45b-work/wt`, on `land/gsw-6a-statements`.
  - The branch was not checked out anywhere else.
  - `git fetch` showed the remote head `ad9c4fc7` before the job started.
  - The worktree was removed afterwards. The local branch is at `d154c883`.
- **Commit:** `git commit -S -F <msg> -- <2 paths>`.
  - The subject is "LE-g45b: docstring follow-up (one-based cycle notation; const_eval no longer a target)".
  - A short body follows, and the message ends with exactly the two required trailers.
  - Author and committer are `Claude <noreply@anthropic.com>`.
  - The SSHSIG key is `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the same as `ad9c4fc7`. This is key
    identity only (`sigkey.py`).
- **Push**, after the replay and every check below:
  - Before: `ls-remote` gave `ad9c4fc7`.
  - `git push origin HEAD:land/gsw-6a-statements` gave `ad9c4fc70..d154c8830`, with no force.
  - After: `ls-remote` gives `d154c883…`.

## Replay (LE-g45's recipe, on LE-g45's tree)
- **Copy:** `cp -al $SP/olean-replay-6a-stmt-g45 $SP/olean-replay-6a-stmt-g45b`.
  - It has 1472 files, all hard links, and 3346 Mathlib symlinks.
  - `olean-replay-6a-stmt-g45` was never written.
- **Pre-check:** before the copy, the parent tree rehashed 0/0/0 against LE-g45's map (`3cb140cb…`, `replayverify.py`).
  The state check of LE-g45's `state.json` (`0a56622f…`) at `ad9c4fc7` gave 1440/1440 OK on both the parent and the
  copy.
- **Export:** a `git archive` of `d154c883` limited to `TCSlib TCSlib.lean audits scripts lakefile.lean lean-toolchain
  lake-manifest.json`, with `.lake/packages` symlinked. It has 1592 files, all blob-exact, the same set as LE-g45's.
  - An unscoped first export (2.2 GB) briefly brought free disk down to 287 MB.
  - It was deleted at once, before any Lean process ran: the slot count was 0, and free disk went back to 2521 MB.
- **Plan:**
  - `downorder.py d154c883 ad9c4fc7` gives changed 2 and **down 16**.
  - `fullorder.py` gives 1440 modules, byte-identical to LE-g45's order.
  - `stateplan plan` gives **16 to build and 1424 reused**. The queue equals `down.txt` and LE-g45's queue.
  - The 16 are the same modules as LE-g45's.
- **Build** (`tools/run-build-g45b.sh`, 11:35:04–11:36:57): the recipe's `runner.py`, unmodified, one module per call.
  - **16/16 rc 0.** `permod.py` gives `error:` 0, `error(` 0, substring 0, and no log/record mismatch.
  - There are 68 warnings, all `declaration uses 'sorry'`, with the same per-module counts as LE-g45.
  - `warncmp` against LE-g45's build gives 14 SAME and 2 NEWSRC (`Barrington`, `Combinators`). The NEWSRC warning lists
    equal LE-g45's once the new line numbers are shifted by −3 (`run/build/newsrc-shift.txt`).
- **Accept:**
  - `stateplan update` took 16 modules and left none out.
  - `check` at `d154c883` gives **1440/1440 RESULT OK**, and again at the end. The resulting `state.json` is
    `788ec08cb411d0647ea9b12d42bb07fb94667ffa3cd8780ac50f25da91881993`.
  - **Link count 1** holds for exactly the 16 rebuilt oleans, whose object hash equals the record.
- **Rehash of the parent tree `olean-replay-6a-stmt-g45`:** `replayverify` gives **0/0/0, RESULT OK** at the start,
  after the build and at the end. The state check at `ad9c4fc7` gives 1440/1440 OK at all three points.
  - `$SP/olean-snapshot` was not used, because another job is replacing it with snapshot #6.

## Output map
- **`$SP/olean-replay-6a-stmt-g45b`** (REV `d154c883`, tree `be58919e`):
  - **Map:** `mapnoml.py`, Mathlib excluded, 1471 entries, SHA-256
    **`fa2067748de73f7fd1d0645ed17e5a5163f365a9556a2155d37910f5817d904c`**.
  - The map file is `run/output-map/olean-replay-6a-stmt-g45b.map-d154c883.noMathlib.tsv`.
  - `replayverify` against it at the end gives OK.
  - **Against `olean-replay-6a-stmt-g45`:** 1469 equal, **2 changed** (`Barrington`, `Combinators`; their docstrings
    are stored in the olean), 0 added and 0 removed. The other 14 rebuilt oleans are byte-identical.
- **Adoptable** in place of `olean-replay-6a-stmt-g45` under LE-g45's conditions, with tree `be58919e`:
  - the merge follows O1 (#358) directly, with the records tip otherwise Lean-equal to snapshot #5;
  - the merge's Lean paths equal tree `be58919e`;
  - the recipe's step-6 checks are run at adoption.
- `olean-replay-6a-stmt-g45` (REV `ad9c4fc7`) is no longer adoptable for #359. It is kept, and this job never writes or
  deletes it.

## Checks
- **Admissions** (`admcheck.py` against `e1d39836`, using LE-g45's merged logs with this run's 16 on top;
  `touched.json` regenerated at `d154c883` over LE-g45's 17 files):
  - The names, statuses and kinds in `touched` equal LE-g45's.
  - Head 97: Combinators 23, Barrington 11, and all others as in LE-g45.
  - **Exact-target check:** the delivered row map minus `rename_eval`, `depth_rename` and `const_eval` gives 97 targets,
    97 admitted, 97 matched, 0 extra, 0 twice and 0 missing: **EXACT**.
  - The admitted (file, name) set equals LE-g45's (0 diff lines).
- **Axioms:**
  - `AxiomsStmt.lean` and `AxiomsG45.lean` are LE-g45's sources, unchanged, run on the new tree. Both logs are
    **byte-identical** to LE-g45's head logs.
  - `axtrace` output is identical to LE-g45's:
    - 545 constants;
    - no non-standard axiom other than `sorryAx`;
    - `sorryAx` in 102 constants, the 97 targets plus the 5 dependents (two definitions and three theorems).
  - `eval_node_nil` and `const_eval` use `[propext, Classical.choice, Quot.sound]`. Their home is `Combinators`.
- **Rule 10, canonical coe-A** (`tools/rule10_g45b.sh`; collector and `mkseals_coe.py` as in LE-g45; `SEAL_CHUNK=1000`;
  owners `Combinators` and `Barrington`; head only, compared with LE-g45's head records by `sealcmp_g45b.py`):

  | Owner | Requests (LE-g45b / LE-g45) | Errors | Request names | Closure modules | Error lines |
  |---|---|---|---|---|---|
  | `Combinators` | 174 / 174 | 0 / 0 | equal | 3 / 3 | equal (none) |
  | `Barrington` | 119 / 119 | 0 / 0 | equal | 2 / 2 | equal (none) |

  - The sealsum rows (requested, rc, errors, install, EOF, failing declarations) are equal: `RESULT OK`.
  - The probe and source SHA-256 differ only because the comments differ.
  - `Hierarchy` was not re-sealed: it is not edited, and its olean is byte-identical to LE-g45's.
- **Lint** (from the export):
  - `campaign_style_lint TCSlib/Complexity --check8b` gives 25 FAIL / 390 WARN over 513 files. The FAIL/WARN line set is
    identical to LE-g45's head (0 diff lines).
  - Only 3 INFO lines change: Barrington 465 → 468 lines, and Combinators 633 → 636 lines on two lines.
  - `style_lint` on `Combinators`, `Barrington` and `Hierarchy` gives output byte-identical to LE-g45's head. Its 2
    findings are the pre-existing `Hierarchy:17` false positives.
- **`git diff`:** limited to the two files.

## PR description
- The #359 body was updated by `update_pull_request` and read back. The stored text equals the text sent, and the ending
  is exactly the required two lines. No reset was needed.
- **Changed:**
  - the head (`d154c883`, tree `be58919e`) and the eight commits, with what LE-g45 and LE-g45b each changed;
  - admissions 97 (Combinators 23);
  - files 18, since `Hierarchy` is added by LE-g45;
  - axioms (545 constants, and `eval_node_nil`/`const_eval`);
  - the LE-g45/LE-g45b replay, seal and lint lines;
  - the Gate 45 round 1 result: #358 CLEAR, #359 HOLD on G45-01, fixed by LE-g45; G45-02 and G45-03 fixed, with
    LE-g45b completing G45-03's wording;
  - the merge order now names `olean-replay-6a-stmt-g45b`, tree `be58919e` and the new map SHA-256.
- **Fixed slip:** "98 targets and five definitions" became "97 targets and five dependents, two definitions and three
  theorems".
- **Not changed:** the PR **title** still says "(98 targets)". It was outside the brief (body only) and is left for the
  coordinator.

## Deviations and notes
- **Disk dip:** the first export was unscoped. See the Replay section: it was deleted at once, and no Lean process was
  running.
- **Rule 10 scope:** head-only seals, compared with LE-g45's head records. LE-g45 sealed against a re-run base. That was
  not needed here, because the comparison target is LE-g45's verified head.
- **Not touched:**
  - `$SP/olean-snapshot`, which another job is swapping;
  - `olean-replay-6a-stmt-g45`, which was read and hard-linked only;
  - `le-g45-work`, which was read only, with files copied out of it;
  - other agents' directories, every other records file, and the fill branches.
- **Cleanup:**
  - Removed: the worktree and the export.
  - Kept: `$SP/olean-replay-6a-stmt-g45b` and `$SP/le-g45b-work/run` (4.6 MB).
  - Disk: 2524 MB free at the start, 2576 MB at the end.
