# Gate 36 · Special encryption and garbling probability (`sc-garble`, U1, [PS10, §6.2.2–6.2.3]) · round 2

The auditor is Codex. Round 1 was HOLD (0/1/0/0); its findings are `findings/gate36-sc-garble-findings.md` (SHA-256
`b14b8860…`). This round re-audits the fix of G36-01 and checks that nothing new is undisclosed. The round-1 pack
(`pack.md`) still defines the scope; its questions stand for anything round 1 left unverified.

- **PR:** draft [PR #323](https://github.com/Shilun-Allan-Li/tcslib/pull/323), now at
  `8c3f3e3fe2912784f680c10f8c478d2eeeeb7f6a` (branch `land/pass-shelat-sc-garble`, tree
  `41e3febe1241c7af505bc208b72092cfd2e5f513`). Round 1 audited `cd9a48438c2a6548fe9e246ce569be57c9df96b3`.
- **Base:** `1321b9cb358867f5b51974b8c5d0781519a9cfdb`, unchanged: the PR was **not** rebased. It is the merge
  base with the records tip `b0ebd475eb0b4131449bce58462f168f27eee17b`. Since `1321b9cb` the tip has merged #313
  (learning, `10cc8c97`) and records.
- **New since round 1:** one commit, **LE-gate36** `8c3f3e3f`, whose parent is the round-1 head `cd9a4843` (G36-01;
  `SpecialEncryptionMulti/SliceParser.lean` only, +2/−11). It is by the maintainer (author and committer Claude,
  SSH-signed). It was fast-forward pushed (decision-log row "derand and seq-zk reviewed", 2026-11-16);
  `refs/pull/323/head` is `8c3f3e3f`.
- **Built as a replica** (§ 2): the evidence was built on a scratch replica of the branch rebased onto the tip, with the
  same patch. Its hashes differ from the pushed commit's, but the tree it built is exactly the tree of the pushed head
  merged into the tip.
- **Resolutions:** `resolutions-r1.md`, and the decision-log rows of 2026-11-16 (in `verification-r2.zip`).
- **Pending merge condition** (not an audit item; § 5): whichever of #323 and another open PR with a shared
  downstream merges second needs an integration rebuild on the merged tip; the maintainer runs that build.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `SC/` is
`SecureComputation/`.

## What to check

### 1. G36-01: is the duplicate gone, and does `slicePost_encode` use the public lemma?

The diff is `git diff cd9a4843 8c3f3e3f`, the same as the evidence's `checks/le-gate36.diff` and
`landing/0001-…patch`. In `SC/SpecialEncryptionMulti/SliceParser.lean`:

```lean
+import TCSlib.Cryptography.Asymptotic.BlockEncryptor          -- first import line
-/-- Each encoded list has at least as many bits as entries:
-`l.length ≤ (PrivateKeyScheme.encodeList l).length`. -/
-theorem length_le_encodeList (l : List (List Bool)) :
-    l.length ≤ (PrivateKeyScheme.encodeList l).length := by
-  induction l with
-  | nil => rw [List.length_nil, PrivateKeyScheme.encodeList_nil, List.length_nil]
-  | cons a l ih =>
-    rw [List.length_cons, PrivateKeyScheme.encodeList_cons, length_pairEncode]
-    omega
-
   -- in slicePost_encode, local hfuel:
-    have h := length_le_encodeList (l.map Prod.snd)
+    have h := TCSlib.Cryptography.length_le_length_encodeList (l.map Prod.snd)
```

This is your proposed replacement. The public lemma is `TCSlib.Cryptography.length_le_length_encodeList`
(`Asymptotic/BlockEncryptor.lean:70`), whose blob is unchanged from the base to the tip and the head.

Check that the duplicate is removed with nothing in its place, that its one use now reads the public lemma, and that
the import is acyclic. Re-checked for this pack from git objects (`checks/lecheck.txt`):
- The commit touches `SliceParser.lean` only (+2/−11, three hunks). Its declarations go 10 → 9: exactly
  `length_le_encodeList` is removed. The other 9 keep their headers, docstrings, order and definition blocks.
- `length_le_encodeList` occurs nowhere in `TCSlib/` or `audits/` at the head. At round 1 it occurred twice: the
  declaration and this use.
- The new import is acyclic. `SliceParser`'s import closure grows by exactly `Asymptotic/BlockEncryptor` and
  `Encryption/PrivateKey/FromPRG` (147 → 149 modules, the module itself included), and `SliceParser` is not in
  `BlockEncryptor`'s closure. Of the unit files, only the upstream reader file `DAGCircuit` is in that closure. The
  unit's closure grows by `BlockEncryptor` alone (166 → 167), because `FromPRG` was already in it.
- The module docstring's `## Main results` never listed the deleted lemma, so it is unchanged.
- In all 14 unit files, the 259 remaining declarations have byte-identical headers at `cd9a4843` and `8c3f3e3f`, with
  no docstring change.
- decls2 from `cd9a4843` to the head is exactly 1 REMOVED (the duplicate). Against the base it is 54 ADDED, 0 CHANGED,
  0 REMOVED (round 1: 55 ADDED).

**The overlap record:** G36-01 is fixed, not debt, so no ledger row is added. The decision-log rows of 2026-11-16 and
`resolutions-r1.md` record the duplicate and its removal.

**Evidence** (`landing-r1/`): `gate36-le-evidence.zip` (SHA-256
`f77628dd1666d7c2d5eabefce813fa6aee731a496c3d26b89f57b219c201548a`; 670 entries: 41 directories, 629 files = the 628
paths of its manifest `evidence-SHA256SUMS` plus `SHA256SUMS`) and its `PROVENANCE.txt`. At the replica head
`d32328f7` (tree `5662520d`, § 2):
- **Statements** (`statements/`):
  - decls2 against the parent is exactly 1 line, REMOVED `SliceReduction.length_le_encodeList`.
  - The frozen check (issue base `fbd37f44` → head, the review's 6 files, with SG-1's six helpers expected removed)
    gives 0 differences. Apart from the FILE header lines, it is byte-identical to the review's `frozen-check-le.txt`.
  - Against the parent: 0 differences, and 1 of 1 expected removal.
  - `touched`: 1 CHANGED (`slicePost_encode`, its proof), 1 REMOVED, 258 UNCHANGED.
- **Integration build** (`build/`): 392/392 rc 0, 0 errors in both forms (G26-N1), substring "error" 0, 2122 s. This
  is **#323's integration build against the merged #313**.
  - The build set is the downstream of the 14 unit modules (277) plus 115 base-delta modules they need, with root
    `TCSlib` and both `audits/*/Checks`.
  - The 14 unit modules have rc 0, 0 errors and 0 sorries, except Yao's 2 tip admissions. Their only warnings are the
    two SG-F06 ones (`SliceParser`, now line 159; `NestedBounds`).
  - 390 of the 392 modules are byte-identical in source and olean to a reference build. `SliceParser` has the new
    source. `SliceReduction` has the same source but a different olean, because its import closure changed; a rerun
    gives the same olean, so the difference is deterministic.
  - Whole-tree check: RESULT OK (1292 files).
  - Every built source equals its blob in `5662520d` and in the tree of the pushed head merged with the current tip
    (`checks/srcequality.txt`).
- **Axioms:** the 7 targets, B2 (`uprob_not_good_le_of_perm`) and `SliceReduction.slicePost_encode` use
  `[propext, Classical.choice, Quot.sound]`; `length_le_length_encodeList` uses `[propext, Quot.sound]`.
  `yaoHybrid_hbcSecure` and `yaoProtocol_hbcSecure` keep `sorryAx`, traced to the tip's admissions as in round 1.
- **Rule 10** (`rule10/`): `SliceParser.lean` at the head was sealed in strict A/B (2102/2103 requests) and coe A/B
  (2101/2102). All 4 pass (rc 0, 0 errors, install and EOF records), run with `-DmaxErrors=0`. That is 18 more
  requests than round 1's 2084–2085, from the 2 added modules.
  - The collector stores 11 constants (round 1: 13).
  - Paired controls add a row for `PrivateKeyScheme.encodeList`: negative its `rfl` unfolding on a cons, positive
    the published reader `encodeList_cons`.
  - Coe: 4 probes and 7 sealed negatives, `ctlcheck-coe.log` ALL_OK.
  - Strict: 4 probes and 9 sealed negatives, each failing exactly once. `ctlCoeReader` fails in the 2 sealed strict
    probes (the harness effect, as in round 1).
- **Admissions:** 215 at the tip `654323f2` → 208 at the head, −7, the 7 targets (`SpecialEncryptionSecurity` 3 → 0,
  `Garbling` and `GarblingSecurity` 1 → 0, `Yao` 3 → 2, `SpecialEncryptionMulti` 1 → 0); the 9 new unit modules have 0.
- **Lint:** 92 FAIL / 101 WARN, line set identical to the int-313-323-324 merge's.
- **Trial merge with #324** (`trial/`): `git merge-tree --write-tree d32328f7 a6eaebd7` is clean (tree `a025d7ab`);
  both merge orders give the same tree. The downstream of #324 (19 modules, including the 3 it shares with #323) built
  19/19 rc 0, byte-identical to the int-313-323-324 build.
- **Restore:** the olean tree was restored to `457ba704…`, and the snapshot is equal.

### 2. The replica and the pushed commit

The job's `git rebase` of the branch onto the tip was refused by its session's permission system before it ran
(`landing/rebase-refused.log`). So it built and checked an unsigned, unreferenced **scratch replica** instead. The
maintainer then applied the same patch to the real branch, **without a rebase**, as signed `8c3f3e3f` on `cd9a4843`.
The hashes differ, but the content is the same. Re-checked from git objects (`checks/replica.txt`):

| object | replica (evidence) | pushed |
|---|---|---|
| base | the tip `654323f2` (#313 merged) | `1321b9cb` (round 1's base) |
| series | `4366cd96` = the 8 round-1 commits replayed, range-diff 8/8 `=` | the round-1 commits unchanged, head `cd9a4843` |
| LE-gate36 | `d32328f7` (unsigned, no ref) | `8c3f3e3f` (signed) |
| patch | `git diff 4366cd96 d32328f7` | `git diff cd9a4843 8c3f3e3f`, **byte-identical** |
| message | `landing/commit-msg.txt` | identical |
| tree | `5662520d` | `41e3febe` (no #313) |

- `git merge-tree --write-tree 654323f2 8c3f3e3f` is **exactly `5662520d`**, the tree that was built. The replica
  parent's tree `63ce05ff` is likewise `merge-tree(654323f2, cd9a4843)`.
- The tip has since moved to `b0ebd475` with records only (21 paths, no `.lean`). `merge-tree(b0ebd475, 8c3f3e3f)` is
  `f9041e78`. Its `TCSlib` and `audits` subtrees are identical to `5662520d`'s, and it differs from `5662520d` only in
  `briefs/` and the decision log.
- So merging the pushed head into the tip gives the built tree, in every Lean path.

Is anything lost by building the replica rather than the pushed commit?

### 3. The series

`checks/rebase.txt`: `1321b9cb..8c3f3e3f` has 9 commits, each with one `gpgsig`: the 7 Codex worker commits
(author Seyoon Ragavan, committer Claude), LE-doc `cd9a4843` and LE-gate36 `8c3f3e3f` (both author and committer
Claude). The first 8 are round 1's, unchanged.

- **`pr.diff-r2.txt`** is `git diff origin/cryptography/pass-shelat-ch2-4...8c3f3e3f`, which equals
  `1321b9cb..8c3f3e3f` byte for byte (14 paths, 1892 insertions, 122 deletions; round 1: 1901/122).
- **`source-head-r2.json`** differs from `source-head.json` only in `SliceParser.lean` (180 → 171 lines, SHA-256
  `648ac56e…`, none over 100 characters).
- **`sources-r2.zip`** (167 files) is round 1's `sources.zip` (166) plus `Asymptotic/BlockEncryptor.lean`. It differs
  in one other entry, `SliceParser.lean`.

### 4. Duplication: is there any new undisclosed copy since round 1?

- **Since round 1** (`checks/dupscan.txt` A): the only lines changed in the unit files from `cd9a4843` to the head are
  LE-gate36's. No declaration is added; one is removed (the duplicate).
- **Reading-lemma lines** (B): the headD/getD-class and `encodeList`-length lines added since the base are those of
  round 1, with the duplicate's lines gone and the call of `length_le_length_encodeList` added. The `encodeList_nil` /
  `encodeList_cons` rewrites are uses of the published readers. `SliceReduction.length_encodeList_le` (lines 73–84,
  the upper bound `(encodeList l).length ≤ l.length * (2 * B + 2)`) is a different statement and was in round 1's
  scope.
- **Newly merged public lemmas** (C): a statement scan was run, comparing binders and type after whitespace
  normalisation. Each of the 46 theorems new at the head was compared against every theorem in the files the tip
  changed since round 1's base (#313's 5 Learning files) and in each other open PR (#318, #319, #324, #326, #327). It
  found 0 identical statements. No new name of #323 is declared in a file any of them changed
  (`checks/namecheck.txt`). This scan is a mechanical aid; the round-1 search list stands.
- **The pre-existing copies.** DL-46 and DL-47 (with SG-F04) are unchanged. **They are not findings.**
- **Any further undisclosed duplicate of a public lemma is a major**, as in round 1.

### 5. The merge interaction

`git merge-tree --write-tree 8c3f3e3f <x>` is clean for each (`checks/mergetrees.txt`). No path is shared with any
of them. #326 and #327 are taken at their origin heads at the time of the check.

| `<x>` | head | merged tree | downstream of both (`checks/downstream.txt`) | built? |
|---|---|---|---|---|
| the tip | `b0ebd475` | `f9041e78` | 7: #313's 5 Learning modules, `Randomness`, root `TCSlib` | **yes**: § 2, every Lean path = `5662520d` |
| #318 (sc-ot) | `b0bad23a` | `8cdcecbd` | 6: `ObliviousTransfer`, `OT/Predictor`, `OT/ViewB`, `SecureComputation`, `YaoReal`, root `TCSlib` | no |
| #319 (canonizer) | `47daa907` | `32aea21e` | 33 (27 under `TCSlib/Complexity/`, 3 under `Randomness/`, `Asymptotic/Universal`, `audits/pass-shelat/Checks`, root `TCSlib`) | no |
| #324 (sc-compose) | `a6eaebd7` | `db04d413` | 3: `SecureComputation`, `YaoReal`, root `TCSlib` | trial on the tip: 19/19 (§ 1) |
| #326 (derand) | `941b5a1e` | `7b050eb8` | 228 | no |
| #327 (seq-zk) | `e9b5ea47` | `d87f1bab` | 41 (27 under `Composability/`, 12 under `ZeroKnowledge/`, `audits/pass-shelat/Checks`, root `TCSlib`) | no |

- **#326** changes `TCSlib/Complexity/ClassP/DTIME.lean` and `TCSlib/Complexity/Randomized/Build/IterateFind.lean`,
  which are in the unit's closure. Its shared downstream is therefore large (228 modules). No other open PR, and not
  the tip's delta, changes a module of the unit's closure.
- In the other direction, #323's `DAGCircuit` is in the closure of #318's `ObliviousTransfer`, `Predictor` and `ViewB`.
- **Source equality** (`checks/srcequality.txt`), of the 392 built modules:
  - all have the tip-merged source;
  - 387 have the pushed head's own source (the 5 Learning modules differ, because the head does not contain #313);
  - 386 have the source merged with #318, #319 or #324;
  - 385 have the source merged with #326 or #327.
- **Pending merge condition (not an audit item).** A combined integration build of all open PRs is running
  concurrently and is **pending**. Whichever of #323 and #318, #319, #324, #326 or #327 merges second needs an
  integration rebuild of the shared downstream on the merged tip before it merges; the maintainer runs that build.
  Treat it as a condition on the merge, not as something for this audit to establish. What you can raise: a concrete
  reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions and slips (not findings)

- **"REBASE NOT RUN", "no signed commit made" and "PUSH: NOT DONE" in `landing-r1/PROVENANCE.txt`** (and
  `landing/rebase-refused.log` in the ZIP): all were true of the job. Afterwards the maintainer committed the same
  patch as signed `8c3f3e3f` on `cd9a4843` and fast-forward pushed it (§ 2). The branch was never rebased.
- **The PROVENANCE's "the maintainer's rebase + this patch gives the same tree".** The maintainer did not rebase. The
  equivalent statement for what was pushed is § 2's: merging `8c3f3e3f` into the tip gives the built tree.
- **SG-F06** (the two unused-simp-argument warnings) is unchanged from round 1; the `SliceParser` one moved from line
  168 to 159.
- **The PR description is still round 1's.** It does not list LE-gate36; the maintainer updates it before #323 is
  marked ready (it is not in this pack).
- **Job-local names.** `landing-r1/PROVENANCE.txt` refers to `../gate36-le-evidence.zip` and to `$SP` paths; the
  records copies have the same bytes.

## Evidence files

- **`resolutions-r1.md`:** the disposition of G36-01.
- **`findings/`:** the round-1 findings.
- **`landing-r1/`:** `PROVENANCE.txt` (= the ZIP's), `gate36-le-evidence.zip` and its manifest. The patch is the ZIP's
  `landing/0001-…patch`.
- **`verification-r2.zip`** (23 entries; `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source):
  - byte-identical originals at records `b0ebd475eb0b4131449bce58462f168f27eee17b` of the decision log, the
    duplication ledger (DL-46, DL-47), the round-1 sc-garble review and the int-313-323-324 PROVENANCE (the reference
    build);
  - `checks/`, generated from git objects alone: merge trees, downstream, source equality, names, the replica, the
    series, the edit, the duplication scan and decls2, with their scripts.
- **`pr.diff-r2.txt`:** `git diff` from the base to `8c3f3e3f`, 14 paths, 1892/122.
- **`source-head-r2.json`:** hashes, line counts and over-width counts of the 14 changed files at `8c3f3e3f`.
- **`sources-r2.zip`:** the source closure at `8c3f3e3f` of every changed module, 167 files.
- **Round 1:** `outbox/gates/36-sc-garble-gate/` on the exchange at `ab34c528748af26491d896e0f504373b45e4ada1`, with
  records `fb18d199fdce1f8cd1ae94ea9e092c52b157ce86`; `pack.md` here is its pack.

## Findings delivery

Return `gate36-sc-garble-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.
Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report the audited
head and the counts by severity. The gate closes at zero blockers and zero majors.
