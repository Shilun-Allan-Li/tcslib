## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/pack-r2.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/resolutions-r1.md =====

# Gate 36 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 1 major, 0 minors, 0 notes.
- **Findings:** `findings/gate36-sc-garble-findings.md`, SHA-256 `b14b8860d26206cb6016cc00f7b9a376bed619a0ac94ffbc2aaffe0889c1f4fb`. The companion ZIP was not supplied.
- **Audited head:** `cd9a48438c2a6548fe9e246ce569be57c9df96b3`, records `fb18d199`, exchange `ab34c528`.

Codex found all seven targets and B2 correct against [PS10 §§6.2.2–6.2.3], with every edge case covered. It also confirmed:
- `specialScheme_multiMessageSecure` is proved directly from D4;
- the B1 maximization keeps the empty-set convention;
- Gate 27 obligations (1)–(6) are met;
- SG-1 removes exactly six helpers, and both controls behave as specified;
- the stricter `Yao.lean` rule holds;
- the SG-F01 reader adds exactly nine lines;
- the seals and controls verify, and seal B's nine new errors are the disclosed `PolyExpr.eval` ones;
- the axioms are standard.

| # | Severity | Disposition |
|---|---|---|
| G36-01 | major | **To be fixed by LE-gate36, a maintainer landing edit.** `SliceReduction.length_le_encodeList` (`SpecialEncryptionMulti/SliceParser.lean:119–126`) re-proves the public `TCSlib.Cryptography.length_le_length_encodeList` (`Asymptotic/BlockEncryptor.lean:53–76`) for the same encoder and domain. The fix removes the new duplicate and points its one use in `slicePost_encode` at the public lemma. It imports `Asymptotic/BlockEncryptor`, which is acyclic and adds 2 modules to the closure. The overlap record is corrected. No frozen declaration changes. |

**Next:** the edit is made on the landing branch, rebased onto the tip (which includes #313), then rebuilt and re-sealed. After that, Gate 36 round 2 runs.

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/findings/gate36-sc-garble-findings.md =====

# Pass–shelat Gate 36 — sc-garble

**Verdict: HOLD.** **0 blockers, 1 major, 0 minors, 0 notes.** The seven target proofs and B2 survive this source/evidence audit. G36-01 is an undisclosed re-proof of an existing public lemma, which the dispatch explicitly grades as a major.

| Pin | Audited revision |
|---|---|
| Repository / PR | `Shilun-Allan-Li/tcslib` / draft [#323](https://github.com/Shilun-Allan-Li/tcslib/pull/323) |
| Lean head | `cd9a48438c2a6548fe9e246ce569be57c9df96b3` |
| Lean tree | `13aa553d035fd55cf73c7123ebb73c1940019f1c` |
| Landing base | `1321b9cb358867f5b51974b8c5d0781519a9cfdb` |
| Campaign records | `fb18d199fdce1f8cd1ae94ea9e092c52b157ce86` |
| Exchange | `ab34c528748af26491d896e0f504373b45e4ada1` |

I read the pinned README, pack, bundle, changed sources, relevant providers, rulings and evidence. I reran byte, archive, declaration and scope checks against git objects, and checked the supplied build/seal records against their raw logs and source/probe hashes. **I did not execute Lean:** this environment has no Lean/lake toolchain. Kernel-build and seal outcomes below therefore describe verified supplied evidence, not an independent compilation.

**Finding**

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G36-01 | **major** | `SecureComputation/SpecialEncryptionMulti/SliceParser.lean:119–126`, `SliceReduction.length_le_encodeList` | Re-proves the existing public `TCSlib.Cryptography.length_le_length_encodeList` on precisely the same encoder and domain, without disclosing that overlap. | `Asymptotic/BlockEncryptor.lean:53–76`; worker report, “Overlap and reuse”; DL-46/DL-47. See `evidence/G36-01-source-excerpts.txt`. | Remove the new duplicate and use the existing public lemma in `slicePost_encode`'s fuel bound; import its provider and rerun the affected checks. |

Paths in this finding are under `TCSlib/Cryptography/`.

The equality of the statements is exact after resolving the existing file's `open PrivateKeyScheme (encodeList)`:

```lean
-- New: SecureComputation.SliceReduction.length_le_encodeList
-- Existing: TCSlib.Cryptography.length_le_length_encodeList
(l : List (List Bool)) → l.length ≤ (PrivateKeyScheme.encodeList l).length
```

The existing theorem is public and byte-identical at both the issue base `fbd37f44…` and the audited head. Both proofs induct on `l`, use the encoder's nil/cons equations and the pairing length formula, and finish with arithmetic. This is not merely a similar bound for another carrier.

The worker report instead identifies the private `ETTGame.length_le_length_encodeLog` and the structured-history bounds `EffFill.length_le_length_encodeHist` / `length_encodeLog_le` as the nearest relatives. It does not identify this exact public theorem. The review's duplication search repeats those relatives and misses it. DL-46 covers the `encodeList_eq_flatMap` copies and named related material; DL-47 covers getD/headD copies, including SG-F04. Neither lists this length-bound duplicate. Those dispositions therefore do not discharge G36-01.

A direct replacement at the use in `slicePost_encode` is:

```lean
have h := TCSlib.Cryptography.length_le_length_encodeList (l.map Prod.snd)
```

The current import graph has no path from `Asymptotic/BlockEncryptor.lean` to `SliceParser.lean`, so importing that provider introduces no import cycle. This proposed repair has not been compiled here. Update the overlap report and declaration inventory after removing the duplicate; keep every frozen declaration unchanged.

**Proof audit**

The source comparison used [PS10, §§6.2.2–6.2.3](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf), Algorithm 157.2 and the extra wrong-key property, together with the frozen interfaces and the pack's stated deviations. The formal garbling conclusion is correctness of the first successful opening; its weaker relationship to the book's unique-opening wording is already disclosed.

1. **`spDecStr_wrongKey` — correct.** `spDecStr_none_iff_prefix_ne` proves that honest ciphertexts pass all length guards and failure is exactly inequality of the two pad prefixes. `hG'.easy` supplies the efficient evaluator used by the test; the conclusion's potentially inefficient `E'` is needed only on canonical inputs, where `hGE'` specifies the same family. The reduction uses D3's one-query machine and D1 at budget one. Conditional on the nonce and independent comparison key, a random-function answer has a uniform `n`-bit prefix, so acceptance is exactly `2⁻ⁿ`. The PRF advantage plus `2⁻ⁿ` bounds prefix collision; one further positive `2⁻ⁿ` gives the frozen strict inequality. At `n = 0`, both prefixes are empty and the extra positive term still gives strictness.

2. **`specialScheme_wrongKey` — correct.** The new key/nonce equivalences preserve their encoded strings. The public activation readers identify the scheme's algorithms with string encryption/decryption, and `uprob_fst` averages away decryption coins. String failure produces a word of length `n+1`, so `decodeFin n` returns `none`. Monotonicity transfers the strict string bound to the required scheme event.

3. **`specialScheme_multiMessageSecure` — correct and directly from D4.** The proof invokes `MultiMsg.exists_negligible_distAdv_prfEncRealOut` in `SpecialEncryptionSecurity.lean`, with full-width masks `0^n ++ m_i`. The shared zero-prefix identity identifies each encoded ciphertext after the key/nonce coin equivalence. `acceptProb_comp_equiv` transports both acceptance probabilities. The proof does not depend on downstream B1 or `specialScheme_multiMessageSecure_of_joint`; the import graph confirms the required direction.

4. **`nestedSpecial_wrongKeyBot` — correct.** The two string bounds give success errors whose nonnegativity is derived from probability nonnegativity. With zero positions there are no distinct assignments. With one position the independent key/nonce marginal gives the inner bound. With two positions, a different first choice permits conditioning on the inner ciphertext and applying the outer bound; an equal first choice opens the outer layer correctly and leaves a different second choice for the inner bound. `length_nestedInner` supplies the exact inner message length. Adding the unused nonnegative error gives `ε₁ + ε₂` in both cases.

5. **B2 and `uprob_not_good_le` — correct.** The B2 header equals the binding draft after whitespace normalization. `IsFaninTwo` supplies distinct argument vertices and arity at most two; `args_lt` separates them from the output vertex. The published restriction/evaluation laws therefore give the independent plaintext key, argument-key table and row coin required by `WrongKeyBot`. Correctness opens the intended row; permutation surjectivity places it in the table, and absence of cross-openings determines the first successful value. The number of ordered distinct assignment pairs is `2^arity * (2^arity - 1)`, namely `0`, `2` or `12`. Two finite union bounds give the required coefficient. Cross-opening events ignore row order, so the uniform-data theorem legitimately allows seed-dependent permutations. Fixed-permutation B2 is its identity-map specialization; the frozen uniform-seed theorem averages B2 over permutations, rather than repeating its proof.

6. **`yaoSeed_good_whp` — correct.** The key blocks lie below `2*sizeBound`, and the row-half blocks begin there and lie below `10*sizeBound`; the block-index injection and the bounded, injective assignment fold establish disjointness. Restricting the raw bit table gives the joint uniform key/row-coin law, including zero-length bit blocks. The stronger uniform-data theorem applies to the actual XOR-shift permutations without an independence requirement. Each output collision has probability `2⁻ⁿ`; a union bound over output positions remains valid when vertices repeat. The final error is exactly the stated polynomial multiple of the nesting error plus `outLen(n)*2⁻ⁿ`, and is negligible.

7. **B1, `sliceMultiMessageSecure_of_prfOut` — correct.** Offsets and lengths are bounded by the polynomial output width, and both dependent message vectors range over finite types. Maximizing over `Option (Pack n)` with `none` valued at zero implements the empty-fit-set convention. The maximizing slice descriptors have polynomial-length unary advice. `slicePost` is total and polynomial-time on arbitrary words through the existing iterate-and-emit host and its state-length bound. `slicePost_tuple` establishes the exact same-seed identity with the slice ciphertexts through the published tuple, real-sampler and mask readers. The NUPPT composition/advice API gives the postprocessed distinguisher with a coin equivalence. D4 chooses its negligible bound before the masks; `distAdv_comp` and coin invariance transfer it to the maximizing pair, which dominates every fitting choice. If the maximum is `none`, applying D4 to equal zero masks proves the required nonnegative error bound. This also handles a zero maximum when fitting configurations exist.

Gate 27 obligations (1)–(6) are met respectively by the maximizing advice, the efficient parser and its same-seed law, the full-pad random-function law already inside D2/D4, D4's triangle bound, the direct D4 proof of the frozen scheme theorem with the still-proved downstream corollary, and B2. No hybrid or random-function proof is reconstructed in B1.

The remaining edge cases are covered without strengthened hypotheses: `ℓ(n) = 0` or `< n`, `q(n) = 0` (one ciphertext), empty messages, exact fits including Yao's outer slice, arities zero/one/two, constant gates, zero-argument XOR shifts, zero gates, and coinciding outputs.

**Integrity, Rule 10 and documentation**

| Check | Result |
|---|---|
| Pack `SHA256SUMS` | **21/21 verified**, using the exact exchange git objects. |
| Nested manifests | `verification.zip`: 147 files, exactly 146 manifest paths plus the manifest; review archive: 1201 files and 72 directories, exactly 1200 manifest paths plus the manifest. Every hash verifies. |
| Sources and diff | All **166** source files equal pinned head blobs. All 14 source-head hashes, line counts and width counts verify. `pr.diff.txt` equals the base-to-head git diff: 14 files, +1901/−122. |
| Public statements | Replayed decls2: **55 ADDED, 0 CHANGED, 0 REMOVED**. |
| Frozen declarations | Replayed the inspected supplied checker against git blobs: **0 unexpected differences** over 139 owned-file and 72 DAGCircuit base declarations. |
| SG-1 | Exactly **six private removals**, zero changed surviving headers/definitions; the one-character `of_joint` header control and seventh-removal control each reproduce exactly one difference. Private-name uses at the issue base are confined to `SpecialEncryptionMulti.lean`. `of_joint` keeps its entire docstring and header. |
| Other proofs and Yao restriction | **126** other surviving pre-existing theorem/lemma declarations remain byte-identical. Yao has exactly the three permitted hunks: the target's result bullet, sketch and body; no import changes. |
| SG-F01 | DAGCircuit has exactly the approved nine added lines, no removals; the new reader is `Iff.rfl`. Its sealed negative/reader control bites as required. |
| LE-doc | Exactly three files; deleting doc comments makes each pre-edit/head pair byte-identical. The added result entries and sketch sentence describe the delivered code. |
| Canonical coe-A seals | Supplied results: **14/14 head, 6/6 base pass**. Strict A has the same pass counts. |
| Seal coverage | Rechecked all four variants at base/head: exact eligible closure rows, every collected term reference covered or explicitly excluded as notation/reducible/abbreviation, correct source reconstruction from recorded insertions, matching source/probe hashes, and complete install/EOF verification. Every run records `maxErrors = 0`. |
| Seal B / SG-F07 | **30 head errors versus 21 base errors**. The nine new errors are the disclosed `PolyExpr.eval` conversions: 1 in GarblingSecurity, 1 in NestedBounds, 2 in SpecialEncryptionSecurity, 5 in WrongKey. Raw diagnostics agree with the attribution; no additional forbidden-definition read was found. `of_joint` passes all variants. |
| Paired controls | Canonical: **24 probes, 43 sealed negatives**, each negative fails once and readers pass. Strict: **28 probes, 57 negatives**; the only reader failures are the 14 disclosed `ctlCoeReader` failures. |
| Axioms | The seven targets, B2, the two stronger uniform-data endpoints, `garbling_good_whp` and `of_joint` have exactly the standard three axioms in the supplied census. Of 531 stored constants, only the three disclosed Yao-hybrid admissions retain `sorryAx`. |
| Build evidence | Rechecked **388 build + 9 edit-build records**, their raw log hashes and zero-error fields. The last build source hash of every one of the 388 distinct modules equals its final-head blob. These are supplied compilation results. |
| Documentation/API | New public definitions have readers; the two Prop-valued “NO-FORMULA” rows do state their formulas. The supplied 21 long-proof sketches match the inspected proofs. No additional formula/sketch defect was found. |

The disclosed DL-46/DL-47 material, including SG-F04, is not re-raised. SG-F02, SG-F03/LE-doc, SG-F05, SG-F06 and SG-F07 retain their stated dispositions. G36-01 is additional to those dispositions.

The merged-tip integration rebuilds with #313, #318, #319 or #324 remain the maintainer's pending merge conditions, as instructed. Dispatch and merging remain with the user.

The accompanying ZIP contains this Markdown and the auditor's hash results, statement/control replays, scope checks, source excerpts and build/seal evidence checks. **Gate 36 remains HOLD until G36-01 is resolved.**

Glossary: `n` is the security parameter; `ℓ` is the polynomial output/message-width expression at the relevant declaration; `q` is the polynomial ciphertext budget minus one; `arity` is a gate's number of arguments; `ε₁, ε₂` are the inner/outer string success-error bounds. All declaration names and other parameters are those of the pinned source.

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/landing-r1/PROVENANCE.txt =====

#323 (sc-garble) LE-gate36 (Gate 36 G36-01) and #323's integration build against the merged #313, maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I; Lean 4.25.0; one Lean process at a time, only on $SP/dl-oleans (dl-oleans-2 not touched); builds through
  scripts/lean_check_tree.sh (worktree copy byte-equal, checks/runner-equal.txt) via tools-used/review/runner.py (G26-N1, both error
  forms); probes through tools-used/runner_full.py (lean -DmaxErrors=0, no -o); no lake command; nothing pushed; no branch moved and
  no signed commit made (see landing/). Run after the int-313-323-324 job, whose restore left the tree at the base snapshot.
Method and tools: the int-313-323-324 tools (tools-used/, review/) plus, from the sc-garble final-r1 review evidence
  (fills/sc-garble/final-r1/review-evidence.zip, SHA-256 5a121c0290969e1f7725f997b8e5683169613a62ba4db203669a74590bd0e658; extract
  1200/1200 OK against evidence-SHA256SUMS, path set exact), unmodified: runner_full.py, decls2.py, frozencheck{,_sg,_lib}.py,
  review/{mkcollect.py, NmCollect.template.lean, mkseals_ab.py, mkseals_coe.py, mkctl_sg.py, sealsum.py, sealtable.py, ctlcheck2.py,
  touched.py, archived-gate10-tools/}; rule10_b.sh from gate29-le-b (gates/29-learning/landing-r2/gate29-le-b-evidence.zip, SHA-256
  66898704b4fb1734ebc64df691fcdb3ae6623d440ddb88ac45c6fbfb19b5b43a, 461/461 OK). New: legate36_edit.py (the edit, 3 exact
  replacements), review/mkctl_g36.py (mkctl_sg.py + one row, below), upclosure.py (import closure of one module).

landing (landing/):
  - REBASE NOT RUN (landing/rebase-refused.log): `git rebase 654323f2` on land/pass-shelat-sc-garble ($SP/wt-land-sc-garble) was
    refused by the session's permission system before it ran; not retried, no workaround on the branch. The branch, its worktree
    and origin/land/pass-shelat-sc-garble are unchanged at cd9a48438c2a6548fe9e246ce569be57c9df96b3. PUSH: NOT DONE (not asked).
  - Scratch replica instead (landing/replica-chain.txt; unsigned `git commit-tree --no-gpg-sign` objects, no ref): the 8 commits of
    1321b9cb..cd9a4843 replayed onto origin/cryptography/pass-shelat-ch2-4 654323f27fbbed3a1b3664908b6c14cf563e52a2 (#313 merged as
    10cc8c977) with `git merge-tree --write-tree --merge-base=<c>^`: every step rc 0, no conflict; original authors and messages,
    committer Claude, date fixed. Replica head 4366cd962ceab226b680760b14c48dc17e54a3b1, tree 63ce05ff49c0295a946d4e9fa4fcfc38bfab5bb4
    (= `git merge-tree --write-tree 654323f2 cd9a4843`). landing/range-diff.txt: 8/8 `=` (identical patches). vs the tip: the same
    14 paths, +1901/-122.
  - Edit commit (scratch) d32328f79cdef7d7e9c2a628d9f22c105f768a1c, tree 5662520d23695e1451bb3aa849ace82f71685393, parent 4366cd96,
    author = committer = Claude <noreply@anthropic.com>, subject "sc-garble landing edit LE-gate36: use the public
    length_le_length_encodeList (G36-01)", message landing/commit-msg.txt with the two trailers; patch landing/0001-*.patch. The
    maintainer's rebase + this patch (or legate36_edit.py) gives the same tree; hashes will differ (signing, dates).
edit (checks/le-gate36.diff; tools-used/legate36_edit.py), SpecialEncryptionMulti/SliceParser.lean, 2 insertions / 11 deletions:
  - `import TCSlib.Cryptography.Asymptotic.BlockEncryptor` added (first import line). Acyclic: SliceParser's local import closure
    146 -> 148 modules, added exactly Asymptotic/BlockEncryptor and Encryption/PrivateKey/FromPRG (checks/sliceparser-closure-*.txt).
  - `SliceReduction.length_le_encodeList` and its docstring deleted (lines 117-127 at the parent).
  - its one use, `hfuel` in `slicePost_encode`: `have h := TCSlib.Cryptography.length_le_length_encodeList (l.map Prod.snd)`
    (compiled first time; the rest of the proof unchanged).
  - The module docstring's `## Main results` (polyTimeComputable_slicePost, slicePost_encode) never listed the deleted lemma: unchanged.
  - The deleted name occurs nowhere else: `git grep length_le_encodeList cd9a4843` (all paths) = the declaration and the use only;
    0 occurrences at the edit head in TCSlib/ and audits/.
statements (statements/):
  - decls2-vs-parent.tsv (decls2.py over the 14 unit files, parent 4366cd96 vs head): exactly 1 line, REMOVED
    SliceReduction.length_le_encodeList; nothing ADDED or CHANGED; decls2.err empty.
  - frozen-check.txt (frozencheck_sg.py, issue base fbd37f447596d4207c8d08b7ef7602f57fe95198 vs head d32328f7, the review's 6 files,
    --expect-removed the six SG-1 helpers): RESULT differences 0; byte-identical, apart from the FILE header lines, to the review's
    frozen-check-le.txt. frozen-check-vs-parent{,-all}.txt (parent vs head, SliceParser / all 14 files, expect-removed the duplicate):
    differences 0, 1 of 1 expected removal.
  - touched-parent-vs-head.tsv: 1 CHANGED (slicePost_encode, its proof), 1 REMOVED (the duplicate), 258 UNCHANGED.
build (build/; order/ from downorder.py at d32328f7 against eff2dcd0: changed 87 = 68 base delta + #313's 5 + the 14 unit modules;
  buildset.py seeds = the 14 (order/seed.txt): down-seed 277, build set 392 (+115 base-delta modules needed), excluded 0; root TCSlib,
  audits/garg-ch1-3/Checks, audits/pass-shelat/Checks in it). This is #323's integration build against the merged #313.
  - build/summary.txt: 392/392 rc 0, 0 errors (both forms; build/per-module.tsv, log/record mismatches []), substring "error" 0,
    38 sorry warnings, 115 warnings, 2122 s (00:26:45-01:02:08 UTC), max RSS 4.56 GB. build/seed-modules.txt: the 14 unit modules
    rc 0, 0 errors, 0 sorry except Yao 2 (yaoHybrid_polyTime, yaoHybrid_simulators); warnings only SliceParser 1 (unused simp argument
    pairSndD_pairEncode, now line 159:36, was 168:36 in the int build: SG-F06, shifted by the 9 removed lines) and NestedBounds 1 (SG-F06).
    BlockEncryptor and FromPRG: rc 0 (BlockEncryptor's 10 warnings inherited, unchanged source).
  - refcmp (build/refunion.txt, vs-int-313-323-324.txt; references int-313-323-324 build (copied), sc-garble final-r1 build+edit-build,
    gate29-le-b build): 390/392 byte-identical in source and olean to a reference. SliceParser: new source (the edit), no reference.
    SliceReduction: same source as the int build and the sc-garble review, different olean; it is one of SliceParser's two direct
    importers (the other, SpecialEncryptionMulti, is byte-identical) and its import closure changed (SliceParser edited,
    +BlockEncryptor, +FromPRG).
    A rerun (build-rerun/) gives the same olean SHA-256 (90e0bbf2...), so the difference is deterministic and comes from the changed
    imports; its log is identical to the int build's up to line numbers. Every module further downstream (SpecialEncryptionMulti,
    GarblingSecurity, Yao, YaoReal, TCSlib, both audits Checks, ...) is byte-identical to the int build. ComposeSecurity here is the
    tip's (#324 not merged): src-DIFF vs the int build (which had #324), byte-identical to the sc-garble review and gate29-le-b.
  - tree/tree-check-head.txt (treecheck.py; order/order.txt 1261; admissions/records-head.jsonl = base records + build + rerun):
    RESULT OK (1292 files, no stray olean, no empty dir).
trial merge with #324 (trial/): `git merge-tree --write-tree d32328f7 a6eaebd7` clean, tree a025d7ab7c4911b6e42ef18b0c05b1c2ac1d4251,
  scratch 1f7bf42db6bbc7f210e5106a201ecf119f31112b (unsigned, -p head -p #324); other order (tip x #324 = e6dfe0b8, then x head) = the
  same tree a025d7ab, so both orders are covered. Shared paths 0; vs the int-313-323-324 merge S3 the trial's code differs only in
  SliceParser.lean (trial/int-merge-vs-trial-code.txt). Downstream (trial/order/bothdown.out, at 1f7bf42d): of #323's 14 277, of
  #324's 16 19, both 3 (SecureComputation, YaoReal, root TCSlib). trial/build/ = down(#324) in imports-first order, 19 modules
  (#324's 16 + those 3): 19/19 rc 0, 0 errors, 0 sorry, 0 warnings, 50 s; trial/vs-int-313-323-324.txt: all 19 byte-identical in
  source and olean to the int build. tree/tree-check-trial.txt (order 1276, records-trial.jsonl): RESULT OK (1307 files).
Rule 10 (rule10/; tools-used/rule10_b.sh with mkctl_g36.py), SliceParser.lean at d32328f7, probes under G36Probe/ in the worktree:
  - Collector G36Probe/CollectHead (mkcollect.py, owners = SliceParser; rule10/probe-sources/CollectHead.lean.txt; probe-runs/ rc 0):
    2817 CAT lines; stored constants 11 (the review: 13).
  - Seals (mkseals_ab.py strict, mkseals_coe.py canonical; B with SEAL_EVAL=1): requests strict A 2102 / B 2103, coe A 2101 / B 2102
    (the review's pre-edit SliceParser seals 2084/2085/2083/2084: +18 from the 2 added modules). seals-{A,B,coe-A,coe-B}.tsv: all 4
    pass, rc 0, 0 errors, install and EOF records present; every probe run with -DmaxErrors=0 (seal-runs/).
  - Paired controls (review/mkctl_g36.py = mkctl_sg.py + a row for PrivateKeyScheme.encodeList, the definition under
    length_le_length_encodeList: negative its rfl unfolding on a cons, positive the published reader encodeList_cons; rows chosen by the
    seal requests: PolyExpr.eval (B), the FinDist CoeFun instance (strict), DAGCircuit.IsFaninTwo, encodeList). controls-coe: 4 probes,
    7 sealed negatives; ctlcheck-coe.log ALL_OK True. controls-strict: 4 probes, 9 sealed negatives, each failing exactly once; ALL_OK
    False only because ctlCoeReader fails in the 2 sealed strict probes (it elaborates to the sealed CoeFun instance: harness effect,
    as in the sc-garble review; rule10/controls-strict-attribution.txt). Unsealed controls all pass. The new encodeList row: negative
    fails sealed (A and B, strict and coe), reader passes.
  - The G36Probe sources (rule10/probe-files-in-worktree.txt, 14 files; copies in seals*/, controls*/, probe-sources/) were removed
    from the worktree after use; runner_full writes no olean (0 G36Probe files in the tree).
axioms (axioms/AxiomsHead.lean.txt -> AxiomsHead.log; G36Probe/AxiomsHead, runner_full, rc 0, 0 errors, 0 warnings):
  [propext, Classical.choice, Quot.sound] for the 7 targets spDecStr_wrongKey, specialScheme_wrongKey, specialScheme_multiMessageSecure,
  nestedSpecial_wrongKeyBot, uprob_not_good_le, yaoSeed_good_whp, sliceMultiMessageSecure_of_prfOut, for uprob_not_good_le_of_perm (B2)
  and for SliceReduction.slicePost_encode (the edited proof); TCSlib.Cryptography.length_le_length_encodeList [propext, Quot.sound].
  yaoHybrid_hbcSecure, yaoProtocol_hbcSecure keep sorryAx: trace (direct sorryAx) for yaoProtocol_hbcSecure: hbcSecure_compose
  (sc-compose, #324 not merged here), otProtocol_polyTime, otProtocol_simulators, yaoHybrid_polyTime, yaoHybrid_simulators; for
  yaoHybrid_hbcSecure: yaoHybrid_polyTime, yaoHybrid_simulators (as in the sc-garble review).
admissions (admissions/): tip count (tip-census-654323f2.txt, tipcensus.py by source SHA-256 over the base records, int-317,
  gate29-le-b, int-313-323-324, sc-garble and sc-compose records; 1253 modules matched, 0 disagreeing): 215 tree-wide at 654323f2
  (= 216 - predictAdv_prfConcept_negligible, #313 merged); 38 in the prf-long issued-r1 modules, + SpecialEncryptionMulti 1 outside the
  list (admissions/tip-count.txt). Head (head-census-d32328f7.txt, records base + build): 208 tree-wide = 215 - 7; sorry-census.txt
  (sorrycensus.py, issue base 7b307d62): issued modules 38 -> 32 (SpecialEncryptionSecurity 3->0, Garbling 1->0, GarblingSecurity 1->0,
  Yao 3->2) and SpecialEncryptionMulti 1->0; tip-vs-head-census.diff: no other count changes; the 9 new unit modules 0.
  No admission in a unit module that it did not already have (Yao's 2 are tip admissions).
lint (lint/): campaign_style_lint.py TCSlib/Cryptography --check8b at d32328f7: 92 FAIL / 101 WARN over 362 files (rc 1);
  FAIL/WARN line set identical to the int-313-323-324 merge's (linediff-int-merge-vs-head.txt empty); SliceParser has no FAIL/WARN
  (INFO: 180 -> 171 lines, 10 -> 9 public declarations).
olean tree $SP/dl-oleans: pre tree/snapshot-pre.txt 1230 files SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f;
  330 base oleans backed up before the build (tree/backed-up.txt, copies verified), 62 new listed (tree/new-oleans.txt); the trial
  build's 4 overwritten oleans were head-build outputs, its 15 new ComposeSecurity modules new. restore/ (restore-log.txt): 330
  restored, 0 hash failures; restoreplan.py --delete: 77 extra files (= 62 + 15, restore/extra-vs-expected.txt empty) deleted with
  12 emptied dirs; 0 changed, 0 missing. tree/snapshot-post.txt byte-identical to snapshot-pre.txt (1230 files, 457ba704...).
cleanup: worktree $SP/wt-gate36 (sparse, briefs/ excluded, .lake/packages link; clean, checks/worktree-status.txt only .lake/) removed
  with `git worktree remove --force`, pruned; backups and the reference extracts removed.
SHA256SUMS: every file here except itself (paths without "./"); ../gate36-le-evidence.zip holds exactly these paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/36-sc-garble/pack.md =====

# Gate 36 · Special encryption and garbling probability (`sc-garble`, U1, [PS10, §6.2.2–6.2.3])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #323](https://github.com/Shilun-Allan-Li/tcslib/pull/323) at
  `cd9a48438c2a6548fe9e246ce569be57c9df96b3` (branch `land/pass-shelat-sc-garble`, tree
  `13aa553d035fd55cf73c7123ebb73c1940019f1c`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `1321b9cb358867f5b51974b8c5d0781519a9cfdb` (the merge base: the records tip after #317 and #316 merged).
  - The fill was issued on `fbd37f447596d4207c8d08b7ef7602f57fe95198`, the head of #315 (prf-long), under the
    proved-modulo rule: the proof uses prf-long's D1–D4. #315 has since merged (`10b9be17`), then #314, #317 and #316;
    their 10 Lean files are not in the PR. The 14 PR paths are byte-identical at the issue base and at `1321b9cb`
    (`pack-checks/rebase.txt`), and the review's build covers the delta (below).
  - The records tip is now `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`; it is records only since `1321b9cb`, so the
    PR is current with the tip.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...cd9a4843`, which equals `1321b9cb..cd9a4843`
    byte for byte (14 paths, 1901 insertions, 122 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #313, #318, #319 and #324 is
    clean in each case, and no path is shared (`pack-checks/mergetrees.txt`). **Pending merge condition** (not an audit
    item): whichever of #323 and each open PR with a shared downstream merges second needs an integration rebuild on
    the merged tip; the maintainer runs these builds (question 7).
- **Commits:** 8, all committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Codex worker's 7 commits (job `sc-garble`, on Seyoon's Mac under the host addendum; author Seyoon Ragavan),
    delivered with `commit.gpgsign=false` and a `COMMITS.tsv` signing column (`none` throughout). `git am` at the issue
    base with the delivered committer data reproduces all 7 hashes unsigned (review `logs/git-am-integrity.log`). They
    were rebased onto `1321b9cb` without conflict, author kept: `git range-diff fbd37f44..81795f77 1321b9cb..e5cb6129`
    is 7/7 `=`. At `e5cb6129` the 14 files are byte-identical to the worker's `src/` (exchange `a73072f1`).
  - Landing edit **LE-doc** `cd9a48438c2a6548fe9e246ce569be57c9df96b3` (the head): docstrings only, 3 files.
- **Scope:** a **proof audit** of seven admitted, frozen statements, and the stronger garbling bound B2:

  | Target | File | Source |
  |---|---|---|
  | `spDecStr_wrongKey` | `SpecialEncryptionSecurity.lean` | Claim 157.a (ii), strings |
  | `specialScheme_wrongKey` | the same | Claim 157.a (ii), the scheme |
  | `specialScheme_multiMessageSecure` | the same | Claim 157.a (i); Definition 93.1, Theorem 99.2 |
  | `nestedSpecial_wrongKeyBot` | `GarblingSecurity.lean` | Claim 157.a (ii) for the nesting |
  | `uprob_not_good_le` | `Garbling.lean` | Claim 159.a, probabilistic part |
  | `yaoSeed_good_whp` (that body only) | `Yao.lean` (shared with `sc-yao`) | Claim 159.a for Protocol 162.6's seed |
  | `sliceMultiMessageSecure_of_prfOut` (B1) | `SpecialEncryptionMulti.lean` | §6.2.2, Theorem 99.2 with slices; [LP09] |
  | **B2** `uprob_not_good_le_of_perm` (new) | `Garbling.lean` | Claim 159.a, fixed-permutation form |

  The first six passed the prong statement phase and Gate 06; B1 passed Gate 27 (CLEAR) and merged in #311. All seven
  are quoted in the brief. Their consumer `garbling_good_whp` (unchanged) now uses only the standard axioms.
- **Brief:** `fills/sc-garble/issued-r1/brief.md` (SHA-256 `203d42ea…`) with **ruling SG-1** (`ruling-SG-1.md`, which
  overrides the brief where they differ). Three checkpoints (the wrong-key property; B2 and Yao's seed; B1 and Claim
  157.a (i)). Five owned files, four helper directories, every other file frozen; `Yao.lean` stricter. The import
  direction for `specialScheme_multiMessageSecure`; the B1 consumer map; Gate 27's hand-off obligations (1)–(6); the
  binding duplication rule with an `## Overlap and reuse` section; Rule 10 with the projection-coercion ruling and seals
  with `PolyExpr.eval` both excluded and sealed; the docstring and sketch rules; the G26-N1 error count; the
  evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/` unless they start with `TCSlib/`. The PR touches 14 Lean
files: 6 modified (the 5 owned files and `DAGCircuit`) and 8 new helpers (1901 insertions, 122 deletions). Lines are
base → head (`source-head.json`; every line at most 100 characters).

| File | Status | Lines |
|---|---|---:|
| `SpecialEncryptionSecurity.lean` | owned | 157 → 332 |
| `SpecialEncryptionMulti.lean` | owned (SG-1) | 325 → 368 |
| `Garbling.lean` | owned | 427 → 659 |
| `GarblingSecurity.lean` | owned | 87 → 115 |
| `Yao.lean` | owned, shared with `sc-yao` (body only) | 942 → 970 |
| `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` | frozen, one approved reader (SG-F01) | 627 → 636 |
| `Garbling/CoinBlocks.lean`, `Garbling/Probability.lean` | helpers, new | 206, 113 |
| `GarblingSecurity/CoinMarginals.lean`, `GarblingSecurity/NestedBounds.lean` | helpers, new | 58, 215 |
| `SpecialEncryptionMulti/SliceParser.lean`, `SpecialEncryptionMulti/SliceReduction.lean` | helpers, new | 180, 150 |
| `SpecialEncryptionSecurity/Pad.lean`, `SpecialEncryptionSecurity/WrongKey.lean` | helpers, new | 116, 226 |

Each owned file imports its own helpers; after #305 no facade edit is needed, and none was made.

**The proof** (REPORT § *Proofs and edge cases*; review § *Content*; the targets' sketches were rewritten to describe
the delivered proof, the statement prose is unchanged):
1. **`spDecStr_wrongKey`** (`WrongKey`). The distinguisher evaluates `hG'.easy`'s evaluator on `⟨k', r⟩`;
   `MultiMsg.exists_oneQuery_nuppt` (D3) gives the one-query machine; D1 at budget `1`
   (`exists_negligible_prefix_collision`: `prfAdv + 2^{-n}`); against a random function the prefix collision has
   probability `2^{-n}` (`uprob_random_prefix`). `ε = that + 2^{-n}` gives the strict `<`, `n = 0` included.
2. **`specialScheme_wrongKey`**: the string bound at `ℓ = .var`, the coin relabelling, the `dec` coins averaged out
   (`uprob_fst`), and the overlong failure word decodes to `none` (`specialScheme_dec_runAt`).
3. **`nestedSpecial_wrongKeyBot`** (`NestedBounds`, `CoinMarginals`): two string bounds, `δ = ε₁ + ε₂`, and the case
   analysis of `nestedSpecial_wrongKeyBot_of_string_bounds` (0, 1, 2 positions).
4. **B2** `uprob_not_good_le_of_perm` has the brief's signature exactly (whitespace-collapsed, the binding draft). It is
   a corollary of the stronger `uprob_not_good_le_of_uniform_data` (uniform keys and row coins as the push-forward
   `d` of a uniform `Ω`; permutations `π w` may depend on the seed; SG-F02), proved through `good_of_no_crossOpening`
   (correct row opens and no cross-opening ⇒ the first success is the right key; row order irrelevant), 12 events per
   gate (arity ≤ 2) and `uprob_exists_le` twice. **`uprob_not_good_le`** averages B2 over uniform permutations.
5. **`yaoSeed_good_whp`** uses the uniform-data form with Yao's XOR shifts as the seed-dependent permutations,
   `pushesUniform_key_row_blocks` for the disjoint key and row-coin blocks (`b·S + v` and
   `2S + 2(4i + idx(a)) + b`, injective below `10S`), and the output collision `outLen · 2^{-n}`;
   `δ = 12 · S · δ₀ + outLen · 2^{-n}`. The generic push-forward is in `Garbling/CoinBlocks`, so `Yao.lean` changes only
   in this body.
6. **B1** `sliceMultiMessageSecure_of_prfOut` (`SliceParser`, `SliceReduction`, `Pad`): an `Option` of fitting
   configurations with `none ↦ 0` (**the empty-set convention**), the slice vector as unary advice, the parser
   `slicePost` (`polyTimeComputable_slicePost`, `slicePost_tuple`: the pointwise identity with the slice sampler on the
   same seed), `D' = D ∘ P` by `exists_slicePost_nuppt`, D4's `ε` before the masks, `distAdv_comp` and
   `acceptProb_coins_equiv`; the `none` branch uses D4 at equal zero masks for `0 ≤ ε`.
7. **`specialScheme_multiMessageSecure`** is proved **directly from D4** in its own file
   (`MultiMsg.exists_negligible_distAdv_prfEncRealOut` at masks `0^n ‖ m_i`, the relabelled coins,
   `acceptProb_comp_equiv`), upstream of the corollary `specialScheme_multiMessageSecure_of_joint`, as the import
   direction requires (`SpecialEncryptionMulti` imports `SpecialEncryptionSecurity`).

**Gate 27's hand-off obligations** (REPORT § *Gate 27 hand-off*): (1) the maximizing advice with the empty-set
convention, in the B1 proof (`Config`, `Pack`, `adv`, `μ`, `β`; `length_sliceAdvice_le`, `exists_slicePost_nuppt`);
(2) the post-processor `slicePost` with `slicePost_tuple`; (3) the random-function slice law: D2/D4's full pads are
uniform, so every selected window is (`slicePost_tuple` only identifies the windows); (4) the triangle bound: D4
itself; (5) the frozen theorem `specialScheme_multiMessageSecure` proved directly, `of_joint` still proved beside B1;
(6) B2.

**Ruling SG-1.** The six frozen private relabelling helpers of `SpecialEncryptionMulti.lean`
(`specialScheme_gen_runAt`, `specialScheme_enc_runAt`, `specialKeyEq`, `ofFn_specialKeyEq`, `specialNonceEq`,
`ofFn_specialNonceEq`) are deleted. They are published once beside `specialScheme` in
`SpecialEncryptionSecurity.lean`: `specialScheme_gen_runAt`, `specialScheme_enc_runAt` (same names, now public),
`specialScheme_keyCoinsEquiv` (`_eq`, `_ofFn`), `specialScheme_nonceCoinsEquiv` (`_eq`, `_ofFn`), and also
`specialScheme_dec_runAt`. `specialScheme_multiMessageSecure_of_joint` is re-proved through them, proof only: four reader
names and one re-wrap (`pack-checks/sg1.txt` shows both texts).

**The frozen-file change** (SG-F01): `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` gains

```lean
theorem isFaninTwo_iff :
    C.IsFaninTwo ↔
      (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
        ∀ g ∈ C.gates, g.args.length ≤ 2 := Iff.rfl
```

with a formula docstring and the tag `[AB09, Definition 6.1]`. Seyoon approved it in the worker's session (the
delivery's `scope-request/`) and **confirmed his approval on 2026-11-15** (decision log). sc-yao's SY-3 reader is
byte-identical to it.

**Statements.** decls2 from the issue base (and from `1321b9cb`) to the head gives **55 ADDED, 0 CHANGED, 0 REMOVED**
(public declarations; review `statements/head/decls2-vs-base.tsv`; re-checked, `pack-checks/decls2-*.tsv`; 0 rows for
LE-doc).
- The frozen check (`frozencheck_sg.py`, at the final head) compares the **139** base declarations of the 5 owned files
  (6 + 18 + 37 + 2 + 76) and the **72** of `DAGCircuit`: file, kind, name, order, header bytes, statement prose and
  every definition body. It finds **0 differences**, with `SpecialEncryptionMulti`'s six SG-1 helpers listed as
  EXPECTED-REMOVED, 6 of 6 (`landing/frozen-check.txt`).
- **The SG-1 check: exactly 6 REMOVED, 0 CHANGED.** Its 11 controls each report exactly one difference
  (`statements/frozen/controls-summary.txt`), among them the brief's one-character header control (`of_joint`) and
  SG-1's **seventh-removal control** (deleting `zipWith_xor_append_of_le` in a copy reports 1 MISSING).
- Re-checked for this pack from git objects, private declarations included (`pack-checks/headers.txt`, `sg1.txt`):
  every base header in the 6 files byte-identical at the head and in order; removed exactly the six SG-1 names, each
  private at the base; every remaining definition block identical (2 + 3 + 15 + 0 + 24 + 27); only the targets' docstrings
  changed (and `isFaninTwo_iff` new); `of_joint`'s header and docstring byte-identical; the six names occur at the
  issue base only in `SpecialEncryptionMulti.lean`, and at the head only `specialScheme_gen_runAt`/`_enc_runAt`
  remain, as the public readers and their uses; `zipWith_xor_append_of_le` is still present.
- **`Yao.lean`** (`pack-checks/yao.txt`, review `statements/frozen/yao.diff`): 942 → 970 lines, three hunks: the
  `## Main results` bullet (head lines 96–99), the target's sketch (799–806) and its body (813–848). No other
  declaration's header or docstring, no import and no name changes.

## Rulings and records in force

1. **SG-1 (Seyoon, 2026-11-15, before dispatch): the frozen-file exception** above, with its header check (exactly six
   REMOVED, zero CHANGED), its two controls, the private-use search and the `of_joint` seals. With the private copies
   gone the relabelling is not debt, and no ledger row is opened.
2. **SG-F01 (Seyoon confirmed, 2026-11-15):** `DAGCircuit.isFaninTwo_iff`, `Iff.rfl`, equal line for line to the
   approved patch (`pack-checks/dagcircuit.txt`: the 9 added lines = the patch's, 0 removed; the head file with them cut
   out is the base file byte for byte). It is the only change to a frozen file. **Not a finding.**
3. **DL-46** (prf-long, disclosed): `MultiMsg.encodeList_eq_flatMap` is a third copy of the public
   `encodeList_eq_flatMap`; the brief forbids a fourth (none was added). The `zipWith_xor_append_of_le` clash class.
4. **DL-47, extended by SG-F04 (Seyoon, 2026-11-15: ledger).** The new inline getD-of-`List.ofFn` chain in
   `Garbling/CoinBlocks.lean:73–74` (`List.getD_eq_getElem`, `List.getElem_ofFn`, in `pushesUniform_bits_of_blocks`)
   is the chain of Yao's private `getD_ofFn'`; it is re-pointed onto the planned generic getD reader in the cleanup.
   **Not a finding:** any item DL-46 or DL-47 lists.
5. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical; the strict variant is run and its differences
   attributed.
6. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A** is canonical; seal B is run and reported, and
   its new failures attributed from the raw logs (Gate 31). So **coe-A is the canonical variant**.
7. **The facade-completeness lint fix, #305.** The baseline is **92 FAIL / 101 WARN** (Cryptography) and **25 / 391**
   (Complexity).
8. **LE-doc (the maintainer's landing edit): docstrings only** (SG-F03). `NestedBounds` and `WrongKey` `## Main results`
   now list their main theorems; the `**Proof sketch.**` of `nestedSpecial_wrongKeyBot` gains one sentence naming the
   delivered route. Re-checked (`pack-checks/lecheck.txt`): `e5cb6129..cd9a4843` touches 3 files (+14/−1), each
   identical with doc comments deleted; one declaration docstring and two module docstrings change; widths ≤ 98.
9. **The host addendum** (`fills/codex-host-2026-11-15/host-addendum.md`): the worker ran on Seyoon's Mac with a
   host-wide 3-slot Lean cap; the preflight, `slots.log` (543 acquire/release pairs) and `-k 3` on every `lake` call
   pass (review § *Integrity*). The REPORT's environment notes (a rejected checkpoint push, the overnight
   "best judgment" authorization in `scope-request/autonomy.md`) are information, not findings.

## What is frozen

- **The seven targets' statements** (quoted in the brief) and every other pre-existing declaration of the five owned
  files, private ones included, with their statement prose; every definition body (`specialScheme`, `GarbleSeed`,
  `Good`, `sliceEnc`, `yaoSeed`, …), apart from the six SG-1 deletions.
- **`Yao.lean`** apart from the one body, its sketch and its bullet.
- **Every other file**, in particular `DAGCircuit.lean` apart from the approved reader, `SpecialEncryption.lean`,
  `GarblingSpecial.lean`, `YaoReal.lean`, prf-long's files (`Functions/Asymptotic/Defs`, `Encryption/PrivateKey/FromPRF*`,
  `PrivateKey.lean`), `Pseudorandom/*`, `Encryption/*` and `Games/*`.
- **The landing edit:** LE-doc, three docstrings.

## Questions for the audit

**1. Correctness against the frozen statements and [PS10, §6.2.2–6.2.3]**
- **`spDecStr_wrongKey`:** does the length guard always pass on honest ciphertexts, so that `none` is exactly the
  prefix mismatch? Is the evaluator of `hG'.easy` the right stand-in for `E'` (which has no `PolyTimeComputable`
  hypothesis; they agree on canonical inputs by `hGE'`)? Is the one-query reduction at budget `1` with
  `exists_oneQuery_nuppt` and D1 right, and is `ε = prfAdv + 2^{-n} + 2^{-n}` (the strict `<` at `n = 0`) correct?
- **`specialScheme_wrongKey`** and **`nestedSpecial_wrongKeyBot`:** the relabellings, the `dec`-coin average, the
  failure word's decoding, the three nesting cases and `δ = ε₁ + ε₂`.
- **B2 and `uprob_not_good_le`:** is `uprob_not_good_le_of_perm` exactly the brief's signature, and is it a corollary of
  `uprob_not_good_le_of_uniform_data`? Is `good_of_no_crossOpening` right (arguments distinct and below the gate by
  `IsFaninTwo`, at most two; constant gates add no event; row order irrelevant), is 12 events per gate right, and is
  the average over uniform permutations a corollary, not a second proof?
- **`yaoSeed_good_whp`:** are the key and row-coin blocks disjoint and inside `yaoCoins = 10 S n + 2 S`
  (`key_row_blocks_injective`), is the XOR-shift family a valid seed-dependent permutation family for the uniform-data
  form, and is the output collision `outLen(n) · 2^{-n}` (outputs may coincide) right?
- **B1:** is `slicePost_tuple` the pointwise identity `P_{o,ℓ}(encodeTupleOut (prfEncRealOut (G n) w t)) =
  sliceMultiEncDist G n q o len m t` on the same seed, reading `prfEncRealOut`, `encodeTupleOut` and `sliceEnc` only
  through their readers? Is the advice polynomial (`length_sliceAdvice_le`) and `slicePost` polynomial-time? Does the
  maximization **keep the empty-set convention** (`none ↦ 0`, e.g. `ℓ(n) < n`), with D4's `ε` chosen before the masks,
  so that every fitting `o, ℓ, m, m'` is bounded? Are **Gate 27's obligations (1)–(6)** met, and does the delivery
  follow **Gate 31's B1 consumer map** (masks `0^{o_i+n} ‖ m_i ‖ 0^{…}`, `D' = D ∘ P` with the slices as advice, steps
  1–3 inside D4)?
- **`specialScheme_multiMessageSecure`:** is it proved **directly from D4** (masks `0^n ‖ m_i`, all slices `(0, n)`, no
  post-map) through the new readers and `acceptProb_comp_equiv`, with no use of the downstream corollary?
- Are the brief's edge cases covered: `n = 0`; `ℓ(n) = 0` and `ℓ(n) < n`; `q(n) = 0`; empty messages; exact fits (Yao's
  outer slice `(2n, 4n + 2)`); `len = 1, 2` and constant gates; fewer than two arguments; the XOR shift at `len = 0`;
  `|gates| = 0`; coinciding output vertices?

**2. Frozen-statement integrity**
- Is the frozen check **0** over the 139 + 72 base declarations, and is the SG-1 report **exactly 6 REMOVED, 0 CHANGED**,
  with both controls (the one-character header control and the seventh-removal control) biting once each? See
  `landing/frozen-check.txt`, `statements/frozen/`, `pack-checks/headers.txt` and `sg1.txt`.
- Is decls2 **55 ADDED / 0 CHANGED / 0 REMOVED**, the six removals all private (so outside decls2), and is every new
  declaration in an owned file or a permitted helper directory?
- **The stricter `Yao.lean` rule:** does `Yao.lean` change only in `yaoSeed_good_whp`'s body, its `**Proof sketch.**` and
  its `## Main results` bullet (`pack-checks/yao.txt`, `statements/frozen/yao.diff`)?
- In `SpecialEncryptionMulti.lean`, did only what SG-1 and the brief allow change: the imports, the title, `## Main
  results` and `## Contents`, the B1 proof and sketch, the six removals and `of_joint`'s proof (header and docstring
  byte-identical)? See `statements/frozen/specialEncryptionMulti.diff`.

**3. The frozen-file change**
- Is `DAGCircuit.isFaninTwo_iff` exactly the approved patch (`worker/final/evidence/scope-request/fanin-reader.patch`,
  `pack-checks/dagcircuit.txt`) and true by `Iff.rfl` from the frozen `IsFaninTwo`? Is it needed under the seal
  (the `Iff.rfl` control fails sealed, the reader passes; `logs/ctlcheck.log`, row `ctlFanin`) and sufficient? Is
  anything else changed in a frozen file?

**4. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's `## Overlap and reuse`, **DL-46** and **DL-47** (with SG-F04)? **Any further undisclosed duplicate
  of a public lemma is a major.** The recent majors of this class are G23-01, G24-01, prf-mac F-01, learning
  (`uprob_eq_point`), G29-01 (`hj` = `OneWay.uexp_const`), G29-02 (`firstBit_of_pos`), sc-ot F-01 and G34-01
  (`OT.getD_zero_eq`/`getD_one_eq'` re-proving `headD_drop`).
- Search in particular:
  - probability and expectation (`uprob_*`, `uexp_*`, `acceptProb_*`, `distAdv_*`, `pushesUniform_*`,
    `uprob_not_injective_le`, `MultiMsg.uprob_eq_pair`, `uprob_exists_le`, `uprob_not`);
  - list windows and XOR (`ofFn_drop_take`, `take_ofFn_castLE`, `take_drop_ofFn_blocks`, `headD_drop_ofFn`,
    `zipWith_xor_*`, `MultiMsg.zipWith_xor_*`, `encodeList_eq_flatMap`, `List.take_append_of_le_length`, …);
  - the getD/headD-of-`List.ofFn` class beyond SG-F04 (`pack-checks/dupscan.txt` and review
    `dup/getd-headd-added-lines.txt`: the other added getD lines are statements, `change` lines and `Option.getD`);
  - coin relabellings (`prfScheme_coinsEquiv`, `coinsEquiv`, `NUPPT.coinsCongr_ofFn`) and machine plumbing (D3's
    machines, `NUPPT.exists_comp`, `exists_withAdvice`, `Games.polyTimeComputable_iterEmit`, `polyTimeComputable_blockMap`,
    `NMSim.chunkMap`);
  - encoding lengths (`length_le_encodeList`, `length_encodeList_le` against `ETTGame.length_le_length_encodeLog`,
    `EffFill.length_le_length_encodeHist`, `EffFill.length_encodeLog_le`, and the private
    `CircuitComplexity/Uniform.lean:208` short-name relative).
- Are the disclosed relations accurate and their "why not reused" reasons valid (for example `length_nestedInner` vs
  `GarblingSpecial`'s inline `hc`, `spEncStr_eq_sliceMask` vs the frozen private `zipWith_xor_append_of_le`, the B1
  maximum vs D4's `Finset.exists_max_image`)? The review's independent search is `evidence/logs/duplication-review.txt`.

**5. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 14 files over
  the full closure, at the base and the head, in all four variants, run with `-DmaxErrors=0` and install/EOF records?
  Requests per file go up to 2106 (0 for `DAGCircuit`, whose closure has no TCSlib definition; `logs/mkseals-*.log`).
  The base phase sealed the six base files in their own base closure (a base `SpecialEncryptionMulti` cannot be sealed
  against the head `SpecialEncryptionSecurity`, whose public `specialScheme_gen_runAt` would clash with the private
  copy).
- With **coe-A canonical**, does every file pass? The review has **A head 14/14 and base 6/6, strict and coe**; strict
  = coe throughout (`logs/seal-table-seals{,-coe}.txt`).
- **SG-1:** does `of_joint` pass A and B, strict and coe, with the new readers?
- **Seal B (SG-F07):** 30 errors at the head in 5 files against 21 at the base in 3 (`GarblingSecurity` 3/2,
  `SpecialEncryptionSecurity` 6/4, `Yao` 15/15, and the new `NestedBounds` 1 and `WrongKey` 5). The 9 new errors are in
  new bodies (`spDecStr_wrongKey`, `nestedSpecial_wrongKeyBot_of_string_bounds`,
  `exists_negligible_prefix_collision` and their calls); `logs/seal-B-attribution.txt` attributes every head B error,
  read from the raw logs, to a `PolyExpr.eval` conversion, matching the worker's `B-attribution.md`. Is that right, and
  is none a foreign-definition unfold?
- Do the paired controls bite? Rows: `PolyExpr.eval` (B), the `FinDist` CoeFun instance, `DAGCircuit.IsFaninTwo` (the
  approved reader), `spEncStr`, `Good`, `sliceMask`, `SliceReduction.slicePost`, `SpecialWrongKey.prefixTest`. Coe
  (canonical): 24 probes, 43 sealed negatives, `logs/ctlcheck.log` ALL_OK. Strict: 28 probes, 57 sealed negatives;
  every sealed negative fails exactly once, and only `ctlCoeReader` fails in the 14 strict sealed probes (the harness
  effect of sc-ot F-09; `logs/controls-strict-attribution.txt`). The first control attempt (`controls-attempt1/`, it
  opened `Turing` where Garbling's closure lacks it) is superseded and kept.
- Explicit-unfold scan at the head: 774 items, 594 theorems, 31 owned definitions, 147 local or unresolved, 2 flagged
  foreign, both local `let` binders (`P`, `g`) resolved to global names (`logs/scan-attribution.txt`): **0 foreign**.
  Does any proof read a foreign definition other than through a published reader (`spEncStr`, `spDecStr`, `sliceEnc`,
  `Good`, `WrongKeyBot`, `nestedSpecial`, `yaoSeed`, `readBits`, `xorShift`, `prfEncRealOut`, `encodeTupleOut`, the
  `NUPPT` layer; one helper's definitions read from another)?

**6. The landing edit and the docstring and sketch rules**
- **LE-doc (ruling 8):** docstrings only (`landing/le-doc.diff`, `landing/le-doc-doconly.txt` in the review ZIP;
  `pack-checks/lecheck.txt`)? Do the new `## Main results` entries and the sketch sentence describe the code?
- Does every new public declaration's docstring state its formula, in Lean argument order, with a `[PS10, …]` tag where
  it comes from the source? The review's docaudit (`statements/head/docaudit.tsv`, before LE-doc, which added no
  formula) has 55 OK and 8 NO-FORMULA: the frozen prose of 5 targets, `of_joint`'s frozen docstring, and 2 Prop
  formulas without a relation symbol (`nestedSpecial_wrongKeyBot_of_string_bounds`, `polyTimeComputable_slicePost`), a
  tool artifact. Are those 2 acceptable?
- Does every proof of 15 lines or more carry a `**Proof sketch.**` (`statements/head/sketchaudit.txt`: 21, 0 without),
  and do the long proofs (B1, B2, `yaoSeed_good_whp`) have step comments? A misstated formula or sketch is a minor.
- Does every new public `def` land with its readers (`sliceMask`, `slicePost`, `parserStep`, `parserEmit`, the two coin
  equivalences with `_eq` and `_ofFn`; lint check 8)? Is nothing new `@[simp]`, an instance or an abbreviation (census:
  none)?

**7. The merge interaction**
- `git merge-tree --write-tree cd9a4843 <x>` is clean, and no path is shared (`pack-checks/mergetrees.txt`):

  | `<x>` | head | merged tree | downstream of both (`pack-checks/downstream.txt`) |
  |---|---|---|---|
  | the tip | `540bac18` | `bb5289bb` | none (records only since the base) |
  | #313 (learning) | `2b6c2981` | `34984d25` | 7: the 5 Learning modules, `Randomness`, root `TCSlib` |
  | #318 (sc-ot) | `f62a25b3` | `23c029c1` | 6: `ObliviousTransfer`, `OT/Predictor`, `OT/ViewB`, `YaoReal`, `SecureComputation`, `TCSlib` |
  | #319 (canonizer) | `6421ac16` | `59401ef7` | 33, through the downstream of `DAGCircuit` and of #319's machine-library files |
  | #324 (sc-compose) | `a6eaebd7` | `e6911ef7` | 3: `YaoReal`, `SecureComputation`, `TCSlib` |

- No open PR changes a module of the unit's closure (166 modules). `DAGCircuit` is upstream of much of the library
  (the review: 273 modules downstream of it), which is why the shared downstream with #313 and #319 is large.
- Of the 388 built modules (build plus edit-build, at the head), all have the tip-merged source and 387 each other
  PR's merged source (`pack-checks/srcequality.txt`). None of the 53 new short names is declared in a file another PR
  changes (`pack-checks/namecheck.txt`); the review's name-clash scan over all TCSlib files has 0 exact clashes.
- **Pending merge condition (not an audit item).** The combined trees are **not** built. Whichever of #323 and #313,
  #318, #319 or #324 merges second needs an integration rebuild of the shared downstream on the merged tip before it
  merges; the maintainer runs that build. Treat it as a condition on the merge, not as something for this audit to
  establish. What you can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **SG-F02** (info, disclosed): `yaoSeed_good_whp` goes through the stronger seed-dependent bound. **SG-F03** (info):
  the `## Main results` and sketch gaps, fixed by LE-doc. **SG-F05** (info): the generic
  `uprob_not_good_distinct_le_of_uniform_data` sits in `GarblingSecurity/NestedBounds`, not `Garbling/`; moved in the
  cleanup. **SG-F06** (info): two unused-simp-argument warnings (`SliceParser:168`, `NestedBounds:89`); cleanup.
  **SG-F07** (info): seal B's 9 new errors, all `PolyExpr.eval` conversions.
- **The worker was Codex**, though the brief names Claude (Seyoon moved the job, decision log 2026-11-15); the worker
  commits carry Seyoon's authorship.
- **The review's PROVENANCE** says docaudit's NO-FORMULA rows are "the 6 frozen target proses"; the rows show 5 (the
  8 = 5 + `of_joint` + 2 Prop formulas). Its `statements/head/` audits and `sizes-widths.txt` are at the pre-edit head
  `e5cb6129` (`GarblingSecurity` 111 lines there, 115 at the head); `source-head.json` is at the head.
- **`yaoProtocol_hbcSecure` keeps `sorryAx`** through `yaoHybrid_*` (sc-yao), `otProtocol_*` (#318) and
  `hbcSecure_compose` (#324); `yaoSeed_good_whp` is no longer among its admissions (review DepTrace).
- **Old (pre-#305) lint** shows 8 more lines of the facade class for the 8 helpers (`lint/oldlint-linediff.txt`);
  recorded, not a finding.
- **The worker's promotion requests** (the option-complement bound, the dependent row marginal, the first-success
  dichotomy, the bit-block restriction, `length_nestedInner` beside `nestedSpecial`, the `encodeList` length bounds)
  are for the deferred cleanup.

## Also check

**Axioms**
- At the head, the seven targets, B2, `uprob_not_good_le_of_uniform_data`, `uprob_not_good_distinct_le_of_uniform_data`,
  `garbling_good_whp`, `specialScheme_multiMessageSecure_of_joint` and the helper endpoints each print
  `[propext, Classical.choice, Quot.sound]`; `DAGCircuit.isFaninTwo_iff` depends on no axioms (`landing/census-head.log`).
  At the base every target and `garbling_good_whp` had `sorryAx`.
- The census has **531** stored constants (= the worker's); the axiom union is the standard three plus `sorryAx`, which
  occurs only in `yaoHybrid_polyTime`, `yaoHybrid_simulators` and `yaoHybrid_hbcSecure` (sc-yao's admissions).
  Against the base: removed = the SG-1 privates and their auxiliaries; `specialScheme_gen_runAt`/`_enc_runAt` moved
  private → public with equal types; 0 type-changed; 8 axiom-changed (the 7 targets and `garbling_good_whp`)
  (`logs/census-base-vs-head.tsv`, name map `statements/namemap-sg1.txt`).

**Admissions:** 32 in 15 modules → **25 in 11**, by exactly the seven targets (`Yao.lean` keeps `yaoHybrid_polyTime`,
`yaoHybrid_simulators`; `logs/sorry-census.txt`).

**Sizes and widths:** every file at most 970 lines (`Yao.lean` ≤ 1000), every line at most 100 characters
(`source-head.json`).

**Build:** at the head, **388/388 modules rc 0, 0 errors in both diagnostic forms** (G26-N1; substring "error" 0): the
downstream of every module changed since `eff2dcd0` (82 = 68 base delta + 14 unit; `DAGCircuit` alone puts 273 modules
downstream of the unit) through root `TCSlib` and both `audits/*/Checks` (`landing/root-checks.jsonl`, at the pre-edit
head `e5cb6129`), then the 9 modules LE-doc touches and their dependants (`landing/edit-build-results.jsonl`). The unit
modules have no `sorry` and only the two SG-F06 warnings. Whole-tree check at the head: 1257 modules, RESULT OK
(`landing/tree-check-head.txt`). Restore: `dl-oleans` back at `457ba704…`. Every built source equals its blob at
`cd9a4843` (`pack-checks/srcequality.txt`).

**Lint:** Cryptography 92/101 and Complexity 25/391 at the tip and the head, with identical line sets; the one
changed Complexity line is `DAGCircuit`'s check-8 WARN, which loses `IsFaninTwo` (it now has a reader).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (SG-F01–SG-F07).
- **`verification.zip`** (147 entries): every file the review cites and the pack uses, as byte-identical originals.
  Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/sc-garble/final-r1/`, SHA-256 `5a121c02…`) and `review-evidence-SHA256SUMS`, its
    manifest: 1273 entries, 72 directories and 1201 files, exactly the 1200 manifest paths plus `SHA256SUMS`
    (byte-identical to the manifest; no top folder); every hash verifies;
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `records/` (19): the issue package `fills/sc-garble/issued-r1/` (with `ruling-SG-1.md`), the duplication ledger
    (DL-46, DL-47 with SG-F04), the decision log, Gate 27's resolutions (the hand-off obligations), Gate 31's findings,
    resolutions and worker report (the B1 consumer map), the secure-computation plan, the Codex host addendum and
    sc-yao's `ruling-SY.md` (SY-3), at records `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`;
  - `evidence/` (83): byte copies of the ZIP entries this pack cites;
  - `worker/final/` (19): byte copies from exchange `a73072f19787ee437f2201777711c7eb3154c714`
    (`inbox/fills/sc-garble/`): `COMMITS.tsv`, the scope request and approved patch, the seal-B attribution and
    summary, the axiom summary, the preflight, the header-check results, controls and `Yao.diff`, the corollary diff,
    the private-use search, the clash log and the final signatures (17 of them also byte-identical to the review's
    `logs/delivery-extracts/`);
  - `pack-checks/` (21): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `a73072f1`, under `inbox/fills/sc-garble/`. Its top `SHA256SUMS`
  lists 1278 files and `evidence/SHA256SUMS` 1254, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`), `build-summary.txt`,
  `edit-build-results.jsonl`, `edit-build-summary.txt`, `census-head.log` (= `probe-runs/mods/PlProbe_H_CensusHead.log`),
  `frozen-check.txt` (= `statements/frozen/frozen-check-le.txt`) and `tree-check-head.txt`.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `a73072f1`.
- **`pr-description.md`:** the PR #323 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (14 paths, 1901 insertions, 122 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 14 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 166 files.
- **The bundle** adds, as context at the head: `SpecialEncryption.lean` (`spEncStr`, `spDecStr` and their readers),
  `GarblingSpecial.lean` (`nestedSpecial`), `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean` (D4) and the frozen
  `DAGCircuit.lean` hunk (in `pr.diff.txt`).

## Findings delivery

Return `gate36-sc-garble-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-46 and DL-47, or necessary
  evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. |

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti/SliceParser.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficient slice post-processor

## Main definitions

* `SliceReduction.slicePost`: read slice descriptors and ciphertexts in parallel.

## Main results

* `SliceReduction.polyTimeComputable_slicePost`: the parser is polynomial-time on all words.
* `SliceReduction.slicePost_encode`: its exact law on encoded descriptor/ciphertext pairs.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, Theorem 99.2 with slices.
-/

namespace TCSlib.Cryptography.SecureComputation.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- Drop one descriptor and one ciphertext from the paired parser state:
`parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
def parserStep (z : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z))

/-- `parserStep z = ⟨snd (fst z), snd (snd z)⟩`. -/
theorem parserStep_eq (z : List Bool) :
    parserStep z = pairEncode (pairSndD (pairFstD z)) (pairSndD (pairSndD z)) := rfl

/-- Emit one slice ciphertext chunk. A descriptor `⟨u,v⟩` selects offset `|u|` and width
`|v|`; on a state `⟨advice,ciphertexts⟩`, read both first entries, keep the nonce, cut the
body, and emit `⟨⟨nonce,body.drop |u| |>.take |v|⟩,[]⟩`. Emit nothing if ciphertexts are empty. -/
def parserEmit (z : List Bool) : List Bool :=
  if pairSndD z = [] then [] else
    pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
      (((pairSndD (pairFstD (pairSndD z))).drop
        (pairFstD (pairFstD (pairFstD z))).length).take
          (pairSndD (pairFstD (pairFstD z))).length)) []

/-- `parserEmit z` is empty if `snd z=[]`; otherwise it is the encoded chunk
`⟨⟨fst (fst (snd z)),(snd (fst (snd z))).drop |fst (fst (fst z))|
  |>.take |snd (fst (fst z))|⟩,[]⟩`. -/
theorem parserEmit_eq (z : List Bool) :
    parserEmit z = if pairSndD z = [] then [] else
      pairEncode (pairEncode (pairFstD (pairFstD (pairSndD z)))
        (((pairSndD (pairFstD (pairSndD z))).drop
          (pairFstD (pairFstD (pairFstD z))).length).take
            (pairSndD (pairFstD (pairFstD z))).length)) [] := rfl

/-- The total slice parser runs `|z|+1` emissions:
`slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
def slicePost (z : List Bool) : List Bool :=
  Games.iterEmit parserStep parserEmit (z.length + 1) z

/-- `slicePost z = Games.iterEmit parserStep parserEmit (z.length+1) z`. -/
theorem slicePost_eq (z : List Bool) :
    slicePost z = Games.iterEmit parserStep parserEmit (z.length + 1) z := rfl

/-- Dropping both list heads never lengthens the state beyond the empty pair:
`(parserStep z).length ≤ max z.length 2`.

**Proof sketch.** Reuse the published pair-state bound after shortening the second
component. Shortening the first component can only reduce its contribution to the public
pairing length formula. -/
theorem length_parserStep_le (z : List Bool) : (parserStep z).length ≤ max z.length 2 := by
  rw [parserStep_eq]
  have hf := length_pairSndD_le (pairFstD z)
  have hs := OneWay.PosLoop.length_pairEncode_pairFstD_le z
    (pairSndD (pairSndD z)) (length_pairSndD_le (pairSndD z))
  refine le_trans ?_ hs
  rw [length_pairEncode, length_pairEncode]
  omega

/-- The slice parser is polynomial-time on every input word:
`PolyTimeComputable slicePost`.

**Proof sketch.** Total pair projections read the current descriptor and ciphertext.
The descriptor's two unary lengths drive the published polynomial-time drop and take
operations. Pair the retained nonce and cut body and emit a self-delimited list chunk.
The step drops both list heads and stays within `max |z| 2`, so the published iterate-and-emit
host gives a polynomial-time parser, including malformed inputs. -/
theorem polyTimeComputable_slicePost : PolyTimeComputable slicePost := by
  have hf := polyTimeComputable_pairFstD
  have hs := polyTimeComputable_pairSndD
  have hadv := hf.comp' hf
  have hct := hf.comp' hs
  have ho := hf.comp' hadv
  have hw := hs.comp' hadv
  have hbody := hs.comp' hct
  have hdrop := (polyTimeComputable_pairDropPoly .var).comp' (ho.pairEncode hbody)
  have htake := (polyTimeComputable_pairTakePoly .var).comp' (hw.pairEncode hdrop)
  have hemit : PolyTimeComputable parserEmit := by
    have hnil := polyTimeComputable_isNil.comp' hs
    have hout := ((hf.comp' hct).pairEncode htake).pairEncode (polyTimeComputable_const [])
    convert polyTimeComputable_ite hnil (polyTimeComputable_const []) hout using 1
    funext z
    rw [parserEmit_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
    by_cases h : pairSndD z = []
    · rw [if_pos h, decide_eq_true h]; rfl
    · rw [if_neg h, decide_eq_false h]; rfl
  exact Games.polyTimeComputable_iterEmit
    ((hs.comp' hf).pairEncode (hs.comp' hs)) hemit 2 length_parserStep_le

/-- On paired encoded lists of descriptors and ciphertexts, the parser cuts every body
and keeps every nonce:
`slicePost ⟨encodeList (l.map fst),encodeList (l.map snd)⟩ = encodeList
  (l.map fun (d,c) => ⟨fst c,(snd c).drop |fst d| |>.take |snd d|⟩)`.
[PS10, Theorem 99.2, with slices]

**Proof sketch.** Regard the state as one encoding of a list of descriptor/ciphertext
pairs. The step removes the two heads, the empty state is fixed, and emission reads the
specified chunk of each ciphertext. The list encoding contains at least one bit per entry,
so `|state|+1` iterations suffice. Apply the existing iterate-and-emit encoding theorem and
the existing flat-map law for the ciphertext list encoding. -/
theorem slicePost_encode (l : List (List Bool × List Bool)) :
    slicePost (pairEncode (PrivateKeyScheme.encodeList (l.map Prod.fst))
      (PrivateKeyScheme.encodeList (l.map Prod.snd))) =
        PrivateKeyScheme.encodeList (l.map fun e => pairEncode (pairFstD e.2)
          (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) := by
  let enc : List (List Bool × List Bool) → List Bool := fun t =>
    pairEncode (PrivateKeyScheme.encodeList (t.map Prod.fst))
      (PrivateKeyScheme.encodeList (t.map Prod.snd))
  let g : (List Bool × List Bool) → List Bool := fun e =>
    pairEncode (pairEncode (pairFstD e.2)
      (((pairSndD e.2).drop (pairFstD e.1).length).take (pairSndD e.1).length)) []
  have hnil : enc [] = pairEncode [] [] := by
    simp only [enc, List.map_nil, PrivateKeyScheme.encodeList_nil]
  have hcons (e : List Bool × List Bool) (t : List (List Bool × List Bool)) :
      enc (e :: t) = pairEncode
        (pairEncode e.1 (PrivateKeyScheme.encodeList (t.map Prod.fst)))
        (pairEncode e.2 (PrivateKeyScheme.encodeList (t.map Prod.snd))) := by
    simp only [enc, List.map_cons, PrivateKeyScheme.encodeList_cons]
  have hstep_nil : parserStep (enc []) = enc [] := by
    rw [hnil, parserStep_eq, pairFstD_pairEncode, pairSndD_pairEncode]
    simp only [pairSndD_eq, pairDecode_nil, Option.map_none, Option.getD_none]
  have hstep : ∀ e ∈ l, ∀ t, parserStep (enc (e :: t)) = enc t := by
    intro e he t
    rw [hcons, parserStep_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, enc]
  have hemit_nil : parserEmit (enc []) = [] := by
    rw [hnil, parserEmit_eq, pairSndD_pairEncode, if_pos rfl]
  have hemit : ∀ e ∈ l, ∀ t, parserEmit (enc (e :: t)) = g e := by
    intro e he t
    rw [hcons, parserEmit_eq, pairSndD_pairEncode, if_neg (pairEncode_ne_nil _ _)]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, g]
  have hfuel : l.length ≤ (enc l).length + 1 := by
    have h := TCSlib.Cryptography.length_le_length_encodeList (l.map Prod.snd)
    rw [List.length_map] at h
    dsimp only [enc]
    rw [length_pairEncode]
    omega
  rw [slicePost_eq]
  change Games.iterEmit parserStep parserEmit ((enc l).length + 1) (enc l) = _
  rw [Games.iterEmit_encode parserStep parserEmit enc g l hstep_nil hstep
    hemit_nil hemit _ hfuel, MultiMsg.encodeList_eq_flatMap, List.flatMap_map]

end TCSlib.Cryptography.SecureComputation.SliceReduction

## ===== TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The iterated block encryptor and tuple decryptor

The honest iterated machines behind the public-key constructions of [PS10, §3.10]: the
**block encryptor** `blockEncFun E L B` which, on the state word `⟨u, ⟨pk, ⟨m, r⟩⟩⟩`, encrypts the
consecutive `L(|u|)`-bit blocks of the message string `m` under the public key `pk` with a fresh
`B(|u|)`-coin segment of `r` each, returning the nested-pair tuple of the ciphertexts; and the
**tuple decryptor** `decListFun Dc` which, on `⟨sk, ⟨c₀, ⟨c₁, …⟩⟩⟩`, concatenates `Dc ⟨sk, cᵢ⟩`.
With one-bit blocks they are the encryptor and decryptor of the bitwise scheme built from a
single-bit secure scheme [PS10, p. 103]; with `n`-bit blocks the encryptor is the
"efficiently generate encryptions of any message, without knowing the secret key" step of the
hybrid reductions of the single ⇒ multi-message theorem for public-key encryption
[PS10, p. 103] and of the multi-value hiding of commitments [PS10, Theorem 126.4]. Both are
instances of `Complexity.polyTimeComputable_iterateEmit` (D11), with the unfolding lemmas
`blockEncFun_spec`, `blockList_ofFn`, `decListFun_spec` proved.

## Main definitions

* `TCSlib.Cryptography.blockState`, `blockStep`, `blockEmit`, `blockEncFun`, `blockList` — the
  block encryptor, its step, emission and ideal output.
* The common `TCSlib.Cryptography.coinBlock` from `Asymptotic.Adversary` supplies coin segments.
* `TCSlib.Cryptography.decListStep`, `decListEmit`, `decListFun` — the tuple decryptor.

## Main results

* `TCSlib.Cryptography.blockEncFun_spec`, `blockList_ofFn` — unfolding of the block encryptor.
* `TCSlib.Cryptography.blockEncFun_poly`, `decListFun_poly` — both machines are polynomial-time.
* `TCSlib.Cryptography.decListFun_spec` — unfolding of the tuple decryptor.
* `TCSlib.Cryptography.encodeList_eq_flatMap`, `pairEncode_nil_append`,
  `length_le_length_encodeList` — the tuple encoding as a concatenation of blocks.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.10, p. 103; §4.6, Theorem 126.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026.
-/

namespace TCSlib.Cryptography

open Complexity Turing
open PrivateKeyScheme (encodeList)

/-! ## The tuple encoding as a concatenation of blocks -/

/-- The nested-pair encoding is the concatenation of the self-delimiting blocks `⟨c, []⟩`. -/
theorem encodeList_eq_flatMap (l : List (List Bool)) :
    encodeList l = l.flatMap fun c => pairEncode c [] := by
  induction l with
  | nil =>
    rw [PrivateKeyScheme.encodeList_nil]
    rfl
  | cons c cs ih => simp [PrivateKeyScheme.encodeList_nil, PrivateKeyScheme.encodeList_cons, ih,
      pairEncode_eq]

/-- A tuple encoding is at least as long as the tuple. -/
theorem length_le_length_encodeList (l : List (List Bool)) :
    l.length ≤ (encodeList l).length := by
  induction l with
  | nil => simp
  | cons c cs ih => simp only [PrivateKeyScheme.encodeList_nil, PrivateKeyScheme.encodeList_cons,
      length_pairEncode, List.length_cons]; omega

/-! ## The iterated block encryptor and decryptor -/

/-- The state word `⟨u, ⟨pk, ⟨m, r⟩⟩⟩` of the block encryptor: unary parameter `u`, public key
`pk`, remaining message `m`, remaining coins `r`. -/
def blockState (u pk m r : List Bool) : List Bool := pairEncode u (pairEncode pk (pairEncode m r))

/-- A block state is the nested pair encoding of its parameter, key, message and coins. -/
theorem blockState_eq (u pk m r : List Bool) :
    blockState u pk m r = pairEncode u (pairEncode pk (pairEncode m r)) := rfl

/-- One step of the block encryptor: drop `L(|u|)` message bits and `B(|u|)` coins. -/
def blockStep (L B : PolyExpr) (w : List Bool) : List Bool :=
  blockState (pairFstD w) (pairFstD (pairSndD w))
    ((pairFstD (pairSndD (pairSndD w))).drop (L.eval (pairFstD w).length))
    ((pairSndD (pairSndD (pairSndD w))).drop (B.eval (pairFstD w).length))

/-- The emission of the block encryptor: nothing once the message is exhausted, otherwise the
block `⟨E ⟨⟨⟨u, ⟨pk, m.take L⟩⟩, []⟩, r.take B⟩, []⟩` (the evaluator `E` is an `NUPPT.output` run
on the uniform layout with the next coin segment). The emptiness test is written in the shape
of `Complexity.polyTimeComputable_lenLe`. -/
def blockEmit (E : List Bool → List Bool) (L B : PolyExpr) (w : List Bool) : List Bool :=
  if decide ((pairSndD (pairEncode [] (pairFstD (pairSndD (pairSndD w))))).length ≤
      (pairFstD (pairEncode [] (pairFstD (pairSndD (pairSndD w))))).length) then []
  else pairEncode (E (NUPPT.layout (pairFstD w)
    (pairEncode (pairFstD (pairSndD w))
      ((pairFstD (pairSndD (pairSndD w))).take (L.eval (pairFstD w).length)))
    [] ((pairSndD (pairSndD (pairSndD w))).take (B.eval (pairFstD w).length)))) []

/-- The **block encryptor**: on a state word `x = ⟨u, ⟨pk, ⟨m, r⟩⟩⟩`, the concatenation of the
emissions along `|x| + 1` steps — the nested-pair tuple of the encryptions of the consecutive
`L(|u|)`-bit blocks of `m` under `pk`, each with a fresh `B(|u|)`-coin segment of `r`. -/
def blockEncFun (E : List Bool → List Bool) (L B : PolyExpr) (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => blockEmit E L B ((blockStep L B)^[i] x)

/-- The block encryptor concatenates the emissions of rounds `0, …, |x|` from `x`. -/
theorem blockEncFun_eq (E : List Bool → List Bool) (L B : PolyExpr) (x : List Bool) :
    blockEncFun E L B x =
      (List.range (x.length + 1)).flatMap fun i => blockEmit E L B ((blockStep L B)^[i] x) := rfl

/-- The ideal list of block encryptions with fuel `k`: `[]` once the message is empty. -/
def blockList (E : List Bool → List Bool) (L B : ℕ) (u pk : List Bool) :
    ℕ → List Bool → List Bool → List (List Bool)
  | 0, _, _ => []
  | k + 1, m, r => if m = [] then [] else
      E (NUPPT.layout u (pairEncode pk (m.take L)) [] (r.take B)) ::
        blockList E L B u pk k (m.drop L) (r.drop B)

/-- `blockList` with no fuel: `blockList E L B u pk 0 m r = []`. -/
theorem blockList_zero (E : List Bool → List Bool) (L B : ℕ) (u pk m r : List Bool) :
    blockList E L B u pk 0 m r = [] := rfl

/-- `blockList` with fuel `k + 1`: `[]` on the empty message, otherwise the encryption of the first
`L` bits with the first `B` coins followed by the list of the rest:
`blockList E L B u pk (k + 1) m r = if m = [] then [] else
E (layout u ⟨pk, m.take L⟩ [] (r.take B)) :: blockList E L B u pk k (m.drop L) (r.drop B)`. -/
theorem blockList_succ (E : List Bool → List Bool) (L B : ℕ) (u pk : List Bool) (k : ℕ)
    (m r : List Bool) :
    blockList E L B u pk (k + 1) m r = if m = [] then [] else
      E (NUPPT.layout u (pairEncode pk (m.take L)) [] (r.take B)) ::
        blockList E L B u pk k (m.drop L) (r.drop B) := rfl

/-- Unfolding: the step on a state word. -/
theorem blockStep_blockState (L B : PolyExpr) (u pk m r : List Bool) :
    blockStep L B (blockState u pk m r) =
      blockState u pk (m.drop (L.eval u.length)) (r.drop (B.eval u.length)) := by
  simp [blockStep, blockState]

/-- Unfolding: the emission on a state word. -/
theorem blockEmit_blockState (E : List Bool → List Bool) (L B : PolyExpr) (u pk m r : List Bool) :
    blockEmit E L B (blockState u pk m r) = if m = [] then [] else
      pairEncode (E (NUPPT.layout u (pairEncode pk (m.take (L.eval u.length))) []
        (r.take (B.eval u.length)))) [] := by
  simp [blockEmit, blockState, List.length_eq_zero_iff]

/-- The projections of the empty word are empty. -/
private theorem pairFstD_nil : pairFstD [] = [] :=
  pairFstD_of_pairDecode_eq_none Turing.pairDecode_nil

/-- The projections of the empty word are empty. -/
private theorem pairSndD_nil : pairSndD [] = [] :=
  pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil

/-- The block `⟨c, []⟩` followed by a tuple is the tuple extended by `c`. -/
theorem pairEncode_nil_append (c w : List Bool) :
    pairEncode c [] ++ w = pairEncode c w := by
  simp [pairEncode_eq]

/-- **Unfolding of the block encryptor** on a state word: with `k` rounds and a message of at
most `k · L(|u|)` bits (`L(|u|) > 0`), the concatenated emissions are the nested-pair tuple of
`blockList` with fuel `k + 1`.

**Proof sketch.** Induction on `k` generalizing `m, r`: `List.range_succ_eq_map` splits off the
first emission (`blockEmit_blockState`); the remaining emissions are those of the state after
one step (`Function.iterate_succ_apply`, `blockStep_blockState`), covered by the induction
hypothesis at `m.drop L` (`List.length_drop`), and `pairEncode_nil_append` reassembles the
tuple; an empty message emits nothing forever. -/
theorem blockEncFun_spec (E : List Bool → List Bool) (L B : PolyExpr) (u pk : List Bool) :
    ∀ (k : ℕ) (m r : List Bool), m.length ≤ k * L.eval u.length →
      ((List.range (k + 1)).flatMap fun i =>
        blockEmit E L B ((blockStep L B)^[i] (blockState u pk m r))) =
      encodeList (blockList E (L.eval u.length) (B.eval u.length) u pk (k + 1) m r) := by
  intro k
  induction k with
  | zero =>
    intro m r hm
    have hm0 : m = [] := List.length_eq_zero_iff.mp (by simpa using hm)
    subst hm0
    simp [blockEmit_blockState, blockList, PrivateKeyScheme.encodeList_nil,
        PrivateKeyScheme.encodeList_cons]
  | succ k ih =>
    intro m r hm
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply, blockStep_blockState]
    by_cases hm0 : m = []
    · subst hm0
      simp only [List.drop_nil]
      rw [ih [] (r.drop (B.eval u.length)) (by simp)]
      simp [blockEmit_blockState, blockList, PrivateKeyScheme.encodeList_nil,
          PrivateKeyScheme.encodeList_cons]
    · rw [ih (m.drop (L.eval u.length)) (r.drop (B.eval u.length)) (by
        rw [List.length_drop, Nat.add_mul, one_mul] at *
        omega)]
      simp only [blockEmit_blockState, hm0, if_false, blockList, PrivateKeyScheme.encodeList_nil,
          PrivateKeyScheme.encodeList_cons]
      exact pairEncode_nil_append _ _

/-- A step grows a word by at most six symbols (an invalid word collapses to the empty state).

**Proof sketch.** Case analysis on the validity of the three nested pairs (`pairDecode`
`none` versus `eq_pairEncode_of_pairDecode`); `length_pairEncode`, `List.length_drop`. -/
private theorem length_blockStep_le (L B : PolyExpr) (w : List Bool) :
    (blockStep L B w).length ≤ w.length + 6 := by
  have key : ∀ z : List Bool, (pairFstD z = [] ∧ pairSndD z = []) ∨
      2 * (pairFstD z).length + 2 + (pairSndD z).length = z.length := by
    intro z
    cases hz : pairDecode z with
    | none => exact Or.inl ⟨by simp [pairFstD_eq, hz], by simp [pairSndD_eq, hz]⟩
    | some p =>
      obtain ⟨a, b⟩ := p
      rw [eq_pairEncode_of_pairDecode z a b hz]
      exact Or.inr (by simp [length_pairEncode])
  simp only [blockStep, blockState, length_pairEncode, List.length_drop]
  rcases key w with ⟨hw1, hw2⟩ | hw
  · simp only [hw1, hw2, pairFstD_nil, pairSndD_nil, List.length_nil]
    omega
  rcases key (pairSndD w) with ⟨ht1, ht2⟩ | ht
  · simp only [ht1, ht2, pairFstD_nil, pairSndD_nil, List.length_nil]
    omega
  rcases key (pairSndD (pairSndD w)) with ⟨hs1, hs2⟩ | hs
  · simp only [hs1, hs2, List.length_nil]
    omega
  omega

/-- Orbit bound for a step that grows words by at most `c` symbols. -/
private theorem length_iterate_le {g : List Bool → List Bool} {c : ℕ}
    (hg : ∀ w, (g w).length ≤ w.length + c) (x : List Bool) :
    ∀ i, (g^[i] x).length ≤ x.length + c * i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := hg (g^[i] x)
    rw [Nat.mul_succ]
    omega

/-- The block step is polynomial-time (pair projections, `polyTimeComputable_pairDropPoly`). -/
theorem blockStep_poly (L B : PolyExpr) : PolyTimeComputable (blockStep L B) := by
  have hu := polyTimeComputable_pairFstD
  have hpk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hr := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h := hu.pairEncode (hpk.pairEncode
    (((polyTimeComputable_pairDropPoly L).comp (hu.pairEncode hm)).pairEncode
      ((polyTimeComputable_pairDropPoly B).comp (hu.pairEncode hr))))
  convert h using 1
  funext w
  simp [blockStep, blockState, Function.comp_apply]

/-- The block emission is polynomial-time for a polynomial-time `E`
(`polyTimeComputable_ite`, `polyTimeComputable_lenLe`, `polyTimeComputable_pairTakePoly`,
`NUPPT.polyTimeComputable_layout`). -/
theorem blockEmit_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) (L B : PolyExpr) :
    PolyTimeComputable (blockEmit E L B) := by
  have hu := polyTimeComputable_pairFstD
  have hpk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hr := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hp := polyTimeComputable_lenLe.comp ((polyTimeComputable_const []).pairEncode hm)
  have hbody := (hE.comp (NUPPT.polyTimeComputable_layout hu
    (hpk.pairEncode ((polyTimeComputable_pairTakePoly L).comp (hu.pairEncode hm)))
    (polyTimeComputable_const []) ((polyTimeComputable_pairTakePoly B).comp (hu.pairEncode hr)))).pairEncode
    (polyTimeComputable_const [])
  have h := polyTimeComputable_ite hp (polyTimeComputable_const []) hbody
  convert h using 1
  funext w
  simp only [blockEmit, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The block encryptor is polynomial-time**: an instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := var` rounds and the orbit bound
`7 · |x|` (`length_blockStep_le`, `length_iterate_le`). -/
theorem blockEncFun_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) (L B : PolyExpr) :
    PolyTimeComputable (blockEncFun E L B) := by
  have h := polyTimeComputable_iterateEmit (blockStep_poly L B) (blockEmit_poly hE L B)
    .var (.mul (.const 7) .var) (fun x i hi => by
      have := length_iterate_le (length_blockStep_le L B) x i
      simp only [PolyExpr.eval_var] at hi
      simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      nlinarith)
  exact h

/-- One step of the tuple decryptor on `⟨sk, cs⟩`: drop the first ciphertext. -/
def decListStep (w : List Bool) : List Bool := pairEncode (pairFstD w) (pairSndD (pairSndD w))

/-- The emission of the tuple decryptor on `⟨sk, cs⟩`: nothing once the tuple is exhausted,
otherwise `Dc ⟨sk, c₀⟩` (test in the shape of `polyTimeComputable_lenLe`). -/
def decListEmit (Dc : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide ((pairSndD (pairEncode [] (pairSndD w))).length ≤
      (pairFstD (pairEncode [] (pairSndD w))).length) then []
  else Dc (pairEncode (pairFstD w) (pairFstD (pairSndD w)))

/-- The **tuple decryptor**: on `x = ⟨sk, ⟨c₀, ⟨c₁, …⟩⟩⟩` the concatenation
`Dc ⟨sk, c₀⟩ ++ Dc ⟨sk, c₁⟩ ++ ⋯` along `|x| + 1` steps. -/
def decListFun (Dc : List Bool → List Bool) (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => decListEmit Dc (decListStep^[i] x)

/-- The defining equation of `decListFun`: the emissions of rounds `0, …, |x|`, concatenated. -/
theorem decListFun_eq (Dc : List Bool → List Bool) (x : List Bool) :
    decListFun Dc x =
      (List.range (x.length + 1)).flatMap fun i => decListEmit Dc (decListStep^[i] x) := rfl

/-- **Unfolding of the tuple decryptor**: with `k ≥ |l|` rounds on `⟨sk, encodeList l⟩` the
emissions concatenate to `l.flatMap (fun c => Dc ⟨sk, c⟩)`.

**Proof sketch.** Induction on `k` generalizing `l`, cases on `l`; `List.range_succ_eq_map`,
`Function.iterate_succ_apply`; the step on `⟨sk, ⟨c, rest⟩⟩` is `⟨sk, rest⟩` and the step on
`⟨sk, []⟩` is `⟨sk, []⟩`. -/
theorem decListFun_spec (Dc : List Bool → List Bool) (sk : List Bool) :
    ∀ (k : ℕ) (l : List (List Bool)), l.length ≤ k →
      ((List.range (k + 1)).flatMap fun i => decListEmit Dc (decListStep^[i] (pairEncode sk (encodeList l)))) =
        l.flatMap fun c => Dc (pairEncode sk c) := by
  intro k
  induction k with
  | zero =>
    intro l hl
    have hl0 : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hl0
    simp [decListEmit, PrivateKeyScheme.encodeList_nil, PrivateKeyScheme.encodeList_cons]
  | succ k ih =>
    intro l hl
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]
    cases l with
    | nil =>
      have hstep : decListStep (pairEncode sk (encodeList [])) = pairEncode sk (encodeList []) := by
        simp [decListStep, PrivateKeyScheme.encodeList_nil, PrivateKeyScheme.encodeList_cons,
            pairSndD_nil]
      rw [hstep, ih [] (by simp)]
      simp [decListEmit, PrivateKeyScheme.encodeList_nil, PrivateKeyScheme.encodeList_cons]
    | cons c cs =>
      have hstep : decListStep (pairEncode sk (encodeList (c :: cs))) = pairEncode sk (encodeList cs) := by
        simp [decListStep, PrivateKeyScheme.encodeList_nil, PrivateKeyScheme.encodeList_cons]
      rw [hstep, ih cs (by simpa using hl)]
      simp [decListEmit, PrivateKeyScheme.encodeList_nil, PrivateKeyScheme.encodeList_cons,
          length_pairEncode]

/-- The tuple decryptor's step grows a word by at most two symbols. -/
private theorem length_decListStep_le (w : List Bool) : (decListStep w).length ≤ w.length + 2 := by
  simp only [decListStep, length_pairEncode]
  cases hz : pairDecode w with
  | none =>
    simp [pairFstD_eq, pairSndD_eq, hz, Turing.pairDecode_nil]
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [eq_pairEncode_of_pairDecode w a b hz]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode]
    have : (pairSndD b).length ≤ b.length := by
      cases hb : pairDecode b with
      | none => simp [pairSndD_eq, hb]
      | some p' =>
        obtain ⟨a', b'⟩ := p'
        rw [eq_pairEncode_of_pairDecode b a' b' hb]
        simp [length_pairEncode]
    omega

/-- **The tuple decryptor is polynomial-time** for a polynomial-time `Dc`
(`polyTimeComputable_iterateEmit`, `R := var`, orbit bound `7 · |x|`). -/
theorem decListFun_poly {Dc : List Bool → List Bool} (hD : PolyTimeComputable Dc) :
    PolyTimeComputable (decListFun Dc) := by
  have hstep : PolyTimeComputable decListStep :=
    polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hemit : PolyTimeComputable (decListEmit Dc) := by
    have hp := polyTimeComputable_lenLe.comp
      ((polyTimeComputable_const []).pairEncode polyTimeComputable_pairSndD)
    have h := polyTimeComputable_ite hp (polyTimeComputable_const [])
      (hD.comp (polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
    convert h using 1
  have h := polyTimeComputable_iterateEmit hstep hemit .var (.mul (.const 7) .var)
    (fun x i hi => by
      have := length_iterate_le length_decListStep_le x i
      simp only [PolyExpr.eval_var] at hi
      simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      nlinarith)
  exact h

/-- `blockList` with one-bit blocks and enough fuel on an `n`-bit message is the list of the `n`
bit encryptions with the consecutive coin segments.

**Proof sketch.** Induction on `n`; `List.ofFn_succ` splits off the first bit, the fuel is a
successor, and the segments of `r.drop B` are the shifted segments of `r` (`List.drop_drop`). -/
theorem blockList_ofFn (E : List Bool → List Bool) (B : ℕ) (u pk : List Bool) :
    ∀ (n : ℕ) (m : Fin n → Bool) (r : List Bool) (k : ℕ), n ≤ k →
      blockList E 1 B u pk k (List.ofFn m) r =
        List.ofFn fun i : Fin n => E (NUPPT.layout u (pairEncode pk [m i]) [] (coinBlock B i r)) := by
  intro n
  induction n with
  | zero =>
    intro m r k _
    cases k <;> simp [blockList]
  | succ n ih =>
    intro m r k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [blockList, List.cons_ne_nil, if_false, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, coinBlock_eq, Fin.val_zero, zero_mul, List.cons.injEq,
      true_and]
    rw [ih (fun i => m i.succ) (r.drop B) k (by omega)]
    congr 1
    funext i
    simp only [coinBlock_eq, Fin.val_succ, List.drop_drop]
    rw [show (B + ↑i * B) = (↑i + 1) * B by ring]

end TCSlib.Cryptography
