# Gate 34 · Oblivious transfer from trapdoor permutations (`sc-ot`, Protocol 160.4 and Proposition 161.5) · round 2

The auditor is Codex. Round 1 was HOLD (0/2/0/0); its findings are `findings/gate34-sc-ot-findings.md` (SHA-256
`9ab967ee…`). This round re-audits the fix of G34-01, the recorded disposition of G34-02, the rebase, and
duplication since round 1. The round-1 pack (`pack.md`) still defines the scope; its questions stand for anything
round 1 left unverified.

- **PR:** draft [PR #318](https://github.com/Shilun-Allan-Li/tcslib/pull/318), now at
  `b0bad23ae611983e3323460bb8c564da90ad6e8c` (branch `land/pass-shelat-sc-ot`, tree
  `3b4301cf650324a3b6d5a59f2c3b60fb6f963dfd`). Round 1 audited `f62a25b3eda099c9cf9371900664752e7b89007d`.
- **Base:** `05d26fe5b41fcb9426ec220d877d03264b9c8e8c`, the merge base with the records tip
  `b0ebd475eb0b4131449bce58462f168f27eee17b`. Round 1's base was `a334ec2e`. The PR was **rebased** (§ 3). Since
  `05d26fe5` the tip has merged #313 (learning, `10cc8c97`) and records; #318 is not rebased onto #313 (§ 5).
- **New since round 1:**
  - **the rebase** of the 5 round-1 commits onto `05d26fe5`, ending at `e0ecdf223490ad9c99fc9151ca5bef5821e6cf29`
    (= `f62a25b3` rebased; the 7 unit files byte-identical);
  - **LE-gate34** `b0bad23a` on `e0ecdf22` (G34-01; `ObliviousTransfer/Efficiency.lean` only, +8/−5), by the
    maintainer (author and committer Claude, SSH-signed).
- **Pushed:** the maintainer force-pushed the branch with lease, with Seyoon's approval (decision-log row "derand and
  seq-zk reviewed", 2026-11-16). `refs/pull/318/head` is `b0bad23a`.
- **Resolutions:** `resolutions-r1.md` (ruling Seyoon, 2026-11-15: "fix 01, ledger 02"), and the decision-log rows
  of 2026-11-15 and 2026-11-16 (in `verification-r2.zip`).
- **Pending merge condition** (not an audit item; § 5): whichever of #318 and another open PR with a shared
  downstream merges second needs an integration rebuild on the merged tip; the maintainer runs that build.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `OT/` is
`SecureComputation/ObliviousTransfer/`.

## What to check

### 1. G34-01: is LE-gate34 proof only, and are both readers now the public `headD_drop`?

The diff is `landing/le-gate34.diff` in the round-2 evidence (= `git diff e0ecdf22 b0bad23a`). The public lemma is
`TCSlib.Cryptography.headD_drop {α} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d`
(`Foundations/BitLists.lean:52` at the head). In `OT/Efficiency.lean`:

```lean
-- before (round 1)
theorem getD_zero_eq (y : List Bool) : y.getD 0 false = y.headD false := by
  cases y <;> rfl
theorem getD_one_eq' (y : List Bool) : y.getD 1 false = (y.drop 1).headD false := by
  rcases y with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl
-- after
theorem getD_zero_eq (y : List Bool) : y.getD 0 false = y.headD false := by
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.headD_drop y 0 false).symm
theorem getD_one_eq' (y : List Bool) : y.getD 1 false = (y.drop 1).headD false :=
  (TCSlib.Cryptography.headD_drop y 1 false).symm
```

These are your proposed bodies. Each docstring gains the line "It is the public
`TCSlib.Cryptography.headD_drop` at `i = 0` (resp. `i = 1`), reversed." (a pure insertion). No import is added:
`Foundations/BitLists` was already in `Efficiency`'s closure, at round 1 and at the head.

Check that both headers are unchanged, that only these two bodies and docstrings changed, and that the new proofs use
`headD_drop` as published. Re-checked for this pack from git objects (`checks/lecheck.txt`): the commit touches
`OT/Efficiency.lean` only (+8/−5, three hunks). Its 38 declarations keep their headers, order and definition blocks,
and its imports are unchanged. Only the docstrings of `getD_zero_eq` and `getD_one_eq'` change. Both names are used
only in `Efficiency.lean` (one `rw` at line 228 and one docstring at line 216). `getD_one_eq'` loses its `by` after
`:=`; the header, which runs to the top-level `:=`, is byte-identical.

**The overlap records:** the evidence's `landing-gate34/NOTE.txt` is the sc-ot overlap record after Gate 34. DL-48
also says that G34-01 is fixed by LE-gate34 and is not debt (§ 2).

**Evidence** (`landing-r1/`): `gate34-le-evidence.zip` (SHA-256
`145d557402f025f62ba9ac2e389c7212df12fb3123646909472c29f88d49a771`; 460 entries = the 459 paths of its manifest
`evidence-SHA256SUMS` plus `SHA256SUMS`) and its `PROVENANCE.txt`. At `b0bad23a`:
- **Statements:** decls2 against the parent `e0ecdf22` is empty; the frozen check gives 38 → 38 declarations, 0
  HEADER/BODY differences and 2 PROSE (the two insertions, `statements/docstring-insertion-check.txt`). The control
  (one header character of `getD_one_eq'` changed) gives exactly one more difference, a HEADER one. `touched.tsv` has
  exactly the two lemmas CHANGED.
- **Integration build** (`build/`): 270/270 rc 0, 0 errors in both forms (G26-N1), substring "error" 0, 1513 s. The
  270 modules are the downstream of the 76 modules changed since `eff2dcd0`, the olean snapshot's base (69 of the base
  delta #303–#317 and the 7 unit modules). They include both `audits/*/Checks` and root `TCSlib`. The 7 unit modules,
  `YaoReal`, `SecureComputation` and `TCSlib` have 0 warnings. This is **#318's integration build against #314–#317**.
  Whole-tree check (1255 modules): every module rc 0 at the head source with olean = record. Every built source
  equals its blob at `b0bad23a` (`checks/srcequality.txt`).
- **Axioms:** `otProtocol_polyTime`, `otProtocol_simulators` and `otProtocol_hbcSecure` use
  `[propext, Classical.choice, Quot.sound]`; `getD_zero_eq` and `getD_one_eq'` use `[propext]`. `yaoProtocol_hbcSecure`
  keeps `sorryAx` (Yao, from the base). The census has 234 stored constants (= round 1), and the axiom union is
  standard.
- **Rule 10:** the seals (`seals/{A,B}`, `seals-coe/{A,B}`; 1109–1111 requests) were all run with `-DmaxErrors=0`
  (`tools/probefull.sh`, new `tools/runfull.py`). All 4 pass: rc 0, 0 errors, install and EOF records present. Paired
  controls (rows `PolyExpr.eval`, the `FinDist` CoeFun, `NUPPT.layout`, `Strategy.encodeMsgs`, `otFunctionality`,
  `OT.mask`): `controls/` 4 probes and 9 sealed negatives, `controls-strict/` 4 and 11. `logs/ctlcheck.log` is
  ALL_OK. In strict, every negative fails exactly once, and `ctlCoeReader` fails in the 2 strict sealed probes (the
  known harness effect, round-1 F-09).
- **Admissions:** 216 at the tip `05d26fe5` → 214 at the head, exactly the two targets (`ObliviousTransfer` 2 → 0).
- **Lint:** Cryptography 92 FAIL / 101 WARN and Complexity 25 / 391, the same at the head and at `05d26fe5`, with
  identical line sets.
- **Restore:** the olean tree was restored to `457ba704…`, and the tree check is OK.

### 2. G34-02: is the disposition recorded?

Seyoon ruled "ledger 02": `OT.length_ofFn_coins` (`OT/Simulators.lean:210–212`) stays as **DL-48 debt**. It is a
verbatim copy of the public `Composability.NMSim.length_ofFn_coins`
(`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); reusing that directly would bring 69
non-malleability modules into the OT closure (78 → 147). Re-checked (`checks/dl48.txt`):
- The DL-48 row of `duplication-ledger.md` at the tip (in `verification-r2.zip`, last changed in `540bac18`) has the
  entry **"Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger)"**, which names both declarations with their lines.
- It has the cleanup line: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or
  `Randomized/NonUniform`) and re-point both copies.
- It also has the note that G34-01 is fixed, not debt.
- `OT/Simulators.lean` is byte-identical at `f62a25b3` and `b0bad23a`. Both copies are where round 1 found them, with
  identical headers, and `Rounds.lean` is not in the unit's closure.

Is the record accurate and complete enough to discharge G34-02 as disclosed debt?

### 3. The rebase: is the PR the round-1 PR plus LE-gate34?

- **Range-diff** (`checks/rebase.txt`): `git range-diff a334ec2e..f62a25b3 05d26fe5..e0ecdf22` is 5/5 `=` (the 3
  worker commits, LE-doc, LE-reuse). The 7 unit files are byte-identical at `f62a25b3` and `e0ecdf22`, so
  `git diff f62a25b3 b0bad23a` on the unit files is exactly LE-gate34. All 6 commits from `05d26fe5` are authored and
  committed by Claude and carry one `gpgsig` each.
- **Headers since round 1** (`checks/lecheck.txt`): all 193 declarations of the 7 files (55, 15, 38, 44, 5, 14, 22)
  have byte-identical headers at `f62a25b3` and `b0bad23a`, in order. Every definition block is identical, and only
  the two docstrings of § 1 change. decls2 from `f62a25b3` to the head is empty (193 unchanged). Against the new base
  it is 141 ADDED, 0 CHANGED, 0 REMOVED, as in round 1.
- **The base delta** (`checks/basemove.txt`). From `a334ec2e` to `05d26fe5` two PRs merged: **#316** (headD
  promotion, `1c09448c`) and **#317** (prf-mac, `1d9b2ac3`). Both were already in round 1's records tip `5d719839`
  and in its merge-tree checks; round 1's pack listed them as merged after the base. #314 and #315 were already in
  round 1's base `a334ec2e`.
  - The `.lean` delta is 8 files. Only `Foundations/BitLists` (#316) is in the unit's closure.
  - The closure is unchanged: 128 modules, the same set as at round 1.
  - § 1's build covers every module changed since `eff2dcd0`, so it covers #314–#317.
- **`sources-r2.zip`** (128 files) has the same paths as round 1's `sources.zip`. It differs in two entries,
  `Foundations/BitLists.lean` (#316) and `OT/Efficiency.lean`.
- **`source-head-r2.json`** differs from `source-head.json` only in `OT/Efficiency.lean` (545 → 548 lines, SHA-256
  `fb134dc1…`, none over 100 characters).
- **`pr.diff-r2.txt`** is `git diff origin/cryptography/pass-shelat-ch2-4...b0bad23a`, which equals
  `05d26fe5..b0bad23a` byte for byte (7 paths, 2259 insertions, 40 deletions).

Does the rebase, or the base delta, introduce anything that round 1 would have raised?

### 4. Duplication: is there any new undisclosed copy since round 1?

- **Since round 1** (`checks/dupscan.txt` A): the only lines changed in the unit files from `f62a25b3` to the head
  are LE-gate34's. No declaration is added or removed: the 193 names are those of round 1. LE-gate34 removes two
  case-split proofs and adds two calls of `headD_drop`.
- **Reading-lemma lines** (B): the headD/getD-class and coin-length lines added since the base are those of round 1
  plus the two `headD_drop` calls. The `List.headD_cons` rewrites are uses of the Mathlib lemma, and the
  `length_ofFn_coins` uses are the G34-02 copy (§ 2).
- **Newly merged public lemmas** (C): a statement scan was run, comparing binders and type after whitespace
  normalisation. Each of the 107 theorems new at the head was compared against every theorem in the files the tip
  changed since round 1's base (13 files: #316, #317 and #313's 5 Learning files) and in each other open PR (#319,
  #323, #324, #326, #327). It found 0 identical statements. No new name of #318 is declared in a file any of them
  changed (`checks/namecheck.txt`). This scan is a mechanical aid; the round-1 search list stands.
- **The pre-existing copies.** DL-47 lists the pre-existing headD/getD copies; none is in a #318 file. **They are not
  findings.** DL-48's other items (F-02, F-04, F-07) are unchanged.
- **Any further undisclosed duplicate of a public lemma is a major**, as in round 1.

### 5. The merge interaction

`git merge-tree --write-tree b0bad23a <x>` is clean for each (`checks/mergetrees.txt`). No path is shared with any
of them. #326 and #327 are taken at their origin heads at the time of the check.

| `<x>` | head | merged tree | downstream of both (`checks/downstream.txt`) |
|---|---|---|---|
| the tip | `b0ebd475` | `bd129bfa` | root `TCSlib` (the tip's delta is #313's 5 Learning modules) |
| #319 (canonizer) | `47daa907` | `705cab61` | root `TCSlib` |
| #323 (sc-garble) | `8c3f3e3f` | `8cdcecbd` | 6: `ObliviousTransfer`, `OT/Predictor`, `OT/ViewB`, `SecureComputation`, `YaoReal`, root `TCSlib` |
| #324 (sc-compose) | `a6eaebd7` | `0106b2fb` | 3: `SecureComputation`, `YaoReal`, root `TCSlib` |
| #326 (derand) | `941b5a1e` | `a69cfdb8` | 10: the 7 unit modules, `SecureComputation`, `YaoReal`, root `TCSlib` |
| #327 (seq-zk) | `e9b5ea47` | `89568060` | root `TCSlib` |

- **#323** changes `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` (the approved reader `isFaninTwo_iff`),
  which is in the closure of `ObliviousTransfer`, `OT/Predictor` and `OT/ViewB`.
- **#326** changes `TCSlib/Complexity/ClassP/DTIME.lean` and `TCSlib/Complexity/Randomized/Build/IterateFind.lean`,
  which are in the closure of every unit module.
- No other open PR, and not the tip's delta, changes a module of the unit's closure.
- **Source equality** (`checks/srcequality.txt`), of the 270 built modules:
  - all have the head's source;
  - 269 have the tip-merged source and #319's, #324's merged source;
  - 268 have #326's and #327's;
  - 266 have #323's.
- **Already built:** the combined #318 + #319 tree `705cab61` (the same tree as here) was built 73/73 rc 0
  (`gates/35-canonizer/integration/`, evidence `830395f8`; on `05d26fe5`, before #313).
- **Pending merge condition (not an audit item).** No other combined tree with this head is built. A combined
  integration build of all open PRs is running concurrently and is **pending**. Whichever of #318 and the tip (#313),
  #323, #324, #326 or #327 merges second needs an integration rebuild of the shared downstream on the merged tip
  before it merges; the maintainer runs that build. Treat it as a condition on the merge, not as something for this
  audit to establish. What you can raise: a concrete reason a merged tree cannot build, or a name or instance
  interaction.

## Known dispositions and slips (not findings)

- **"push: NOT performed" in `landing-r1/PROVENANCE.txt`** (and `landing/push.log` in the ZIP): this was written when
  the job's own push was refused. The maintainer then force-pushed `b0bad23a` with lease, with Seyoon's approval; the
  remote head is that commit.
- **Round 1's line numbers.** `getD_zero_eq` and `getD_one_eq'` are now at `OT/Efficiency.lean:199,206` (were
  198, 203). `headD_drop` is at `Foundations/BitLists.lean:52`; round 1 cited 50–51 at the old `BitLists` blob, which
  #316 changed.
- **The integration build ran before #313 merged.** It is on `05d26fe5`. The tip's only Lean delta since then is
  #313's Learning unit, which shares only root `TCSlib` with #318 (§ 5).
- **The PR description is still round 1's.** It does not list the rebase or LE-gate34; the maintainer updates it
  before #318 is marked ready (it is not in this pack).
- **Job-local names.** `landing-r1/PROVENANCE.txt` refers to `../gate34-le-evidence.zip` and to `$SP` paths; the
  records copies have the same bytes.

## Evidence files

- **`resolutions-r1.md`:** the dispositions of G34-01 and G34-02.
- **`findings/`:** the round-1 findings.
- **`landing-r1/`:** `PROVENANCE.txt` (= the ZIP's), `gate34-le-evidence.zip` and its manifest. The LE-gate34 patch is
  the ZIP's `landing/le-gate34.diff`; the rebase log is `landing/rebase-r4.log`.
- **`verification-r2.zip`** (23 entries; `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source):
  - byte-identical originals at records `b0ebd475eb0b4131449bce58462f168f27eee17b` of the decision log, the
    duplication ledger (DL-47, DL-48) and the round-1 sc-ot review;
  - `checks/`, generated from git objects alone: merge trees, downstream, source equality, names, the rebase, the
    edit, the base move, DL-48, the duplication scan and decls2, with their scripts.
- **`pr.diff-r2.txt`:** `git diff` from the base to `b0bad23a`, 7 paths, 2259/40.
- **`source-head-r2.json`:** hashes, line counts and over-width counts of the 7 changed files at `b0bad23a`.
- **`sources-r2.zip`:** the source closure at `b0bad23a` of every changed module, 128 files.
- **Round 1:** `outbox/gates/34-sc-ot-gate/` on the exchange at `a74d11833a0814bb686a4b961c5712957008d6a9`, with
  records `5d719839503c1f29f65f5ffa200410349a782276`; `pack.md` here is its pack.

## Findings delivery

Return `gate34-sc-ot-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.
Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report the audited
head and the counts by severity. The gate closes at zero blockers and zero majors.
