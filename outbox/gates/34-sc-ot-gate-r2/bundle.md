## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/pack-r2.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/resolutions-r1.md =====

# Gate 34 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 0 minors, 0 notes.
- **Findings:** `findings/gate34-sc-ot-findings.md`, SHA-256 `9ab967ee0fcf23c393ccefaeb57ad0ff6e397e09553ce492d03a2d9485cbc8e6`. Codex's evidence ZIP was not supplied.
- **Audited head:** `f62a25b3eda099c9cf9371900664752e7b89007d`, records `5d719839`, exchange `a74d1183`.

Codex found no mathematical defect. It checked:
- the efficiency bound;
- Alice's `2δ(n)` at every `n`;
- Bob's predictor identities and the 16 summed instances;
- the freeze (141/0/0);
- the Rule-10 controls, including F-09;
- the builds and the axioms.

| # | Severity | Disposition (ruling Seyoon, 2026-11-15: "fix 01, ledger 02") |
|---|---|---|
| G34-01 | major | **To be fixed by LE-gate34, proof only.** `OT.getD_zero_eq` and `OT.getD_one_eq'` (`ObliviousTransfer/Efficiency.lean:198,203`) will be re-derived from the public `TCSlib.Cryptography.headD_drop`. It is already in the closure, so no import is needed. The headers are kept, and the overlap records are corrected. |
| G34-02 | major | **Ledger debt, DL-48.** `OT.length_ofFn_coins` (`Simulators.lean:210–212`) is a verbatim copy of the public `Composability.NMSim.length_ofFn_coins` (`NonMalleability/Simulation/Rounds.lean:41–43`). Reusing it directly would bring 69 non-malleability modules into the OT closure (78 → 147). The cleanup will promote it to the `NUPPT` layer and re-point both copies. |

**Next:** LE-gate34 runs together with #318's integration rebuild against #316/#317. Then **Gate 34 round 2** checks G34-01's
fix and the disclosure.

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/findings/gate34-sc-ot-findings.md =====

# Pass–shelat Gate 34 — sc-ot findings

**Verdict: HOLD.** Severity counts: **0 blockers, 2 majors, 0 minors, 0 notes**.

The proof audit found no mathematical defect in the two targets. The hold is for two further public-lemma duplications whose actual public relatives are absent from the disclosures and DL-48.

| Pin | Audited revision |
|---|---|
| Repository / PR | `Shilun-Allan-Li/tcslib`, draft [#318](https://github.com/Shilun-Allan-Li/tcslib/pull/318) |
| Lean head | `f62a25b3eda099c9cf9371900664752e7b89007d` |
| PR base | `a334ec2e1d87dbde7eac40812286ba60e85c9078` |
| Campaign records | `5d719839503c1f29f65f5ffa200410349a782276` |
| Exchange | `a74d11833a0814bb686a4b961c5712957008d6a9` |
| Audit date | 2026-11-15 |

## Findings

Paths in the first column are relative to `TCSlib/Cryptography/`.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G34-01 | **major** | `SecureComputation/ObliviousTransfer/Efficiency.lean:198,203` · `OT.getD_zero_eq`, `OT.getD_one_eq'` | Both re-prove specializations of the already imported public `TCSlib.Cryptography.headD_drop`; this public overlap is undisclosed. | `Foundations/BitLists.lean:50–51`; worker report §3; review duplication search item 8; independent import-closure check. | Preserve the headers and derive both proofs from `headD_drop`, then correct the overlap records. No new import is needed. |
| G34-02 | **major** | `SecureComputation/ObliviousTransfer/Simulators.lean:210–212` · `OT.length_ofFn_coins` | This repeats the existing public `Composability.NMSim.length_ofFn_coins`, including its statement and proof. That overlap is undisclosed. | `Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`; exact declaration-code comparison; worker report §3. | Preserve the header and use the existing public theorem with an explicit import, or obtain an explicit disposition for a shared promotion. Correct the overlap records. |

### G34-01: the missing public relative is `headD_drop`

The existing public theorem is

```lean
theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) :
    (l.drop i).headD d = l.getD i d
```

Consequently, the two new statements follow directly from its symmetric instances at `i = 0, 1`. Proposed replacement proof bodies are:

```lean
-- getD_zero_eq
by
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.headD_drop y 0 false).symm

-- getD_one_eq'
(TCSlib.Cryptography.headD_drop y 1 false).symm
```

The delivered proofs instead split the list into cases and finish by reflexivity. `BitLists` is already in `Efficiency`'s transitive import closure, through `Shape`, `Defs`, and `Asymptotic/Adversary`. The public theorem is unchanged since the issue base.

The worker lists these two new names, but identifies only `List.getD_cons_zero` and `List.getD_cons_succ`, explaining that those cover cons lists only. The exact general public relative above is missing. The maintainer's duplication review item 8 likewise misses it. DL-48's F-07 concerns **`OT.getD_one_eq` without the apostrophe**, the encoded-history reader; it does not cover these two list readers. This is therefore outside that disposition and is major under the gate's binding duplication rule.

### G34-02: an identical generic coin-length theorem already exists

Both declarations contain exactly this code, under different namespaces:

```lean
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]
```

The existing namespace is `TCSlib.Cryptography.Composability.NMSim`; the new one is `TCSlib.Cryptography.SecureComputation.OT`. The existing declaration is public and unchanged since the issue base. The independent comparison confirms identical declaration code.

The worker's overlap table groups `OT.length_ofFn_coins` with coin equivalences and cites `Collection.owfCoinsEquiv` / `NUPPT.coinsEquivPoly`, with “specific layouts” as the explanation. This theorem is generic over every `NUPPT`; that row does not disclose its identical public predecessor. DL-48 does not name this overlap. The dependency check finds no import path from `NonMalleability/Simulation/Rounds` back to the OT simulator helper, so importing the existing theorem has no source-level cycle.

The replacement snippets and import proposal above are recommendations; they were not locally compiled or applied.

## Verification and proof assessment

**Integrity and scope.** Independently verified all **18/18** top-level `SHA256SUMS` entries, **112/112** entries inside `verification.zip`, and **810/810** entries inside `review-evidence.zip`. The archives contain exactly their manifests plus `SHA256SUMS`, with no duplicate or extra entries. Every top-level pack file matches the pinned exchange Git object. All **128/128** source-closure files match the pinned Lean head, and the archive equals the independently computed import closure. The seven-file diff matches `pr.diff.txt` byte-for-byte with nine-digit Git index abbreviations. Every changed file lies in the permitted scope.

The 14 supplied records match their declared `1321b9cb` provenance. At the requested campaign pin, 13 remain identical; the plan only appends the Gate 34 registration row. That causes no substantive discrepancy.

**Frozen statements and landing edits.** Independent source comparison confirms **141 added, 0 changed, 0 removed** statement headers: all 52 pre-existing declarations retain their headers and order; every pre-existing definition and every non-target proof retains its code. Only the two target docstrings change, with their statement prose preserved. `EnhancedHardCore` and its docstring are unchanged under G3-8. The supplied frozen checker reports zero differences, with exactly one difference in each of its five controls. LE-doc changes exactly 50 docstrings and no other text; LE-reuse changes only the permitted proof and provenance parenthesis in `Efficiency.lean`.

**Efficiency.** The raw-machine equalities cover empty, singleton, two-message, and longer histories, including empty messages. Polynomial-time composition uses published machine and encoding readers. The message-length argument bounds the index by `Q₁`, samples by `Q₂`, evaluations by `Q₃`, Bob's pair by `3(Q₂ + Q₃) + 2`, and Alice's mask pair by 5. Thus the stated `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` covers the five-message transcript and both empty fillers.

**Alice.** At every generated index, the proof chains statistical closeness bounds

\[
\operatorname{eval}(\operatorname{Sample})
\;\xrightarrow{\delta(n)}\;
\operatorname{encD}(\operatorname{perm}(U))
\;\xrightarrow{0}\;
\operatorname{encD}(U)
\;\xrightarrow{\delta(n)}\;
\operatorname{Sample}.
\]

Here the first step uses `SampleClose`, the middle step uses the permutation bijection, and the last uses canonical decoding. The shared-index product lemma averages a bound valid for each index; the second sample and the branch-dependent coin swap preserve it. Mapping to the full view and applying `distAdv_le_of_statClose` gives **`2δ(n)` for every `n`**, with no eventual threshold.

**Bob.** The masks are correctly read through `inv_runAtL_ones`, `inv_eq_encD`, canonical decoding, and `henc`. `viewDist` retains the challenge's sampler coins inside Bob's tape and retains `D`'s advice. With the pack's acceptance quantities `U₊, U₋`, the verified identities are

\[
P_{\rm real}=U_+,\qquad
P_{\rm ideal}=\frac{U_++U_-}{2},\qquad
\Pr[\mathrm{predict}_{\rm false/true}=B]
=\frac12\pm\frac{U_+-U_-}{2}.
\]

The two hard-core bounds therefore give

\[
\frac{U_+-U_-}{2}\le\varepsilon_{t,0}(n),\quad
-\frac{U_+-U_-}{2}\le\varepsilon_{t,1}(n),\quad
\operatorname{distAdv}_B
=\frac{|U_+-U_-|}{2}
\le |\varepsilon_{t,0}(n)|+|\varepsilon_{t,1}(n)|.
\]

All eight input triples and both signs are instantiated: **16 fixed machines**, whose absolute negligible bounds are summed. This supplies one input-uniform negligible `ε_B`, and the final `2|δ| + ε_B` bounds both sides. The reduction does not require a predictor to know the generated trapdoor. The protocol and Alice simulator agree with [PS10, Protocol 160.4 and Proposition 161.5, pp. 161–162](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf); the source leaves Bob's simulator as an exercise. The declared enhanced hypothesis is preserved as ruled.

**Rule 10 and controls.** All 32 supplied base/head seal probes across strict/coe and A/B have verified probe hashes. Removing their recorded insertions reconstructs the corresponding audited source bytes exactly. The 121 imported non-unit sources are unchanged from the r1 base to the audited head, supporting transfer of the r1 probes. Canonical coe-A passes all seven modules. The canonical controls have 20 probes and 61 sealed negatives, all correct. Strict controls have 71 sealed negatives, each failing once; their only ten discrepancies are `ctlCoeReader`. The raw diagnostic confirms the stated mismatch between a projected `.prob` reader and the sealed `CoeFun.coe` statement. The strict `ctlCoe` negative does fail once. F-09's attribution is correct. The supplied explicit-read scan records 742 items and zero foreign-definition reads.

**Builds, axioms, and documentation.** Verified all 139 reported build-source hashes against the head and all 139 raw log hashes; every return code is zero and neither error form occurs. The 234 census rows have only `propext`, `Classical.choice`, and `Quot.sound`; this includes both targets and `otProtocol_hbcSecure`. The supplied whole-tree result is OK for 1250 modules. New formulas, readers, sketches, sizes, and widths show no further defect; the seven Prop-formula docstrings are acceptable, and `receiverNext_eq`'s long header with an `rfl` proof is a sketch-checker artifact.

This was an independent source and supplied-evidence audit. Lean was not rerun locally. The pending merged-tip integration rebuild remains the maintainer's merge condition, as instructed, and is not a finding.

## Closure requirement

Resolve **G34-01 and G34-02** by reuse, or obtain an explicit user disposition covering these additional overlaps. Then refresh the affected source, disclosure, build, axiom, and seal evidence. Existing DL-48 dispositions remain respected.

## Notation

`n` is the security parameter; `U` is a uniform domain element; `δ(n)` is the sampler's statistical-closeness bound; `D` is the distinguisher. `B` in the predictor identities is the enhanced bit; `P_real, P_ideal` denote real and ideal acceptance probabilities, and `U₊, U₋` denote acceptance with that bit and its complement. `t = (b,a₀,a₁)` comprises Bob's choice bit and Alice's two input bits; `ε_{t,0}, ε_{t,1}` are the two negligible prediction bounds, and `ε_B` is their sum of absolute values over all triples. In the efficiency paragraph, `Q₁, Q₂, Q₃` bound the index, sample, and evaluation lengths, and `B` instead denotes the message-length polynomial, following the pack.

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/landing-r1/PROVENANCE.txt =====

LE-gate34 and the #318 (sc-ot) integration build, maintainer job, 2026-11-15 UTC (coordinator's job A, run between the derand and
seq-zk reviews on $SP/dl-oleans-2).
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I; one Lean process at a time, only on $SP/dl-oleans-2; no lake build, no cache get; records checkout only read.
Ruling: Gate 34 HOLD on #318 (records briefs/pass-shelat-ch5-8/gates/34-sc-ot/, resolutions-r1.md; decision log 2026-11-15):
  "fix 01, ledger 02". G34-01 fixed here; G34-02 -> DL-48 (landing-gate34/NOTE.txt).

rebase (landing/rebase-r4.log): land/pass-shelat-sc-ot f62a25b3eda099c9cf9371900664752e7b89007d (= origin, on a334ec2e) onto origin
  cryptography/pass-shelat-ch2-4 05d26fe5b41fcb9426ec220d877d03264b9c8e8c (#316 headD_drop_ofFn/BitLists and #317 merged since
  a334ec2e; records only after them): rc 0, range-diff 5/5 '=', the 7 unit files unchanged; head e0ecdf223490ad9c99fc9151ca5bef5821e6cf29.
LE-gate34 (tools/legate34.py; landing/le-gate34.diff, le-gate34-commit.txt, commit-msg-le-gate34.txt):
  ObliviousTransfer/Efficiency.lean: OT.getD_zero_eq := by simpa only [List.drop_zero] using
  (TCSlib.Cryptography.headD_drop y 0 false).symm; OT.getD_one_eq' := (TCSlib.Cryptography.headD_drop y 1 false).symm.
  No import added (BitLists is in Efficiency's closure). Each docstring gains "It is the public `TCSlib.Cryptography.headD_drop`
  at `i = k`, reversed." (statements/docstring-insertion-check.txt: pure insertions).
  Commit b0bad23ae611983e3323460bb8c564da90ad6e8c (author = committer = Claude, SSH-signed by the environment default, the two
  trailers), tree 3b4301cf650324a3b6d5a59f2c3b60fb6f963dfd. landing/commits.txt (6 commits, all gpgsig), series landing/series/,
  landing/changed-paths-vs-origin.txt (7 files, +2259/-40).
verify:
  - statements/decls2-vs-parent.tsv (vs e0ecdf22): empty. statements/frozen-check.txt: 38 -> 38 declarations, 0 HEADER/BODY
    differences, 2 PROSE (the two insertions); control statements/control-header-getD_one_eq.txt (one header character changed):
    exactly one more difference (HEADER). touched.tsv: exactly the two lemmas CHANGED.
  - build (build/, tools/runner.py, G26-N1): order/ = tools/downorder.py at b0bad23a vs eff2dcd0 (the olean snapshot's base):
    76 changed since eff2dcd0 (69 base delta #303-#317 + the 7 unit modules), down.txt 270; order/A/ (tools/buildset.py; seeds the 7,
    both audits/*/Checks, root TCSlib): build set 270 = down.txt; build-queue.txt imports-first. 270/270 rc 0, 0 errors in both forms,
    error substring 0, 1513 s (logs/build-summary.txt). The 7 unit modules, YaoReal, SecureComputation, TCSlib: 0 warnings;
    audits/pass-shelat/Checks and audits/garg-ch1-3/Checks rc 0. This is #318's integration build against #314-#317.
  - logs/tree-check-head.txt (tools/treecheck.py, order/order.txt 1255 modules, logs/records-head.jsonl = base records + build):
    every module rc 0 at the head source with olean = record; strays only the 2 probe oleans.
  - axioms (probe-sources/CensusHead.lean, tools/mkcensus_scot.py; probe-runs/): otProtocol_polyTime, otProtocol_simulators,
    otProtocol_hbcSecure: [propext, Classical.choice, Quot.sound]; yaoProtocol_hbcSecure keeps sorryAx (Yao, base). logs/census-
    summary.txt: 234 stored constants (= sc-ot r1), axiom union standard, no sorryAx; getD_zero_eq / getD_one_eq': [propext].
  - seals (probe-sources/CollectHead.lean -> probe-runs/; tools/mkseals_ab.py -> seals/{A,B}, tools/mkseals_coe.py -> seals-coe/{A,B};
    1109-1111 requests): run with tools/runfull.py (new; tools/probefull.sh = lean -DmaxErrors=0, no -o) -> seal-runs/: all 4 rc 0,
    0 errors, install and EOF records present.
  - controls (tools/mkctl_scot.py on the Efficiency records; rows PolyExpr.eval, FinDist CoeFun, NUPPT.layout, Strategy.encodeMsgs,
    otFunctionality, OT.mask) -> controls/ (4 probes, 9 sealed negatives), controls-strict/ (4, 11), runfull -> control-runs/:
    logs/ctlcheck.log ALL_OK True; strict: every negative fails exactly once; ctlCoeReader fails in the 2 strict sealed probes
    (the known harness effect, sc-ot r1 F-09).
  - admissions (logs/admissions.txt): full-order sorry warnings at the head 214 = tip 216 - 2 (exactly the two targets;
    ObliviousTransfer 2 -> 0).
  - lint (lint/): Cryptography 92/101 and Complexity 25/391 at the head and at the tip 05d26fe5; line sets identical (linediff-*.txt empty).
push: NOT performed. `git push --force-with-lease=land/pass-shelat-sc-ot:f62a25b3... origin land/pass-shelat-sc-ot` was denied by
  the session's permission system (landing/push.log). Local branch land/pass-shelat-sc-ot = b0bad23a; origin still f62a25b3.
tree: shared with int-319 (one backup set for A, B and the combined build): tree/backed-up.txt (270), tree/new-oleans.txt (57);
  restore after int-319 (tree/restore-log-shared-with-int-319.txt: 270 restored, 0 hash failures, 57 deleted, 3 probe oleans
  deleted, SNAPSHOT EQUAL 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f; tree/tree-check-post.txt RESULT OK).
tools/: the derand-r1 tools plus legate34.py and runfull.py (new).
SHA256SUMS: every file here except itself; ../gate34-le-evidence.zip holds exactly the manifest's paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/34-sc-ot/pack.md =====

# Gate 34 · Oblivious transfer from trapdoor permutations (`sc-ot`, Protocol 160.4 and Proposition 161.5)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #318](https://github.com/Shilun-Allan-Li/tcslib/pull/318) at
  `f62a25b3eda099c9cf9371900664752e7b89007d` (branch `land/pass-shelat-sc-ot`, tree
  `163be55abcd012eac6595af41807ce5cc57ef8f3`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `a334ec2e1d87dbde7eac40812286ba60e85c9078` (the merge base: the records tip after #315 merged).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. The owned file's blob is the same at the issue
    base and at `a334ec2e` (`pack-checks/headers.txt`). Between them #307, #311, #312, #314 and #315 merged; the
    review's builds cover them (`build-r3`: the downstream of every module changed since `eff2dcd0`).
  - The records tip is now `1321b9cb358867f5b51974b8c5d0781519a9cfdb`. Since `a334ec2e` it has merged **#317**
    (prf-mac, `1d9b2ac3`) and **#316** (headD promotion, `1c09448c`). Their 8 Lean files are not in the PR, and the
    PR is **not** rebased onto them (below, *Pending merge condition*).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...f62a25b3`, which equals `a334ec2e..f62a25b3`
    byte for byte (7 paths, 2256 insertions, 40 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #313 (`94b31964`), #316
    (`c18afbe6`), #317 (`590d1a56`) and #319 (`6421ac16`, canonizer) is clean in each case, and no path is shared
    (`pack-checks/mergetrees.txt`). Every unit module is downstream of #316's `Foundations/BitLists` (now on the tip).
    **Pending merge condition** (not an audit item): #318 needs an integration rebuild on the merged tip before it
    merges, and whichever of #318 and #319 merges second needs one too; the maintainer runs these builds (question 7).
- **Commits:** 5, all authored and committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Claude worker's 3 commits (job `sc-ot`), applied with `git am` with the delivered committer data. The three
    worker hashes `fc7d0366`, `a643e566`, `e2c6f1a8` reproduce only with the environment's signing on (review F-05).
    They were then rebased three times without conflict, author kept: `8d4290678ef1b27df17fd9dde7bc4518fd1dfc22`
    (checkpoint 1: `otProtocol_polyTime`), `53969e06170b57b8815e25194a07220e11869946` (checkpoint 2: Alice's side)
    and `b2e817cae4737dbcbeaf4171c9598b3e2b21fd57` (final: Bob's side). At `b2e817ca` the 7 files are
    byte-identical to the worker's `src/` (exchange `a8972fa0`; `pack-checks/rebase.txt`).
  - Landing edit **LE-doc** `7a1fa29bae093192e21344fb9110d8a087d0a123`: 50 formula docstrings, docstrings only.
  - Landing edit **LE-reuse** `f62a25b3eda099c9cf9371900664752e7b89007d` (the head): review finding F-01, proof
    only.
- **Scope:** a **proof audit**. The job proves the admitted `SecureComputation.otProtocol_polyTime` [PS10, Protocol
  160.4; Definition 155.1's efficiency requirement] and `SecureComputation.otProtocol_simulators` [PS10, Proposition
  161.5 with the explicit simulators `S_A`, `S_B`]. Both statements are frozen (prong B, ruling G3-8 applied in
  `587843c7`, Gate 06B PASS) and quoted in the brief. Their consumer `otProtocol_hbcSecure` (unchanged) now uses only
  the standard axioms.
- **Brief:** `fills/sc-ot/issued-r1/brief.md` on the records branch (SHA-256 `b4b5c73a…`). Three checkpoints
  (`otProtocol_polyTime`; Alice's side; Bob's side). The owned file plus the helper directory
  `SecureComputation/ObliviousTransfer/` only; every other file frozen. The binding duplication rule with an
  `## Overlap and reuse` section, and the expected adapted copy of `exists_pkPredictor`. Rule 10 with the
  projection-coercion ruling, and seals with `PolyExpr.eval` both excluded and sealed. The formula-docstring and
  sketch rules, the G26-N1 error count and the evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/`; `OT/` is `ObliviousTransfer/`. The PR touches 7 Lean files:
1 modified and 6 new (2256 insertions, 40 deletions). Line counts are base → worker head `b2e817ca` → LE-doc
`7a1fa29b` → PR head.

| File | Status | Lines |
|---|---|---:|
| `ObliviousTransfer.lean` | owned, modified | 671 → 747 → 748 → 748 |
| `OT/Shape.lean` | helper, new | 206 → 216 → 216 |
| `OT/Efficiency.lean` | helper, new | 526 → 545 → 545 |
| `OT/Simulators.lean` | helper, new | 431 → 435 → 435 |
| `OT/ViewA.lean` | helper, new | 186 → 186 → 186 |
| `OT/Predictor.lean` | helper, new | 206 → 212 → 212 |
| `OT/ViewB.lean` | helper, new | 534 → 545 → 545 |

The owned file imports the six helpers directly, so after #305 no facade edit is needed, and none was made.

**The design.** The helpers cannot import the owned file (it imports them). So they state every result for every
protocol and every pair of machines of the *shapes* of Protocol 160.4 and of `S_A`, `S_B`. The shapes are the
predicates `OT.IsOT`, `OT.IsSimA` and `OT.IsSimB`, which restate the owned definitions' bodies (review F-06, by design).
The owned file proves that `otProtocol`, `otSimA` and `otSimB` have these shapes, from its own published readers
(`otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB`). Then:

```lean
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) :=
  OT.polyTime_of_isOT T hH (otProtocol_isOT T H)

theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) : … :=
  OT.simulators_of_isOT T H hH henc (otProtocol_isOT T H) (otProtocol_outV T H henc)
    (otProtocol_outP T H) (otSimA_isSimA T) (otSimB_isSimB T hH) hT
    ((enhancedHardCore_iff T h).1 hEHC)
```

The proof follows [PS10, Protocol 160.4, Proposition 161.5] and the frozen sketches. The targets' step lists were
rewritten to describe the delivered proof; the statement prose is unchanged. See REPORT § 2 and the review's
*Content* line.
1. **Shape** (`Shape`). `OT.IsOT T H π`: the next-message functions are `OT.senderNext` and `OT.receiverNext`. Alice
   uses `Gen`'s coins and Bob two sampler blocks. There are five messages, Alice first. `OT.exec_five` gives the five
   moves, and `OT.transcriptWith_isOT` the transcript `([y, []], [i, z, []])` with its two empty fillers.
2. **`otProtocol_polyTime`** (`Efficiency`; checkpoint 1). The raw functions `OT.senderRaw` and `OT.receiverRaw` read
   the case off the encoded history by emptiness tests. `NUPPT.ofPolyTimeUniform` of them computes the next-message
   functions (`senderRaw_advInput`, `receiverRaw_advInput`). The messages are bounded by
   `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` (`OT.exists_messages_le`): the index by `Gen`'s `runLenPoly` `Q₁`, the pair by two
   sampler outputs (`Q₂`) or evaluations (`Q₃`), and one bit per mask.
3. **Alice's side** (`Simulators`, `ViewA`; checkpoint 2). On the coins `(r, s₁, s₂)` (`OT.realCoins`,
   `OT.simACoins`), the real view carries `⟨f_i(w₁), w₂⟩` (swapped when `b`), and `S_A`'s carries `⟨w₁, w₂⟩`.
   `OT.statClose_eval_sample` shows that at every generated index `eval ⟨i, Sample⟩` is `2δ(n)`-close to `Sample`
   under `SampleClose δ`. `OT.statClose_prod_of_forall` lifts this to the joint samplers.
   `OT.distAdv_realA_idealA_le`: Alice's side is at most **`2δ(n)` at every `n`**, for every distinguisher and all
   inputs.
4. **Bob's side** (`Predictor`, `ViewB`; final). `OT.bobView` is Bob's view with the unselected mask
   `[β ⊕ a_{1−b}]`. The real view has `β = B s₂`, the enhanced bit `OT.hcBit = h_i(perm_i⁻¹(dec_i(Sample(i; s₂))))`;
   the ideal view has a fresh coin. So the advantage is `|U₊ − U₋| / 2` with `U± = E_r accB r (±B)`
   (`acceptProb_realB`, `acceptProb_idealB`, `uprob_xor_shear`).
   - The machine `OT.viewDist D b a₀ a₁` (`NUPPT.ofPolyTime` of `OT.viewDistRaw`, with `D`'s advice) reads
     `⟨i, ⟨s', [β]⟩⟩`. It builds Bob's view around the challenge, with Bob's tape containing `s'`, and runs `D`.
   - The published **`tdpPredictor (viewDist …) fl`** of Algorithm 104.3 is the predictor. Through `uprob_tdpPredictor`
     and the **signed-predictor identity** `OT.uprob_signedPredictor_false/_true`, it predicts `B` from `⟨i, s'⟩` with
     probability `1/2 ± (U₊ − U₋)/2` (`uprob_predictor_false/_true`).
   - **`hEHC` is applied to 16 machines**: 8 triples `t = (b, a₀, a₁)` × 2 signs `fl`.
     `ε_B(n) = Σ_t Σ_fl |ε_{t,fl}(n)|` is negligible (`OT.negligible_finset_sum`). For the inputs' bits `t`,
     `distAdv_realB_idealB_le` bounds the advantage by `|ε_{t,0}(n)| + |ε_{t,1}(n)| ≤ ε_B(n)`
     (`OT.exists_negligible_bob`).
5. **Together** (`OT.simulators_of_isOT`): `ε(n) = 2|δ(n)| + ε_B(n)`, with `δ` from `T.OneWay`'s `sampleClose`.
   `EnhancedHardCore` enters only through `enhancedHardCore_iff` (unchanged).

**Route differences from the frozen sketch** (statements unchanged; REPORT § 2.4). The predictor is the published
`tdpPredictor` around an `ofPolyTime` machine, not a new `NUPPT.exists_comp` composite. Each triple is hard-wired in
its own machine and the sixteen bounds are summed, instead of the worst triple as advice; `D`'s advice is kept.

The brief's edge cases: `b = 0, 1` (the branches of `realA_realCoins`, `realB_realCoins`, `idealB_simBCoins`, and the
block swap); all eight `(b, a₀, a₁)` (sixteen machines); the five-message layout and its two empty fillers
(`exec_five`, `transcriptWith_isOT`); non-canonical strings (`apply_of_decD` in `mask_eval`, canonical decoding in
`statClose_eval_sample` and `mask_raw`); the inverter's fixed all-`true` tape (`inv_runAtL_ones`, `OT.maskRaw`);
small `n` (`SampleClose δ` holds at every `n`, so Alice's bound has no threshold); the distinguisher's advice (kept by
`viewDist` and `tdpPredictor`).

**Statements.** decls2 from the issue base to the head gives **141 ADDED, 0 CHANGED, 0 REMOVED** (review
`statements/head-le/decls2-vs-base.tsv`; `decls2-vs-worker.tsv`, empty).
- The frozen check (`frozencheck.py`, at the LE head) compares the owned file's 52 base declarations: kind, name,
  order, header bytes, statement prose and every definition body, `EnhancedHardCore` included (G3-8). It finds **0
  differences** (52 → 55 declarations; `landing/frozen-check.txt`). Each of its 5 one-character controls reports
  exactly one difference (`statements/frozen/control-*`).
- `touched`: 2 CHANGED (the two targets: proofs and sketches only), 50 UNCHANGED, 3 ADDED in the owned file, 138 in the
  new files.
- Re-checked for this pack from git objects with `maintainer/tools/decls2.py`'s parser: 141 ADDED and 52 unchanged
  against both the issue base and `a334ec2e`; 0 rows for `b2e817ca..7a1fa29b` (LE-doc) and for `7a1fa29b..f62a25b3`
  (LE-reuse). The owned file's 52 base headers are byte-identical at the head, in order, with only the two targets'
  docstrings changed. `EnhancedHardCore`'s block and docstring are byte-identical (`pack-checks/headers.txt`).

## Rulings and records in force

1. **DL-48 (Seyoon, 2026-11-15): "ledger debt, disclosed."** It covers three items, deferred to the cleanup:
   - **F-02**: `OT.splitLen` / `splitLen_symm_ofFn` (`OT/Simulators.lean`) restate the public `coinsEquiv`, read
     backwards, and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`). The body is also the private ElGamal
     `dlc_splitEquiv`. Reuse needs a new import and a definition change, so it is not landing-fixable. Cleanup:
     `(coinsEquiv h).symm`.
   - **F-04**: `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor`, because `pkPredictor` has no public
     reader. This is the disclosed, expected copy; a promotion with `pkPredictor_apply` is deferred.
   - **F-07**: undisclosed near-relatives, `GI.pairSndD_encodeMsgs` (for `getD_one_eq`) and `predict_eq`, and the
     promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five` and `length_runAtL_le`.

   **Not a finding:** any item DL-48 lists.
2. **F-01 is fixed by LE-reuse.** `OT.pairSndD_nil'` (`pairSndD [] = []`) restated the public
   `BinArith.iterate_pairSndD_nil` at `1` (`Complexity/ClassP/BinaryArith/Words.lean:158`, already in `Efficiency`'s
   closure). It was not disclosed.
3. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`, the only projection coercion in this closure. The coe-variant seals are canonical; the
   strict variant is run and its differences attributed. **For this unit the seals agree in every row, strict and coe.**
   The strict *controls* differ only in `ctlCoeReader` (F-09, attributed).
4. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A**, which exempts it, is **canonical**; seal B
   is run and reported because the brief asks for both. So **coe-A is the canonical variant**.
5. **The facade-completeness lint fix, #305 (Seyoon's ruling of 2026-11-14).** The baseline is **92 FAIL / 101 WARN**
   (Cryptography) and 25 / 391 (Complexity). At the final head both have line sets identical to the tip `a334ec2e`
   (review `lint/linediff-r3.txt`, empty).
6. **LE-doc (the maintainer's landing edit): docstrings only.** It adds formulas, in Lean argument order, to the 50 new
   public declarations the review's docaudit flagged NO-FORMULA: 3 in the owned file, 18 `Efficiency`, 6 `Predictor`,
   4 `Shape`, 11 `Simulators`, 1 `ViewA` and 7 `ViewB`. The frozen target `otProtocol_polyTime` keeps its base prose.
   Re-checked for this pack from git objects: `b2e817ca..7a1fa29b` touches the 7 files, each identical with doc
   comments deleted, with 50 docstrings changed and every line within 100 characters (`pack-checks/lecheck.txt`).
7. **LE-reuse (the maintainer's landing edit): proof only** (review finding F-01). `pairSndD_nil'`'s proof
   `List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (length_pairSndD_le []))` becomes `BinArith.iterate_pairSndD_nil 1`.
   Its docstring's provenance parenthesis now names the public lemma. It is +2/−2, one file, no import. The statement is
   unchanged (`statements/head-le/decls2-vs-worker.tsv`, empty), and a trial build passed before the commit
   (`lereuse-trial/`: `Efficiency` rc 0, 0 warnings). Re-checked for this pack: `7a1fa29b..f62a25b3` touches
   `Efficiency.lean` only, in 2 hunks, with its 38 headers identical, only `pairSndD_nil'`'s docstring changed, and
   the imports identical (`pack-checks/lecheck.txt`).
8. **The landing edits are the maintainer's** (the ext-nosrc, cca2-ett, dl-crh, hash-sign, lamport, learning and
   prf-mac precedents).
9. **G3-8 is closed.** The enhanced hard-core predicate was ruled (A) on 2026-11-05 and applied in prong B.
   `EnhancedHardCore` is a frozen definition and a hypothesis of the target. Whether any collection has such a
   predicate limits the use of the result, not its proof (module docstring).

## What is frozen

- **The two targets' statements** (quoted in the brief), the 50 other pre-existing declarations of
  `ObliviousTransfer.lean` and their statement prose, in particular `EnhancedHardCore` and `enhancedHardCore_iff`, the
  protocol and simulator definitions with their readers, `otProtocol_outV/_outP` and `otProtocol_hbcSecure`. Also the
  global simp attributes.
- **Every file outside** `SecureComputation/ObliviousTransfer.lean` and `SecureComputation/ObliviousTransfer/`. That
  includes `SecureComputation/Defs.lean` (the functionality and `realA/B`, `idealA/B`), `Encryption/PublicKey/
  Trapdoor.lean` and `TrapdoorPredictor.lean` (`exists_pkPredictor`, `tdpPredictor`), `Asymptotic/Collections*.lean`
  and `Games/Efficiency.lean`.
- **The landing edits:** LE-doc 50 docstrings; LE-reuse one proof and one docstring parenthesis.

## Questions for the audit

**1. Correctness against [PS10, Protocol 160.4 and Proposition 161.5]**
- **`otProtocol_polyTime`:** do `OT.senderRaw` and `OT.receiverRaw` compute the parties' next-message functions on
  every history (cases `[]`, one, two, three or more messages; `senderRaw_advInput`, `receiverRaw_advInput`)? Are
  they polynomial-time with the stated coins? Is the message bound `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5` correct for the
  five-message layout, including the two empty fillers and one-bit masks?
- **Alice's side:** is `OT.distAdv_realA_idealA_le` (≤ `2δ(n)` at every `n`) right?
  - Are `OT.realA_realCoins` and `OT.idealA_simACoins` the real and ideal samplers on `(r, s₁, s₂)`, for both `b`?
  - Is `OT.statClose_eval_sample` right: `δ` to the uniform element mapped by `encD ∘ perm`, `0` from `perm`, `δ`
    back by canonical decoding (`SamplerCanonical`)?
  - Is the dependent product `OT.statClose_prod_of_forall` (closeness for every value of a shared coordinate) sound?
  - Is the use of `acceptProb_comp_equiv` along the coin equivalences sound?
- **Bob's side:** is the route through `tdpPredictor`/`viewDist` with the signed identity right?
  - Is `OT.hcBit` exactly the bit `EnhancedHardCore` (through `enhancedHardCore_iff`) asks the predictor to guess,
    with the challenge `⟨i, s'⟩` and `s'` the sampler coins?
  - Does `viewDist` rebuild Bob's real view around the challenge, with Bob's tape `s₁ ++ s'` and `D`'s advice and
    coins kept (`distinguisherL_viewDist`)?
  - Is the signed-predictor identity `OT.uprob_signedPredictor_false/_true` (`1/2 ± (U₊ − U₋)/2` for uniform coin
    challenges) correct, and are `acceptProb_realB` (`E_r accB r B`) and `acceptProb_idealB`
    (`E_r (accB r B + accB r ¬B)/2`) right, with the masks read by `mask_eval` and `mask_raw` through
    `inv_runAtL_ones`, `inv_eq_encD`, `henc` and `apply_of_decD`?
  - Are the **16 `hEHC` instances** (8 triples × 2 signs) and their **sum** `ε_B` a negligible bound uniform over
    all inputs (`exists_negligible_bob`, `negligible_finset_sum`)?
- Does `OT.simulators_of_isOT` give the frozen statement with `ε(n) = 2|δ(n)| + ε_B(n)` for every `D`?
- Do `otProtocol_isOT`, `otSimA_isSimA` and `otSimB_isSimB` prove the shapes from the owned file's published
  readers only, and are the restated bodies (`OT.mask`, `senderNext`, `receiverNext`, `simAView`, `simBView`, …)
  exactly the owned definitions?
- Are the brief's edge cases covered (listed above)? Do the rewritten target sketches describe the delivered proof?

**2. Frozen-statement integrity**
- Are the two targets' headers and the other 50 pre-existing declarations byte-identical, with
  **`EnhancedHardCore` unchanged** (G3-8)? See `landing/frozen-check.txt`, `statements/frozen/` and
  `pack-checks/headers.txt`.
- In the owned file, did only the targets' bodies and sketches, the imports, the title ("(statement phase)" dropped),
  the `## Main results` lines and the new `## Contents` change?
- Is decls2 **141 ADDED / 0 CHANGED / 0 REMOVED**, is frozencheck **0** with 5 biting controls, and is every new
  declaration in the owned file or the permitted helper directory?

**3. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's `## Overlap and reuse` table and **DL-48** (ruling 1)? F-01 is fixed by LE-reuse; F-02 and F-04
  are ruled debt (DL-48), and F-07's items are DL-48 notes.
- **Any further undisclosed duplicate of a public lemma is a major.** The recent majors of this class are G23-01,
  G24-01 (`inputWord_take` re-proving `take_ofFn_castLE`), prf-mac F-01, learning (`uprob_eq_point`), G29-01
  (`hj` = `OneWay.uexp_const`), G29-02 (`firstBit_of_pos` re-proving `LamportFill.headD_drop_ofFn`) and sc-ot F-01
  itself.
- Search in particular:
  - probability and closeness identities (`uprob_*`, `uexp_*`, `acceptProb_*`, `StatClose.*`, `statClose_*`,
    `distAdv_*`);
  - negligible-function closure (`Negligible.*`, finite sums);
  - coin equivalences and their `ofFn` readers (`splitCoins`, `coinsEquiv`, `owfCoinsEquiv`, `coinsEquivPoly`,
    `Fin.appendEquiv`);
  - history and list readings (`pairFstD`/`pairSndD`, `encodeMsgs`, `getD`/`headD`, `iterate_pairSndD_*`, now also
    the tip's `TCSlib.Cryptography.headD_drop_ofFn` from #316);
  - execution unfoldings (`exec_succ`, `exec_*`);
  - trapdoor readings (`inv_eq_encD`, `apply_of_decD`, `tdpPredictor`, `predProb_*Predictor_*`);
  - machine lengths (`runLenPoly`, `length_runAt*`).
- Are the disclosed relations accurate and their "why not reused" reasons valid? See in particular `hcBit` vs the
  private `tdpSampled`, `mask_eval`/`mask_raw` vs the private `tdpBitScheme_pkEncDist`, `getD_zero_eq`/`getD_one_eq'`,
  and the GI/3-col machine pattern of the raw functions. The review's independent search is
  `evidence/logs/duplication-review.txt`; the worker's are `worker/evidence/logs/{checkpoint1,final}-searches.log`.

**4. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 7 files over
  the full closure, at the base and the head, in all four variants? See review `logs/seal-table-seals{,-coe}.txt` and
  `logs/seal-head-*.tsv`. Requests per file (coe A): owned 1721, `Shape` 1105, `Efficiency` 1109, `Simulators` 1109,
  `ViewA` 1124, `Predictor` 1706, `ViewB` 1711; strict = coe + 1, the instance (`logs/mkseals-*.log`).
- With **coe-A canonical** (rulings 3 and 4), does every file pass? The review has head A 7/7 and B 7/7 in both
  variants, base 1/1, and 0 new failing declarations; strict = coe.
- Do the paired controls bite? The coe records (canonical) have 20 probes and 61 sealed negatives, `logs/ctlcheck.log`
  ALL_OK. The rows are `PolyExpr.eval` (B), the `FinDist` CoeFun instance, `NUPPT.layout`, `Strategy.encodeMsgs`,
  `otFunctionality`, `OT.mask`, `OT.simSeg`, `OT.inA2`, `OT.bobView` and `OT.hcBit`.
  - The strict records have 20 probes and 71 sealed negatives. Every negative fails exactly once, but `ctlCoeReader`
    fails in the 10 strict sealed probes, a harness effect: the statement elaborates to `CoeFun.coe` (F-09,
    `logs/controls-strict-attribution.txt`). Is that attribution right?
  - F-09 also notes that the strict negative `ctlCoe` *does* fail once, against the worker's claim. Is that right?
- Explicit-unfold scan at r1 (`fb6075d8`; the unit's 128-module closure is byte-identical at the head,
  `pack-checks/rebase.txt`): 742 items, 645 theorems, 21 owned definitions, 76 local or unresolved, **0 foreign**
  (`logs/scan2-head.log`, `logs/scan-owned-and-local.txt`). The owned items are the base file's 18 pre-existing proofs
  and 3 in-file helper definitions (`viewDist`, `simACoins`, `simBCoins`).
  - Does any proof read a foreign definition other than through a published reader? Candidates: the
    `SecureComputation/Defs` functionality, `realA/B`, `idealA/B`, `distAdv`; `NUPPT.layout`, `advInput`,
    `ofPolyTime*`; `Strategy.encodeMsgs`, `exec`; `tdpPredictor`, `TrapdoorCollection.*`; `FinDist` internals; the
    owned file's definitions read from a helper; one helper's definitions read from another.

**5. The landing edits**
- **LE-doc (ruling 6):** does each of the 50 new formulas state what its declaration says, with arguments in the Lean
  order (review `landing/le-doc.diff`, `landing/le-doc-doconly.txt`)? Is it docstrings only?
- **LE-reuse (ruling 7):** is it proof only, plus the docstring parenthesis? Is `BinArith.iterate_pairSndD_nil 1` a
  correct instance (`pairSndD^[1] [] = []` is `pairSndD [] = []` by `Function.iterate_one`, definitionally)? See
  `landing/le-reuse.diff`.
- Were the seals, controls and scan, run at r1 `fb6075d8`, rightly carried to the head? `pack-checks/rebase.txt`: the
  range-diff `0e5e725d..fb6075d8` → `a334ec2e..f62a25b3` is 5/5 `=`, and all 128 modules of the unit's closure are
  byte-identical at `fb6075d8` and `f62a25b3`.

**6. The docstring and sketch rules**
- Does every new public declaration's docstring state its formula, with arguments in the Lean order and a `[PS10, …]`
  tag where it comes from the source? The review's docaudit after LE-doc (`statements/head-le/docaudit.tsv`) has
  110 OK, 25 LABEL (all state the equation) and 8 NO-FORMULA. The 8 are the frozen `otProtocol_polyTime`'s base prose
  and 7 docstrings stating a Prop formula without a relation symbol, such as `OT.IsOT T H (otProtocol T H)` and
  `PolyTimeComputable (genRaw T)`, which the tool does not accept. Are those 7 acceptable?
- Does every proof of 15 lines or more carry a `**Proof sketch.**`, and do the long proofs (`exists_negligible_bob`,
  `distAdv_realA_idealA_le`, the raw-machine efficiency proofs) have step comments? `statements/head-le/sketchaudit.txt`
  has 13 theorems and 1 flagged: `OT.receiverNext_eq`, a `:= rfl` under a 19-line statement, a tool artifact. A
  misstated formula or sketch is a minor.
- Does every new public `def` land with its readers (`_eq`, `_iff`, `_apply`, or for the coin equivalences `_ofFn`
  readers; lint check 8)? Is nothing new `@[simp]`, an instance, reducible or an abbreviation? The census has none
  (`logs/census-summary.txt`).

**7. The merge interaction**
- `git merge-tree --write-tree f62a25b3 <x>` is clean (`pack-checks/mergetrees.txt`). No path is shared with any of
  them, and the changed path sets of #318, #319 and (tip delta ∪ #313) are pairwise disjoint.

  | `<x>` | head | merged tree |
  |---|---|---|
  | the tip | `1321b9cb` | `fe5b9a3c` |
  | #313 | `94b31964` | `8baffe99` |
  | #316 (merged) | `c18afbe6` | `3c18fffc` |
  | #317 (merged) | `590d1a56` | `16633b31` |
  | #319 | `6421ac16` | `e59d63a7` |
- **Downstream** (`pack-checks/downstream.txt`):
  - **The tip.** Every unit module has #316's `Foundations/BitLists` in its closure. In the merged tree, 10 modules
    are downstream of both: the 7 unit modules, `SecureComputation`, `YaoReal` and root `TCSlib`. #317's files are
    not in the unit's closure.
  - **#313 and #319.** Neither changes a module in the unit's closure; root `TCSlib` is the only module downstream of
    both.
  - **The build.** Of the review's 139 built modules (`build-r3`, at this head), 137 have the tip-merged source. The
    other two are #317's `MAC/FromPRF` and #316's `Lamport/MachineSpec`. `BitLists` itself was not rebuilt, since it
    is unchanged from `a334ec2e` to this head. All 139 have #319's merged source, and 138 have #313's
    (`pack-checks/srcequality.txt`).
- **No name interaction:** none of the 141 new names is declared in a file the tip, #313, #316, #317 or #319 changed
  (`pack-checks/namecheck.txt`). The review's own open-PR check (`logs/open-pr-overlap.txt`) predates #316 and #317;
  this pack's check covers them.
- **Pending merge condition (not an audit item).** The combined trees are **not** built.
  - Because #316 and #317 merged after this branch's base, #318 needs an integration rebuild on the merged tip before
    it merges: the downstream of `BitLists`, `MachineSpec` and `MAC/FromPRF`, which contains every unit module.
  - Whichever of #318 and #319 merges second needs the same.
  - The maintainer runs those builds. Treat them as conditions on the merge, not as something for this audit to
    establish. What you can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **F-03** (info): the 50 missing formulas, fixed by LE-doc. **F-05** (info): `COMMITS.tsv` hashes reproduce only
  with the environment's deterministic SSH signing (`logs/git-am-integrity*.log`), as prf-long F-03. **F-06** (info,
  disclosed): the helpers restate the owned file's definition bodies by design. **F-08** (info): the worker removed
  another fill's worktree on its own host, an environment matter on the worker's host. **F-09** (info): the strict
  `ctlCoeReader` harness effect, attributed.
- **Finding numbers in the evidence log.** The review's `logs/duplication-review.txt` numbers `pairSndD_nil'` as F-02
  and `splitLen` as F-03. The review's findings table (`review.md`) and DL-48 number them **F-01** and **F-02**; the
  table governs.
- **The probes ran at r1.** The seals, controls, scan and census probes ran at `fb6075d8` (on `0e5e725d`). The builds
  `build-r2` (on #314) and `build-r3` (on #315, at this head) and the whole-tree check (1250 modules, RESULT OK) came
  after. The unit's closure is unchanged throughout (question 5).
- **Admissions:** the issued 31 in 14 modules become 29; only `SecureComputation/ObliviousTransfer` changes (2 → 0;
  `logs/sorry-census-r3.txt`). The build's 12 sorry warnings are all in admitted base or base-delta modules.
- **`yaoProtocol_hbcSecure` keeps `sorryAx`** through Yao's admitted hybrid; base, not this unit.
- **Old (pre-#305) lint** shows 6 more lines of the facade class #305 fixed (`lint/oldlint-linediff.txt`); recorded,
  not a finding.
- **The worker's promotion and reader requests** are recorded for the deferred cleanup (DL-48). These are
  `uprob_signedPredictor_*` with `pkPredictor_apply`, `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`,
  `length_runAtL_le`, and the readers `owpPair_apply`, `owpGen_apply` and `owpGenNot_apply`.

## Also check

**Axioms**
- At the head, `otProtocol_polyTime`, `otProtocol_simulators` and the consumer `otProtocol_hbcSecure` each print
  `[propext, Classical.choice, Quot.sound]`, and so do the helper endpoints. `pairSndD_nil'` uses no axioms
  (`landing/census-head.log`, `CensusHead.lean`). At the base the targets had `sorryAx`.
- The census has 234 stored constants in the 7 files (owned 70, `Shape` 15, `Efficiency` 49, `Simulators` 55, `ViewA`
  7, `Predictor` 15, `ViewB` 23, the worker's counts). The axiom union is the standard three, with no `sorryAx`. Against
  the base: 66 → 234, 0 removed, 0 type- or attribute-changed, 3 axiom-changed (the two targets and
  `otProtocol_hbcSecure`, `sorryAx` dropped; `logs/census-base-vs-head.tsv`).

**Sizes and widths:** every file has at most 748 lines and every line at most 100 characters (`source-head.json`;
review `statements/head-le/sizes-widths.txt`).

**Build:** at the head `f62a25b3`, the 139 modules have rc 0 and 0 errors in both diagnostic forms (G26-N1; substring
"error" 0). The modules are the downstream of every module changed since `eff2dcd0`, through root `TCSlib` and
`audits/pass-shelat/Checks` (`landing/root-checks.jsonl`, whose last line is the runner's `done` record;
`landing/build-summary.txt`). The unit modules have 0 warnings. The whole-tree check is at the head, 1250 modules,
RESULT OK (`landing/tree-check-head.txt`). The olean tree was restored to the base snapshot afterwards
(`restore/r3/snapshot-post.txt` = `tree/snapshot-pre.txt`, `457ba704…`). Every built module's `source_sha256` equals
the blob at `f62a25b3` (`pack-checks/srcequality.txt`).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (F-01–F-09).
- **`verification.zip`** (113 entries): every file the review cites and the pack uses, as byte-identical
  originals. Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/sc-ot/final-r1/`, SHA-256 `aa3bcfc3…`) and `review-evidence-SHA256SUMS`, its
    manifest: 811 entries, all files, under `sc-ot-r1/` exactly the 810 manifest paths plus that folder's
    `SHA256SUMS` (byte-identical to the manifest); every hash verifies. It covers integrity, the landing and both
    landing edits, the three rebases, the builds (r1, LE, r2, r3) and the whole-tree checks with the restore, decls2,
    the frozen check with its controls, `touched`, the docstring and sketch audits, the census and axioms, the strict
    and coe seals at the base and the head, the paired controls, the scan, the lint, sizes and the duplication review;
  - `landing/` (13): the review's extracts (`final-r1/landing/`), each a byte copy of a ZIP entry: `PROVENANCE.txt`,
    the commits, the series log, the LE-doc and LE-reuse diffs and messages, the doc-only check, the rebase logs and
    the origin delta;
  - `records/` (14): the issue package `fills/sc-ot/issued-r1/`, the duplication ledger (DL-48), the decision log,
    the #305 record (README and patch) and the secure-computation plan (§ 2.1–2.2), at records
    `1321b9cb358867f5b51974b8c5d0781519a9cfdb`;
  - `evidence/` (54): byte copies of the ZIP entries this pack cites;
  - `worker/` (11): byte copies from exchange `a8972fa063a58ad2ffbfd221d625653d34a53ee8` (`inbox/fills/sc-ot/`):
    `patches/COMMITS.tsv`, the final axioms, both searches, the census and lint diffs, the repro, width and control
    logs, `seals-compare.log` and `scan-compare.log`;
  - `pack-checks/` (17): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `a8972fa063a58ad2ffbfd221d625653d34a53ee8`, under
  `inbox/fills/sc-ot/`. Its top `SHA256SUMS` lists 219 files and `evidence/SHA256SUMS` 206, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries.
  - `root-checks.jsonl` (= `build-r3/results.jsonl`): the 139 modules, rc 0.
  - `build-summary.txt` (= `build-r3/summary.txt`).
  - `census-head.log` (= `probe-runs/CensusHead.log`): the axiom prints and the census rows at the head.
  - `frozen-check.txt` (= `statements/head-le/frozen-check.txt`): the frozen check at the LE head.
  - `tree-check-head.txt` (= `tree/r3/tree-check-head.txt`): the whole-tree check at the head.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `a8972fa0`.
- **`pr-description.md`:** the PR #318 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (7 paths, 2256 insertions, 40 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 7 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 128 files.
- **The bundle** adds, as context at the head:
  - `SecureComputation/Defs.lean` (the functionality, `realA/B`, `idealA/B`, `PolyTime`);
  - `Encryption/PublicKey/TrapdoorPredictor.lean` (`tdpPredictor`, `uprob_tdpPredictor`, `uexp_half_add/_sub`);
  - `Encryption/PublicKey/Trapdoor.lean` (`exists_pkPredictor` and the private `predProb_pkPredictor_eq`).

## Findings delivery

Return `gate34-sc-ot-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-48, or necessary evidence that
  cannot be verified.
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

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: Protocol 160.4 runs in polynomial time

Both parties of a protocol of the shape of [PS10, Protocol 160.4] (`OT.IsOT`) are efficient
strategies, and the messages of its honest executions are polynomially bounded: the
efficiency requirement `Functionality.PolyTime` of Definition 155.1 for `otFunctionality`.

Each next-message function branches on the number of messages received, which the raw machine
reads off the encoded history `⟨m₁, ⟨m₂, …⟩⟩` by emptiness tests of its iterated second
components (`polyTimeComputable_isNil`); the branches are compositions of `Gen`, the sampler and
the inverter (uniform machines, `NUPPT.polyTimeComputable_output`), the evaluator (`eval_poly`),
`H`, pairing and one XOR. The machines are `NUPPT.ofPolyTimeUniform` of these raw functions.

## Main definitions

* `OT.senderRaw`, `OT.receiverRaw`: the raw functions of the two parties' machines.

## Main results

* `OT.polyTimeComputable_senderRaw`, `OT.polyTimeComputable_receiverRaw`: they are
  polynomial-time.
* `OT.senderRaw_advInput`, `OT.receiverRaw_advInput`: they compute the next messages.
* `OT.length_runAtL_le`: the output-length bound of a machine on an untyped tape.
* `OT.polyTime_of_isOT`: [PS10, Protocol 160.4] runs in polynomial time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and Protocol 160.4 (book pp. 155, 160).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### Reading the encoded history -/

/-- The first message of a history is the first projection of its encoding:
`hist.headD [] = fst (encodeMsgs hist)` (`Strategy.pairFstD_encodeMsgs`). -/
theorem headD_eq_pairFstD (hist : List (List Bool)) :
    hist.headD [] = pairFstD (Strategy.encodeMsgs hist) :=
  (Strategy.pairFstD_encodeMsgs hist).symm

/-- The second projection of the empty word is empty, `pairSndD [] = []`
(`BinArith.iterate_pairSndD_nil` at `1`). -/
theorem pairSndD_nil' : pairSndD ([] : List Bool) = [] :=
  BinArith.iterate_pairSndD_nil 1

/-- The second message of a history is read off its encoding:
`hist.getD 1 [] = fst (snd (encodeMsgs hist))`. -/
theorem getD_one_eq (hist : List (List Bool)) :
    hist.getD 1 [] = pairFstD (pairSndD (Strategy.encodeMsgs hist)) := by
  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
  · rw [Strategy.encodeMsgs_nil, pairSndD_nil', pairFstD_nil]
    rfl
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairSndD_pairEncode, pairFstD_nil]
    rfl
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, pairSndD_pairEncode,
      pairFstD_pairEncode]
    rfl

/-- A uniform machine's activation is its output on the layout with empty advice:
`A.runAtL n y r = A.output (layout 1^n y [] r)` (`NUPPT.runAtL_eq_output_layout`). -/
theorem runAtL_eq_layout {A : NUPPT} (hA : A.Uniform) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (NUPPT.layout (List.replicate n true) y [] r) := by
  rw [NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA]

/-- The raw layout of a strategy activation: `⟨⟨advInput n a, []⟩, r⟩ = layout 1^n a [] r`. -/
theorem advInput_layout (n : ℕ) (a r : List Bool) :
    pairEncode (pairEncode (NUPPT.advInput n a) []) r =
      NUPPT.layout (List.replicate n true) a [] r := by
  rw [NUPPT.advInput_eq, NUPPT.layout_eq]

/-! ### Alice's machine -/

/-- `Gen`'s output on the raw layout `z`: `Gen(inParam z; inCoins z)` with empty argument,
`genRaw T z = Gen.output (layout (inParam z) [] [] (inCoins z))`. -/
def genRaw (z : List Bool) : List Bool :=
  T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))

/-- The defining equation of `genRaw`: `genRaw T z = Gen.output (layout (inParam z) [] []
(inCoins z))`. -/
theorem genRaw_eq (z : List Bool) :
    genRaw T z = T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z)) := rfl

/-- `genRaw` is polynomial-time: `PolyTimeComputable (genRaw T)`. -/
theorem polyTimeComputable_genRaw : PolyTimeComputable (genRaw T) :=
  (T.gen.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)).congr
    fun z => (genRaw_eq T z).symm

/-- Alice's mask on the raw layout `z`, for the element `yj` and the bit word `bt`:
`zipWith xor (H ⟨i, Inv(⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
def maskRaw (z yj bt : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
    (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
      (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt

/-- The defining equation of `maskRaw`: `maskRaw T H z yj bt =
zipWith xor (H ⟨i, Inv(inParam z, ⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
theorem maskRaw_eq (z yj bt : List Bool) :
    maskRaw T H z yj bt =
      List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
        (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
          (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt := rfl

/-- The raw mask is polynomial-time in `z` for polynomial-time `yj` and `bt`:
`PolyTimeComputable (fun z => maskRaw T H z (Y z) (B z))` for polynomial-time `H`, `Y`, `B`.

**Proof sketch.** Pair the index (first projection of `genRaw`) with the inverter's output on
the layout of `1^n`, `⟨t, yj⟩` and the all-`true` tape (`polyTimeComputable_unaryPoly`), apply
`H`, pair with `bt` and XOR (`polyTimeComputable_pairXor`). -/
theorem polyTimeComputable_maskRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    {Y B : List Bool → List Bool} (hY : PolyTimeComputable Y) (hB : PolyTimeComputable B) :
    PolyTimeComputable fun z => maskRaw T H z (Y z) (B z) := by
  have hG := polyTimeComputable_genRaw T
  have hinv := T.inv.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam ((polyTimeComputable_pairSndD.comp' hG).pairEncode hY)
    (polyTimeComputable_const [])
    ((polyTimeComputable_unaryPoly T.inv.coins).comp' NUPPT.polyTimeComputable_inParam))
  have h := polyTimeComputable_pairXor.comp'
    ((hH.comp' ((polyTimeComputable_pairFstD.comp' hG).pairEncode hinv)).pairEncode hB)
  refine h.congr fun z => ?_
  rw [maskRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **Alice's raw function** on `z = layout 1^{|x|} ⟨⟨x, y⟩, w⟩ [] r` with `w` the encoded
history: `fst (genRaw z)` if `w = []`; the two masks if `snd w = []`; else `[]`. -/
def senderRaw (z : List Bool) : List Bool :=
  if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
    pairEncode
      (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
        [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
      (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
        [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
  else []

/-- The defining equation of `senderRaw`: with `w = snd (inArg z)`, `fst (genRaw T z)` if
`w = []`, the two raw masks if `snd w = []`, else `[]`. -/
theorem senderRaw_eq (z : List Bool) :
    senderRaw T H z =
      if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
        pairEncode
          (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
            [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
          (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
            [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
      else [] := rfl

/-- **Alice's raw function is polynomial-time** (`polyTimeComputable_ite` on the two emptiness
tests `polyTimeComputable_isNil`, `polyTimeComputable_maskRaw`, `polyTimeComputable_headD`,
`polyTimeComputable_tail`): `PolyTimeComputable (senderRaw T H)` for polynomial-time `H`. -/
theorem polyTimeComputable_senderRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (senderRaw T H) := by
  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
  have hy := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg)
  have hm := polyTimeComputable_pairFstD.comp' hw
  have h₁ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairFstD.comp' hm)
    (polyTimeComputable_headD.comp' hy)
  have h₂ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairSndD.comp' hm)
    (polyTimeComputable_headD.comp' (polyTimeComputable_tail.comp' hy))
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw)
    (polyTimeComputable_pairFstD.comp' (polyTimeComputable_genRaw T))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
      (h₁.pairEncode h₂) (polyTimeComputable_const []))
  exact h.congr fun z => (senderRaw_eq T H z).symm

/-- `Gen`'s output on the layout of an activation at `1^{|x|}` is `Gen(1^{|x|}; r)`:
`genRaw T (layout 1^n a [] r) = Gen.runAtL n [] r`. -/
theorem genRaw_layout (n : ℕ) (a r : List Bool) :
    genRaw T (NUPPT.layout (List.replicate n true) a [] r) = T.gen.runAtL n [] r := by
  rw [genRaw_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout, runAtL_eq_layout T.gen_uniform]

/-- The raw mask on the layout of an activation is Alice's mask:
`maskRaw T H (layout 1^n a [] r) yj [c] = mask T H n i t yj c` with `⟨i, t⟩ = Gen(1^n; r)`. -/
theorem maskRaw_layout (n : ℕ) (a r yj : List Bool) (c : Bool) :
    maskRaw T H (NUPPT.layout (List.replicate n true) a [] r) yj [c] =
      mask T H n (pairFstD (T.gen.runAtL n [] r)) (pairSndD (T.gen.runAtL n [] r)) yj c := by
  rw [maskRaw_eq, genRaw_layout, NUPPT.inParam_layout, List.length_replicate, mask_eq,
    runAtL_eq_layout T.inv_uniform]

/-- `y.getD 0 false` is the head bit: `y.getD 0 false = y.headD false`.
It is the public `TCSlib.Cryptography.headD_drop` at `i = 0`, reversed. -/
theorem getD_zero_eq (y : List Bool) : y.getD 0 false = y.headD false := by
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.headD_drop y 0 false).symm

/-- `y.getD 1 false` is the head bit of `y.drop 1`:
`y.getD 1 false = (y.drop 1).headD false`.
It is the public `TCSlib.Cryptography.headD_drop` at `i = 1`, reversed. -/
theorem getD_one_eq' (y : List Bool) : y.getD 1 false = (y.drop 1).headD false :=
  (TCSlib.Cryptography.headD_drop y 1 false).symm

/-- **Alice's raw function computes her next message**: on the raw input of the activation
`⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `senderNext T H x y r hist`:
`senderRaw T H ⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩ =
senderNext T H x y r hist`.

**Proof sketch.** Cases on the history: `[]` (the encoding is empty), `[m]` (its second
projection is empty), and two or more messages (neither is empty); `genRaw_layout`,
`maskRaw_layout` and `getD_zero_eq`, `getD_one_eq'` identify the branches with
`senderNext_nil`, `senderNext_single`, `senderNext_eq`. -/
theorem senderRaw_advInput (x y r : List Bool) (hist : List (List Bool)) :
    senderRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
      (pairEncode (pairEncode x y) (Strategy.encodeMsgs hist))) []) r) =
      senderNext T H x y r hist := by
  rw [advInput_layout, senderRaw_eq, NUPPT.inArg_layout, genRaw_layout, pairSndD_pairEncode,
    pairFstD_pairEncode, pairSndD_pairEncode]
  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), senderNext_nil]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_pos (by simp), pairFstD_pairEncode, senderNext_single,
      maskRaw_layout, maskRaw_layout, getD_zero_eq, getD_one_eq']
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_neg (by simp [pairEncode_ne_nil]), senderNext_eq,
      if_neg (by simp), if_neg (by simp)]

/-! ### Bob's machine -/

/-- Bob's sampled element on the raw layout `z`, at the index `i = fst w` of the encoded
history `w = snd (inArg z)`: the sampler on the first `coins_Sample(n)` coins. -/
def knownRaw (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
    ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `knownRaw`: `knownRaw T z = Sample(inParam z, fst w;
(inCoins z).take coins_Sample(n))` with `w = snd (inArg z)`. -/
theorem knownRaw_eq (z : List Bool) :
    knownRaw T z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
        ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- Bob's raw element on the raw layout `z`: the sampler on the coins after the first block,
`rawRaw T z = Sample(inParam z, fst w; (inCoins z).drop coins_Sample(n))` with
`w = snd (inArg z)`. -/
def rawRaw (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
    ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `rawRaw`: `rawRaw T z = Sample(inParam z, fst w;
(inCoins z).drop coins_Sample(n))` with `w = snd (inArg z)`. -/
theorem rawRaw_eq (z : List Bool) :
    rawRaw T z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
        ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- Bob's output on the raw layout `z`: `H ⟨i, w⟩ ⊕ z_b` with `z_b` the second or first
projection of the second message, by the choice bit `b`:
`outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b` with `w = snd (inArg z)`. -/
def outRaw (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
    (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
      pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
    else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))))

/-- The defining equation of `outRaw`: `outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b`
with `z_b` the second or first projection of `fst (snd w)` by the choice bit. -/
theorem outRaw_eq (z : List Bool) :
    outRaw T H z =
      List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
        (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
          pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
        else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) := rfl

/-- Bob's ordered pair on the raw layout `z`: `⟨w', eval ⟨i, w⟩⟩` if `b`, else
`⟨eval ⟨i, w⟩, w'⟩`, with `w = knownRaw T z`, `w' = rawRaw T z`, `i = fst (snd (inArg z))` and
`b = (snd (fst (inArg z))).headD false`. -/
def pairRaw (z : List Bool) : List Bool :=
  if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
    pairEncode (rawRaw T z)
      (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
  else
    pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
      (rawRaw T z)

/-- The defining equation of `pairRaw`: `⟨rawRaw, eval ⟨fst w, knownRaw⟩⟩` if `b`, else
`⟨eval ⟨fst w, knownRaw⟩, rawRaw⟩`, i.e. `pairRaw T z = if b then ⟨rawRaw T z, eval ⟨fst w,
knownRaw T z⟩⟩ else ⟨eval ⟨fst w, knownRaw T z⟩, rawRaw T z⟩` with `w = snd (inArg z)`. -/
theorem pairRaw_eq (z : List Bool) :
    pairRaw T z =
      if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
        pairEncode (rawRaw T z)
          (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
      else
        pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
          (rawRaw T z) := rfl

/-- **Bob's raw function** on `z = layout 1^{|x|} ⟨⟨x, z_B⟩, w⟩ [] r`: `outRaw` if `w = []`, the
pair if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
def receiverRaw (z : List Bool) : List Bool :=
  if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
  else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
  else outRaw T H z

/-- The defining equation of `receiverRaw`: with `w = snd (inArg z)`, `outRaw` if `w = []`,
`pairRaw` if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
theorem receiverRaw_eq (z : List Bool) :
    receiverRaw T H z =
      if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
      else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
      else outRaw T H z := rfl

/-- **Bob's raw function is polynomial-time**: the sampler on the two coin blocks
(`polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`), `eval_poly`, `H`, XOR,
pairing, and branches on the choice bit and three emptiness tests (`polyTimeComputable_ite`):
`PolyTimeComputable (receiverRaw T H)` for polynomial-time `H`.

**Proof sketch.** Build `knownRaw`, `rawRaw`, `outRaw`, `pairRaw` from the projections and the
machines' output functions, then nest three `polyTimeComputable_ite`. -/
theorem polyTimeComputable_receiverRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (receiverRaw T H) := by
  have hU := NUPPT.polyTimeComputable_inParam
  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
  have hi := polyTimeComputable_pairFstD.comp' hw
  have hb := polyTimeComputable_headD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg))
  have htake := (polyTimeComputable_pairTakePoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hdrop := (polyTimeComputable_pairDropPoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hk : PolyTimeComputable (knownRaw T) :=
    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
      (polyTimeComputable_const []) htake)).congr fun z => by
        rw [knownRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have hr : PolyTimeComputable (rawRaw T) :=
    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
      (polyTimeComputable_const []) hdrop)).congr fun z => by
        rw [rawRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have he := T.eval_poly.comp' (hi.pairEncode hk)
  have hm := polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have ho : PolyTimeComputable (outRaw T H) :=
    (polyTimeComputable_pairXor.comp' ((hH.comp' (hi.pairEncode hk)).pairEncode
      (polyTimeComputable_ite hb (polyTimeComputable_pairSndD.comp' hm)
        (polyTimeComputable_pairFstD.comp' hm)))).congr fun z => by
      rw [outRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have hp : PolyTimeComputable (pairRaw T) :=
    (polyTimeComputable_ite hb (hr.pairEncode he) (he.pairEncode hr)).congr
      fun z => (pairRaw_eq T z).symm
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw) ho
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
      hp (polyTimeComputable_ite (polyTimeComputable_isNil.comp'
        (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)))
        (polyTimeComputable_const []) ho))
  exact h.congr fun z => (receiverRaw_eq T H z).symm

/-- On the layout of an activation, `knownRaw` is the sampler on the first coin block:
`knownRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
Sample.runAtL n (hist.headD []) (r.take coins_Sample(n))`. -/
theorem knownRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
    knownRaw T
        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
      T.sample.runAtL n (hist.headD []) (r.take (T.sample.coins.eval n)) := by
  rw [knownRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
    runAtL_eq_layout T.sample_uniform]

/-- On the layout of an activation, `rawRaw` is the sampler on the second coin block:
`rawRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
Sample.runAtL n (hist.headD []) (r.drop coins_Sample(n))`. -/
theorem rawRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
    rawRaw T
        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
      T.sample.runAtL n (hist.headD []) (r.drop (T.sample.coins.eval n)) := by
  rw [rawRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
    runAtL_eq_layout T.sample_uniform]

/-- **Bob's raw function computes his next message**: on the raw input of the activation
`⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `receiverNext T H x z r hist`:
`receiverRaw T H ⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩ =
receiverNext T H x z r hist`.

**Proof sketch.** `knownRaw_layout`, `rawRaw_layout`, `headD_eq_pairFstD` and `getD_one_eq`
identify `outRaw` with the last branch of `receiverNext` on every history and `pairRaw` with the
first. Then cases on the history: `[]`, `[i]`, two messages, and three or more, by the emptiness
of the iterated second projections of the encoding. -/
theorem receiverRaw_advInput (x z r : List Bool) (hist : List (List Bool)) :
    receiverRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist))) []) r) =
      receiverNext T H x z r hist := by
  rw [advInput_layout, receiverRaw_eq]
  have hout : outRaw T H (NUPPT.layout (List.replicate x.length true)
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
      List.zipWith xor (H (pairEncode (hist.headD [])
        (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := by
    rw [outRaw_eq, knownRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode, pairFstD_pairEncode,
      pairSndD_pairEncode, ← headD_eq_pairFstD, getD_one_eq]
  have hpair : pairRaw T (NUPPT.layout (List.replicate x.length true)
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
      receiverNext T H x z r [hist.headD []] := by
    rw [pairRaw_eq, knownRaw_layout, rawRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode,
      pairFstD_pairEncode, pairSndD_pairEncode, ← headD_eq_pairFstD, receiverNext_single]
  rw [hout, hpair, NUPPT.inArg_layout, pairSndD_pairEncode]
  rcases hist with _ | ⟨m, _ | ⟨m', _ | ⟨m'', rest⟩⟩⟩
  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), receiverNext_eq,
      if_neg (show ¬([] : List (List Bool)).length = 1 by simp),
      if_neg (show ¬([] : List (List Bool)).length = 2 by simp)]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_pos (by simp), List.headD_cons]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode, if_pos (by simp),
      receiverNext_pair]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), receiverNext_eq,
      if_neg (show ¬(m :: m' :: m'' :: rest).length = 1 by simp),
      if_neg (show ¬(m :: m' :: m'' :: rest).length = 2 by simp)]

/-! ### Message lengths -/

/-- **The output-length bound on an untyped tape of the right length**: `|A(1^n, y; r)| ≤
runLenPoly A Y (n)` whenever `|y| ≤ Y(n)` and `|r| = coins_A(n)` (the list form of
`NUPPT.length_runAt_le_runLenPoly`, through `List.ofFn_get`). -/
theorem length_runAtL_le (A : NUPPT) {Y : PolyExpr} (n : ℕ) {y r : List Bool}
    (hy : y.length ≤ Y.eval n) (hr : r.length = A.coins.eval n) :
    (A.runAtL n y r).length ≤ (A.runLenPoly Y).eval n := by
  have hr' : r.length = A.coinLen n := hr.trans (A.coinLen_eq n).symm
  have h := A.length_runAt_le_runLenPoly n hy (fun j => r.get (Fin.cast hr'.symm j))
  rwa [NUPPT.runAt_eq, ← List.ofFn_congr hr' r.get, List.ofFn_get] at h

/-- A mask has at most one bit: `|zipWith xor w [a]| ≤ 1`. -/
theorem length_zipWith_singleton_le (w : List Bool) (a : Bool) :
    (List.zipWith xor w [a]).length ≤ 1 := by
  rw [List.length_zipWith, List.length_singleton]
  exact Nat.min_le_right _ _

/-- Alice's mask has at most one bit: `|mask T H n i t yj a| ≤ 1`. -/
theorem length_mask_le (n : ℕ) (i t yj : List Bool) (a : Bool) :
    (mask T H n i t yj a).length ≤ 1 := by
  rw [mask_eq]
  exact length_zipWith_singleton_le _ a

/-- **The messages of Protocol 160.4 are polynomially bounded**: for a protocol of its shape there
is a polynomial `B` with `|msg| ≤ B(n)` for every message of every honest execution on `1^n`.

**Proof sketch.** The transcript is `([y, []], [i, z, []])` (`transcriptWith_isOT`). The index
has `|i| ≤ Q₁(n)` (`Gen`'s `runLenPoly`); the two samples have `≤ Q₂(n)` (the sampler's
`runLenPoly` at `Q₁`, the coin blocks having `coins_Sample(n)` bits); the evaluation has
`≤ Q₃(n)` (the evaluator's polynomial bound at `2Q₁ + 2 + Q₂`); so `|y| ≤ 3(Q₂ + Q₃) + 2`.
The masks have one bit each, so `|z| ≤ 5`. Take `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5`. -/
theorem exists_messages_le {π : Protocol} (hπ : IsOT T H π) :
    ∃ B : PolyExpr, ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
      (y : Fin (otFunctionality.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
      ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
          (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
        msg.length ≤ B.eval n := by
  obtain ⟨-, -, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
  obtain ⟨C, c, hC⟩ := T.eval_poly.output_length_le
  set Q₁ : PolyExpr := T.gen.runLenPoly (.const 0) with hQ₁
  set Q₂ : PolyExpr := T.sample.runLenPoly Q₁ with hQ₂
  set Q₃ : PolyExpr := (PolyExpr.normal C c).subst
    (.add (.add (.mul (.const 2) Q₁) (.const 2)) Q₂) with hQ₃
  refine ⟨.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2)) (.const 5)),
    fun n x y r msg hmsg => ?_⟩
  suffices key : ∀ (w a b : List Bool) (r : π.ExecCoins π.P w),
      ∀ msg ∈ (π.transcript w a b r).1 ++ (π.transcript w a b r).2,
        msg.length ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
          (.const 5))).eval w.length by
    have h := key _ _ _ r msg hmsg
    rwa [List.length_replicate] at h
  intro w a b r msg hmsg
  rw [Protocol.transcript_eq_transcriptWith, transcriptWith_isOT T H hπ] at hmsg
  -- the coin lengths
  have hrA : (List.ofFn r.1).length = T.gen.coins.eval w.length := by
    rw [List.length_ofFn, Strategy.coinLen_eq, hPc]
  have hrB : (List.ofFn r.2).length =
      T.sample.coins.eval w.length + T.sample.coins.eval w.length := by
    rw [List.length_ofFn, Strategy.coinLen_eq, hVc, PolyExpr.eval_add]
  -- the index
  set i := pairFstD (T.gen.runAtL w.length [] (List.ofFn r.1)) with hi_def
  have hi : i.length ≤ Q₁.eval w.length :=
    (length_pairFstD_le _).trans (length_runAtL_le T.gen w.length (by simp) hrA)
  -- the two samples
  have hk : (T.sample.runAtL w.length i
      ((List.ofFn r.2).take (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
    length_runAtL_le T.sample w.length hi (by rw [List.length_take, hrB]; omega)
  have hd : (T.sample.runAtL w.length i
      ((List.ofFn r.2).drop (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
    length_runAtL_le T.sample w.length hi (by rw [List.length_drop, hrB]; omega)
  -- the evaluation
  have he : (T.eval (pairEncode i (T.sample.runAtL w.length i
      ((List.ofFn r.2).take (T.sample.coins.eval w.length))))).length ≤ Q₃.eval w.length := by
    refine (hC _).trans ?_
    rw [hQ₃, PolyExpr.eval_subst, PolyExpr.eval_normal]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hB : ∀ k, k ≤ Q₁.eval w.length + (3 * (Q₂.eval w.length + Q₃.eval w.length) + 2) + 5 →
      k ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
        (.const 5))).eval w.length := by
    intro k hk'
    simpa only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const] using hk'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hmsg
  refine hB _ ?_
  rcases hmsg with h | h | h | h | h <;> subst h
  · -- Bob's pair
    rw [receiverNext_single]
    split_ifs <;> simp only [length_pairEncode] <;> omega
  · simp
  · omega
  · -- Alice's masks
    rw [senderNext_single, length_pairEncode]
    refine le_trans (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (length_mask_le T H _ _ _ _ _)) 2) (length_mask_le T H _ _ _ _ _)) ?_
    omega
  · simp

/-- **Protocol 160.4 runs in polynomial time** [PS10, Definition 155.1, efficiency]: for a
protocol of its shape with a polynomial-time `H`, both parties are efficient strategies (the
machines `ofPolyTimeUniform` of `senderRaw` and `receiverRaw`) and the honest messages are
polynomially bounded (`exists_messages_le`): `IsOT T H π → otFunctionality.PolyTime π`. -/
theorem polyTime_of_isOT {H : List Bool → List Bool} (hH : PolyTimeComputable H) {π : Protocol}
    (hπ : IsOT T H π) : otFunctionality.PolyTime π := by
  obtain ⟨hP, hV, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
  refine (Functionality.polyTime_iff _ _).2 ⟨?_, ?_, exists_messages_le T H hπ⟩
  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform (polyTimeComputable_senderRaw T hH)
      T.gen.coins, NUPPT.ofPolyTimeUniform_uniform _ _,
      hPc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, senderRaw_advInput, hP]
  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform
      (polyTimeComputable_receiverRaw T hH) (.add T.sample.coins T.sample.coins),
      NUPPT.ofPolyTimeUniform_uniform _ _,
      hVc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, receiverRaw_advInput, hV]

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/Foundations/BitLists.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit lists and bit vectors

Generic facts about lists, lists of bits and bit vectors `Fin n → Bool`, shared by the
cryptographic developments: heads of suffixes, flattening singleton blocks, the bit of a one-bit
vector, cancellation of exclusive-or, exclusive-or with a fixed vector as a permutation, and keys of
an association list. They depend on Mathlib only.

## Main definitions

* `TCSlib.Cryptography.xorPerm v`: exclusive-or with the vector `v`, as a permutation.

## Main results

* `TCSlib.Cryptography.headD_drop`: the head of a suffix is an entry.
* `TCSlib.Cryptography.headD_drop_ofFn`: the head of a suffix of a tuple's list is the tuple's
  entry at that index.
* `TCSlib.Cryptography.flatten_ofFn_one`, `flatten_ofFn_singleton`: flattening one-element blocks.
* `TCSlib.Cryptography.headD_ofFn_one`: the bit of a one-bit vector is the head of its string.
* `TCSlib.Cryptography.zipWith_xor_cancel_left`: `(a ⊕ c) ⊕ a = c`.
* `TCSlib.Cryptography.xorPerm_apply`: `xorPerm v y = y ⊕ v`.
* `TCSlib.Cryptography.mem_keys_of_lookup_isSome`: a key with a value in an association list is
  one of its keys.
* `TCSlib.Cryptography.ofFn_eq_map_range`, `ofFn_natAdd_eq_drop`, `decide_map_ofFn`: lists of
  tuples as maps over ranges, tails of tuples, comparing optional tuples through their lists.
* `TCSlib.Cryptography.length_flatten_map_const`, `length_flatten_map_range`: the length of a
  concatenation of equal-length blocks.
* `TCSlib.Cryptography.flatMap_range_drop`: reading the successive suffixes of a list.

## References

Generic list facts; no textbook counterpart.
-/

namespace TCSlib.Cryptography

/-- The head of a dropped list is the element at the dropping index:
`(l.drop i).headD d = l.getD i d`. -/
theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

/-- The head of the suffix of a tuple's list at an index is the tuple's entry there: for
`f : Fin n → α`, `i : Fin n` and any default `d`, `((List.ofFn f).drop i.val).headD d = f i`
(for bit vectors, `d = false` reads the `i`-th bit of the string `List.ofFn f`).

**Proof sketch.** By `headD_drop` the left side is the entry `(List.ofFn f).getD i d`; since
`i < n` it is the in-range entry `f i` (`List.getElem?_ofFn`). -/
theorem headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    ((List.ofFn f).drop i.val).headD d = f i := by
  simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt,
    Option.getD_some]

/-- **Flattening one-element blocks:** concatenating the one-bit blocks `g j` gives their bits,
`(List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j 0` when the blocks have
length `l = 1`.

**Proof sketch.** Induction on the number `k` of blocks (`List.ofFn_succ`, `List.flatten_cons`). -/
theorem flatten_ofFn_one {k l : ℕ} (hl : l = 1) (g : Fin k → Fin l → Bool) :
    (List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j ⟨0, by omega⟩ := by
  subst hl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, ih (fun j => g j.succ), List.ofFn_succ (n := k)]
    simp

/-- Flattening singletons: `(List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten =
List.ofFn f` when `p = 1` (`flatten_ofFn_one` with constant blocks). -/
theorem flatten_ofFn_singleton {p : ℕ} (hp : p = 1) :
    ∀ {k : ℕ} (f : Fin k → Bool),
      (List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten = List.ofFn f :=
  fun f => flatten_ofFn_one hp fun i _ => f i

/-- The bit of a one-bit output is the head of its string: `⟦f⟧.headD false = f 0`. -/
theorem headD_ofFn_one (f : Fin 1 → Bool) : (List.ofFn f).headD false = f 0 := by
  rw [List.ofFn_succ, List.headD_cons]

/-- Exclusive-or with the same list twice cancels: `(a ⊕ c) ⊕ a = c` for `|a| = |c|`. -/
theorem zipWith_xor_cancel_left {a c : List Bool} (h : a.length = c.length) :
    List.zipWith xor (List.zipWith xor a c) a = c := by
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp only [List.getElem_zipWith]
    cases a[i] <;> cases c[i] <;> rfl

section XorPerm

variable {n : ℕ}

/-- Exclusive-or with a fixed vector `v`, as a permutation of `{0,1}ⁿ`: `xorPerm v y = y ⊕ v`. -/
def xorPerm (v : Fin n → Bool) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun y i => xor (y i) (v i)) fun y => funext fun i => by
    simp

/-- `xorPerm v y = y ⊕ v`. -/
theorem xorPerm_apply (v y : Fin n → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl

end XorPerm

/-- A key with a value in an association list is one of its keys:
`(T.lookup x).isSome → x ∈ T.map Prod.fst`.

**Proof sketch.** Core's `List.lookup_isSome_iff` gives a pair `p ∈ T` with `x == p.1`, so `x`
is the first component of an element of `T` (`List.mem_map`). -/
theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α × β)) (x : α)
    (h : (T.lookup x).isSome = true) : x ∈ T.map Prod.fst := by
  obtain ⟨p, hp, hx⟩ := List.lookup_isSome_iff.1 h
  exact List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hx).symm⟩

/-! ### Lists indexed by ranges, tails and blocks of lists -/

/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for every `i : Fin r`, then
`List.ofFn f = (List.range r).map g` (both have `r` entries, entry `i` is `f i = g i`). -/
theorem ofFn_eq_map_range {α : Type*} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k` (`List.ofFn_add`). -/
theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
  rw [List.ofFn_add, List.drop_left' List.length_ofFn]

/-- Comparing strings is comparing their lists:
`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)` (`List.ofFn_inj`). -/
theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
  cases o with
  | none => simp
  | some c' => simp [List.ofFn_inj]

/-- Blocks of `k` entries, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
`k` entries (`List.length_flatten`, a sum of the constant `k`). -/
theorem length_flatten_map_const {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
  rw [List.length_flatten, List.map_map, show (List.length ∘ g) = fun _ => k from funext hg,
    List.map_const', List.sum_replicate_nat]

/-- `r` blocks of `k` entries have `r·k` entries: `|((range r).map g).flatten| = r·k` when
`g 0, …, g (r-1)` have `k` entries each (`List.length_flatten`, a sum of the constant `k`). -/
theorem length_flatten_map_range {β : Type*} (k r : ℕ) (g : ℕ → List β)
    (hg : ∀ i < r, (g i).length = k) : ((List.range r).map g).flatten.length = r * k := by
  rw [List.length_flatten, List.map_map,
    List.map_congr_left (f := List.length ∘ g) (g := fun _ => k)
      fun i hi => hg i (List.mem_range.1 hi),
    List.map_const', List.sum_replicate_nat, List.length_range]

/-- **Reading the suffixes of a list within at least its length many steps:** if `F [] = []`
and `F` reads only the first element of a nonempty suffix, `F (e :: t) = g e` for the members `e`
of `l`, then `(List.range m).flatMap (fun i => F (l.drop i)) = l.flatMap g` for every
`m ≥ |l|`.

**Proof sketch.** Induction on `l`: the first suffix is `l` itself, read as `g e`; the others are
the suffixes of the tail, within `m - 1` steps; the empty suffixes read `[]`. -/
theorem flatMap_range_drop {β γ : Type*} (F : List β → List γ) (g : β → List γ)
    (hnil : F [] = []) :
    ∀ (l : List β), (∀ e ∈ l, ∀ t, F (e :: t) = g e) → ∀ m : ℕ, l.length ≤ m →
      ((List.range m).flatMap fun i => F (l.drop i)) = l.flatMap g := by
  intro l
  induction l with
  | nil =>
    intro _ m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, hnil]
  | cons e t ih =>
    intro hcons m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      hcons e List.mem_cons_self, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih (fun e' he' => hcons e' (List.mem_cons_of_mem _ he')) m'
      (by rw [List.length_cons] at hm; omega)

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: the shape of the simulators of Proposition 161.5

The simulators `S_A` and `S_B` of [PS10, Proposition 161.5] restated for the helper modules
(which cannot import `SecureComputation/ObliviousTransfer.lean`, the owned file that imports them):
the coin segments, the simulated index and samples, and the two simulated views, with the
predicates `OT.IsSimA` and `OT.IsSimB` that the owned file proves for `otSimA` and `otSimB`.
On a tape assembled from typed coin blocks (`OT.splitLen`), the simulated views are computed
explicitly (`OT.simAView_layout`, `OT.simBView_layout`).

## Main definitions

* `OT.splitLen`: a coin string of length `c = a + b` as an `a`-bit and a `b`-bit string.
* `OT.simSeg`, `OT.simIndex`, `OT.simSampled`: a coin segment, the simulated index and a
  simulated sample (the bodies of `coinSeg`, `simIdx`, `simSample`).
* `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView`: the simulators' raw functions (the
  bodies of `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun`).
* `OT.IsSimA`, `OT.IsSimB`: machines of the simulators' shape.

## Main results

* `OT.splitLen_symm_ofFn`: the assembled tape is the concatenation of the blocks.
* `OT.simSeg_layout`, `OT.simIndex_layout`, `OT.simSampled_layout`: the pieces on such a tape.
* `OT.simAView_layout`, `OT.simBView_layout`: the simulated views on such a tape.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5 (book pp. 160–162).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### Splitting coin strings -/

/-- **A coin string of length `c = a + b` split** into its first `a` and last `b` bits:
`splitCoins a b` after the length cast `Fin c ≃ Fin (a + b)`. -/
def splitLen {a b c : ℕ} (h : c = a + b) : (Fin c → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (splitCoins a b)

/-- The tape assembled from two blocks is their concatenation:
`ofFn ((splitLen h).symm (r₁, r₂)) = ofFn r₁ ++ ofFn r₂` (`ofFn_splitCoins_symm`). -/
theorem splitLen_symm_ofFn {a b c : ℕ} (h : c = a + b) (p : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn ((splitLen h).symm p) = List.ofFn p.1 ++ List.ofFn p.2 := by
  rw [← ofFn_splitCoins_symm]
  exact (List.ofFn_congr h _).trans rfl

/-! ### The simulators restated -/

/-- The coin segment of length `q(n)` after the first `p(n)` coins of a raw layout `z` (the body
of `coinSeg`): `(inCoins z).drop p(|inParam z|) |>.take q(|inParam z|)`. -/
def simSeg (p q : PolyExpr) (z : List Bool) : List Bool :=
  ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take (q.eval (NUPPT.inParam z).length)

/-- The defining equation of `simSeg`: `simSeg p q z =
((inCoins z).drop p(|inParam z|)).take q(|inParam z|)`. -/
theorem simSeg_eq (p q : PolyExpr) (z : List Bool) :
    simSeg p q z =
      ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take
        (q.eval (NUPPT.inParam z).length) := rfl

/-- The simulated index (the body of `simIdx`):
`simIndex T z = fst Gen(inParam z; simSeg 0 coins_Gen z)`. -/
def simIndex (z : List Bool) : List Bool :=
  pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    (simSeg (.const 0) T.gen.coins z)))

/-- The defining equation of `simIndex`: `simIndex T z =
fst Gen.output (layout (inParam z) [] [] (simSeg 0 coins_Gen z))`. -/
theorem simIndex_eq (z : List Bool) :
    simIndex T z = pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      (simSeg (.const 0) T.gen.coins z))) := rfl

/-- A simulated sample after `p(n)` coins (the body of `simSample`):
`simSampled T p z = Sample(inParam z, simIndex z; simSeg p coins_Sample z)`. -/
def simSampled (p : PolyExpr) (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) [] (simSeg p T.sample.coins z))

/-- The defining equation of `simSampled`: `simSampled T p z =
Sample.output (layout (inParam z) (simIndex T z) [] (simSeg p coins_Sample z))`. -/
theorem simSampled_eq (p : PolyExpr) (z : List Bool) :
    simSampled T p z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIndex T z) []
        (simSeg p T.sample.coins z)) := rfl

/-- **`S_A`'s raw function** [PS10, Proposition 161.5] (the body of `otSimAFun`):
`simAView T z = ⟨⟨1^n, ⟨a₁, a₂⟩⟩, ⟨r_Gen, [⟨y₁, y₂⟩, []]⟩⟩` with two simulated samples
`y₁, y₂`. -/
def simAView (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (simSeg (.const 0) T.gen.coins z)
      (pairEncode (pairEncode (simSampled T T.gen.coins z)
          (simSampled T (.add T.gen.coins T.sample.coins) z))
        (pairEncode [] [])))

/-- The defining equation of `simAView`: `simAView T z = ⟨⟨inParam z, fst (inArg z)⟩,
⟨simSeg 0 coins_Gen z, [⟨y₁, y₂⟩, []]⟩⟩` with the two simulated samples `y₁, y₂`. -/
theorem simAView_eq (z : List Bool) :
    simAView T z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (simSeg (.const 0) T.gen.coins z)
          (pairEncode (pairEncode (simSampled T T.gen.coins z)
              (simSampled T (.add T.gen.coins T.sample.coins) z))
            (pairEncode [] []))) := rfl

/-- `S_B`'s mask `z_b = h(x) ⊕ a_b` (the body of `otSimZb`). -/
def simZbit (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
    (pairSndD (NUPPT.inArg z))

/-- The defining equation of `simZbit`: `simZbit T H z =
zipWith xor (H ⟨simIndex T z, simSampled T coins_Gen z⟩) (snd (inArg z))`. -/
theorem simZbit_eq (z : List Bool) :
    simZbit T H z =
      List.zipWith xor (H (pairEncode (simIndex T z) (simSampled T T.gen.coins z)))
        (pairSndD (NUPPT.inArg z)) := rfl

/-- `S_B`'s pair `(z₁, z₂)` (the body of `otSimZ`): `z_b` from `simZbit`, `z_{1−b}` one coin,
`simZpair T H z = ⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`. -/
def simZpair (z : List Bool) : List Bool :=
  if (pairFstD (NUPPT.inArg z)).headD false then
    pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
      (simZbit T H z)
  else
    pairEncode (simZbit T H z)
      (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)

/-- The defining equation of `simZpair`: `⟨c, z_b⟩` if the choice bit is set, else `⟨z_b, c⟩`,
with `c` the last coin segment and `z_b = simZbit T H z`. -/
theorem simZpair_eq (z : List Bool) :
    simZpair T H z =
      if (pairFstD (NUPPT.inArg z)).headD false then
        pairEncode (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
          (simZbit T H z)
      else
        pairEncode (simZbit T H z)
          (simSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z) := rfl

/-- **`S_B`'s raw function** [PS10, Proposition 161.5] (the body of `otSimBFun`):
`simBView T H z = ⟨⟨1^n, [b]⟩, ⟨r_B, [i, ⟨z₁, z₂⟩, []]⟩⟩`. -/
def simBView (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
      (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] []))))

/-- The defining equation of `simBView`: `simBView T H z = ⟨⟨inParam z, fst (inArg z)⟩,
⟨simSeg coins_Gen (2 coins_Sample) z, [simIndex T z, simZpair T H z, []]⟩⟩`. -/
theorem simBView_eq (z : List Bool) :
    simBView T H z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (simSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
          (pairEncode (simIndex T z) (pairEncode (simZpair T H z) (pairEncode [] [])))) := rfl

/-- **A machine of `S_A`'s shape**: coins `coins_Gen + (coins_Sample + coins_Sample)`, and
`S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
def IsSimA (S : NUPPT) : Prop :=
  S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
    ∀ n y (r : S.Coins n),
      S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))

/-- The defining property of `IsSimA`: `IsSimA T S` iff `S.coins = coins_Gen + (coins_Sample +
coins_Sample)` and `S(1^n, y; r) = simAView T (layout 1^n y [] r)`. -/
theorem isSimA_iff (S : NUPPT) :
    IsSimA T S ↔
      S.coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) ∧
        ∀ n y (r : S.Coins n),
          S.runAt n y r = simAView T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
  Iff.rfl

/-- **A machine of `S_B`'s shape**: coins `coins_Gen + (coins_Sample + (coins_Sample + 1))`, and
`S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
def IsSimB (S : NUPPT) : Prop :=
  S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
    ∀ n y (r : S.Coins n),
      S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r))

/-- The defining property of `IsSimB`: `IsSimB T H S` iff its coins are `coins_Gen +
(coins_Sample + (coins_Sample + 1))` and `S(1^n, y; r) = simBView T H (layout 1^n y [] r)`. -/
theorem isSimB_iff (S : NUPPT) :
    IsSimB T H S ↔
      S.coins = .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) ∧
        ∀ n y (r : S.Coins n),
          S.runAt n y r = simBView T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) :=
  Iff.rfl

/-! ### The simulators on assembled tapes -/

/-- A coin segment of a tape `A ++ (B ++ C)` with `|A| = p(|u|)` and `|B| = q(|u|)` is `B`. -/
theorem simSeg_layout {p q : PolyExpr} (u y α : List Bool) {A B : List Bool} (C : List Bool)
    (hA : A.length = p.eval u.length) (hB : B.length = q.eval u.length) :
    simSeg p q (NUPPT.layout u y α (A ++ (B ++ C))) = B := by
  rw [simSeg_eq, NUPPT.inCoins_layout, NUPPT.inParam_layout, List.drop_left' hA,
    List.take_left' hB]

/-- The typed tape of a machine as a list has the coin length: `|ofFn r| = coins_A(n)`. -/
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]

/-- On a tape starting with `Gen`'s coins `r`, the simulated index is `index n r`:
`simIndex T (layout 1^n y [] (ofFn r ++ B)) = T.index n r`. -/
theorem simIndex_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n) (B : List Bool) :
    simIndex T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ B)) = T.index n r := by
  have h := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y [] B
    (A := []) (B := List.ofFn r) (by rw [PolyExpr.eval_const, List.length_nil])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.nil_append] at h
  rw [simIndex_eq, h, NUPPT.inParam_layout, Collection.index_eq, NUPPT.runAt_eq,
    NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.gen_uniform]

/-- On a tape `r ++ (A ++ (s ++ C))` with `|A| = p(n) - coins_Gen(n)`, the simulated sample
after `p(n)` coins is `Sample(1^n, index n r; s)`. -/
theorem simSampled_layout {p : PolyExpr} (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (A : List Bool) (s : T.sample.Coins n) (C : List Bool)
    (hA : (List.ofFn r ++ A).length = p.eval n) :
    simSampled T p
        (NUPPT.layout (List.replicate n true) y [] (List.ofFn r ++ (A ++ (List.ofFn s ++ C)))) =
      T.sample.runAt n (T.index n r) s := by
  have h := simSeg_layout (p := p) (q := T.sample.coins) (List.replicate n true) y []
    (A := List.ofFn r ++ A) (B := List.ofFn s) C (by rw [hA, List.length_replicate])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.append_assoc] at h
  rw [simSampled_eq, h, NUPPT.inParam_layout, simIndex_layout,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq T.sample_uniform]

/-- **`S_A`'s view on the tape `r ++ (s₁ ++ s₂)`**:
`⟨⟨1^n, fst y⟩, ⟨r, [⟨Sample(i; s₁), Sample(i; s₂)⟩, []]⟩⟩` with `i = index n r`. -/
theorem simAView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (s₁ s₂ : T.sample.Coins n) :
    simAView T (NUPPT.layout (List.replicate n true) y []
        (List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂))) =
      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
        (pairEncode (List.ofFn r)
          (pairEncode (pairEncode (T.sample.runAt n (T.index n r) s₁)
              (T.sample.runAt n (T.index n r) s₂))
            (pairEncode [] []))) := by
  have h₀ := simSeg_layout (p := .const 0) (q := T.gen.coins) (List.replicate n true) y []
    (A := []) (B := List.ofFn r) (List.ofFn s₁ ++ List.ofFn s₂)
    (by rw [PolyExpr.eval_const, List.length_nil])
    (by rw [length_ofFn_coins, List.length_replicate])
  rw [List.nil_append] at h₀
  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂)
    (by rw [List.append_nil, length_ofFn_coins])
  have h₂ := simSampled_layout T (p := .add T.gen.coins T.sample.coins) n y r
    (List.ofFn s₁) s₂ [] (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins,
      PolyExpr.eval_add])
  rw [List.nil_append] at h₁
  rw [List.append_nil] at h₂
  rw [simAView_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, h₀, h₁, h₂]

/-- **`S_B`'s view on the tape `r ++ (s₁ ++ (s₂ ++ c))`**:
`⟨⟨1^n, fst y⟩, ⟨s₁ ++ s₂, [i, Z, []]⟩⟩` with `i = index n r`, `z_b = H ⟨i, Sample(i; s₁)⟩ ⊕ snd y`
and `Z = ⟨c, z_b⟩` if `(fst y).headD false`, else `⟨z_b, c⟩`.

**Proof sketch.** The coin segments of the tape are `s₁ ++ s₂` and `c` (`simSeg_layout`), the
simulated index is `index n r` (`simIndex_layout`) and the first simulated sample is
`Sample(i; s₁)` (`simSampled_layout`); rewrite `simBView`, `simZpair` and `simZbit` with them. -/
theorem simBView_layout (n : ℕ) (y : List Bool) (r : T.gen.Coins n)
    (s₁ s₂ : T.sample.Coins n) (c : Fin 1 → Bool) :
    simBView T H (NUPPT.layout (List.replicate n true) y []
        (List.ofFn r ++ (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c)))) =
      pairEncode (pairEncode (List.replicate n true) (pairFstD y))
        (pairEncode (List.ofFn s₁ ++ List.ofFn s₂)
          (pairEncode (T.index n r)
            (pairEncode
              (if (pairFstD y).headD false then
                pairEncode (List.ofFn c)
                  (List.zipWith xor (H (pairEncode (T.index n r)
                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
              else
                pairEncode (List.zipWith xor (H (pairEncode (T.index n r)
                    (T.sample.runAt n (T.index n r) s₁))) (pairSndD y))
                  (List.ofFn c))
              (pairEncode [] [])))) := by
  have hs := simSeg_layout (p := T.gen.coins) (q := .add T.sample.coins T.sample.coins)
    (List.replicate n true) y [] (A := List.ofFn r) (B := List.ofFn s₁ ++ List.ofFn s₂)
    (List.ofFn c) (by rw [length_ofFn_coins, List.length_replicate])
    (by rw [List.length_append, length_ofFn_coins, length_ofFn_coins, PolyExpr.eval_add,
      List.length_replicate])
  rw [List.append_assoc] at hs
  have hc := simSeg_layout (p := .add T.gen.coins (.add T.sample.coins T.sample.coins))
    (q := .const 1) (List.replicate n true) y []
    (A := List.ofFn r ++ (List.ofFn s₁ ++ List.ofFn s₂)) (B := List.ofFn c) []
    (by rw [List.length_append, List.length_append, length_ofFn_coins, length_ofFn_coins,
      length_ofFn_coins, PolyExpr.eval_add, PolyExpr.eval_add, List.length_replicate])
    (by rw [List.length_ofFn, PolyExpr.eval_const])
  rw [List.append_nil, List.append_assoc, List.append_assoc] at hc
  have hi := simIndex_layout T n y r (List.ofFn s₁ ++ (List.ofFn s₂ ++ List.ofFn c))
  have h₁ := simSampled_layout T (p := T.gen.coins) n y r [] s₁ (List.ofFn s₂ ++ List.ofFn c)
    (by rw [List.append_nil, length_ofFn_coins])
  rw [List.nil_append] at h₁
  rw [simBView_eq, simZpair_eq, simZbit_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, hs, hc,
    hi, h₁]

/-! ### The coin spaces -/

/-- **The real coins of a protocol of the shape of Protocol 160.4**: Alice's tape is `Gen`'s
coins and Bob's two sampler blocks, `ExecCoins ≃ Coins_Gen × (Coins_Sample × Coins_Sample)`. -/
def realCoins {π : Protocol} (hπ : IsOT T H π) (n : ℕ) :
    π.ExecCoins π.P (List.replicate n true) ≃
      T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
  Equiv.prodCongr
    (Equiv.arrowCongr (finCongr (by
      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1, List.length_replicate,
        NUPPT.coinLen_eq])) (Equiv.refl Bool))
    (splitLen (by
      rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.2.1, List.length_replicate,
        PolyExpr.eval_add, NUPPT.coinLen_eq]))

/-- Alice's real tape is `Gen`'s coins: `ofFn ((realCoins hπ n).symm p).1 = ofFn p.1`. -/
theorem realCoins_symm_fst_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((realCoins T H hπ n).symm p).1 = List.ofFn p.1 :=
  (List.ofFn_congr (by rw [Strategy.coinLen_eq, ((isOT_iff T H π).1 hπ).2.2.1,
    List.length_replicate, NUPPT.coinLen_eq]) _).trans rfl

/-- Bob's real tape is the two sampler blocks:
`ofFn ((realCoins hπ n).symm p).2 = ofFn p.2.1 ++ ofFn p.2.2`. -/
theorem realCoins_symm_snd_ofFn {π : Protocol} (hπ : IsOT T H π) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((realCoins T H hπ n).symm p).2 = List.ofFn p.2.1 ++ List.ofFn p.2.2 :=
  splitLen_symm_ofFn _ p.2

/-- **`S_A`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × Coins_Sample)` for a machine of
`S_A`'s shape. -/
def simACoins {S : NUPPT} (hS : IsSimA T S) (n : ℕ) :
    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n) :=
  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimA_iff T S).1 hS).1, PolyExpr.eval_add,
    NUPPT.coinLen_eq])).trans
    (Equiv.prodCongr (Equiv.refl _) (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])))

/-- `S_A`'s tape from blocks: `ofFn ((simACoins hS n).symm p) = ofFn p.1 ++ (ofFn p.2.1 ++
ofFn p.2.2)`. -/
theorem simACoins_symm_ofFn {S : NUPPT} (hS : IsSimA T S) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    List.ofFn ((simACoins T hS n).symm p) =
      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ List.ofFn p.2.2) := by
  rw [simACoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
    splitLen_symm_ofFn]

/-- **`S_B`'s coins**: `Coins_S ≃ Coins_Gen × (Coins_Sample × (Coins_Sample × {0,1}))` for a
machine of `S_B`'s shape. -/
def simBCoins {S : NUPPT} (hS : IsSimB T H S) (n : ℕ) :
    S.Coins n ≃ T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool))) :=
  (splitLen (by rw [NUPPT.coinLen_eq, ((isSimB_iff T H S).1 hS).1, PolyExpr.eval_add,
    NUPPT.coinLen_eq])).trans
    (Equiv.prodCongr (Equiv.refl _) ((splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq])).trans
      (Equiv.prodCongr (Equiv.refl _)
        (splitLen (by rw [PolyExpr.eval_add, NUPPT.coinLen_eq, PolyExpr.eval_const])))))

/-- `S_B`'s tape from blocks: `ofFn ((simBCoins hS n).symm p) =
ofFn p.1 ++ (ofFn p.2.1 ++ (ofFn p.2.2.1 ++ ofFn p.2.2.2))`. -/
theorem simBCoins_symm_ofFn {S : NUPPT} (hS : IsSimB T H S) (n : ℕ)
    (p : T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) :
    List.ofFn ((simBCoins T H hS n).symm p) =
      List.ofFn p.1 ++ (List.ofFn p.2.1 ++ (List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2)) := by
  rw [simBCoins, Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.symm_trans_apply, splitLen_symm_ofFn, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, Equiv.refl_symm, Equiv.refl_apply, splitLen_symm_ofFn]

/-! ### The OT inputs and outputs -/

/-- Alice's OT input length is `2`, `otFunctionality.inA.eval n = 2` (`otFunctionality_inA`). -/
theorem inA_eval (n : ℕ) : otFunctionality.inA.eval n = 2 := by
  rw [otFunctionality_inA, PolyExpr.eval_const]

/-- Bob's OT input length is `1`, `otFunctionality.inB.eval n = 1` (`otFunctionality_inB`). -/
theorem inB_eval (n : ℕ) : otFunctionality.inB.eval n = 1 := by
  rw [otFunctionality_inB, PolyExpr.eval_const]

/-- Alice's OT input read as two bits: `inA2 a j = a (cast j)`. -/
def inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) : Fin 2 → Bool :=
  fun j => a (Fin.cast (inA_eval n).symm j)

/-- The defining equation of `inA2`: `inA2 a j = a (Fin.cast (inA_eval n).symm j)`. -/
theorem inA2_apply {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) (j : Fin 2) :
    inA2 a j = a (Fin.cast (inA_eval n).symm j) := rfl

/-- Reading the input as two bits keeps its string: `ofFn (inA2 a) = ofFn a`. -/
theorem ofFn_inA2 {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) :
    List.ofFn (inA2 a) = List.ofFn a :=
  ((List.ofFn_congr (inA_eval n) a).trans rfl).symm

/-- Bob's OT input read as one bit: `inB1 b j = b (cast j)`. -/
def inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) : Fin 1 → Bool :=
  fun j => b (Fin.cast (inB_eval n).symm j)

/-- The defining equation of `inB1`: `inB1 b j = b (Fin.cast (inB_eval n).symm j)`. -/
theorem inB1_apply {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) (j : Fin 1) :
    inB1 b j = b (Fin.cast (inB_eval n).symm j) := rfl

/-- Reading the input as one bit keeps its string: `ofFn (inB1 b) = ofFn b`. -/
theorem ofFn_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (inB1 b) = List.ofFn b :=
  ((List.ofFn_congr (inB_eval n) b).trans rfl).symm

/-- Bob's choice string is the one-bit list `[inB1 b 0]`: `List.ofFn b = [inB1 b 0]`. -/
theorem ofFn_eq_inB1 {n : ℕ} (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn b = [inB1 b 0] := by
  rw [← ofFn_inB1, List.ofFn_succ, List.ofFn_zero]

/-- Alice's OT output is empty: `ofFn (f n a b).1 = []`. -/
theorem ofFn_f_fst (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (otFunctionality.f n a b).1 = [] :=
  List.eq_nil_of_length_eq_zero
    (by rw [List.length_ofFn, otFunctionality_outA, PolyExpr.eval_const])

/-- Bob's OT output is the chosen bit: `ofFn (f n a b).2 = [a_b]` with
`a_b = inA2 a (if inB1 b 0 then 1 else 0)` (`otFunctionality_f_snd_apply`). -/
theorem ofFn_f_snd (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    List.ofFn (otFunctionality.f n a b).2 = [inA2 a (if inB1 b 0 then 1 else 0)] := by
  have h : otFunctionality.outB.eval n = 1 := by
    rw [otFunctionality_outB, PolyExpr.eval_const]
  rw [List.ofFn_congr h, List.ofFn_succ, List.ofFn_zero, otFunctionality_f_snd_apply]
  rfl

end TCSlib.Cryptography.SecureComputation.OT

## ===== TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin strings of the IND ⇒ SIM machines

A local fact used by the two machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] (the
simulator and the NM adversary): a machine's coin string has `coins(n)` bits
(`length_ofFn_coins`).

The generic facts first proved here now live in shared modules: the readers of a round input are
`Games.InteractiveHandler.rU`, …, `rAns`; the calls and finalizations whose rounds return at once
or after one outer query are `Games.InteractiveHandler.impl_of_ret_padFin`,
`impl_of_query_padFin` and `finish_of_ret_padFin`; the cost of a one-shot oracle is
`Games.simulate_costBoundedBy_once`; the split of a padded concatenation is
`Games.padFin_append_split`; the seeds made of coins are `EnsembleLemmas.seedEquiv` and
`EnsembleLemmas.seedEquivPoly`.

## Main results

* `NMSim.length_ofFn_coins`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- A machine's coins have `coins(n)` bits: `|⟦r⟧| = A.coins.eval n`. -/
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]

end TCSlib.Cryptography.Composability.NMSim
