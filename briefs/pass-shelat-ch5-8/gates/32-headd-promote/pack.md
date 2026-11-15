# Gate 32 · Promotion of `headD_drop_ofFn` to the shared bit-list layer (Gate 29 G29-02)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). A small
promotion/refactor PR: one new public lemma and one proof-only re-derivation.

- **PR:** draft [PR #316](https://github.com/Shilun-Allan-Li/tcslib/pull/316) at
  `c18afbe66101381eed1617801d942dcf691506ea` (branch `promote/pass-shelat-headd-ofFn`, tree
  `68caf9d0f20e2ef9c51d2794dd5c248766337e50`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `dd98360d4886ac68fab34899b8bd0d12ae9a0aef`, its parent and the merge base with the tip. (GitHub's PR record still
  shows base `0e5e725d`, the tip when the PR was opened.)
  - From the base to the records tip `e99987221593020b9f7dbb87fe577bd6aac5ecbb` there are 11 commits. Their only
    non-record paths are #314's two Lean files, `Pseudorandom/Functions/Defs.lean` and
    `Encryption/PrivateKey/EncryptThenTag/Reduction.lean` (**#314 merged at `59c2c1fb`**, second parent `a24a6313`,
    after LE-gate30). Neither is a PR path. Re-checked for this pack from git objects (`pack-checks/` in
    `verification.zip`): `Pseudorandom/Functions/Defs` **is in the closure of `Lamport/MachineSpec`** (through
    `Lamport/Machine`, `Games/Efficiency`, `Efficiency/OracleBridge` and `Functions/Asymptotic/Defs`;
    `downstream314.txt`); `BitLists` is downstream of neither #314 file, and `EncryptThenTag/Reduction` is downstream
    of `BitLists`. 91 TCSlib/audits tip modules are downstream of both a #314 module and a #316 module.
    `git merge-tree --write-tree` of the head with the tip gives tree `7d5ec65a595c605afeaccfe0e40d8220629500d7` with
    no conflict; it differs from the head exactly in #314's two files and from the tip exactly in the PR's two
    (`mergetrees.txt`). **Pending merge condition** (not an audit item): #316 needs an integration rebuild of the
    downstream of `BitLists` and `MachineSpec` on the merged tip before it merges; the maintainer runs that build
    (question 6).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...c18afbe6`, which equals `dd98360d..c18afbe6`
    byte for byte, and also equals the evidence entry `checks/promote.diff` (2 paths, 18 insertions, 4 deletions).
- **Commits:** 1, by the maintainer (author and committer Claude, SSH-signed by the environment default):
  `c18afbe6` "Promote headD_drop_ofFn to the shared list layer (Gate 29 G29-02, Seyoon 2026-11-15)", cut on
  `dd98360d` and not rebased (`evidence/checks/commit.txt`).
- **Scope:** a **promotion audit**. Seyoon's ruling on Gate 29's major G29-02 (2026-11-15, "promote it now"): publish
  the generic reader in a shared list layer upstream of both consumers, and re-derive Lamport's public copy from it
  with a proof-only change that keeps its API. #313 then re-points `firstBit_of_pos` by a proof-only landing edit,
  LE-gate29b, on its own branch, and Gate 29 round 2 follows; that edit is **not** part of this PR.

## What changed

Paths are under `TCSlib/Cryptography/`. 2 Lean files, both modified (18 insertions, 4 deletions).

| File | Lines | Change |
|---|---:|---|
| `Foundations/BitLists.lean` | 179 → 192 | one `## Main results` bullet; the new theorem after `headD_drop`, in namespace `TCSlib.Cryptography` |
| `Authentication/Signatures/Lamport/MachineSpec.lean` | 268 → 269 | `LamportFill.headD_drop_ofFn`: body replaced by the new lemma; one docstring paragraph inserted |

The new theorem (formula docstring, proof sketch, no attribute):

```lean
theorem TCSlib.Cryptography.headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    ((List.ofFn f).drop i.val).headD d = f i
```

Its proof is the Lamport proof verbatim (`simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
dif_pos i.isLt, Option.getD_some]`). It generalizes `LamportFill.headD_drop_ofFn` from `Bool` with default `false` to
any `α : Type*` and any default `d`. `LamportFill.headD_drop_ofFn` is now
`:= TCSlib.Cryptography.headD_drop_ofFn m i false`, and its docstring gains "This is the published
`TCSlib.Cryptography.headD_drop_ofFn` at `α = Bool` and `d = false`." No import changes in either file.

**Statements:** decls2 against `dd98360d` gives 1 ADDED (the new theorem), 0 CHANGED, 0 REMOVED
(`evidence/statements/decls2-vs-parent.tsv`, `decls2.err` empty). All 23 pre-existing declaration headers of the two
files (14 in `BitLists`, 9 in `MachineSpec`) are byte-identical (`evidence/statements/header-bytes-vs-parent.txt`; the
one MISSING row is the new theorem). `touched`: 1 ADDED, 1 CHANGED (`LamportFill.headD_drop_ofFn`, body and
docstring), 22 UNCHANGED. Re-checked for this pack from git objects: decls2's parser gives 1 ADDED and 23 unchanged
against both `dd98360d` and the tip (`pack-checks/decls2-vs-*.tsv`); every base header is identical, every base
docstring but `LamportFill.headD_drop_ofFn`'s is identical, and the order is kept (`pack-checks/headers.txt`).

## Rulings and records in force

1. **G29-02 (Seyoon, 2026-11-15): promote it now.** Codex's Gate 29 major: #313's new public
   `LearnPRF.firstBit_of_pos` (`Randomness/Learning/Random.lean:66–69`) re-proves the index-0 case of the public
   `LamportFill.headD_drop_ofFn` (`gates/29-learning/findings/gate29-learning-findings.md`, G29-02). The ruling
   (`gates/29-learning/resolutions-r1.md`; decision-log rows of 2026-11-15): a small PR promotes the reader to a shared
   list layer upstream of both consumers and re-derives Lamport's copy proof-only; after it merges, #313 re-points
   `firstBit_of_pos` (LE-gate29b) and Gate 29 has a round 2.
2. **DL-47 (duplication ledger, Seyoon 2026-11-15: "Ledger row, dispatch now").** The copies of the fact that
   predate the promotion, found at Gate 32 staging (question 3), are recorded as **DL-47, Open (deferred)**, with
   `TCSlib.Cryptography.headD_drop_ofFn` (#316) as the existing copy. They are not re-pointed in #316, which does not
   change: NextBit:454 and the index-0 cases move onto `headD_drop_ofFn`, and the getD forms onto one shared getD
   reader, in the deferred cleanup; Yao's private `getD_ofFn'` waits for sc-garble and sc-yao (`Yao.lean` is shared).
   The row is in the bundle's `duplication-ledger.md` (at the records pin). **Not a finding:** any copy DL-47 lists.
   DL-45 (the learning unit's overlaps) stays open; G29-01 is fixed by LE-gate29a (`94b31964`, #313), and G29-02 by
   this PR with LE-gate29b.
3. **The earlier consolidation (dl-consolidation, item L1, Gate 20).** `Foundations/BitLists.lean` was created by
   dl-consolidation (merged); its item L1 replaced `CommitmentLemmas.headD_drop`, `BitwiseSim.headD_drop`, **NextBit's
   private `headD_drop_ofFn`** and `GI.getD_eq_headD_drop` by the generic `headD_drop`, and NextBit's one use became the
   inline rewrite chain `headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn` (`fills/dl-consolidation/
   issued-r1/brief.md` § L; `gates/20-dl-consolidation/worker-report.md`, L1 and "Re-pointing changes"). L3 moved
   `headD_ofFn_one` into `BitLists`.
4. **Rule 10.** `PolyExpr.eval` is notation (Q1, 2026-11-07; seal A canonical, B also reported); a `CoeFun`/`Coe`
   instance whose body is a structure projection is notation (Seyoon, 2026-11-14; coe seals canonical, strict run and
   attributed). For this PR strict and coe agree in every row.
5. **Lint, #305 baseline.** `campaign_style_lint.py TCSlib/Cryptography --check8b` gives **92 FAIL / 101 WARN** at
   the parent and at the head, with identical FAIL and WARN lines; the full diff is the two INFO lines (line counts,
   and `BitLists`' public count 14 → 15) (`evidence/lint/`).
6. **Policy** (`policy.md`, in the bundle). §2: a purely technical glue lemma with no textbook counterpart may omit
   the source tag (`BitLists`' module docstring: "Generic list facts; no textbook counterpart"); every public
   statement's docstring states its formula. §3: nontrivial proofs carry a `**Proof sketch.**`. The definitions rule:
   core and Mathlib definitions are not passed to `simp`/`rw`/`unfold`; their lemmas are.

## Questions for the audit

**1. Placement and identity**
- Is `Foundations/BitLists.lean`, after `headD_drop` (which the proof uses) and before `headD_ofFn_one`, the right
  home, and is the name `TCSlib.Cryptography.headD_drop_ofFn` appropriate beside the kept
  `Authentication.LamportFill.headD_drop_ofFn`?
- Does the PR add no import cycle and no import beyond what it discloses? `pack-checks/imports.txt`: the import lines
  of both files are identical at the parent and the head; `BitLists` imports four Mathlib modules and no project
  module, so its project closure is empty and no cycle is possible; `MachineSpec` imports it directly; #313's
  `Learning/Random` (at `94b31964`) reaches it through `Learning/Law`, `Distinguisher`, `Sample`,
  `FromPRF/ReductionMachine`, `Asymptotic/EnsemblesLemmas` and `Asymptotic/Adversary`; 5 of #315's 6 changed modules
  already have it in their closure. The maintainer's alternative, `Asymptotic/ReductionSupport.lean`, is in both
  closures but imports 5 project modules (`evidence/checks/imports.txt`). 244 modules are downstream of `BitLists`
  and 5 of `MachineSpec` (the record's 245 and 6 count the module itself).
- Name resolution (`pack-checks/namecheck.txt`): the only unqualified use is `run_input`'s `rw [..., headD_drop_ofFn]`
  (`MachineSpec.lean:218`) inside namespace `TCSlib.Cryptography.Authentication.LamportFill` with `open
  TCSlib.Cryptography`. Lean resolves the innermost namespace first, so it still names the Lamport lemma. No other
  file names `headD_drop_ofFn` at the head, the tip, #313 or #315. Every downstream module with a same-source
  reference built a byte-identical olean (249 of 253; `landing/build-refcmp.txt`). Does that settle that no downstream
  elaboration changed?
- Is the statement as general as it should be (any `α : Type*`, any default `d`; `i : Fin n` rather than `i : ℕ` with
  `i < n`), and is `[propext]` alone, the axiom set of both lemmas, expected?

**2. The Lamport re-derivation (proof only, API unchanged)**
- Is `LamportFill.headD_drop_ofFn`'s header byte-identical (`evidence/statements/docstring-header-Lamport.txt`: header
  identical; its `RESULT FAIL` is the docstring comparison, by design) and is the only other change one inserted
  docstring paragraph (`evidence/statements/docstring-delta-Lamport.txt`, a pure insertion;
  `pack-checks/headers.txt`)? Does its use in `run_input` build unchanged (`landing/root-checks.jsonl`), and do
  `run_input` and `Authentication.lamport_oneTimeSecure` keep `[propext, Classical.choice, Quot.sound]`
  (`landing/axioms-head.txt`)?
- The Lamport lemma is kept, as the ruling says, so `MachineSpec` keeps its 9 public declarations. Is keeping it
  (rather than deleting it and re-pointing `run_input`) right for a promotion under the frozen-API rule?

**3. Other copies of the fact (DL-47; recent gates graded undisclosed duplicates of public lemmas as majors)**
- Known and to be re-pointed after this merges: #313's `firstBit_of_pos` (G29-02; LE-gate29b, the PR draft's shape
  `rw [firstBit_eq]; simpa only [List.drop_zero] using TCSlib.Cryptography.headD_drop_ofFn y ⟨0, hn⟩ false`, matched by
  statement only, not run).
- **Disclosed and ruled as DL-47 debt, not findings of this gate** (ruling 2). Found by the maintainer for this pack
  (`pack-checks/dupscan.txt`, the candidate statements and proof lines; `pack-checks/relatives-tip.txt`, the ones read
  by hand, with `path:line` at the tip as in DL-47; `relatives.txt` gives them at the head, where `headD_ofFn_one` is
  line 88). Every `Cryptography/` file below already has `BitLists` in its closure except
  `ZeroKnowledge/Encoding.lean`.
  - **Inline headD chain:** `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn`), the inline remnant of NextBit's former private `headD_drop_ofFn` (ruling 3).
  - **The headD form at index 0:** `headD_ofFn_one` (`BitLists.lean:75` at the tip, `(List.ofFn f).headD false = f 0`
    for `f : Fin 1 → Bool`), `GIZK.headD_ofFn_block` (`GraphIsomorphismZK/Closeness.lean:280`), the private
    `eq_const_headD` (`NonMalleability/Simulation/SimIND.lean:88`).
  - **The getD form** `(List.ofFn f).getD i d = f i`: `GI.getD_ofFn_lt'` (`GraphIsomorphism/SoundnessRep.lean:61`),
    `GI.getD_ofFn_lt` (`GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt`
    (`GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ThreeColoring/ProtocolProofs.lean:391`),
    Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`).
  - **Inline getD chains** (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`):
    `ThreeColoring/Simulator.lean:861`, `ThreeColoring/Language.lean:429` (in the private `ofFn_getD_tape`),
    `ZeroKnowledge/Encoding.lean:359`, and outside the cryptography files `TCSlib/Complexity/ClassNP/SAT.lean:149`,
    `ClassNP/Tautology.lean:142` and `SpaceComplexity/Codec/Word.lean:135`.
  - No core or Mathlib lemma states either form (a text search of the toolchain's `Init/Data/List/OfFn.lean`, Mathlib
    and Batteries finds `List.getElem?_ofFn`, `List.getElem_ofFn` and `List.head_ofFn` only). #315's changed files add
    no copy (`dupscan.txt`, its section).
- **Your task here:** look for **further** copies of the fact, public or private, statement-level or inline, that
  DL-47 does not list (in `TCSlib/` or `audits/` at the head, or in #313's and #315's changed files). Any such copy is
  a **major** under the usual rule. Is the DL-47 list accurate (each entry really the fact or its getD form, each
  `path:line` right)? You may note whether the getD form is the better shared reader for the cleanup.

**4. Rule 10**
- Seals A and B, strict and coe, pass for both changed files (requests: `MachineSpec` strict 2088 (A) and 2089 (B),
  coe 2087 and 2088; `BitLists` 0 in every variant; `evidence/rule10/seals-*.tsv`). `BitLists`' closure has no TCSlib
  module, so its request set is empty and its seals are **vacuous**; its proofs read only Mathlib/core lemmas and its
  own `headD_drop`. Is that an adequate Rule-10 record for a Mathlib-only file?
- The paired controls (the Lamport review rows `padFin`, `ProbComp.expect`, `ProbComp.sample`, `OracleComp.bind`,
  `LamportFill.secretWord`, `LamportFill.signatureBlock`, `LamportMachine.u`, and `PolyExpr.eval` in B, selected by
  covering subset from `MachineSpec`'s records; the unmodified `mkctl_lamport.py`) are ALL_OK in both harnesses: 4
  probes and 15 sealed negatives each (A 7, B 8), each sealed negative failing exactly once
  (`evidence/rule10/ctlcheck-*.log`). No control row can apply to `BitLists`. Do the controls bite for the one file
  that has a request set? `probe-copies-check.txt`: 18 worktree probe sources equal the evidence copies.
- Does the new proof read only published readers? Its `simp only` list names the theorems quoted above and no
  definition; the re-derived Lamport body is a term application of a theorem.

**5. The docstring and sketch rules**
- Is the new docstring's formula right with the arguments in Lean order (`((List.ofFn f).drop i.val).headD d = f i`,
  with the bit-vector remark "`d = false` reads the `i`-th bit of the string `List.ofFn f`")? Is omitting a source tag
  right for this glue lemma (policy §2; the module's References section)?
- Is the `**Proof sketch.**` ("By `headD_drop` the left side is the entry `(List.ofFn f).getD i d`; since `i < n` it
  is the in-range entry `f i` (`List.getElem?_ofFn`)") accurate, and acceptable in naming lemmas (policy §3 asks for
  mathematical English; a one-line `simp only` may need no sketch at all)?
- Are the new `## Main results` bullet and the inserted Lamport docstring paragraph accurate? A misstated formula is a
  minor.

**6. Downstream effects and the merge interaction**
- **The G29-02 consumer.** After #316 merges, #313 (`94b31964`, Gate 29 HOLD) re-points `firstBit_of_pos` by
  LE-gate29b; no import is needed. Is the promoted statement enough for that re-point (index `⟨0, hn⟩`, after
  `firstBit_eq` and `List.drop_zero`)? `git merge-tree --write-tree c18afbe6 94b31964` gives
  `718840dc34d7b9531663ba18878eb9831591d011` with no conflict; not built.
- **#315** (`fbd37f44`, prf-long, Gate 31) is open and touches neither file; `BitLists` is in 5 of its 6 changed
  modules' closures. `git merge-tree --write-tree c18afbe6 fbd37f44` gives
  `55cc92c2508777629b9a0000490bc0203c8065d3` with no conflict, differing from #315 exactly in the PR's two files; not
  built.
- **Pending merge condition (not an audit item).** The build ran on a tree at the `eff2dcd0` base with the PR at
  `dd98360d`, without #314. Because #314 merged first and `MachineSpec` is downstream of its `Functions/Defs`, #316
  needs an integration rebuild of the downstream of `BitLists` and `MachineSpec` on the merged tip before it merges
  (it contains the 91 modules downstream of both a #314 and a #316 module, `pack-checks/downstream314.txt`). The
  maintainer runs that build; treat it as a condition on the merge, not as something for this audit to establish. What
  you can raise: a concrete reason the merged tree cannot build, or a name or instance interaction. Of the 253 built
  modules, 252 have the merged tree's source; the other is #314's `EncryptThenTag/Reduction`
  (`pack-checks/srcequality.txt`).
- **Records downstream.** The issued `sc-garble` brief's search-first list names `headD_drop_ofFn` and
  `LamportFill.headD_drop_ofFn` (`fills/sc-garble/issued-r1/brief.md`, the overlap rule); both names stay valid. Its
  issue base `fbd37f44` does not contain the new lemma.

## Known dispositions (not findings)

- **The build base.** The 253-module queue is the 245 modules of `BitLists`, `MachineSpec` and their downstream united
  with the 65 of the #303/#306–#309, #311 and #312 base delta and its downstream, through root `TCSlib`,
  `audits/garg-ch1-3/Checks` and `audits/pass-shelat/Checks`. 253/253 rc 0, 0 errors in both diagnostic forms; the 24
  sorries are all pre-existing (including #312's two stated `SeedMajority` sorries). Every built module's
  `source_sha256` equals the blob at `c18afbe6` (checked for this pack; `pack-checks/srcequality.txt`).
- **The restore.** The first restore rebuild used an alphabetical order and failed on `Authentication` (an olean of the
  head layout had been deleted with the extras); the replanned imports-first restore rebuilt 11 modules, each equal to
  the base record, and the whole-tree check is RESULT OK with the snapshot equal to the pre-run snapshot
  (`evidence/restore/tree-check-post.txt`; `PROVENANCE.txt`). Disclosed by the maintainer.
- **`rule10.sh`'s final display line** was corrected after the run; its outputs are unaffected (`PROVENANCE.txt`).
- **The PR description differs from the records draft.** `maintainer/promote-headd-2026-11-15/pr-body.md` (also in the
  evidence ZIP; `PROVENANCE.txt` calls it "draft PR description (not opened; nothing pushed)") is the long draft; its
  evidence line still names the scratch paths `dl-review/promote-headd*`, since filed under
  `maintainer/promote-headd-2026-11-15/`. The opened description (`pr-description.md`, fetched 2026-11-15) is a shorter
  rewrite. The Lean file is authoritative. What you can raise: a claim in either description that is false.
- **"No open PR touches it"** (both descriptions) was written when #313 and #314 were the open PRs; #315, opened later,
  touches neither file either.

## Also check

**Axioms:** `TCSlib.Cryptography.headD_drop_ofFn` and `LamportFill.headD_drop_ofFn` print `[propext]`;
`LamportFill.run_input` and `Authentication.lamport_oneTimeSecure` print `[propext, Classical.choice, Quot.sound]`; the
log also has the `#check` of both elaborated statements (`landing/axioms-head.txt`).

**Sizes and widths:** `BitLists.lean` 192 lines, `MachineSpec.lean` 269, both with maximum width 100 and no line over
100 at the parent and the head (`source-head.json`, `evidence/checks/widths.txt`).

**Build:** 253/253 rc 0, 0 errors in both diagnostic forms, through root `TCSlib` and both `audits/*/Checks`
(`landing/root-checks.jsonl`, whose last line is the runner's `done` record; `evidence/build/summary.txt`); `BitLists`
0 warnings, `MachineSpec` its 2 inherited warnings. The olean tree was restored to the base snapshot.

## Evidence

- **`verification.zip`** (62 entries): byte-identical originals; `SHA256SUMS` lists every other entry and
  `PROVENANCE.txt` gives each entry's source.
  - `promote-headd-evidence.zip` (`maintainer/promote-headd-2026-11-15/`, SHA-256 `5efc53e2…`) and
    `evidence-SHA256SUMS`, its manifest: 518 entries, 41 directory entries and 477 files, exactly the 476 manifest
    paths plus `SHA256SUMS` (byte-identical to the manifest); every hash verifies. It covers the patch and diff, the
    commit, imports, statements, the build with the olean comparison, axioms, seals and controls, lint, the restore,
    the pre-commit trial and the tools used;
  - `records/` (8): `PROVENANCE.txt` and `pr-body.md` beside the ZIP (each equal to the ZIP entry), the decision log,
    the duplication ledger (before DL-47, which is in the bundle's ledger at the pin), Codex's Gate 29 findings and
    Gate 29's round-1 resolutions, and the dl-consolidation brief and worker report, at records
    `e99987221593020b9f7dbb87fe577bd6aac5ecbb`;
  - `evidence/` (30): byte copies of the ZIP entries this pack cites;
  - `pack-checks/` (20): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`),
  `build-refcmp.txt` (= `build/refcmp.txt`), `axioms-head.txt` (= `axioms/AxiomsHead.log`).
- **`pr-description.md`:** the PR #316 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (2 paths, 18 insertions, 4 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 2 changed files.
- **`sources.zip`:** the source closure at the head of both changed modules, 149 files.
- **The bundle** adds, as context: `Pseudorandom/NextBit.lean` at the head (the inline chain of question 3), and #313's
  `Randomness/Learning/Random.lean` and `Learning/Sample.lean` at `94b31964` (`firstBit_of_pos` and `firstBit_eq`, the
  G29-02 consumer).

## Findings delivery

Return `gate32-headd-promote-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a changed API of `LamportFill.headD_drop_ofFn`, a cycle, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read not covered by the rulings, an undisclosed duplicate of a
  public lemma (or an undisclosed copy left behind that this PR claims to remove), or necessary evidence that cannot be
  verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
