## ===== briefs/pass-shelat-ch5-8/gates/32-headd-promote/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/findings/gate29-learning-findings.md =====

# Pass–shelat Gate 29 — learning

**Verdict: HOLD.** The proof, frozen statements and supplied seal evidence pass inspection. Two further undisclosed re-proofs remain outside the worker’s overlap table and DL-45. Under the pack’s severity rule, both are majors.

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 2 | 0 | 0 |

| Pin | Audited revision |
|---|---|
| PR | [Shilun-Allan-Li/tcslib #313](https://github.com/Shilun-Allan-Li/tcslib/pull/313), draft |
| Lean head | `8befc58966fd39f974a54250849736df194584b9` |
| PR base | `4561c3407f9f015da55255a6a4cbcfc5840fd1f3` |
| Campaign records | `7bd85992f8bd61df48f43092bc5c845d5fac1b27` |
| Exchange | `341f61def10e0481a7c29fa4787a80d6ece7d5df` |

## Findings

All source line numbers below refer to the audited head.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G29-01 | major | `Randomness/Learning/Random.lean:172–179`, local `hj` in `abs_gameProb_random_sub_half_le` | The remaining collision calculation re-proves the public constant-average lemma inline. | After `uprob_prod` and `uprob_eq_point`, lines 176–179 expand `uexp_def`, sum the constant, prove positive cardinality and cancel the denominator. This is `OneWay.uexp_const`, `OneWayFunctions/Basic.lean:69–73`, already public at the PR base and already called at line 170. Neither the overlap table nor DL-45 discloses this additional re-proof. | Replace the constant-average calculation by `OneWay.uexp_const`; preserve the theorem header. |
| G29-02 | major | `Randomness/Learning/Random.lean:66–69`, `firstBit_of_pos` | This new public theorem independently re-proves the zero-index case of an existing public bit reader. | After `firstBit_eq`, its conclusion is `(List.ofFn y).headD false = y ⟨0, hn⟩`. Public `Authentication.LamportFill.headD_drop_ofFn`, `Authentication/Signatures/Lamport/MachineSpec.lean:195–199`, gives that equation at index `⟨0, hn⟩` after `List.drop_zero`. The reader is present and unchanged at the PR base. This overlap is absent from the worker’s table and DL-45. | Re-derive the theorem through an existing reader, or obtain an explicit disposition for this additional overlap. Importing the cited Lamport helper is acyclic; a shared reader can also avoid that additional import. |

### G29-01: exact remaining overlap

The unreused mathematical step is

```lean
uexp (fun _ : ((Fin m → Fin n → Bool) × ρ) => (1 : ℝ) / 2 ^ n)
  = (1 : ℝ) / 2 ^ n
```

The averaging type is finite and nonempty under the theorem’s existing hypotheses, exactly as required by `OneWay.uexp_const`. The surrounding Fubini step and point-mass specialization remain useful glue. The duplicated part is the subsequent sum-and-cancellation proof.

A replacement proof shape for `hj` is:

```lean
    intro j
    rw [uprob_prod]
    simp only [uprob_eq_point, OneWay.uexp_const]
```

This needs no new import. LE-reuse correctly repairs its two listed overlaps, but leaves this separate occurrence unchanged. DL-45’s coupling-bound disposition does not identify this constant-average re-proof.

### G29-02: exact specialization

The existing reader says

```lean
((List.ofFn y).drop i.val).headD false = y i
```

Specializing `i` to `⟨0, hn⟩` and rewriting `List.drop_zero` gives the new theorem’s entire conclusion after `firstBit_eq`. Its current proof instead splits the positive length and uses `List.ofFn_succ` and `List.headD_cons` to establish that conclusion again.

For example, after importing the cited helper, a replacement proof shape is:

```lean
  rw [firstBit_eq]
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.Authentication.LamportFill.headD_drop_ofFn y ⟨0, hn⟩)
```

The overlap table’s `firstBit` row explains its relationship to the owned `prfConcept`; it does not disclose this relationship to the existing bit reader. DL-45 records the flip operations and other named overlaps, but not `firstBit_of_pos`. The replacement snippets above were checked by statement matching, not by a new Lean run.

## Proof audit

The delivered proof establishes the frozen prediction statement on inspection, following the first-output-bit concept of [PS10, §8.1, Theorem 179.1, book p. 179](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf#page=191).

1. **Efficient distinguisher.** `exists_learnDist` calls the public `MultiMsg.exists_queryChain_nuppt` with zero message vectors and a polynomial-time learner/verdict machine. Its coin equivalence supplies exactly `m(n) + 1` uniform points and the learner’s coins. The public chain contract gives the stated verdict within budget `m(n) + 1`; it introduces no timeout discrepancy. The disclosed substitution for T1/T4 is valid.
2. **Real-game law.** `iid_uniform`, the product-uniform readers and `snocEquiv` identify the PAC experiment with the distinguisher’s acceptance probability. No conditioning excludes repeated points. Both sides interpret the learner’s prediction as `decide (output = [true])`, including all other output words.
3. **Random-function bound.** For positive `n`, `flipAt` is an involution of function tables. When the test point is absent from the examples, it preserves every example label and negates the test label. Uniform probability is preserved, so success equals its complement and is exactly `1/2`. The public coupling bound and the union bound then give

   \[
   |\operatorname{gameProb}-1/2|
   \le \Pr[\exists j,\ s_j=x]
   \le \sum_{j<m(n)}2^{-n}
   =m(n)/2^n.
   \]

4. **Negligibility.** The owned proof applies the triangle inequality to obtain

   \[
   \operatorname{predictAdv}
   \le \operatorname{prfAdv}+m(n)/2^n
   \qquad(n\ge1).
   \]

   `PRF.negligible_prfAdv` uses precisely the polynomial budget `m + 1`. Polynomial-times-exponential decay, addition and eventual domination finish the argument. The finite exception `n = 0` is handled by the cutoff `1`. With no examples, the empty union gives zero collision probability.

Part (c)’s complete source suffix, including its proof, is byte-identical to the PR base. It combines eventual prediction advantage at most `1/n` with `δ < γ` and the published PAC bridge. The final axiom prints for both (b) and (c) contain exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Integrity and evidence checks

- **Pack:** all 17 `SHA256SUMS` entries verify. All 14 bundle sections match their pinned repository originals, allowing only the bundle’s framing newlines. Every one of the 138 source-closure files matches the Lean-head git blob.
- **Nested evidence:** `verification.zip` has exactly its 30 manifest paths plus `SHA256SUMS`. The review archive verifies all 488 manifest entries; the reuse archive verifies all 248. Their external and internal manifests agree, with no extra file entries.
- **Freeze:** exactly the five authorized Lean files differ from the PR base. All nine pre-existing declaration headers are byte-identical; there are 47 new public declarations. Part (c) is unchanged. The owned-file changes stay within the permitted imports, module prose, target sketch and target proof.
- **LE-doc:** only doc comments change in its four files. The 17 added formulas agree with their declarations and argument order; no documentation finding was found. The rewritten target sketch describes the delivered proof.
- **LE-reuse:** only `Random.lean` changes: the two disclosed proof bodies, one import and the two permitted docstring insertions. Both cited public lemmas instantiate correctly. `HybridLemmas` adds exactly one module to `Random`’s closure, from 123 to 124, with no cycle and no additional definition. Carrying forward the four unchanged files’ seals is justified.
- **Rule 10:** independently checked the request sets against the supplied catalogs and stored-term references, including matchers and private-name components; removed instrumentation to recover the exact pinned source bytes; and checked installation and EOF records. All 28 seal probes have zero errors: 20 at LE-doc, four for the base owned file, and four for final `Random`. The older base-seal revision `eff2dcd0` has the same 130 source files in the owned file’s closure as the PR base.
- **Controls:** recounted both diagnostic forms directly from raw logs. The canonical review controls have 16 probes and 46 sealed negatives; each negative fails once, reader positives pass, and unsealed controls pass. The strict review controls have 54 correct negative failures plus the disclosed 16 reader-positive failures, confined to `ctlUniformReader` and `ctlCoeReader` in eight sealed probes. Their type mismatches match the projection-coercion attribution. Final reuse controls pass in both variants, with seven sealed negatives per variant. No additional forbidden definition read was found.
- **Builds and axioms:** checked the raw 66-module final build records, their source hashes against the audited git head, their log hashes, and zero error/sorry counts. The supplied census covers 71 stored constants with the standard axiom union. The whole-tree check remains the supplied LE-doc check of 1245 modules; the pack’s separate combined-tree rebuild requirement for the PR merging second remains applicable.
- **Lint and size:** independently reran the final lint: 92 FAIL / 101 WARN, with exactly the same 193 FAIL/WARN lines as the supplied baseline. Files have 220, 275, 137, 174 and 189 lines; every line is at most 100 characters.

**Validation limit:** no Lean toolchain is installed in this audit environment. I independently checked source, manifests, import graphs, instrumentation and raw supplied execution evidence; I did not rerun Lean elaboration or the seals.

**Closure condition:** resolve G29-01 and G29-02 through reader-based proofs or explicit user dispositions, then supply validation for the revised head. No repository change, review submission, dispatch or merge was made by this audit.

**Notation:** `m(n)` means `m.eval n`; `ρ` is the learner’s coin type; `hn` proves `0 < n`; `i` is a bit index; `s_j` is example `j`; `x` is the fresh test point; `Pr` is uniform probability. Other names are the audited Lean declarations.

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/resolutions-r1.md =====

# Gate 29 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 0 minors, 0 notes.
- **Findings:** `findings/gate29-learning-findings.md`.
- **Audited head:** `8befc58966fd39f974a54250849736df194584b9`.
- Codex found the proof correct, part (c) sorry-free and the frozen statements intact. The seals and controls pass.
  Both majors are re-proofs that the review missed and nobody disclosed.

| # | Severity | Disposition |
|---|---|---|
| G29-01 | major | **Fixed by LE-gate29a, proof only** (`94b31964ee94b97bf3ed3b4b4338cacae8183194`, tree `b283709e`). The four-line calculation in `hj` is now `simp only [uprob_eq_point, OneWay.uexp_const]`, no new import; the sketch names the lemma. `decls2` empty, headers 63/63 identical. Evidence `landing-r1/gate29-le-a-evidence.zip`, SHA-256 `b1ce1c5057d7b836d0546562a7f7dab503e4b5237fb28939bcf61ffc96fcffb2`. Pushed to #313. |
| G29-02 | major | **Ruling (Seyoon, 2026-11-15): promote it now.** The new `firstBit_of_pos` re-proves the zero-index case of the public `LamportFill.headD_drop_ofFn`. A small PR promotes `headD_drop_ofFn` to a shared list layer that is upstream of both consumers, and re-derives Lamport's copy proof-only. After that PR merges, #313 re-points `firstBit_of_pos` (LE-gate29b), and Gate 29 round 2 follows. |

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
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `PRF.prfAdv_eq_expect` (to be published); the list readers above; `GGMRed.tblEnc` | Open | F-01 by the promotion PR; F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). |

## ===== briefs/pass-shelat-ch5-8/maintainer/promote-headd-2026-11-15/pr-body.md =====

## Promote `headD_drop_ofFn` to the shared list layer (Gate 29 G29-02)

Seyoon's ruling of 2026-11-15 on Gate 29 finding G29-02 is "promote it now". The finding is that the learning unit's new
`LearnPRF.firstBit_of_pos` (#313, `Randomness/Learning/Random.lean`) re-proves the index-0 case of the public Lamport
bit reader `Authentication.LamportFill.headD_drop_ofFn`. This PR publishes that reader, in generic form, in a shared
layer upstream of both files. The Lamport copy is re-derived from it, proof only. The learning re-point of
`firstBit_of_pos` is a later #313 landing edit, after this PR merges. It is **not** part of this PR.

**Branch:** `promote/pass-shelat-headd-ofFn` at `c18afbe6`. It is 1 commit on `cryptography/pass-shelat-ch2-4` at
`dd98360d`. That tip has the same Lean tree as `711a9f4a`: the commits after it change records only.

### Changes

**`TCSlib/Cryptography/Foundations/BitLists.lean`**
- New theorem `TCSlib.Cryptography.headD_drop_ofFn`, placed right after `headD_drop`, which its proof uses. It has a
  formula docstring and a proof sketch, and no attribute:
  ```lean
  theorem headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
      ((List.ofFn f).drop i.val).headD d = f i
  ```
- It generalizes the Lamport reader from `Bool` with `d = false` to any type and any default. The `headD false` form
  is `headD_drop_ofFn f i false`. The proof is the Lamport proof unchanged.
- One new `## Main results` bullet.
- **Why this home.**
  - `BitLists` is the generic list and bit-vector file ("heads of suffixes" is in its scope). It depends on Mathlib
    only, and it already holds `headD_drop` and `headD_ofFn_one`.
  - It is already in both consumers' closures. `Lamport/MachineSpec` imports it directly. `Randomness/Learning/Random`
    (#313) reaches it through `Asymptotic.Adversary`. So **no import changes**, and there is no cycle, because
    `BitLists` imports no project module.
  - No open PR touches it. #313 touches only `Randomness/Learning*` and #314 only PRF `Defs` and ETT `Reduction`.
    Nor do prf-long's files (`Asymptotic/Defs`, `FromPRF*`, the `Functions` facade, `PrivateKey.lean`).
  - `Asymptotic/ReductionSupport.lean` is also in both closures, but it is further downstream and not Mathlib-only.

**`TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean`**
- `LamportFill.headD_drop_ofFn` is now `:= TCSlib.Cryptography.headD_drop_ofFn m i false` (proof only).
- Its name and statement are unchanged. Its docstring is unchanged except for one inserted sentence: "This is the
  published `TCSlib.Cryptography.headD_drop_ofFn` at `α = Bool` and `d = false`."
- Its use in `run_input` builds unchanged.

No other file changes.

### Checks
- **Statements.** decls2 against `dd98360d` shows 1 ADDED (the new theorem), 0 CHANGED and 0 REMOVED. All 23
  pre-existing declaration headers of the two files (14 in BitLists, 9 in MachineSpec) are byte-identical.
- **Build.** I built with `scripts/lean_check_tree.sh`, one module at a time, with no `lake`, on a tree at the
  `eff2dcd0` base.
  - The queue was 253 modules: the 2 changed files and their downstream (245 modules with them), plus the
    #303–#309, #311 and #312 base delta and its downstream (65), up to root `TCSlib`, `audits/garg-ch1-3/Checks` and
    `audits/pass-shelat/Checks`.
  - All 253 returned rc 0 with 0 errors.
  - The only sorries are the 24 pre-existing ones, including #312's two stated `SeedMajority` sorries.
  - BitLists has 0 warnings. MachineSpec has its 2 inherited warnings.
  - Each of the 249 modules with a same-source reference build produced a byte-identical olean. The 4 without one
    are the 2 edited files and the 2 #312 modules.
- **Axioms.** `TCSlib.Cryptography.headD_drop_ofFn` and `LamportFill.headD_drop_ofFn` depend on `[propext]`.
  `LamportFill.run_input` and `Authentication.lamport_oneTimeSecure` depend on `[propext, Classical.choice, Quot.sound]`.
- **Rule 10.** Seals A and B, strict and coe, pass for both changed files.
  - MachineSpec: 2088/2089 requests (strict) and 2087/2088 (coe).
  - BitLists: 0 requests in each variant, because its closure has no TCSlib module. Its seals are vacuous, and no
    control row can apply to it.
  - Paired controls for MachineSpec use the Lamport review rows: `padFin`, `ProbComp.expect`, `ProbComp.sample`,
    `OracleComp.bind`, `secretWord`, `signatureBlock`, `LamportMachine.u`, and `PolyExpr.eval` in B. The result is
    ALL_OK in both harnesses: 4 probes and 15 sealed negatives each.
- **Lint.** `campaign_style_lint.py TCSlib/Cryptography --check8b` gives 92 FAIL and 101 WARN at both the parent and
  the head, with identical FAIL and WARN lines. Max line width is 100 in both files, unchanged; no line is over 100.

Evidence: `dl-review/promote-headd/` (PROVENANCE.txt, SHA256SUMS), zipped as `dl-review/promote-headd-evidence.zip`.

### Follow-up
- #313 (learning landing edit, after this merges): re-derive `LearnPRF.firstBit_of_pos` as
  `rw [firstBit_eq]; simpa only [List.drop_zero] using TCSlib.Cryptography.headD_drop_ofFn y ⟨0, hn⟩ false`.
  This needs no import. The shape was checked by statement matching only, not run.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== briefs/pass-shelat-ch5-8/gates/32-headd-promote/pr-description.md =====

## Summary

This PR implements Seyoon's ruling of 2026-11-15 on Gate 29's major G29-02 ("promote it now"). The `learning` delivery (#313) re-proved the zero-index case of the public `Authentication.LamportFill.headD_drop_ofFn`. That lemma is a generic list fact, so it now has a shared home:

```lean
theorem TCSlib.Cryptography.headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    ((List.ofFn f).drop i.val).headD d = f i
```

- **Where it lives:** `Foundations/BitLists.lean`, beside `headD_drop` and `headD_ofFn_one`. The file imports only Mathlib. It is already upstream of both consumers, `Lamport/MachineSpec` directly and `Randomness/Learning/Random` through `Asymptotic.Adversary`, so no import changes and there is no cycle. No open PR and none of prf-long's files touch it. The lemma carries a formula docstring and a sketch, and no attribute.
- **Generalized:** the `Bool` specialization is dropped. The `headD false` form is `headD_drop_ofFn f i false`.
- **Lamport's copy re-derived:** `LamportFill.headD_drop_ofFn` is now `:= TCSlib.Cryptography.headD_drop_ofFn m i false`. Its name and statement are unchanged, and its docstring gains one sentence naming the published lemma.
- **Follow-up:** after this merges, #313 re-points `firstBit_of_pos` to the new lemma with a proof-only edit, and Gate 29 has a round 2.

## Checks

- **Statements:** decls2 gives 1 ADDED, 0 CHANGED, 0 REMOVED. All 23 pre-existing headers are byte-identical.
- **Build:** 253/253 modules rc 0, through root `TCSlib` and both `audits/*/Checks`. The only admissions are ones that already existed. 249 oleans are byte-identical to earlier builds.
- **Axioms:** both lemmas use `[propext]`. `lamport_oneTimeSecure` uses only the standard three.
- **Rule 10:** seals A and B pass in both the strict and the coe form, and the paired controls are ALL_OK.
- **Lint:** 92/101, unchanged.
- **Evidence:** `promote-headd-evidence.zip`, SHA-256 `5efc53e2…`. It will be filed under `briefs/pass-shelat-ch5-8/maintainer/promote-headd-2026-11-15/`.

A Codex gate follows.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/32-headd-promote/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean
index 60fb7d4ac..1087da75d 100644
--- a/TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean
@@ -191,11 +191,12 @@ theorem advIn_context {n ℓ : ℕ} (W : PolyExpr)
 end KeyWindows
 
 /-- The selected bit of a serialized message is its typed bit at that position: `((List.ofFn m).drop
-i.val).headD false = m i`. -/
+i.val).headD false = m i`.
+
+This is the published `TCSlib.Cryptography.headD_drop_ofFn` at `α = Bool` and `d = false`. -/
 theorem headD_drop_ofFn {n : ℕ} (m : Fin n → Bool) (i : Fin n) :
-    ((List.ofFn m).drop i.val).headD false = m i := by
-  simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
-    dif_pos i.isLt, Option.getD_some]
+    ((List.ofFn m).drop i.val).headD false = m i :=
+  TCSlib.Cryptography.headD_drop_ofFn m i false
 
 /-- On canonical input, the machine returns the typed signature and records the old abort
 bit or equality `m_i=c`. This statement covers both safe and aborting calls. -/
diff --git a/TCSlib/Cryptography/Foundations/BitLists.lean b/TCSlib/Cryptography/Foundations/BitLists.lean
index a8d70ef50..758ca630c 100644
--- a/TCSlib/Cryptography/Foundations/BitLists.lean
+++ b/TCSlib/Cryptography/Foundations/BitLists.lean
@@ -26,6 +26,8 @@ an association list. They depend on Mathlib only.
 ## Main results
 
 * `TCSlib.Cryptography.headD_drop`: the head of a suffix is an entry.
+* `TCSlib.Cryptography.headD_drop_ofFn`: the head of a suffix of a tuple's list is the tuple's
+  entry at that index.
 * `TCSlib.Cryptography.flatten_ofFn_one`, `flatten_ofFn_singleton`: flattening one-element blocks.
 * `TCSlib.Cryptography.headD_ofFn_one`: the bit of a one-bit vector is the head of its string.
 * `TCSlib.Cryptography.zipWith_xor_cancel_left`: `(a ⊕ c) ⊕ a = c`.
@@ -50,6 +52,17 @@ namespace TCSlib.Cryptography
 theorem headD_drop {α : Type*} (l : List α) (i : ℕ) (d : α) : (l.drop i).headD d = l.getD i d := by
   rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]
 
+/-- The head of the suffix of a tuple's list at an index is the tuple's entry there: for
+`f : Fin n → α`, `i : Fin n` and any default `d`, `((List.ofFn f).drop i.val).headD d = f i`
+(for bit vectors, `d = false` reads the `i`-th bit of the string `List.ofFn f`).
+
+**Proof sketch.** By `headD_drop` the left side is the entry `(List.ofFn f).getD i d`; since
+`i < n` it is the in-range entry `f i` (`List.getElem?_ofFn`). -/
+theorem headD_drop_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
+    ((List.ofFn f).drop i.val).headD d = f i := by
+  simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt,
+    Option.getD_some]
+
 /-- **Flattening one-element blocks:** concatenating the one-bit blocks `g j` gives their bits,
 `(List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j 0` when the blocks have
 length `l = 1`.

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

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Functional contracts of the planted Lamport machine

## Main definitions

None.

## Main results

* `advIn_context` identifies the machine's public key with the typed planted public table.
* `run_input` identifies its query answer and abort flag.
* `out_nonabort` identifies its final signature-block extraction.

The exact finite-tuple `coinBlock` reader is passed as a parameter, so this helper neither
imports the owned consumer nor copies that consumer's public lemma.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity Turing TCSlib.Cryptography.Games
open TCSlib.Cryptography

/-- The serialized public table is the concatenation of its self-delimiting image-pair
blocks: `publicWord Y = (List.ofFn fun i : Fin n => pairEncode (pairEncode (List.ofFn (Y (i,
false))) (List.ofFn (Y (i, true)))) []).flatten`. This reads the public tuple encoding through
`encodeList_eq_flatMap`. -/
theorem publicWord_flatten {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) :
    publicWord Y = (List.ofFn fun i : Fin n =>
      pairEncode (pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) []).flatten := by
  rw [publicWord_eq, encodeList_eq_flatMap, List.flatMap_def, List.map_ofFn]
  rw [Function.comp_def]

section KeyWindows

variable (hcoin : ∀ {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
  (i : Fin q), coinBlock B i (List.ofFn g).flatten = g i)

include hcoin in
/-- Reading the first `n`-bit half of the selected sampled row returns `T(i,false)`:
`LamportMachine.first (seedIn n (pairEncode challenge (List.replicate i.val true)) (c :: secretWord
T)) = List.ofFn (T (i, false))`.

**Proof sketch.** On this context `first` takes `n` bits of `secretWord T` after the offset `2n·i`
(`first_eq`, `tape_seedIn`, `offset_eq`, `pos_seedIn`, `u_seedIn`). By `hcoin`, the `2n` bits there
are row `i`, that is `T (i, false) ‖ T (i, true)`, and the first `n` of them are `T (i, false)`. -/
theorem first_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
    LamportMachine.first (seedIn n (pairEncode challenge (List.replicate i.val true))
      (c :: secretWord T)) = List.ofFn (T (i, false)) := by
  rw [LamportMachine.first_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hrow := hcoin (B := 2 * n)
    (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
  rw [coinBlock_eq, ← secretWord_eq] at hrow
  have h := congrArg (fun w : List Bool => w.take n) hrow
  dsimp only at h
  rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' List.length_ofFn] at h
  exact h

include hcoin in
/-- Reading the second `n`-bit half of the selected sampled row returns `T(i,true)`:
`LamportMachine.second (seedIn n (pairEncode challenge (List.replicate i.val true)) (c :: secretWord
T)) = List.ofFn (T (i, true))`.

**Proof sketch.** On this context `second` takes `n` bits of `secretWord T` after the offset `2n·i +
n` (`second_eq`, `tape_seedIn`, `offset_eq`, `pos_seedIn`, `u_seedIn`). By `hcoin`, the `2n` bits
after offset `2n·i` are row `i`, that is `T (i, false) ‖ T (i, true)`, and dropping its first `n`
bits leaves `T (i, true)`. -/
theorem second_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
    LamportMachine.second (seedIn n (pairEncode challenge (List.replicate i.val true))
      (c :: secretWord T)) = List.ofFn (T (i, true)) := by
  rw [LamportMachine.second_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hrow := hcoin (B := 2 * n)
    (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
  rw [coinBlock_eq, ← secretWord_eq] at hrow
  have h := congrArg (fun w : List Bool => w.drop n) hrow
  dsimp only at h
  rw [List.drop_take, show 2 * n - n = n by omega, List.drop_drop,
    List.drop_left' List.length_ofFn] at h
  exact h

include hcoin in
/-- The machine's replacement block serializes the planted row, using the evaluator's
published agreement on `n`-bit inputs: `LamportMachine.replacement E (seedIn n (pairEncode
(List.ofFn challenge) (List.replicate i.val true)) (c :: secretWord T)) = pairEncode (pairEncode
(List.ofFn (plantedPublic g T i c challenge (i, false))) (List.ofFn (plantedPublic g T i c challenge
(i, true)))) []`. -/
theorem replacement_context {n ℓ : ℕ} (g : (Fin n → Bool) → Fin ℓ → Bool)
    (E : List Bool → List Bool)
    (hE : ∀ x : Fin n → Bool,
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
    LamportMachine.replacement E
        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
          (c :: secretWord T)) =
      pairEncode (pairEncode
        (List.ofFn (plantedPublic g T i c challenge (i, false)))
        (List.ofFn (plantedPublic g T i c challenge (i, true)))) [] := by
  rw [LamportMachine.replacement_eq, LamportMachine.bit_seedIn, LamportMachine.u_seedIn,
    LamportMachine.y_seedIn, first_context hcoin, second_context hcoin, hE, hE]
  cases c <;> simp [plantedPublic_eq]

include hcoin in
/-- On a canonical seed context, the machine's public-key input is exactly the serialized
typed planted table: if `W.eval n = 6 * ℓ + 6`, then `LamportMachine.advIn W E G (seedIn n
(pairEncode (List.ofFn challenge) (List.replicate i.val true)) (c :: secretWord T)) = publicWord
(plantedPublic g T i c challenge)`. The only generator/evaluator facts required are their stated
functional contracts; the owned Lamport module supplies them.

**Proof sketch.** The ordinary generated key is a concatenation of width `6ℓ+6` blocks.
The machine takes the blocks before `i`, inserts the planted block, and drops through block
`i`. The general fixed-width replacement lemma identifies this with updating row `i` before
serialization. Every other row retains both images. -/
theorem advIn_context {n ℓ : ℕ} (W : PolyExpr)
    (hW : W.eval n = 6 * ℓ + 6) (g : (Fin n → Bool) → Fin ℓ → Bool)
    (E G : List Bool → List Bool)
    (hE : ∀ x : Fin n → Bool,
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
    (hG : ∀ T : Table n,
      G (NUPPT.layout (List.replicate n true) [] [] (secretWord T)) =
        pairEncode (publicWord (tablePublic g T)) (secretWord T))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
    LamportMachine.advIn W E G
        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
          (c :: secretWord T)) =
      publicWord (plantedPublic g T i c challenge) := by
  have hpk : LamportMachine.honestPk G
      (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
        (c :: secretWord T)) = publicWord (tablePublic g T) := by
    rw [LamportMachine.honestPk_eq, LamportMachine.u_seedIn, LamportMachine.tape_seedIn,
      hG, pairFstD_pairEncode]
  let rows : Fin n → List Bool := fun j => pairEncode (pairEncode
    (List.ofFn (g (T (j, false)))) (List.ofFn (g (T (j, true))))) []
  let plantedRows : Fin n → List Bool := fun j => pairEncode (pairEncode
    (List.ofFn (plantedPublic g T i c challenge (j, false)))
    (List.ofFn (plantedPublic g T i c challenge (j, true)))) []
  have hrows (j : Fin n) : (rows j).length = W.eval n := by
    simp only [rows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
    ring
  have hnew : (plantedRows i).length = W.eval n := by
    simp only [plantedRows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
    ring
  have hupdate : Function.update rows i (plantedRows i) = plantedRows := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
    · have hp0 : (j, false) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
      have hp1 : (j, true) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
      rw [Function.update_of_ne hj]
      simp only [rows, plantedRows, plantedPublic_eq, if_neg hp0, if_neg hp1]
  have hnormal : publicWord (tablePublic g T) = (List.ofFn rows).flatten := by
    rw [publicWord_flatten]
    simp only [tablePublic_eq, rows]
  have hplant : publicWord (plantedPublic g T i c challenge) =
      (List.ofFn plantedRows).flatten := by
    rw [publicWord_flatten]
  simp only [LamportMachine.advIn_eq, hpk, replacement_context hcoin g E hE,
    LamportMachine.offset_eq, LamportMachine.width_eq, LamportMachine.pos_seedIn,
    LamportMachine.u_seedIn, List.length_replicate]
  simp only [hnormal, hplant]
  change (List.ofFn rows).flatten.take (i.val * W.eval n) ++ plantedRows i ++
    (List.ofFn rows).flatten.drop (i.val * W.eval n + W.eval n) =
      (List.ofFn plantedRows).flatten
  rw [show i.val * W.eval n + W.eval n = (i.val + 1) * W.eval n by ring,
    flatten_ofFn_update rows hrows i (plantedRows i) hnew, hupdate]

end KeyWindows

/-- The selected bit of a serialized message is its typed bit at that position: `((List.ofFn m).drop
i.val).headD false = m i`.

This is the published `TCSlib.Cryptography.headD_drop_ofFn` at `α = Bool` and `d = false`. -/
theorem headD_drop_ofFn {n : ℕ} (m : Fin n → Bool) (i : Fin n) :
    ((List.ofFn m).drop i.val).headD false = m i :=
  TCSlib.Cryptography.headD_drop_ofFn m i false

/-- On canonical input, the machine returns the typed signature and records the old abort
bit or equality `m_i=c`. This statement covers both safe and aborting calls. -/
theorem run_input {n : ℕ} (S : List Bool → List Bool)
    (hS : ∀ (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (T : Table n) (i : Fin n) (c bad : Bool) (challenge : List Bool)
    (j : Fin 1) (m : Fin n → Bool) :
    LamportMachine.run S (PolyHandler.input n
        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
        [bad] j (List.ofFn m)) =
      pairEncode (List.ofFn (tableSignature T m)) [bad || decide (m i = c)] := by
  have hb : LamportMachine.blocked (PolyHandler.input n
      (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
      [bad] j (List.ofFn m)) = decide (m i = c) := by
    rw [LamportMachine.blocked_eq, LamportMachine.context_input, LamportMachine.message_input,
      LamportMachine.pos_seedIn, LamportMachine.bit_seedIn, List.length_replicate,
      headD_drop_ofFn]
  simp only [LamportMachine.run_eq, LamportMachine.context_input, LamportMachine.state_input,
    LamportMachine.message_input, LamportMachine.u_seedIn, LamportMachine.tape_seedIn, hS,
    List.headD_cons, hb]

/-- A safe query from non-abort state returns the typed signature and a false abort bit: if `m i ≠
c`, then `LamportMachine.run S (PolyHandler.input n (pairEncode challenge (List.replicate i.val
true)) (c :: secretWord T) [false] j (List.ofFn m)) = pairEncode (List.ofFn (tableSignature T m))
[false]`. -/
theorem run_safe {n : ℕ} (S : List Bool → List Bool)
    (hS : ∀ (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool)
    (j : Fin 1) (m : Fin n → Bool) (hm : m i ≠ c) :
    LamportMachine.run S (PolyHandler.input n
        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
        [false] j (List.ofFn m)) =
      pairEncode (List.ofFn (tableSignature T m)) [false] := by
  rw [run_input S hS]
  simp only [hm, decide_false, Bool.false_or]

/-- Finalization in non-abort state returns exactly the selected block of the typed forged
signature, after its first `n` message bits: if `LamportMachine.pos (seedIn n z ρ) = List.replicate
i.val true`, then `LamportMachine.out (pairEncode (seedIn n z ρ) (pairEncode [false] (List.ofFn
a))) = List.ofFn (signatureBlock (splitBits a).2 i)`.

**Proof sketch.** With state `[false]`, `out` drops the `n` message bits, then `n·i` more bits, and
takes `n` (`out_eq`, `u_seedIn`, `offset_eq`, `hz`). After the message the word is `List.ofFn
(splitBits a).2` (`splitBits_snd`, `ofFn_natAdd_eq_drop`), and its block `i` is the signature block
(`FunFamily.ofFn_blocks`, `signatureBlock_eq`). -/
theorem out_nonabort {n : ℕ} (i : Fin n) (z ρ : List Bool)
    (a : Fin (n + n * n) → Bool)
    (hz : LamportMachine.pos (seedIn n z ρ) = List.replicate i.val true) :
    LamportMachine.out (pairEncode (seedIn n z ρ) (pairEncode [false] (List.ofFn a))) =
      List.ofFn (signatureBlock (splitBits a).2 i) := by
  rw [LamportMachine.out_eq, LamportMachine.state_eq, LamportMachine.context_eq]
  simp only [LamportMachine.context_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    Bool.false_eq_true,
    if_false, LamportMachine.u_seedIn, LamportMachine.offset_eq, hz,
    List.length_replicate, PolyExpr.eval_var]
  have hs : List.ofFn (splitBits a).2 = (List.ofFn a).drop n := by
    have hsplit : (splitBits a).2 = fun j => a (Fin.natAdd n j) := by
      funext j
      exact splitBits_snd a j
    rw [hsplit, ofFn_natAdd_eq_drop]
  rw [← hs, ← FunFamily.ofFn_blocks n n (splitBits a).2 i]
  apply congrArg List.ofFn
  funext k
  rw [FunFamily.blocks_apply, signatureBlock_eq]

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Pseudorandom/NextBit.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Cryptography.Pseudorandom.NextBit.Concrete
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The next-bit characterization of pseudorandom ensembles

The next-bit test bounds the success of every non-uniform polynomial-time predictor by
one half plus a negligible function. The predictor receives `1^n` and the prefix of the
sample [PS10, Definition 75.2 and Remark 75.3]. The reductions implement the finite
predictor and distinguisher as machines. For completeness, the predictor gets the sign in
its advice and reads the position from the prefix length. Where the output length is zero,
the distinguishing advantage is zero and there is no position to choose.

## Main definitions

* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable` gives the next-bit test with a single
  negligible bound for all positions.

## Main results

* `TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom` gives completeness
  of the test [PS10, Theorem 75.4].
* `TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable` gives the converse.
* `TCSlib.Cryptography.Ensemble.uniform_nextBitUnpredictable` establishes the test for
  the uniform ensemble.

## Contents

* `Concrete` gives the finite next-bit experiments, hybrids, and advantage bounds.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.2.2: Definition 75.2, Remark 75.3, Theorem 75.4, Algorithm 76.5.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- **Passing the next-bit test** [PS10, Definition 75.2]: for every non-uniform PPT `A` there
is a negligible `ε` such that for all `n` and all positions `i < ℓ(n)`,
`Pr[t ← X_n : A(1^n, t_1 ⋯ t_i) = t_{i+1}] ≤ 1/2 + ε(n)`. The predictor is the machine `A`
activated at parameter `n` on `⟨1^n, t_1 ⋯ t_i⟩` (`A.predictor n i`), which is the convention
of [PS10, Remark 75.3]: `A` receives `1^n` so that its size and running time may be polynomial
in `n` rather than in the possibly short prefix. The quantifier order `∀ A ∃ ε ∀ n ∀ i` is the
text's (one negligible function for all positions).

**Deviation:** `NextBitUnpredictable`: the position ranges over the existing bits `i < ℓ(n)`
(the text's `i ∈ [0, ℓ(n)]` includes the nonexistent bit `t_{ℓ(n)+1}`); the bound is
`≤ 1/2 + ε(n)` instead of the text's strict `<` (equivalent, `nextBitUnpredictable_iff_lt`);
the predictor receives `1^n` [PS10, Remark 75.3] (D5). -/
def Ensemble.NextBitUnpredictable {ℓ : PolyExpr} (X : Ensemble ℓ) : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1 / 2 + ε n

/-- **The text's strict form of Definition 75.2** — "there exists a negligible `ε` with
success `< 1/2 + ε(n)` for all `n` and `i`" — is equivalent to the frozen `≤` form
[PS10, Definition 75.2]: one direction is `le_of_lt`, the other replaces `ε(n)` by
`ε(n) + 2^{-n}`. -/
theorem Ensemble.nextBitUnpredictable_iff_lt {ℓ : PolyExpr} (X : Ensemble ℓ) :
    X.NextBitUnpredictable ↔ ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) < 1 / 2 + ε n := by
  constructor
  · intro h A
    obtain ⟨ε, hε, hle⟩ := h A
    refine ⟨fun n => ε n + (2 : ℝ)⁻¹ ^ n, hε.add negligible_two_pow_neg, fun n i => ?_⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    linarith [hle n i]
  · intro h A
    obtain ⟨ε, hε, hlt⟩ := h A
    exact ⟨ε, hε, fun n i => (hlt n i).le⟩

/-- A distinguisher whose coin string is reindexed by a bijection has the same acceptance
probability (`uprob_comp_equiv` on the coin factor of the sample space). -/
private theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
    (X : σ → γ) (e : ρ ≃ ρ') (D : γ → ρ' → Bool) (D' : γ → ρ → Bool)
    (h : ∀ x r, D x (e r) = D' x r) : acceptProb X D = acceptProb X D' := by
  simp only [acceptProb_def]
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl σ) e)]
  apply OneWay.uprob_congr
  intro z
  simp [h]

/-! ### Completeness of the next-bit test [PS10, Theorem 75.4] -/

/-- **The next-bit predictor as a machine** [PS10, Algorithm 76.5]: for a distinguisher
machine `D` and signs `flip n`, a non-uniform PPT `A` with coins `ℓ + D.coins` and advice
`⟨D.advice n, [flip n]⟩` such that, at every parameter `n` and every position `i < ℓ(n)`, `A`
on the prefix `t` with coins `(u, c)` (split by `e n`) is exactly the concrete predictor
`nextBitPred (D.distinguisher n (ℓ n)) i (flip n) t (u, c)`: it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `u_{|t|}` or its negation according to the verdict,
negated once more if `flip n`. The position is read off the prefix length `|t| = i`, so only
the sign is hard-wired, and the identity holds at every position (restated so at gate 03c,
finding 2: no choice of position is needed where `ℓ(n) = 0`).

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨D.advice n, [flip n]⟩⟩, r⟩` cuts `r`
into `u := r.take (ℓ n)` and `c := r.drop (ℓ n)` (`polyTimeComputable_pairTakePoly`/
`pairDropPoly ℓ` on `⟨1^n, r⟩`), forms `w := y ++ u.drop |y|` (`pairDropPoly var` on `⟨y, u⟩`,
`PolyTimeComputable.append`), runs `D.output` on `layout 1^n w (D.advice n) c`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), tests the verdict against `[true]`
(`polyTimeComputable_pairEq`), reads `u_{|y|}` as the head of `u.drop |y|` and the sign as the head
of the advice's second component (`polyTimeComputable_headD`), and combines them
(`polyTimeComputable_ite`, `polyTimeComputable_not`, `BinArith.polyTimeComputable_xor`).
`A := ofPolyTime` of it with coins `add ℓ D.coins` and advice bound `2·D.adv + 3`
(`length_pairEncode`); the coin split is `Fin.appendEquiv` composed with `finCongr`, and the
identity is `runAtL_ofPolyTime`, the projection identities of the layout,
`List.take_left'`/`List.drop_left'`, `ofFn_completePrefix` and `headD_drop`. -/
private theorem exists_nextBitPredMachine (ℓ : PolyExpr) (D : NUPPT) (flip : ℕ → Bool) :
    ∃ (A : NUPPT) (e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n),
      ∀ n (i : Fin (ℓ.eval n)) (t : Fin i → Bool) (u : Fin (ℓ.eval n) → Bool) (c : D.Coins n),
        A.predictor n i t (e n (u, c)) =
          nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n) t (u, c) := by
  -- the coin cut `⟨1^n, r⟩ ↦ u = r.take (ℓ n)`, `c = r.drop (ℓ n)`
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hu : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairTakePoly ℓ).comp hcut using 1
    funext z
    simp
  have hc : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairDropPoly ℓ).comp hcut using 1
    funext z
    simp
  -- the suffix `u.drop |y|` and the completed word `w = y ++ u.drop |y|`
  have hud : PolyTimeComputable fun z =>
      ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop (NUPPT.inArg z).length := by
    convert (polyTimeComputable_pairDropPoly .var).comp
      (NUPPT.polyTimeComputable_inArg.pairEncode hu) using 1
    funext z
    simp
  have hw := NUPPT.polyTimeComputable_inArg.append hud
  -- the call to `D` and its verdict
  have hg := D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hw
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice) hc)
  have hgb : PolyTimeComputable fun z => [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hg.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  -- the bit `u_{|y|}` and the sign
  have hui := polyTimeComputable_headD.comp hud
  have hflip : PolyTimeComputable fun z => [(pairSndD (NUPPT.inAdvice z)).headD false] :=
    polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice)
  have hsel : PolyTimeComputable fun z => [if decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (NUPPT.inArg z ++ ((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
        (NUPPT.inArg z).length) (pairFstD (NUPPT.inAdvice z))
      ((NUPPT.inCoins z).drop (ℓ.eval (NUPPT.inParam z).length))) = [true]) then
        (((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false
      else !(((NUPPT.inCoins z).take (ℓ.eval (NUPPT.inParam z).length)).drop
          (NUPPT.inArg z).length).headD false] := by
    convert polyTimeComputable_ite hgb hui (polyTimeComputable_not hui) using 1
    funext z
    split_ifs <;> rfl
  have hF := BinArith.polyTimeComputable_xor hsel hflip
  -- the advice `⟨D.advice n, [flip n]⟩`
  have hadv : ∀ n, (pairEncode (D.advice n) [flip n]).length ≤
      (PolyExpr.add (.add (.mul (.const 2) D.adv) (.const 2)) (.const 1)).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, List.length_singleton]
    have := D.advice_length n
    omega
  let A := NUPPT.ofPolyTime hF (.add ℓ D.coins) _ (fun n => pairEncode (D.advice n) [flip n]) hadv
  have hlen : ∀ n, A.coinLen n = ℓ.eval n + D.coinLen n := fun n => by
    simp only [A, NUPPT.coinLen_eq, NUPPT.coins_ofPolyTime, PolyExpr.eval_add]
  let e : ∀ n, (Fin (ℓ.eval n) → Bool) × D.Coins n ≃ A.Coins n := fun n =>
    (Fin.appendEquiv (ℓ.eval n) (D.coinLen n)).trans
      (Equiv.arrowCongr (finCongr (hlen n).symm) (Equiv.refl Bool))
  refine ⟨A, e, fun n i t u c => ?_⟩
  have hofn : List.ofFn (e n (u, c)) = List.ofFn u ++ List.ofFn c := by
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr (hlen n).symm (Fin.append u c)).symm
  simp only [NUPPT.predictor_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
      hofn, nextBitPred_eq]
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.advInput_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inAdvice_eq,
      NUPPT.inCoins_eq,
    NUPPT.runAtL_eq, List.take_left', List.drop_left', ofFn_completePrefix]
  split_ifs <;> cases u i <;> cases flip n <;> rfl

/-- **Completeness of the next-bit test** [PS10, Theorem 75.4]: if the ensemble `{X_n}` over
`{0,1}^{ℓ(n)}` passes the next-bit test, then it is pseudorandom.

**Repair (run-3 audit P2-2):** the run-2 hypothesis `hσ : ∀ n, Nonempty (X.σ n)` was dropped
(it is the field `Ensemble.nonempty`; with an empty seed type the experiment has probability
`0`, the ensemble passes the next-bit test vacuously, and the always-accepting distinguisher
has advantage `1`); the frozen shape of DESIGN.md §2.12 is restored.

**Repair (gate 03c, finding 2; ruling G3-7b):** the hypothesis `hℓ : ∀ n, 0 < ℓ.eval n`, which
the text does not have, was dropped; the theorem now applies to every ensemble, `ℓ(0) = 0`
included (e.g. `ℓ = n`, `2n`, `n²`).

**Proof sketch.** By contradiction, as in the text. Fix a distinguisher `D` with
`¬ Negligible (fun n => prgAdv (X_n) (D.distinguisher n (ℓ n)))`
(`Ensemble.pseudorandom_iff_prgAdv`); by `not_negligible_iff_exists_polyExpr` there is a
positive syntactic polynomial `p` with `1/p(n) ≤ prgAdv` for infinitely many `n`. At every
`n` with `ℓ(n) > 0`, `exists_nextBitPred` (with the instance `X.nonempty n`) gives a position
`i_n < ℓ(n)` and a sign `flip_n` with
`1/2 + prgAdv/ℓ(n) ≤ nextBitProb (X_n) i_n (nextBitPred (D.distinguisher n (ℓ n)) i_n flip_n)`;
where `ℓ(n) = 0` put `flip_n := false` (`choose` on "a sign, and a position if `ℓ(n) > 0`").
The predictor machine `A` is `exists_nextBitPredMachine ℓ D flip` (advice
`⟨D.advice n, [flip_n]⟩`, coins `ℓ + D.coins`; on `⟨1^n, t⟩` with coins `u ++ c` it runs
`D(1^n, t ++ u.drop |t|; c)` and outputs `xor (if g then u_{|t|} else !u_{|t|}) flip_n`, the
position being read off the prefix length). Its functional identity, at every position `i`,
`A.predictor n i t (e (u, c)) = nextBitPred (D.distinguisher n (ℓ n)) i flip_n t (u, c)`
along the coin split `e : (Fin (ℓ n) → Bool) × D.Coins n ≃ A.Coins n` (`Fin.appendEquiv`)
gives `nextBitProb (X_n) i (A.predictor n i) = nextBitProb (X_n) i (nextBitPred …)`
(`uprob_comp_equiv`). Now `h A` gives a negligible `ε` with `nextBitProb … ≤ 1/2 + ε n` for
all `n, i`. At every `n` of the infinite set, `ℓ(n) > 0`, since at `ℓ(n) = 0` the advantage is
`0 < 1/p(n)` (`prgAdv_eq_zero_of_length_eq_zero`); there
`1/(p(n)(ℓ(n) + 1)) ≤ 1/(p(n) ℓ(n)) ≤ prgAdv/ℓ(n) ≤ ε n`, i.e. `¬ Negligible ε` by
`not_negligible_iff_exists_polyExpr` with the positive polynomial `mul p (ℓ + 1)`, a
contradiction. -/
theorem Ensemble.NextBitUnpredictable.pseudorandom {ℓ : PolyExpr} {X : Ensemble ℓ}
    (h : X.NextBitUnpredictable) : X.Pseudorandom := by
  rw [Ensemble.pseudorandom_iff_prgAdv]
  intro D
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  -- a sign at every `n`, and a position where `ℓ(n) > 0` (the concrete reduction)
  have hex : ∀ n, ∃ flip : Bool, 0 < ℓ.eval n → ∃ i : Fin (ℓ.eval n),
      1 / 2 + prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n) ≤
        nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i flip) := by
    intro n
    by_cases hn : 0 < ℓ.eval n
    · obtain ⟨i, flip, hif⟩ := exists_nextBitPred hn (X.X n) (D.distinguisher n (ℓ.eval n))
      exact ⟨flip, fun _ => ⟨i, hif⟩⟩
    · exact ⟨false, fun hn' => absurd hn' hn⟩
  choose flip hif using hex
  -- the predictor machine, and its identity with the concrete predictor at every position
  obtain ⟨A, e, hA⟩ := exists_nextBitPredMachine ℓ D flip
  obtain ⟨ε, hε, hbound⟩ := h A
  have hprob : ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) =
      nextBitProb (X.X n) i (nextBitPred (D.distinguisher n (ℓ.eval n)) i (flip n)) := by
    intro n i
    simp only [nextBitProb_eq]
    rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (X.σ n)) (e n))]
    apply OneWay.uprob_congr
    rintro ⟨s, u, c⟩
    simp [hA]
  -- `ε` is not negligible, with the positive polynomial `p · (ℓ + 1)`
  refine (not_negligible_iff_exists_polyExpr.mpr
    ⟨.mul p (.add ℓ (.const 1)), fun n => ?_, fun n₀ => ?_⟩) hε
  · simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
    exact Nat.mul_pos (hp n) (Nat.succ_pos _)
  · obtain ⟨n, hn, hpn⟩ := hinf n₀
    refine ⟨n, hn, ?_⟩
    have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
    have h0 : 0 ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) := by
      rw [prgAdv_eq, distAdv_def]
      exact abs_nonneg _
    rw [abs_of_nonneg h0] at hpn
    -- on the infinite set `ℓ(n) > 0`: at `ℓ(n) = 0` the advantage is `0`
    have hℓn : 0 < ℓ.eval n := by
      rcases Nat.eq_zero_or_pos (ℓ.eval n) with hz | hz
      · have hzero := prgAdv_eq_zero_of_length_eq_zero hz (X.X n) (D.distinguisher n (ℓ.eval n))
        have := one_div_pos.mpr hppos
        linarith
      · exact hz
    obtain ⟨i, h1⟩ := hif n hℓn
    have h2 := hbound n i
    rw [hprob n i] at h2
    have hℓpos : (0 : ℝ) < ℓ.eval n := by exact_mod_cast hℓn
    have hstep : (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ) ≤
        (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := by
      rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, div_div]
      push_cast
      exact one_div_le_one_div_of_le (mul_pos hppos hℓpos)
        (mul_le_mul_of_nonneg_left (by linarith) hppos.le)
    calc (1 : ℝ) / ((PolyExpr.mul p (.add ℓ (.const 1))).eval n : ℝ)
        ≤ (1 / (p.eval n : ℝ)) / (ℓ.eval n : ℝ) := hstep
      _ ≤ prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) / (ℓ.eval n : ℝ) := by gcongr
      _ ≤ ε n := by linarith
      _ ≤ |ε n| := le_abs_self _

/-! ### Soundness of the next-bit test -/

/-- **The uniform ensemble passes the next-bit test** (non-vacuity of
[PS10, Definition 75.2]): every predictor succeeds with probability exactly `1/2`, so
`ε := 0` works. -/
theorem Ensemble.uniform_nextBitUnpredictable (ℓ : PolyExpr) :
    (Ensemble.uniform ℓ).NextBitUnpredictable := by
  intro A
  refine ⟨fun _ => 0, negligible_zero, fun n i => ?_⟩
  have hrel : nextBitProb ((Ensemble.uniform ℓ).X n) i (A.predictor n i) =
      nextBitProb (id : (Fin (ℓ.eval n) → Bool) → Fin (ℓ.eval n) → Bool) i (A.predictor n i) := by
    simp only [nextBitProb_eq]
    rw [← uprob_comp_equiv ((Equiv.cast (Ensemble.uniform_σ ℓ n)).prodCongr (Equiv.refl _))]
    refine congrArg uprob (funext fun z => ?_)
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, id_eq,
      Ensemble.uniform_X, Equiv.cast_apply, cast_cast, cast_eq]
  rw [hrel, nextBitProb_id]
  simp

/-- **The next-bit statistical test as a machine**: for a predictor machine `A` and positions
`k n ≤ ℓ(n)`, a non-uniform PPT `Dm` with `A`'s coins and advice `⟨A.advice n, 1^{k n}⟩` which
on `⟨1^n, y⟩` runs `A(1^n, y.take (k n); r)`, reads bit `k n` of `y` and accepts iff the
verdict equals the bit — the untyped form of `nextBitDist (k n) (A.predictor n (k n))`.

**Proof sketch.** The raw function on the layout `⟨⟨⟨1^n, y⟩, ⟨A.advice n, 1^{k n}⟩⟩, r⟩` cuts
`y` at the unary length of the advice's second component (`polyTimeComputable_pairTakePoly`/
`pairDropPoly var` on `⟨1^{k n}, y⟩`), runs `A.output` on `layout 1^n (y.take (k n)) (A.advice n) r`
(`NUPPT.polyTimeComputable_output`, `polyTimeComputable_layout`), reads the bit as the head of
`y.drop (k n)` (`polyTimeComputable_headD`) and compares twice with `polyTimeComputable_pairEq`
(verdict against `[true]`, then against the bit). `Dm := ofPolyTime` of it with `A.coins` and
advice bound `2·A.adv + 2 + ℓ` (`length_pairEncode`, `hk`); the identity is
`runAtL_ofPolyTime` plus the projection identities of the layout. -/
private theorem exists_nextBitDistMachine {ℓ : PolyExpr} (A : NUPPT) (k : ℕ → ℕ)
    (hk : ∀ n, k n ≤ ℓ.eval n) :
    ∃ Dm : NUPPT, Dm.coins = A.coins ∧ ∀ n (y r : List Bool),
      Dm.runAtL n y r = [decide ([decide (A.runAtL n (y.take (k n)) r = [true])] =
        [(y.drop (k n)).headD false])] := by
  have hkk := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice
  have hpair := hkk.pairEncode NUPPT.polyTimeComputable_inArg
  have hy₁ : PolyTimeComputable fun z =>
      (NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp hpair using 1
    funext z
    simp
  have hb : PolyTimeComputable fun z =>
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false] := by
    convert polyTimeComputable_headD.comp ((polyTimeComputable_pairDropPoly .var).comp hpair)
      using 1
    funext z
    simp
  have ha := A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hy₁
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice)
    NUPPT.polyTimeComputable_inCoins)
  have hx : PolyTimeComputable fun z => [decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] := by
    convert polyTimeComputable_pairEq.comp (ha.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp
  have hG : PolyTimeComputable fun z => [decide ([decide (A.output (NUPPT.layout (NUPPT.inParam z)
      ((NUPPT.inArg z).take (pairSndD (NUPPT.inAdvice z)).length) (pairFstD (NUPPT.inAdvice z))
      (NUPPT.inCoins z)) = [true])] =
      [((NUPPT.inArg z).drop (pairSndD (NUPPT.inAdvice z)).length).headD false])] := by
    convert polyTimeComputable_pairEq.comp (hx.pairEncode hb) using 1
    funext z
    simp
  have hadv : ∀ n, (pairEncode (A.advice n) (List.replicate (k n) true)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) ℓ).eval n := fun n => by
    rw [length_pairEncode, List.length_replicate]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have := A.advice_length n
    have := hk n
    omega
  refine ⟨NUPPT.ofPolyTime hG A.coins _
    (fun n => pairEncode (A.advice n) (List.replicate (k n) true)) hadv, NUPPT.coins_ofPolyTime ..,
    fun n y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  refine congrArg (fun b : Bool => [b]) (decide_eq_decide.2 ?_)
  refine Iff.of_eq (congrArg₂ (fun a b : Bool => [a] = [b]) (decide_eq_decide.2 ?_) ?_)
  · simp only [NUPPT.advInput_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
      NUPPT.inAdvice_eq, NUPPT.inCoins_eq, NUPPT.runAtL_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate]
  · simp only [NUPPT.advInput_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
      NUPPT.inAdvice_eq, NUPPT.inCoins_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate]

/-- **Soundness of the next-bit test, asymptotic form** (the converse of
[PS10, Theorem 75.4], implicit in the text's "a pseudorandom distribution needs to pass all
efficiently computable statistical tests", p. 74): a pseudorandom ensemble passes the
next-bit test.

**Proof sketch.** Fix a predictor machine `A` and let
`ε n := max_{i < ℓ n} (nextBitProb (X_n) i (A.predictor n i) − 1/2)` (`0` if `ℓ n = 0`),
attained at some `i_n` (`Finset.exists_max_image`); then `nextBitProb ≤ 1/2 + ε n` for all
`n, i`, and it suffices to show `Negligible ε`. Otherwise `not_negligible_iff_exists_polyExpr`
gives a positive `p` with `1/p(n) ≤ |ε n|` infinitely often. The distinguisher machine `D` is
`exists_nextBitDistMachine A k` with `k n := i_n` (`0` if `ε n` is not attained): advice
`⟨A.advice n, 1^{k n}⟩`, coins `A.coins`; on `⟨1^n, t⟩` it runs `A` on `⟨1^n, t.take (k n)⟩`,
reads bit `k n` of `t` and outputs `[decide (verdict = [bit])]`. At every `n` with `ε n ≠ 0`
(every `n` of the infinite set), `ε n` is attained at `i_n = k n`, and the functional identity
`D.distinguisher n (ℓ n) t (e r) = nextBitDist i_n (A.predictor n i_n) t r` (`ofFn_prefixOf`,
`headD_drop`, coins reindexed by `e : A.Coins n ≃ D.Coins n` from `finCongr`) gives, by
`prgAdv_nextBitDist` and `acceptProb_coins_equiv`,
`prgAdv (X_n) (D.distinguisher n (ℓ n)) = |nextBitProb (X_n) i_n (A.predictor n i_n) − 1/2| =
|ε n| ≥ 1/p(n)` — the advantage being an absolute value, no choice between the predictor and
its negation is needed — contradicting `hX D` through `not_negligible_iff_exists_polyExpr`. -/
theorem Ensemble.Pseudorandom.nextBitUnpredictable {ℓ : PolyExpr} {X : Ensemble ℓ}
    (hX : X.Pseudorandom) : X.NextBitUnpredictable := by
  classical
  intro A
  have hmax : ∀ n, ∃ v : ℝ,
      (∀ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 ≤ v) ∧
      (v = 0 ∨ ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = v) := by
    intro n
    rcases isEmpty_or_nonempty (Fin (ℓ.eval n)) with hemp | hne
    · exact ⟨0, fun j => (hemp.false j).elim, Or.inl rfl⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (ℓ.eval n)))
        (fun j => nextBitProb (X.X n) j (A.predictor n j) - 1 / 2) Finset.univ_nonempty
      exact ⟨_, fun j => hj₀ j (Finset.mem_univ j), Or.inr ⟨j₀, rfl⟩⟩
  choose ε hεle hεeq using hmax
  refine ⟨ε, ?_, fun n j => by linarith [hεle n j]⟩
  by_contra hneg
  obtain ⟨p, hp, hinf⟩ := not_negligible_iff_exists_polyExpr.mp hneg
  let k : ℕ → ℕ := fun n =>
    if h : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n then
      (h.choose : ℕ) else 0
  have hk : ∀ n, k n ≤ ℓ.eval n := by
    intro n
    simp only [k]
    split_ifs with h
    · exact h.choose.isLt.le
    · exact Nat.zero_le _
  obtain ⟨Dm, hc, hDm⟩ := exists_nextBitDistMachine A k hk
  have hlen : ∀ n, A.coinLen n = Dm.coinLen n := fun n => by simp only [NUPPT.coinLen_eq, hc]
  let e : ∀ n, A.Coins n ≃ Dm.Coins n := fun n =>
    Equiv.arrowCongr (finCongr (hlen n)) (Equiv.refl Bool)
  have hofn : ∀ n (r : A.Coins n), List.ofFn (e n r) = List.ofFn r := fun n r =>
    (List.ofFn_congr (hlen n) r).symm
  refine (not_negligible_iff_exists_polyExpr.mpr ⟨p, hp, fun n₀ => ?_⟩)
    ((Ensemble.pseudorandom_iff_prgAdv X).mp hX Dm)
  obtain ⟨n, hn, hpn⟩ := hinf n₀
  refine ⟨n, hn, ?_⟩
  have hppos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
  have hε0 : ε n ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hpn
    have := one_div_pos.mpr hppos
    linarith
  have hex : ∃ j : Fin (ℓ.eval n), nextBitProb (X.X n) j (A.predictor n j) - 1 / 2 = ε n :=
    (hεeq n).resolve_left hε0
  obtain ⟨j₀, hkn, hspec⟩ : ∃ j₀ : Fin (ℓ.eval n), k n = j₀ ∧
      nextBitProb (X.X n) j₀ (A.predictor n j₀) - 1 / 2 = ε n :=
    ⟨hex.choose, by simp only [k, dif_pos hex], hex.choose_spec⟩
  have hid : ∀ (t : Fin (ℓ.eval n) → Bool) (r : A.Coins n),
      Dm.distinguisher n (ℓ.eval n) t (e n r) = nextBitDist j₀ (A.predictor n j₀) t r := by
    intro t r
    rw [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hDm, hkn]
    rw [nextBitDist_eq]
    rw [NUPPT.predictor_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
      ofFn_prefixOf, headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  have hadv : prgAdv (X.X n) (Dm.distinguisher n (ℓ.eval n)) = |ε n| := by
    rw [← hspec, ← prgAdv_nextBitDist (X.X n) j₀ (A.predictor n j₀)]
    simp only [prgAdv_eq, distAdv_def]
    rw [acceptProb_coins_equiv (X.X n) (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid,
      acceptProb_coins_equiv id (e n) _ (nextBitDist j₀ (A.predictor n j₀)) hid]
  rw [hadv, abs_of_nonneg (abs_nonneg _)]
  exact hpn

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Randomness/Learning/Random.lean@94b31964 =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.Learning.Law
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# With a random function, no learner predicts better than `½ ± m/2^n`

Step 2 of [PS10, Theorem 179.1, proof]: in the game with a uniform random function
`R : {0,1}^n → {0,1}^n` in place of the keyed family, every learner `ℓ` predicts the first bit of
`R x` with probability within `m/2^n` of `½`, for `n ≥ 1` (`abs_gameProb_random_sub_half_le`).

**Proof.** Fix the examples `s`, the coins `r` and the fresh point `x`. If `x` is none of the
examples, flipping the first bit of `R x` (`flipAt`, an involution of the random functions) keeps
the labelled examples and negates the label of `x`, so it exchanges the winning and the losing
functions: the probability over `R` is exactly `½` (`uprob_flip_half`). Otherwise the probability
is between `0` and `1`. So the game probability is within `Pr[x ∈ s]` of `½`, and
`Pr[x ∈ s] ≤ Σ_j Pr[x = s_j] = m · 2^{-n}` (`uprob_exists_le`, `uprob_eq_point`).

## Main definitions

* `LearnPRF.flip0`, `LearnPRF.flipAt`: flipping the first bit of a string, and of a function's
  value at a point.

## Main results

* `LearnPRF.firstBit_flip0`, `LearnPRF.flipAt_involutive`.
* `LearnPRF.uprob_flip_half`: at a fresh point, the prediction wins with probability `½`.
* `LearnPRF.uprob_eq_point`: a uniform point hits a given point with probability `2^{-n}`.
* `LearnPRF.abs_gameProb_random_sub_half_le`: the bound `|gameProb − ½| ≤ m/2^n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity TCSlib.Cryptography TCSlib.LearningTheory.PAC Finset

section Random

variable {n : ℕ} (hn : 0 < n)

/-- **Flipping the first bit** of an `n`-bit string (`n ≥ 1`):
`flip0 hn y = update y 0 (!y 0)`. -/
def flip0 (y : Fin n → Bool) : Fin n → Bool := Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)

/-- `flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)`. -/
theorem flip0_eq (y : Fin n → Bool) : flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩) := rfl

/-- Flipping twice is the identity: `flip0 hn (flip0 hn y) = y`. -/
theorem flip0_flip0 (y : Fin n → Bool) : flip0 hn (flip0 hn y) = y := by
  rw [flip0_eq, flip0_eq, Function.update_self, Function.update_idem, Bool.not_not,
    Function.update_eq_self]

/-- The first bit of an `n`-bit string with `n ≥ 1` is its bit `0`:
`firstBit y = y ⟨0, hn⟩`. -/
theorem firstBit_of_pos (y : Fin n → Bool) : firstBit y = y ⟨0, hn⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [firstBit_eq, List.ofFn_succ, List.headD_cons]
  rfl

/-- Flipping the first bit negates it: `firstBit (flip0 hn y) = !firstBit y`. -/
theorem firstBit_flip0 (y : Fin n → Bool) : firstBit (flip0 hn y) = !firstBit y := by
  rw [firstBit_of_pos hn, firstBit_of_pos hn, flip0_eq, Function.update_self]

/-- **Flipping the first bit of a function's value at `x`:**
`flipAt hn x R = update R x (flip0 hn (R x))`. -/
def flipAt (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    (Fin n → Bool) → (Fin n → Bool) :=
  Function.update R x (flip0 hn (R x))

/-- `flipAt hn x R = Function.update R x (flip0 hn (R x))`. -/
theorem flipAt_eq (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    flipAt hn x R = Function.update R x (flip0 hn (R x)) := rfl

/-- `flipAt hn x` is an involution: `flipAt hn x (flipAt hn x R) = R`. -/
theorem flipAt_involutive (x : Fin n → Bool) : Function.Involutive (flipAt hn x) := by
  intro R
  rw [flipAt_eq, flipAt_eq, Function.update_self, flip0_flip0, Function.update_idem,
    Function.update_eq_self]

include hn in
/-- **At a fresh point the prediction wins with probability `½`:** if `x` is none of the
examples `s`, then for every learner `ℓ` and coins `r`, the uniform probability over `R` that
`ℓ (label (firstBit ∘ R) s) r x == firstBit (R x)` is `½`.

**Proof sketch.** `flipAt hn x` is a bijection of the functions (`flipAt_involutive`), so it
preserves the probability (`uprob_comp_equiv`). It keeps the labels of the examples
(`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`), so it maps the event to
its complement; hence `p = 1 − p` (`uprob_not`). -/
theorem uprob_flip_half {m : ℕ} {ρ : Type*}
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) (s : Fin m → Fin n → Bool)
    (r : ρ) (x : Fin n → Bool) (hx : ∀ j, s j ≠ x) :
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true) = 1 / 2 := by
  set σ := Function.Involutive.toPerm (flipAt hn x) (flipAt_involutive hn x) with hσ
  have h1 := uprob_comp_equiv σ (fun R =>
    (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true)
  have h2 : (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (σ R z)) s) r x ==
        firstBit (σ R x)) = true) =
      fun R => ¬ (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true := by
    funext R
    have hl : label (fun z => firstBit (σ R z)) s =
        label (fun z => firstBit (R z)) s := by
      funext j
      rw [label_apply, label_apply, hσ, Function.Involutive.coe_toPerm, flipAt_eq,
        Function.update_of_ne (hx j)]
    rw [hl, hσ, Function.Involutive.coe_toPerm, flipAt_eq, Function.update_self, firstBit_flip0]
    cases ℓ (label (fun z => firstBit (R z)) s) r x <;> cases firstBit (R x) <;> decide
  rw [h2, uprob_not] at h1
  linarith

/-- **A uniform point hits a given point with probability `2^{-n}`:**
`uprob (fun x : {0,1}^n => y = x) = 1 / 2^n`.

**Proof sketch.** This is `OneWay.uprob_eq_one_div_card` with the equation reversed and
`|{0,1}^n| = 2^n`. -/
theorem uprob_eq_point (y : Fin n → Bool) :
    uprob (fun x : Fin n → Bool => y = x) = 1 / 2 ^ n := by
  rw [show (fun x : Fin n → Bool => y = x) = (fun x => x = y) from
      funext fun _ => propext eq_comm, OneWay.uprob_eq_one_div_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_two]

include hn in
/-- **With a random function the prediction is within `m/2^n` of `½`** [PS10, Theorem 179.1,
proof, step 2]: for `n ≥ 1`, every learner `ℓ` and `m` examples,
`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`.

**Proof sketch.** Put the function last (`uprob_comp_equiv`) and average over it first
(`uprob_prod`): for fixed `((s, r), x)` the probability `p` is `½` when `x` is fresh
(`uprob_flip_half`) and in `[0, 1]` otherwise, so `|p − ½| ≤ [x ∈ s]`. Averaging (the
coupling bound `MultiMsg.abs_uexp_sub_le_uprob` against the constant `½`),
`|gameProb − ½| ≤ Pr[∃ j, s_j = x]`, which the union bound (`uprob_exists_le`) bounds by
`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`, `OneWay.uexp_const`). -/
theorem abs_gameProb_random_sub_half_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m : ℕ)
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
    |gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ - 1 / 2| ≤ m / 2 ^ n := by
  classical
  -- the random function last
  let e : (((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) × ((Fin n → Bool) → (Fin n → Bool)) ≃
      (((Fin n → Bool) → (Fin n → Bool)) × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) :=
    { toFun := fun w => ((w.2, w.1.1), w.1.2)
      invFun := fun w => ((w.1.2, w.2), w.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  set p : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → ℝ := fun t =>
    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
      (ℓ (label (fun z => firstBit (R z)) t.1.1) t.1.2 t.2 == firstBit (R t.2)) = true) with hp
  have hgame : gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ = uexp p := by
    rw [gameProb_eq, ← uprob_comp_equiv e, uprob_prod]
    rfl
  -- the bad event: the fresh point is an example
  set bad : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → Prop :=
    fun t => ∃ j ∈ (Finset.univ : Finset (Fin m)), t.1.1 j = t.2 with hbad
  -- the coupling bound against the constant `½`: off the bad event, `p = ½`
  have hdev : |uexp p - 1 / 2| ≤ uprob bad := by
    have h := MultiMsg.abs_uexp_sub_le_uprob p (fun _ => 1 / 2) bad
      (fun _ => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun _ => ⟨by norm_num, by norm_num⟩)
      (fun t hb => uprob_flip_half hn ℓ t.1.1 t.1.2 t.2 fun j hj => hb ⟨j, Finset.mem_univ j, hj⟩)
    rwa [OneWay.uexp_const] at h
  -- the union bound
  have hj : ∀ j : Fin m, uprob (fun t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) =>
      t.1.1 j = t.2) = 1 / 2 ^ n := by
    intro j
    rw [uprob_prod]
    simp only [uprob_eq_point, OneWay.uexp_const]
  have hunion := uprob_exists_le (Finset.univ : Finset (Fin m))
    (fun j (t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) => t.1.1 j = t.2)
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
  rw [hgame]
  refine hdev.trans (hunion.trans (le_of_eq ?_))
  ring

end Random

end TCSlib.Cryptography.Randomness.LearnPRF

## ===== TCSlib/Cryptography/Randomness/Learning/Sample.lean@94b31964 =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The learner's input, computed from the distinguisher's encoded tuple

The distinguisher of [PS10, Theorem 179.1, proof] queries its oracle at `m(n) + 1` points
`ρ_0, …, ρ_m` and receives the encoded tuple of the pairs `(ρ_j, g(ρ_j))`: the concatenation
`tupleWord ρ g` of the blocks `⟨⟨ρ_j, g(ρ_j)⟩, []⟩`, each of `6n + 6` bits (the query chain of
`MultiMsg.exists_queryChain_nuppt`). It runs the learner on the labelled sample of the first
`m(n)` points, labelled by the first bits of the answers, and the last point, and compares the
prediction with the first bit of the last answer.

This file computes, by polynomial-time string functions of `⟨1^n, tupleWord ρ g⟩`:
- `learnIn m`: the learner's input `⟨S, ρ_m⟩`, where `S` is the nested pairs of the labelled
  examples `⟨ρ_j, [g(ρ_j)₁]⟩` (the sample encoding of the learning game);
- `lastLabel m`: the first bit of the last answer.

The labelled sample is a fold of pairs, which is a flat concatenation (`foldr_pairEncode_nil`),
so it is a block map of the first `m(n)` blocks of the tuple (`MultiMsg.flatMap_range_blocks`).

## Main definitions

* `LearnPRF.firstBit`, `LearnPRF.tupleWord`, `LearnPRF.relabel`, `LearnPRF.sampleLen`,
  `LearnPRF.learnIn`, `LearnPRF.lastLabel`.

## Main results

* `LearnPRF.foldr_pairEncode_nil`: a fold of pairs ending in `[]` is a concatenation.
* `LearnPRF.polyTimeComputable_learnIn`, `LearnPRF.polyTimeComputable_lastLabel`.
* `LearnPRF.learnIn_tupleWord`, `LearnPRF.lastLabel_tupleWord`: their values on an encoded tuple.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity Turing TCSlib.Cryptography

/-! ### Folds of pairs -/

/-- **A fold of pairs ending in `[]` is a concatenation:**
`L.foldr pairEncode [] = L.flatMap (fun a => pairEncode a [])`.

**Proof sketch.** Induction on `L`; `pairEncode a w = pairEncode a [] ++ w`
(`GGMRed.pairEncode_append_right`). -/
theorem foldr_pairEncode_nil (L : List (List Bool)) :
    L.foldr pairEncode [] = L.flatMap fun a => pairEncode a [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, ih, List.flatMap_cons, ← GGMRed.pairEncode_append_right,
      List.nil_append]

/-! ### Words -/

/-- The first bit of an `n`-bit string, `false` for `n = 0`: `firstBit y = ⟦y⟧.headD false`. -/
def firstBit {n : ℕ} (y : Fin n → Bool) : Bool := (List.ofFn y).headD false

/-- `firstBit y = (List.ofFn y).headD false`. -/
theorem firstBit_eq {n : ℕ} (y : Fin n → Bool) : firstBit y = (List.ofFn y).headD false := rfl

/-- **The encoded tuple** of the pairs `(ρ_j, g(ρ_j))`: the concatenation of the blocks
`⟨⟨ρ_j, g(ρ_j)⟩, []⟩` (as in `MultiMsg.exists_queryChain_nuppt`):
`tupleWord ρ g = (List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦g (ρ j)⟧⟩, []⟩).flatten`. -/
def tupleWord {n k : ℕ} (ρ : Fin k → Fin n → Bool) (g : (Fin n → Bool) → (Fin n → Bool)) :
    List Bool :=
  (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (g (ρ j)))) []).flatten

/-- `tupleWord ρ g = (List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦g (ρ j)⟧⟩, []⟩).flatten`. -/
theorem tupleWord_eq {n k : ℕ} (ρ : Fin k → Fin n → Bool) (g : (Fin n → Bool) → (Fin n → Bool)) :
    tupleWord ρ g = (List.ofFn fun j =>
      pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (g (ρ j)))) []).flatten :=
  rfl

/-- The block of a pair `(x, y)`: `⟨⟨⟦x⟧, ⟦y⟧⟩, []⟩`. -/
private def blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- A block has `6n + 6 = histBlockLen(n)` bits. -/
private theorem length_blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    (blk p).length = MultiMsg.histBlockLen.eval n := by
  rw [blk, length_pairEncode, length_pairEncode, List.length_ofFn, List.length_ofFn,
    List.length_nil, MultiMsg.eval_histBlockLen]
  omega

/-- **Relabelling a block:** `⟨⟨x, y⟩, []⟩ ↦ ⟨⟨x, [y.headD false]⟩, []⟩`, the encoded labelled
example of the pair:
`relabel w = ⟨⟨pairFstD (pairFstD w), [(pairSndD (pairFstD w)).headD false]⟩, []⟩`. -/
def relabel (w : List Bool) : List Bool :=
  pairEncode (pairEncode (pairFstD (pairFstD w)) [(pairSndD (pairFstD w)).headD false]) []

/-- `relabel w = ⟨⟨pairFstD (pairFstD w), [(pairSndD (pairFstD w)).headD false]⟩, []⟩`. -/
theorem relabel_eq (w : List Bool) :
    relabel w =
      pairEncode (pairEncode (pairFstD (pairFstD w)) [(pairSndD (pairFstD w)).headD false]) [] :=
  rfl

/-- Relabelling is polynomial-time: `PolyTimeComputable relabel`, for
`relabel : List Bool → List Bool`. -/
theorem polyTimeComputable_relabel : PolyTimeComputable relabel := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  exact (((hF.comp hF).pairEncode (polyTimeComputable_headD.comp (hD.comp hF))).pairEncode
    (polyTimeComputable_const [])).congr fun w => rfl

/-- The relabelled block of `(x, y)` is `⟨⟨⟦x⟧, [firstBit y]⟩, []⟩`. -/
private theorem relabel_blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    relabel (blk p) = pairEncode (pairEncode (List.ofFn p.1) [firstBit p.2]) [] := by
  rw [relabel_eq, blk, pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, firstBit_eq]

/-! ### The learner's input and the last label -/

/-- The length `m(n) · (6n + 6)` of the first `m(n)` blocks:
`sampleLen m = m · histBlockLen` as a `PolyExpr`. -/
def sampleLen (m : PolyExpr) : PolyExpr := .mul m MultiMsg.histBlockLen

/-- `(sampleLen m).eval n = m(n) · (6n + 6)`. -/
theorem sampleLen_eval (m : PolyExpr) (n : ℕ) : (sampleLen m).eval n = m.eval n * (6 * n + 6) := by
  rw [sampleLen, PolyExpr.eval_mul, MultiMsg.eval_histBlockLen]

/-- The relabelled first `m(|u|)` blocks of `s`, on `⟨u, s⟩`: the block map of `relabel` over
`s.take (sampleLen m (|u|))` (the function of `Complexity.polyTimeComputable_blockMap`):
`sampleOf m ⟨u, s⟩ = (range (|s'| / b)).flatMap fun i => relabel ((s'.drop (i * b)).take b)`,
with `s' = s.take ((sampleLen m).eval |u|)` and `b = histBlockLen.eval |u|`. -/
def sampleOf (m : PolyExpr) (z : List Bool) : List Bool :=
  (List.range (((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).length /
      MultiMsg.histBlockLen.eval (pairFstD z).length)).flatMap fun i =>
    relabel ((((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).drop
      (i * MultiMsg.histBlockLen.eval (pairFstD z).length)).take
        (MultiMsg.histBlockLen.eval (pairFstD z).length))

/-- `sampleOf m z` is the block map of `relabel` over the first `sampleLen m` bits:
`sampleOf m ⟨u, s⟩ = (range (|s'| / b)).flatMap fun i => relabel ((s'.drop (i * b)).take b)`,
with `s' = s.take ((sampleLen m).eval |u|)` and `b = histBlockLen.eval |u|`. -/
theorem sampleOf_eq (m : PolyExpr) (z : List Bool) :
    sampleOf m z =
      (List.range (((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).length /
          MultiMsg.histBlockLen.eval (pairFstD z).length)).flatMap fun i =>
        relabel ((((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).drop
          (i * MultiMsg.histBlockLen.eval (pairFstD z).length)).take
            (MultiMsg.histBlockLen.eval (pairFstD z).length)) := rfl

/-- The last block's pair `⟨x, y⟩` on `⟨u, s⟩`:
`lastPair m ⟨u, s⟩ = pairFstD (s.drop ((sampleLen m).eval |u|))`. -/
def lastPair (m : PolyExpr) (z : List Bool) : List Bool :=
  pairFstD ((pairSndD z).drop ((sampleLen m).eval (pairFstD z).length))

/-- `lastPair m z = pairFstD ((pairSndD z).drop ((sampleLen m).eval |pairFstD z|))`. -/
theorem lastPair_eq (m : PolyExpr) (z : List Bool) :
    lastPair m z = pairFstD ((pairSndD z).drop ((sampleLen m).eval (pairFstD z).length)) := rfl

/-- **The learner's input** on `⟨1^n, s⟩`: `⟨sampleOf m z, x⟩`, the relabelled first `m(n)`
blocks and the point `x` of the last block: `learnIn m z = ⟨sampleOf m z, pairFstD (lastPair m z)⟩`.
-/
def learnIn (m : PolyExpr) (z : List Bool) : List Bool :=
  pairEncode (sampleOf m z) (pairFstD (lastPair m z))

/-- `learnIn m z = ⟨sampleOf m z, pairFstD (lastPair m z)⟩`. -/
theorem learnIn_eq (m : PolyExpr) (z : List Bool) :
    learnIn m z = pairEncode (sampleOf m z) (pairFstD (lastPair m z)) := rfl

/-- **The last label** on `⟨1^n, s⟩`: the first bit of the answer of the last block,
`lastLabel m z = (pairSndD (lastPair m z)).headD false`. -/
def lastLabel (m : PolyExpr) (z : List Bool) : Bool := (pairSndD (lastPair m z)).headD false

/-- `lastLabel m z = (pairSndD (lastPair m z)).headD false`. -/
theorem lastLabel_eq (m : PolyExpr) (z : List Bool) :
    lastLabel m z = (pairSndD (lastPair m z)).headD false := rfl

/-- The last block's pair is polynomial-time (`polyTimeComputable_pairDropPoly`):
`PolyTimeComputable (lastPair m)`, for `lastPair m : List Bool → List Bool`. -/
theorem polyTimeComputable_lastPair (m : PolyExpr) : PolyTimeComputable (lastPair m) :=
  (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairDropPoly (sampleLen m))).congr
    fun _ => rfl

/-- The learner's input is polynomial-time: the block map of `relabel`
(`Complexity.polyTimeComputable_blockMap`) after the head cut
(`polyTimeComputable_pairTakePoly`), paired with the last point: `PolyTimeComputable (learnIn m)`,
for `learnIn m : List Bool → List Bool`. -/
theorem polyTimeComputable_learnIn (m : PolyExpr) : PolyTimeComputable (learnIn m) := by
  have hcut : PolyTimeComputable fun z => pairEncode (pairFstD z)
      ((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)) :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairTakePoly (sampleLen m))
  have hS : PolyTimeComputable (sampleOf m) :=
    ((polyTimeComputable_blockMap MultiMsg.histBlockLen polyTimeComputable_relabel).comp
      hcut).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, sampleOf_eq]
  exact (hS.pairEncode (polyTimeComputable_pairFstD.comp (polyTimeComputable_lastPair m))).congr
    fun _ => rfl

/-- The last label, as a one-bit output, is polynomial-time:
`PolyTimeComputable fun z => [lastLabel m z]`, for `z ↦ [lastLabel m z] : List Bool → List Bool`. -/
theorem polyTimeComputable_lastLabel (m : PolyExpr) :
    PolyTimeComputable fun z => [lastLabel m z] :=
  (polyTimeComputable_headD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_lastPair m))).congr fun _ => rfl

/-! ### Values on an encoded tuple -/

section Values

variable {n : ℕ} (m : PolyExpr) (ρ : Fin (m.eval n + 1) → Fin n → Bool)
  (g : (Fin n → Bool) → (Fin n → Bool))

/-- The encoded tuple is the first `m(n)` blocks followed by the last block, and the first part
has `sampleLen m` bits. -/
private theorem tupleWord_split :
    tupleWord ρ g =
      (List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten ++
        blk (ρ (Fin.last _), g (ρ (Fin.last _))) ∧
    ((List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten).length =
      (sampleLen m).eval n := by
  refine ⟨?_, ?_⟩
  · rw [tupleWord_eq, List.ofFn_succ', List.concat_eq_append, List.flatten_append,
      List.flatten_singleton]
    rfl
  · rw [MultiMsg.length_flatten_of_length (MultiMsg.histBlockLen.eval n) _ (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        exact length_blk _), List.length_ofFn, sampleLen_eval, MultiMsg.eval_histBlockLen]

/-- **The learner's input on an encoded tuple:** on `⟨1^n, tupleWord ρ g⟩`, `learnIn m` is the
pair of the nested labelled examples `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points and
the last point `⟦ρ_m⟧`:
`learnIn m ⟨1^n, tupleWord ρ g⟩ =
⟨(ofFn j ↦ ⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩).foldr pairEncode [], ⟦ρ_m⟧⟩` (`j < m(n)`).

**Proof sketch.** Split the tuple into its first `m(n)` blocks and the last
(`tupleWord_split`); the head cut keeps the first part and the tail cut the last block
(`List.take_left'`, `List.drop_left'`). The block map over the first part relabels each block
(`MultiMsg.flatMap_range_blocks`, `MultiMsg.flatMap_ofFn`, `relabel_blk`), and the fold of the
examples is the same concatenation (`foldr_pairEncode_nil`). -/
theorem learnIn_tupleWord :
    learnIn m (pairEncode (List.replicate n true) (tupleWord ρ g)) =
      pairEncode ((List.ofFn fun j : Fin (m.eval n) => pairEncode (List.ofFn (ρ j.castSucc))
          [firstBit (g (ρ j.castSucc))]).foldr pairEncode [])
        (List.ofFn (ρ (Fin.last _))) := by
  obtain ⟨hsplit, hlen⟩ := tupleWord_split m ρ g
  have hb : 0 < MultiMsg.histBlockLen.eval n := by rw [MultiMsg.eval_histBlockLen]; omega
  have hblocks : ∀ x ∈ List.ofFn (fun j : Fin (m.eval n) => (ρ j.castSucc, g (ρ j.castSucc))),
      (blk x).length = MultiMsg.histBlockLen.eval n := fun x _ => length_blk x
  have hflat : (List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten =
      (List.ofFn fun j : Fin (m.eval n) => (ρ j.castSucc, g (ρ j.castSucc))).flatMap blk :=
    (MultiMsg.flatMap_ofFn _ blk).symm
  rw [learnIn_eq, sampleOf_eq, lastPair_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, hsplit, List.take_left' hlen, List.drop_left' hlen, blk,
    pairFstD_pairEncode, pairFstD_pairEncode, hflat,
    MultiMsg.flatMap_range_blocks blk relabel hb _ hblocks, foldr_pairEncode_nil,
    MultiMsg.flatMap_ofFn, MultiMsg.flatMap_ofFn]
  congr 2
  exact congrArg List.ofFn (funext fun j => relabel_blk _)

/-- **The last label on an encoded tuple:** on `⟨1^n, tupleWord ρ g⟩`, `lastLabel m` is the first
bit of the last answer: `lastLabel m ⟨1^n, tupleWord ρ g⟩ = firstBit (g ρ_m)`. -/
theorem lastLabel_tupleWord :
    lastLabel m (pairEncode (List.replicate n true) (tupleWord ρ g)) =
      firstBit (g (ρ (Fin.last _))) := by
  obtain ⟨hsplit, hlen⟩ := tupleWord_split m ρ g
  rw [lastLabel_eq, lastPair_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    hsplit, List.drop_left' hlen, blk, pairFstD_pairEncode, pairSndD_pairEncode, firstBit_eq]

end Values

end TCSlib.Cryptography.Randomness.LearnPRF
