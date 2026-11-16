## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/pack-r2.md =====

# Gate 37 · The semi-honest composition theorem (`sc-compose`, [Gol04, §7.3.1, Theorem 7.3.3]) · round 2

The auditor is Codex. Round 1 was HOLD (0/2/1); its findings are `findings/gate37-sc-compose-findings.md` (SHA-256
`21203fb8…`). This round re-audits the fixes of G37-01, G37-02 and G37-03, one side effect of the G37-01 import that
changes two statements in text, and duplication since round 1. The round-1 pack (`pack.md`) still defines the scope;
its questions stand for anything round 1 left unverified.

- **PR:** draft [PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324), now at
  `4bd2d80bfb58fab5243c66c9f1a697a30b533756` (branch `land/pass-shelat-sc-compose`, tree
  `769bcea676ef7935fe3d4a5f6c1980ce10d983c1`). Round 1 audited `a6eaebd78c48e7fdfd06263edb84b70bc00ec593`.
- **Base:** `6ce4658db08a1dc2a03a149987197660db078011`, as in round 1. **No rebase:** the head is the round-1 head
  plus one commit. Since round 1 the tip has merged #318 (sc-ot), #319 (canonizer) and #323 (sc-garble), all on
  2026-11-16; the tip is now `c2f6adeb3f3de2a21352a57e64c6a11a79cc220e`.
- **New since round 1:** **LE-gate37** `4bd2d80b` on `a6eaebd7`, by the maintainer (author and committer Claude,
  SSH-signed): 10 files under `ComposeSecurity/`, +88/−36. It was fast-forward pushed; `refs/pull/324/head` is
  `4bd2d80b`.
- **Resolutions:** `resolutions-r1.md` (ruling Seyoon, 2026-11-16: "re-point via import", headers kept; G37-03
  docstrings), and the decision-log rows of 2026-11-16 (in `verification-r2.zip`).
- **Pending merge condition** (not an audit item; § 6): the merge order. #324 merges **after** #326 and #327.

Lean paths below are under `TCSlib/Cryptography/SecureComputation/` unless they start with `TCSlib/`; `CS/` is
`ComposeSecurity/`.

## What to check

### 1. G37-01 and G37-02: are both lemmas now the public `CommitmentLemmas` lemmas, with headers kept?

The diff is `landing/le-gate37.diff` in the round-2 evidence (= `git diff a6eaebd7 4bd2d80b`). The public lemmas,
in `TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean` (blob unchanged since the base):

```lean
-- :233
theorem encodeMsgs_append (L M : List (List Bool)) :
    Strategy.encodeMsgs (L ++ M) = Strategy.encodeMsgs L ++ Strategy.encodeMsgs M
-- :241
theorem length_encodeMsgs_le (L : List (List Bool)) (M : ℕ) (hM : ∀ m ∈ L, m.length ≤ M) :
    (Strategy.encodeMsgs L).length ≤ L.length * (2 * M + 2)
```

The edit, with doc comments deleted (`checks/lecheck.txt`):

```lean
-- CS/Machines.lean: one import added after the last import
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
-- CS/Machines.lean:145 (was 143); the 7-line induction is replaced
theorem encodeMsgs_append (a b : List (List Bool)) :
    Strategy.encodeMsgs (a ++ b) = Strategy.encodeMsgs a ++ Strategy.encodeMsgs b :=
  TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append a b
-- CS/Bounds.lean:54 (was 53); no import (Bounds imports Machines); the 2-line proof is replaced
theorem length_encodeMsgs_le (l : List (List Bool)) (c : ℕ) (h : ∀ w ∈ l, w.length ≤ c) :
    (Strategy.encodeMsgs l).length ≤ l.length * (2 * c + 2) :=
  TCSlib.Cryptography.CommitmentLemmas.length_encodeMsgs_le l c h
```

- **Headers:** both byte-identical to round 1 (the text before `:=`; only ` by` and the tactic block change). Each
  docstring gains one sentence: "It is the public `CommitmentLemmas.<name>` (`ZeroKnowledge/CommitmentLemmas.lean`)."
  The older parenthetical attributions are kept.
- **The import is acyclic** (`checks/lecheck.txt`): no unit module is in the import closure of `CommitmentLemmas`.
  `CS/Machines`' closure grows from 82 to 129 modules (itself included), **exactly +47**, none under
  `ComposeSecurity/`; the unit's closure grows from 98 to 145 by the same 47. The added modules are listed there; they
  include `TCSlib/Complexity/CircuitComplexity/DAGCircuit` (so 13 unit modules are now downstream of #323's change,
  § 6) and `Asymptotic/CollectionsHelpers` (§ 2).

Are both re-derivations proof only, and do they use the published lemmas as stated?

### 2. The side effect: `ComposeSim.splitCoins` in `CS/Runs.lean`. Please confirm the elaborated types are identical.

**decls2 against round 1 is not empty.** It reports **2 statements CHANGED, in text only**: `composeCoins_fst` and
`composeCoins_snd` (`checks/decls2-a6eaebd7-vs-4bd2d80b.tsv`; 193 unchanged). These are new helper declarations of
this PR, not frozen ones.

**Why.** The new import brings `Asymptotic/CollectionsHelpers.lean` into `CS/Runs`' closure, and with it

```lean
-- TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean:145
def splitCoins (a b : ℕ) : (Fin (a + b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)
```

`CS/Runs.lean` declares its own `ComposeSim.splitCoins {m a q b : ℕ} (h : m = a + q * b) :
(Fin a → Bool) × (Fin q → Fin b → Bool) ≃ (Fin m → Bool)` (line 52) and uses it bare inside
`namespace TCSlib.Cryptography.SecureComputation.HybridProtocol`. There, the enclosing namespace's
`TCSlib.Cryptography.splitCoins` wins over `open ComposeSim`, and even over `open ComposeSim (splitCoins)`
(`checks/name-resolution-probe.txt` in the evidence ZIP: a probe whose two `#check @splitCoins` both print the
`CollectionsHelpers` type). The first attempt of the edit (`b4900559`, amended before any use, on no ref) failed with 5
errors in `CS/Runs` (`build-first-attempt/`).

**The fix** qualifies the bare uses outside `namespace ComposeSim`: **4 occurrences in 3 declarations**
(`checks/splitcoins.txt`). (The LE-gate37 PROVENANCE and the decision log say "three uses"; there are three
declarations, and `composeCoins` has two occurrences.)

```lean
-- CS/Runs.lean:160, def composeCoins (body, 2 occurrences), a new helper def of this PR
      ((ComposeSim.splitCoins (H.composeP_coinLen_eq ρ n)).prodCongr
        (ComposeSim.splitCoins (H.composeV_coinLen_eq ρ n))))
-- CS/Runs.lean:170, theorem composeCoins_fst (statement)
      ComposeSim.splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1) :=
-- CS/Runs.lean:178, theorem composeCoins_snd (statement)
      ComposeSim.splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2) :=
```

**The case that it is the same constant** (all re-checked from git objects, `checks/splitcoins.txt`):
- **At round 1** `CollectionsHelpers` is not in `CS/Runs`' closure (86 modules). The only declaration named
  `splitCoins` in that closure is `ComposeSim.splitCoins` (`CS/Runs.lean:52`). So the bare name denoted it.
- **At the head** the closure (133 modules) has exactly two: that one and `TCSlib.Cryptography.splitCoins`. Every
  `namespace … ComposeSim` line in `TCSlib/` opens `TCSlib.Cryptography.SecureComputation.ComposeSim` (`CS/Runs.lean:48`
  inside `namespace TCSlib.Cryptography.SecureComputation`, and four helpers). So `ComposeSim.splitCoins` names the
  `CS/Runs.lean:52` constant.
- **The two constants cannot be confused silently.** `TCSlib.Cryptography.splitCoins` takes two explicit naturals and
  no proof; applied to `(H.composeP_coinLen_eq ρ n)` it does not elaborate (the 5 errors of `b4900559`).
- **The write-back is exact.** `CS/Runs.lean` at the head, with each `ComposeSim.splitCoins` written back as
  `splitCoins`, equals the round-1 file once doc comments are deleted on both sides. The three declarations are then
  byte-identical to round 1, and their docstrings are unchanged.
- **Build.** The rebuild compiled `CS/Runs` and all 20 other affected modules, rc 0 (§ 4). Every use of
  `composeCoins_fst` and `composeCoins_snd` is in `CS/Runs.lean` (rewrite steps at lines 256, 272, 287–288, 306–307,
  383–384, 424–425, 442, 559 and 630), in code unchanged since round 1.

**What is not available.** No census prints the two types. The LE-gate37 job's census is the axioms probe, and the
review's census (258 constants) is at LE-doc, before this edit. We ask you to confirm from the sources that the
elaborated statements of `composeCoins_fst` and `composeCoins_snd`, and the body of `composeCoins`, are those of
round 1. If you think a printed-type probe is needed (`#check @…` of both at both heads), say so as a condition, and
say whether it should block.

Is the qualification acceptable as a text-only change to two new helper statements, or would you prefer another fix
(renaming `ComposeSim.splitCoins`, or an import that avoids `CollectionsHelpers`)?

### 3. G37-03: are all truncated formulas complete, docstrings only?

`checks/formulas.txt`:
- **Docstrings changed: 22.** They are the 20 formulas that LE-doc cut at 240 characters with " …" (`landing/le-gate37-plan.tsv` in
  the evidence: 254–1040 characters), plus the G37-01/02 sentences of § 1.
  - **The eleven named readers** (`asmView_eq`, `asmW_eq`, `runW_eq`, `ansW_eq`, `composePW_eq`, `composeVW_eq`,
    `goodRuns_iff`, `sampleA_eq`, `sampleB_eq`, `phiV_eq`, `hybW_eq`) all changed.
  - **The nine others the same LE-doc rule cut** are completed too, so that no truncated formula is left:
    - the defs `GoodRuns`, `sampleA` and `sampleB`, whose formula is their reader's;
    - `exists_main_msgs_le`, `exists_main_outV_le` and `exists_main_outP_le` (`CS/Lengths`);
    - `runMsg_composeCoins` (`CS/Runs`);
    - `exists_tmplA_bound` (`CS/SideA`) and `exists_tmplB_bound` (`CS/SideB`).
- **No "…`" is left in the unit.** 11 lines still contain "…". All are worker prose with elided arguments in other
  declarations' docstrings, for example `segW`, `asmW … ⟨…⟩`, `runW …`, `⟦f_A(…)⟧` and Chain's `[f 0, …, f (L−1)]`;
  they are listed in the check.
- **Docstrings only:** 7 of the 10 edited files are identical with doc comments deleted. The other three are
  `CS/Machines`, `CS/Bounds` and `CS/Runs`, whose code changes are §§ 1–2. Every line is at most 100 characters; the
  largest file is `CS/Runs` (637 lines).

Does each completed formula state its declaration's conclusion, in Lean argument order? The round-1 record correction
(20 truncated insertions, not 15) is reflected here.

### 4. The evidence and the rebuild

**Evidence** (`landing-r1/`): `gate37-le-evidence.zip`, SHA-256
`382c09f4f64ab881be3bdfd6de867e52a31ccd2f708c49d39b3bc9f126e701ce`. It has 234 entries: 202 files, which are the 201
paths of its manifest `evidence-SHA256SUMS` plus `SHA256SUMS`. Its `PROVENANCE.txt` is beside it.
- **Statements:** `statements/decls2-vs-parent.tsv` has exactly the two CHANGED rows of § 2. `statements/header-check.txt`
  finds 0 header differences in 9 files and exactly those 2 in `CS/Runs`.
  - Re-checked from git objects (`checks/lecheck.txt`): all 196 declarations of the 16 files keep their order. Their
    headers and definition blocks are identical to round 1, except `composeCoins` (its block) and its two lemmas.
  - decls2 against the base is still **185 ADDED, 0 CHANGED, 0 REMOVED** (`checks/decls2-6ce4658d-vs-4bd2d80b.tsv`).
  - The owned file `ComposeSecurity.lean` is untouched, so the frozen check stands: its 11 pre-existing headers are
    identical.
- **Build** (`build/`): **21/21 rc 0**, 0 errors in both forms (G26-N1), substring "error" 0, 0 sorry, 0 warnings,
  204 s.
  - The 21 modules are the 16 unit modules, their downstream `YaoReal`, `SecureComputation` and root `TCSlib`, and
    both `audits/*/Checks`.
  - They were built on the **combined tree** (§ 6), because `CS/Machines` is also downstream of #326.
  - The 10 edited modules have new sources. The other 11 are byte-identical, in source and olean, to reference builds.
  - Every built source equals its blob at `4bd2d80b`, at the tip-merged tree, and at the final merged tree on the
    current tip (`checks/srcequality.txt`).
- **Rule 10** (`rule10/`): the seals of the two owner files `CS/Machines` and `CS/Bounds`, strict A/B and coe A/B,
  were all run with `-DmaxErrors=0`. All 8 probes give rc 0 and 0 errors, with install and EOF records. Requests:
  Machines 1826/1827/1825/1826, Bounds 1828/1829/1827/1828.
  - **Controls:** coe has 8 probes and 8 sealed negatives, `ALL_OK`. Strict has 8 probes and 12 negatives; each
    negative fails exactly once, and `ctlCoeReader` fails under the strict seal (the known harness effect).
  - **`CS/Runs` was not re-sealed.** Its code change only qualifies a name (§ 2), and round 1's seals of it stand. Say
    if you disagree.
- **Axioms** (the combined probe at `639d16d9`): `composeP_efficient`, `composeV_efficient`, `hbcSecure_compose` and
  `polyTime_compose` use `[propext, Classical.choice, Quot.sound]`. `yaoProtocol_hbcSecure`'s `sorryAx` traces only to
  `yaoHybrid_polyTime` and `yaoHybrid_simulators` (sc-yao).
- **Lint:** 92 FAIL / 101 WARN, with the same line set as the review's landing head.

### 5. Duplication: is there any new undisclosed copy since round 1?

`checks/dupscan.txt`:
- **(A) Since round 1** the only code lines changed in the unit are those of §§ 1–2. No declaration is added or
  removed: the 196 names are round 1's.
- **(B) Reading-lemma lines:** the lines added since the base that use a DL-47-class reader, a coin-length lemma or
  the G37-01/02 lemmas are listed. The new ones are the two `CommitmentLemmas` calls.
- **(C) Statement scan** (binders and type after whitespace normalisation, name excluded). Each of the 153 theorems
  new at the head was compared against the files the tip changed since the base (43, including #318, #319 and
  #323) and against #326 and #327. There are **0 hits**. No new name of #324 is declared in a file any of them changed
  (`checks/namecheck.txt`).
- **(D) The same scan against the whole tree** (20722 theorems in 1279 files) has **8 hits, all DL-49 items:**
  - `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly` and `encodeMsgs_eq_flatMap`;
  - the `padTo` family `padTo_poly`, `length_padTo` and `ofFn_padFin`. The worker's checkpoint-1 table (`worker/cp1/REPORT.md:108` in round 1's `verification.zip`) lists all
    three, with `padTo`, as restated from `ThreeColoring/Machines.lean:303–327`;
  - the third `negligible_polyExpr_mul`, which matches `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport.lean:267`).
  - The two G37 lemmas are not hits, because their binder names differ from the public ones.
- **DL-49 and the other recorded items are not findings.** Any further undisclosed duplicate of a public lemma is a
  major, as in round 1.

### 6. The merge interaction and the integration evidence

`git merge-tree --write-tree 4bd2d80b <x>` is clean for each, and no path is shared (`checks/mergetrees.txt`):

| `<x>` | head | merged tree | downstream of both (`checks/downstream.txt`) |
|---|---|---|---|
| the tip | `c2f6adeb` | `b90cbea6` | 16: the 13 unit modules that import `CS/Machines`, `YaoReal`, `SecureComputation`, root `TCSlib` (through #323's `DAGCircuit`, merged) |
| #326 (derand) | `c27005d6` | `fa624a7e` | the same 16 (#326's `ClassP/DTIME` and `Build/IterateFind` are in the unit closure) |
| #327 (seq-zk) | `bd19c433` | `ae43ea76` | root `TCSlib` |
| #318 (merged) | `b0bad23a` | `4a910595` | 3: `SecureComputation`, `YaoReal`, root `TCSlib` |
| #319 (merged) | `47daa907` | `dd0ac950` | root `TCSlib` |
| #323 (merged) | `8c3f3e3f` | `21239a06` | the same 16 |

#318, #319 and #323 are ancestors of the tip (merge commits `51a25911`, `0053d7c1`, `4ba8f126`); they are included as
the dispatch asked.

**The combined build** (`integration/`, evidence `4f8cb374…`; records `maintainer/int-all-open-2026-11-16/`). It built
the records tip of that time `b0ebd475` plus all six PRs (#324 at this head) as tree
`3fb05ea062395caf069c09643a8caf751d3ad6da`: **694/694 rc 0**, 0 errors in both forms, then the 21-module #324 rebuild.
Re-checked against the current tip (`checks/integration.txt`):
- `b0ebd475..c2f6adeb` changes 25 Lean paths, all from #318, #319 and #323; the other paths are records.
- Merging #324, #326 and #327 onto `c2f6adeb`, in **all six orders**, is clean at every step and ends in the same tree
  `e0d63d61`. Its `TCSlib` and `audits` subtrees equal the built tree's. All 694 built sources equal their blobs there.
- So the combined build is exactly the final state of the remaining merges, in any order.

**Merge order (not an audit item).** #324 alone on the tip was not built. Its downstream is 19 modules, but their
environment needs tip-state oleans for modules that #323 (now merged) and #326 also touch, and no build has that state.
The intermediate states tip + #326, tip + #327 and tip + #326 + #327 are not built either. **#324 merges last**, so
that its merge produces the built tree. Any rebuild for whichever of #326 and #327 merges second is the maintainer's,
if required. What you can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions and slips (not findings)

- **"PUSH: not done" in `landing-r1/PROVENANCE.txt`**: written by the job. The maintainer then fast-forward pushed
  `4bd2d80b`; the remote head is that commit.
- **"three uses"** in the PROVENANCE and the decision log: 4 occurrences in 3 declarations (§ 2).
- **The docstrings of `composeCoins_fst` and `composeCoins_snd`** still write `splitCoins …` unqualified (their LE-doc
  formulas, unchanged by LE-gate37). Say whether you read that as a misstatement.
- **Line numbers:** `encodeMsgs_append` is now `CS/Machines.lean:145` (round 1: 143), `length_encodeMsgs_le`
  `CS/Bounds.lean:54` (53).
- **The PR description is still round 1's.** It does not mention LE-gate37; the maintainer updates it before #324 is
  marked ready (it is not in this pack).
- **The combined build ran on the records tip `b0ebd475`**, before #318, #319 and #323 merged. § 6 shows that this
  makes no difference to the built tree.
- **Job-local names.** The PROVENANCE files refer to `$SP` paths and to `../gate37-le-evidence.zip`; the records
  copies have the same bytes.

## Evidence files

- **`resolutions-r1.md`** and **`findings/`**: the round-1 dispositions and findings.
- **`landing-r1/`**: `PROVENANCE.txt` (= the ZIP's), `gate37-le-evidence.zip` and its manifest. The patch is the
  ZIP's `landing/patch/`; the diff `landing/le-gate37.diff`.
- **`integration/`**: the combined build of all open PRs: `PROVENANCE.txt`, `int-all-open-evidence.zip` (1296 entries;
  its 1249 files are the 1248 manifest paths plus `SHA256SUMS`) and `evidence-SHA256SUMS`.
- **`verification-r2.zip`**: `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each source.
  - Byte-identical originals at records `c2f6adeb3f3de2a21352a57e64c6a11a79cc220e`: the decision log, the duplication
    ledger (DL-49), the deferred-work register and the sc-compose review.
  - `checks/`, generated from git objects alone: merge trees, downstream, names, integration, source equality, the
    series, the edit, the `splitCoins` qualification, the formulas, the duplication scans and decls2, with their
    scripts.
- **`pr.diff-r2.txt`**: `git diff origin/cryptography/pass-shelat-ch2-4...4bd2d80b`, which equals `6ce4658d..4bd2d80b`
  byte for byte (16 paths, 4632 insertions, 60 deletions).
- **`source-head-r2.json`**: hashes, line counts and over-width counts of the 16 changed files at `4bd2d80b` (10
  differ from round 1's `source-head.json`; none over 100 characters).
- **`sources-r2.zip`**: the source closure at `4bd2d80b` of every changed module, 145 files (round 1: 98; the 47 added
  are the `CommitmentLemmas` closure of § 1).
- **Round 1:** `outbox/gates/37-sc-compose-gate/` on the exchange at `5fab5874b1411ab7a4f8343e6dd4e1add234516b`, with
  records `c44557596ee5c714e1277891591cc8b5d51a0ab0`; `pack.md` here is its pack.

## Findings delivery

Return `gate37-sc-compose-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.
Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Say explicitly
whether the elaborated types of § 2 are identical. Report the audited head and the counts by severity. The gate
closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/resolutions-r1.md =====

# Gate 37 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 1 minor.
- **Findings:** `findings/gate37-sc-compose-findings.md`, SHA-256 `21203fb8ce90ef6f86346b0042fabbc10ef7da2a5f8ac31d484f481543877ae2`. The evidence ZIP was not supplied.
- **Audited head:** `a6eaebd78c48e7fdfd06263edb84b70bc00ec593`, records `c4455759`, exchange `5fab5874`.

The proof audit found no mathematical defect in the three targets. Codex checked:
- efficiency, by the raw-function identities;
- security, through all five steps, with ε = ε_A + ε_B;
- the edge cases: zero calls and zero rounds;
- the freeze (185/0/0), Rule 10, the axioms, the builds and the scope.

| # | Severity | Disposition |
|---|---|---|
| G37-01 | major | **To be fixed by LE-gate37** (Seyoon's ruling, 2026-11-16: re-point via import). `ComposeMachines.encodeMsgs_append` (`ComposeSecurity/Machines.lean:143`) is re-derived from the public `CommitmentLemmas.encodeMsgs_append` (`ZeroKnowledge/CommitmentLemmas.lean:233`). Only the proof changes; the header is kept. `ZeroKnowledge.CommitmentLemmas` is imported: acyclic, +47 modules. |
| G37-02 | major | **To be fixed by LE-gate37**, the same way. `ComposeBound.length_encodeMsgs_le` (`ComposeSecurity/Bounds.lean:53`) is re-derived from the public `CommitmentLemmas.length_encodeMsgs_le` (`:241`). Only the proof changes; the header is kept. |
| G37-03 | minor | **To be fixed by LE-gate37, docstrings only.** The formulas of eleven readers were truncated with `…`: `asmView_eq`, `asmW_eq`, `runW_eq`, `ansW_eq`, `composePW_eq`, `composeVW_eq`, `goodRuns_iff`, `sampleA_eq`, `sampleB_eq`, `phiV_eq` and `hybW_eq`. Each gets its complete formula. |

**Record correction:** LE-doc has 20 truncated insertions (16 distinct prefixes), not the 15 the pack stated.

**Next:** LE-gate37 on `land/pass-shelat-sc-compose`, with the overlap record corrected. Then a rebuild and re-seal on the tip, and Gate 37 round 2.

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/findings/gate37-sc-compose-findings.md =====

# Pass–shelat Gate 37 — sc-compose

**Verdict: HOLD.** **0 blockers, 2 majors, 1 minor.** The proof audit found no mathematical defect in the three targets. Two exact public-lemma duplicates remain outside the disclosed relations and DL-49. LE-doc also leaves eleven reader docstrings with incomplete formulas.

| Item | Audited revision |
|---|---|
| [Draft PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324) | `a6eaebd78c48e7fdfd06263edb84b70bc00ec593` |
| Exchange | `5fab5874b1411ab7a4f8343e6dd4e1add234516b` |
| Campaign records | `c44557596ee5c714e1277891591cc8b5d51a0ab0` |
| PR base / issue base | `6ce4658db08a1dc2a03a149987197660db078011` / `107f1e8c218733eac12d6b9bee6fece441271317` |

## Findings

Paths below are under `TCSlib/Cryptography/`. Both existing public lemmas were verified at the **issue base**, so these are not overlaps introduced by parallel work.

| ID | Severity | File · declaration | Finding and evidence | Proposed fix |
|---|---|---|---|---|
| G37-01 | major | `SecureComputation/ComposeSecurity/Machines.lean:143` · `ComposeMachines.encodeMsgs_append` | Re-proves public `CommitmentLemmas.encodeMsgs_append`, `ZeroKnowledge/CommitmentLemmas.lean:233`. Their complete headers are identical after renaming the two bound arguments. Checkpoint 1's overlap table instead cites `ThreeColoring/Machines.encodeMsgs_eq_flatMap` and calls the append form **new**. The exact public duplicate is not disclosed and is not a DL-49 item. | Obtain an approved import or shared placement and re-derive this declaration directly from the existing public lemma, preserving its header. Correct the overlap record and refresh affected checks. An additional debt disposition would require the user's explicit ruling. |
| G37-02 | major | `SecureComputation/ComposeSecurity/Bounds.lean:53` · `ComposeBound.length_encodeMsgs_le` | Re-proves public `CommitmentLemmas.length_encodeMsgs_le`, `ZeroKnowledge/CommitmentLemmas.lean:241`, with the same hypotheses and conclusion modulo bound names. Checkpoint 2's table reports the derivation through `BinArith.length_encWords_le`, but omits this exact existing public statement. DL-49 does not cover it. | Re-derive from the existing public lemma through an approved import or shared placement, preserving the header; correct the overlap record and refresh affected checks. |
| G37-03 | minor | Eleven reader docstrings; representative: `SecureComputation/ComposeSecurity/Runs.lean:330` · `goodRuns_iff` | A defining-equation/property label followed by an unfinished Lean prefix ending in `…` does not state the complete formula. For example, `goodRuns_iff` cuts off before the first output equality is completed and omits Bob's conjunct entirely. The eleven locations are listed below and in `evidence/docs-duplicates.json`. | Give each reader a complete equation/property, using compact explained subexpressions or wrapping the full formula. Keep the declarations and proofs unchanged. |

The G37-01/02 declarations are named in the reports; what is missing is disclosure of their **exact existing public equivalents**. G37-01 is additionally classified as new. These omissions violate the brief's requirement to identify the nearest existing relative and disclose every overlap. The listed DL-49 debt is not reopened.

The eleven G37-03 locations are:

| Helper file | Readers, with declaration line |
|---|---|
| `Assembly.lean` | `asmView_eq:163`, `asmW_eq:204` |
| `Efficiency.lean` | `runW_eq:117`, `ansW_eq:221`, `composePW_eq:360`, `composeVW_eq:403` |
| `Runs.lean` | `goodRuns_iff:330` |
| `SideA.lean`, `SideB.lean` | `sampleA_eq:114`, `sampleB_eq:112` |
| `Sim.lean`, `Template.lean` | `phiV_eq:108`, `hybW_eq:76` |

**Record correction:** LE-doc contains **20** truncated formula insertions, not the pack's 15; they represent 16 distinct prefixes. All 70 inserted formulas match their declarations/readers in argument order, with truncation where applied. The other truncated entries have substantive accompanying descriptions; G37-03 concerns the eleven label-and-prefix readers above.

## Proof assessment

The author-hosted [Goldreich chapter draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/prot.ps), §7.3.1, Theorem 7.3.3, confirms the citation and simulator-composition argument. The deterministic functionalities, calls-first layout, uniform input bounds and `hM` restriction are explicit adaptations of the frozen interface.

**Efficiency:** `composeP_next_eq_composePW` and `composeV_next_eq_composeVW` hold for every history. The raw functions obtain the count, call inputs, interleaved histories, run tapes, padded answers and main activation through polynomial-time operations. `Efficient.exists_polyTime` and `GI.efficient_of_polyTime` supply the two extraction directions. The run branches establish positive run length before division bounds are used.

**Security:** the delivered proof establishes the five steps:

1. `exists_simulator` constructs each simulator before choosing the distinguisher. `phiV` recomputes call inputs from the simulated main view, uses the answer and fresh-coin blocks, and assembles the view; `phiD` preserves the other party's output.
2. `exists_correct` uses worst-input advice to bound the joint output-error event uniformly. `uprob_not_goodRuns_le` gives the union bound `L(n) ε_c(n)`. Under `GoodRuns`, the real sample equals the assembled sample. The output equalities use `hM`.
3. `exists_hyb_step` resamples one coordinate and fixes the remaining coordinates; `abs_chain_le` telescopes the chain. `exists_gap_le` chooses one worst instance per length and stores its polynomially bounded template as advice, yielding one reduction and a bound uniform over all inputs and indices. The existing multicopy interface is restricted to identical independent samplers; the disclosed generalization here permits shared main coins and index-dependent samplers.
4. `acceptProb_realA_dPhi` / `acceptProb_realB_dPhi` and `acceptProb_post_pre` identify the fully simulated sample and simulator sample with the two hybrid-model samples under the same processing. Hybrid security supplies `ε₃`.
5. Each side is bounded by `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)`, which is negligible. `hbcSecure_compose` chooses `ε = ε_A + ε_B` for each distinguisher and derives nonnegativity from the bounded advantages before bounding both sides by this sum.

Bob's proof uses `ρ.V`'s coins, Alice's received moves, `G.outB`, and `H.lead` fillers. Zero calls leave an empty hybrid-instance family and zero union/chain costs; zero run rounds leave empty message chunks. Real tape cuts are exact, `padFin` is read back through published lemmas, and the documented zero-main-round counterexample explains the necessary `hM` hypothesis.

## Verification

These are source checks and rechecks of the supplied evidence, **not a fresh Lean build**.

| Check | Result |
|---|---|
| Pack integrity | All 20 outer manifest entries, 120 verification entries and 850 review-evidence entries verify; each extracted file set equals its manifest plus `SHA256SUMS`. |
| Source provenance | All 28 bundle sections agree with their pinned git objects; all 98 source-closure files agree with the audited head. The diff reproduces with 16 paths, +4580/−60. |
| Frozen declarations | All 11 pre-existing headers and their order are byte-identical. Replayed decls2: **185 ADDED, 0 CHANGED, 0 REMOVED**. Frozen check at LE-doc: 0 differences. At the head, only the approved `polyTime_compose` sentence changes outside the targets' sketches. |
| Landing edits | LE-doc changes 70 docstrings in 13 files; LE-prose changes one docstring in one file. Removing doc comments leaves identical code in both comparisons. |
| Builds | Raw logs verify 279/279 build results and 18/18 edit-build results, all rc 0 and zero errors in both diagnostic forms. The effective 279 source hashes match LE-doc; 278 match the head, with only the approved owned-file docstring differing. |
| Rule 10 | All **64 head** and **4 base** probes pass. Probe bytes, executed-source hashes, requested names, install records and EOF records agree. Coe-A is canonical. Canonical paired controls replay as ALL_OK: 14 probes, 16 sealed negatives. Strict controls have 24 sealed negatives and exactly the eight documented `ctlCoeReader` positive failures. |
| Axioms and attributes | All 258 census rows use only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, new simp attribute or instance. The three reported abbreviations are generated match auxiliaries. |
| Documentation and sketches | The 12 `PolyTimeComputable` propositions are valid statement formulas. The three no-sketch flags are `rfl` readers with long headers. Substantive long proofs have sketches and step comments. G37-03 remains. |
| Scope and size | Only the authorized 16 paths change. Every line is at most 100 characters; every file is below 1000 lines. The supplied lint line-set comparison is unchanged. |

The published readers, coin/block readbacks, history readings and explicit-unfold evidence support the Rule-10 result. The `getD` uses singled out in the pack read filtered ranges, coin blocks or template word lists; they do not independently re-prove the generic `ofFn` readback. The disclosed private `exists_ofFn_eq` restatement is not treated as undisclosed copying.

The head integration rebuild and the required shared-downstream rebuilds with #313, #318, #319 or #323 remain **maintainer merge conditions**, as dispatched. Their absence is not an audit finding. No PR, branch or dispatch record was modified by this audit.

The gate remains **HOLD until G37-01 and G37-02 are resolved**. G37-03 is a documentation repair, not a proof-correctness objection.

**Notation:** `H`: hybrid protocol; `ρ`: subprotocol; `F`, `G`: target and called functionalities; `n`: security parameter; `L(n) = H.calls.eval n`; `Φ`: view/sample processing; `ε_c`, `ε₂`, `ε₃`: correctness, single-step and hybrid-model bounds; `ε_A`, `ε_B`: the two final party bounds.

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/landing-r1/PROVENANCE.txt =====

#324 (sc-compose) LE-gate37 (Gate 37 G37-01/02/03; Seyoon's ruling "re-point via import"), maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I; Lean 4.25.0; one Lean process at a time, only on $SP/dl-oleans; builds through scripts/lean_check_tree.sh via
  tools-used/review/runner.py (G26-N1, both error forms); probes through tools-used/runner_full.py (lean -DmaxErrors=0, no -o);
  no lake command; nothing pushed; no rebase; commit on the existing local branch in its worktree $SP/wt-land-sc-compose.
  Done inside the combined-integration job (../int-all-open/, which supplies the olean tree, the worktree $SP/wt-int-all and
  the combined commit): the coordinator's request arrived while the combined build was running, so (as instructed) that build
  was finished first and #324's affected downstream was then rebuilt on the combined tree with the new head.
Tools: legate37_edit.py, legate37_runs_fix.py (new); from the sc-compose final-r1 review (records
  fills/sc-compose/final-r1/review-evidence.zip, c11ce8bb81d2ab7bf19259740f78c1dd2006d08e14e6672f9b257a131445a24b, 850/850 OK):
  decls2.py, docaudit.py, doconly.py, doconly_sg.py, touched.py, frozencheck_lib.py, mkctl_sc.py, mkcensus_sc.py (unmodified);
  from LE-gate36 (gates/36-sc-garble/landing-r1/gate36-le-evidence.zip, f77628dd1666d7c2d5eabefce813fa6aee731a496c3d26b89f57b219c201548a,
  628/628 OK): runner_full.py, rule10_b.sh, upclosure.py, review/ (mkcollect.py, NmCollect.template.lean, mkseals_ab.py,
  mkseals_coe.py, sealsum.py, ctlcheck2.py, archived-gate10-tools/, ...), unmodified (byte-equal to the sc-compose copies).

landing (landing/): land/pass-shelat-sc-compose, parent a6eaebd78c48e7fdfd06263edb84b70bc00ec593 (= origin = refs/pull/324/head).
  HEAD 4bd2d80bfb58fab5243c66c9f1a697a30b533756, tree 769bcea676ef7935fe3d4a5f6c1980ce10d983c1; author = committer = Claude
  <noreply@anthropic.com>, SSH-signed by the environment default; subject as requested, message landing/commit-msg.txt (both
  trailers); patch landing/patch/, diff landing/le-gate37.diff (10 files, landing/le-gate37.stat).
  b49005592be4703d97affc844d88bb28a22a377e was the first commit of exactly the requested edit; its build failed (below) and
  it was amended, before any use outside this job, into 4bd2d80b (never pushed; no ref keeps it).
edit:
  G37-01 Machines.lean: `import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas` (after the last import);
    ComposeMachines.encodeMsgs_append := TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append a b (namespace checked: the
    file is in TCSlib.Cryptography.SecureComputation.ComposeMachines, the source in TCSlib.Cryptography.CommitmentLemmas,
    CommitmentLemmas.lean:233). Acyclic: Machines' local closure 81 -> 128 modules, exactly +47, none under ComposeSecurity
    (checks/closure/, upclosure.py asserts acyclicity).
  G37-02 Bounds.lean imports Machines, so no import added: ComposeBound.length_encodeMsgs_le :=
    TCSlib.Cryptography.CommitmentLemmas.length_encodeMsgs_le l c h (CommitmentLemmas.lean:241).
    Each of the two docstrings gains one pure-insertion sentence: "It is the public `CommitmentLemmas.<name>`
    (`ZeroKnowledge/CommitmentLemmas.lean`)." (The older parenthetical attributions are kept, as insertion-only was asked.)
  REQUIRED FOLLOW-UP (deviation from "proof-only in the two lemmas"): the new import brings Asymptotic/CollectionsHelpers.lean
    (TCSlib.Cryptography.splitCoins (a b : ℕ)) into Runs.lean's closure. Inside namespace
    TCSlib.Cryptography.SecureComputation.HybridProtocol, the bare `splitCoins` then resolves through the enclosing namespace
    TCSlib.Cryptography instead of the opened ComposeSim.splitCoins; even `open ComposeSim (splitCoins)` does not take
    precedence (checks/name-resolution-probe.txt). Result at b4900559: Runs.lean 5 errors (build-first-attempt/: 6 modules,
    Machines..Assembly rc 0, Runs rc 1). Fix (tools-used/legate37_runs_fix.py): the three bare uses outside namespace
    ComposeSim, in the body of def composeCoins and in the statements of composeCoins_fst / composeCoins_snd, are written
    `ComposeSim.splitCoins` -- the same constant they denoted before the import (CollectionsHelpers is not in Runs' closure at
    the parent, checks/closure/runs-closure-parent.txt). So decls2 is NOT empty: it reports these 2 statements CHANGED (text
    only; statements/decls2-vs-parent.tsv). If Gate 37 prefers another fix (e.g. renaming ComposeSim.splitCoins, or an
    import that avoids CollectionsHelpers), the commit is local and unpushed.
  G37-03 docstrings only: every LE-doc formula the sc-compose LE-doc cut at 240 characters with " …" now carries the complete
    Lean conclusion (extraction as ledoc_sc.py: own conclusion, or for a def its _eq/_iff reader's), wrapped at 100: the 11
    requested readers asmView_eq, asmW_eq (Assembly), runW_eq, ansW_eq, composePW_eq, composeVW_eq (Efficiency), goodRuns_iff
    (Runs), sampleA_eq (SideA), sampleB_eq (SideB), phiV_eq (Sim), hybW_eq (Template), and -- so that no truncated formula is
    left -- the 9 other declarations the LE-doc cut by the same rule: the defs GoodRuns, sampleA, sampleB (same formula as
    their readers) and exists_main_msgs_le, exists_main_outV_le, exists_main_outP_le (Lengths), runMsg_composeCoins (Runs),
    exists_tmplA_bound (SideA), exists_tmplB_bound (SideB). Lengths 254-1040 characters (landing/le-gate37-plan.tsv); every
    cut text located once inside its own docstring; widths <= 100 (largest file Runs.lean 637 lines).
checks:
  - statements/decls2-vs-parent.tsv (decls2.py, the 16 unit files, parent vs head): exactly the 2 Runs statements above;
    decls2.err empty. statements/header-check.txt (frozencheck_lib.compare, parent vs head, every edited file): 0 header
    differences in 9 files; Runs.lean exactly the 2 above. The encodeMsgs_append / length_encodeMsgs_le headers (the text
    before `:=`) are byte-identical; only ` by` and the tactic block after `:=` changed.
  - checks/stripped-code-diff.txt (doc and module comments stripped, parent vs head): code changes only in Machines (the
    import line and the encodeMsgs_append proof), Bounds (the length_encodeMsgs_le proof) and Runs (the three qualified
    names); 0 code lines in the other 7 files. checks/doconly.txt (doconly_sg.py): code-identical True for those 7 files,
    docstring counts unchanged everywhere, max width 100 (RESULT FAIL only because of the 3 code-changed files).
  - statements/head/: touched-vs-parent 25 CHANGED (20 formulas + 2 lemmas + composeCoins, composeCoins_fst, composeCoins_snd),
    172 UNCHANGED; docaudit (107f1e8c -> 4bd2d80b) 145 OK, 29 LABEL, 15 NO-FORMULA = the review's 14 (2 frozen targets +
    12 `PolyTimeComputable …` Prop formulas) + polyTime_compose (its docstring was rewritten by the earlier LE-prose a6eaebd7,
    a Prop formula; not touched here).
  - checks/ellipsis-grep.txt: 11 `…` remain in the unit, none a truncated formula (0 occurrences of " …`"): worker prose with
    elided arguments in other declarations' docstrings (segW_encodeMsgs, asmW_pairEncode, runW_ilayout, the def ansW,
    mainW_ilayout, mainExec_composeCoins, phiV_view; Runs' `⟦f_A(…)⟧`/`⟦f_B(…)⟧`; Chain's list `[f 0, …, f (L−1)]`).
build (build/; on the combined tree, worktree $SP/wt-int-all at the scratch merge 639d16d943d4bb4777c77ae8614cd8c2ed91f1bd =
  the combined e2e26b9e + this head; queue build/queue.txt = the 16 unit modules and their downstream (ComposeSecurity facade,
  YaoReal, SecureComputation, root TCSlib) + both audits/*/Checks, imports-first): 21/21 rc 0, 0 errors (both forms), substring
  "error" 0, 0 sorry, 0 warnings, 204 s (03:24:21-03:27:44 UTC). The 10 edited modules have new sources; the other 11 are
  byte-identical (source and olean) to the int-313-323-324 / sc-compose review / gate36 trial builds (../int-all-open/build/
  refunion-matrix.tsv). Note: Machines and Bounds are also downstream of #326 (derand), so this is the combined environment,
  not tip + #324 alone.
Rule 10 (rule10/; tools-used/rule10_b.sh with mkctl_sc.py; owners Machines.lean and Bounds.lean at 639d16d9; probes under
  G37Probe/ in the worktree, removed afterwards, rule10/probe-files-in-worktree.txt; runner_full writes no olean):
  - collector G37Probe/CollectHead (mkcollect.py; probe-runs/ rc 0; 2478 CAT lines).
  - seals strict A/B (mkseals_ab.py, B with SEAL_EVAL=1) and coe A/B (mkseals_coe.py), every run lean -DmaxErrors=0:
    seals-{A,B,coe-A,coe-B}.tsv: all 8 probes rc 0, 0 errors, install and EOF records present (requests Machines 1826/1827/
    1825/1826, Bounds 1828/1829/1827/1828).
  - paired controls (mkctl_sc.py rows PolyExpr.eval, the FinDist CoeFun instance, HybridProtocol.answersA, ComposeMachines.padTo):
    coe 8 probes, 8 sealed negatives: ctlcheck-coe.log ALL_OK True. strict 8 probes, 12 sealed negatives, each failing exactly
    once; ALL_OK False only because ctlCoeReader also fails under the strict seal (harness effect, as in the sc-compose review;
    rule10/controls-strict-attribution.txt). Unsealed controls all pass.
axioms (axioms/; the combined probe ../int-all-open/axioms/AxiomsAll, run at 639d16d9): composeP_efficient, composeV_efficient,
  hbcSecure_compose, polyTime_compose: [propext, Classical.choice, Quot.sound] (axioms/sc-compose-targets-axioms.txt);
  yaoProtocol_hbcSecure's sorryAx trace: only yaoHybrid_polyTime, yaoHybrid_simulators (axioms/deptrace.txt).
lint (lint/): campaign_style_lint.py TCSlib/Cryptography --check8b at 4bd2d80b (landing worktree): 92 FAIL / 101 WARN; FAIL/WARN
  line set identical to the review's landing-head lint (lint/linediff-review-landing-head-vs-4bd2d80b.txt empty).
PUSH: not done (not asked). New #324 head: 4bd2d80bfb58fab5243c66c9f1a697a30b533756.
SHA256SUMS: every file here except itself (paths without "./"); ../gate37-le-evidence.zip holds exactly these paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/maintainer/int-all-open-2026-11-16/PROVENANCE.txt =====

Combined integration build of every open PR (#318, #319, #323, #324, #326, #327) on the records tip, with each PR's solo coverage,
maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I throughout; Lean 4.25.0 (PATH=$HOME/.elan/bin:$PATH; `lean --version` 4.25.0 cdd38ac5); one Lean process at a time
  (ours: another job's lean on dl-oleans-2 was seen and not touched), only scripts/lean_check_tree.sh (worktree copy byte-equal to
  /home/user/tcslib/scripts/lean_check_tree.sh, checks/runner-equal.txt) through tools-used/review/runner.py (the G26-N1 runner,
  `^\S+\.lean:\d+:\d+: error[:(]`) with TCSLIB_OLEANS=$SP/dl-oleans; probes through tools-used/runner_full.py (lean
  -DmaxErrors=0, no -o); no lake command; nothing pushed; no commit or branch in /home/user/tcslib (only `git fetch`, `git worktree`
  and unreferenced `git commit-tree --no-gpg-sign` objects). The shared .lake/packages was not modified.
Method and tools: the int-313-323-324 evidence (records gates/37-sc-compose/integration/int-313-323-324-evidence.zip, SHA-256
  3917cc1e6136b8562a05e86f005c1505c5f2c2b943a0a9fdc1de3a8aac19df69), extracted into a fresh directory: 527/527 OK against
  evidence-SHA256SUMS, path set exact, SHA256SUMS = evidence-SHA256SUMS. tools-used/: unmodified copies of its tools-used/
  (review/{runner,downorder,snapshot,buildsum,sorrycensus,treecheck}.py; buildset, bothdown, bothdown3, bothdown317, refunion,
  refcmp, permod, restoreplan, tipcensus) and, from the derand review (fills/derand/final-r1/review-evidence.zip, ef0776d5...,
  1317/1317 OK), mloverlay.sh, mathlibextra.sh, restore_derand.sh, and runner_full.py (gate36-le / sc-compose copy). New:
  bothdownN.py (bothdown3.py for N seed sets), refunion2.py (refunion.py, every reference run kept separately, rc-0 records only,
  module x reference matrix), treecheck_ml.py (treecheck.py with the Mathlib overlay attributed and symlinks not followed),
  solocheck.py, soloenv.py, solorun.sh, soloverify.py (solo coverage, below).

trial merge (landing/):
  records tip b0ebd475eb0b4131449bce58462f168f27eee17b (= origin/cryptography/pass-shelat-ch2-4 after `git fetch`, unchanged
    during the job; its code equals 654323f2's: #313 merged).
  heads (refs/pull/N/head by `git ls-remote` at the start): #318 b0bad23ae611983e3323460bb8c564da90ad6e8c, #319
    47daa90792e96b93510384adbab9f6e492ccef3a, #323 8c3f3e3fe2912784f680c10f8c478d2eeeeb7f6a, #324 a6eaebd7 (then the LE-gate37
    head 4bd2d80bfb58fab5243c66c9f1a697a30b533756, see ../gate37-le/), #326 = the derand LE-doc head
    c27005d67298f79c785a4e8ac1648da0a67d3614, #327 = the seq-zk LE-doc head bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa (both from
    ../ledoc-derand-seqzk/). Merge bases (checks/pr-bases.txt): #318/#319/#327 05d26fe5, #323 1321b9cb, #324/#326 6ce4658d; each
    base's code differs from the tip's only in #313's 5 Learning files.
  `git merge-tree --write-tree --messages`, each rc 0 with no conflict message (landing/merge-tree-*.txt, scratch-chain.txt):
    S1 tip x #318 bd129bfa -> d882e2c4; S2 x #319 66b34363 -> 6564ad82; S3 x #323 a7988cd9 -> d30ead70; S4 x #324(a6eaebd7)
    35e9289d -> 6cfe68ac; S5 x #326 0c1134e5 -> 0f43c1e8; S6 x #327 tree 225d0f05fa5f6d03356438e91d2daa8ac2414fca, commit
    e2e26b9e71747c03f71b26d684b99f943442d4d7 (the tree of the main build). Then, at the coordinator's request during the build,
    S7 = S6 x #324 LE-gate37 4bd2d80b: tree 3fb05ea062395caf069c09643a8caf751d3ad6da, commit
    639d16d943d4bb4777c77ae8614cd8c2ed91f1bd = THE FINAL COMBINED TREE (S7a with the superseded b4900559 kept in the chain
    file). Other orders (landing/merge-tree-alt.txt): two orders give 225d0f05 with the old #324 head, three orders give 3fb05ea0
    with the new one, all clean. All scratch commits: author = committer = Claude <noreply@anthropic.com>, date fixed
    2026-11-16T00:00:00Z, unsigned, no ref, never pushed (also the solo merges below).
  checks/: tip-vs-combined-name-status.txt (at 639d16d9) = the union of checks/pr*-name-status.txt: 97 .lean files (79 A, 18 M;
    +17309/-300), #318 7, #319 4, #323 14, #324 16, #326 15, #327 41; shared paths 0 (checks/shared-paths.txt); every blob at the
    combined tree equals its PR head's (checks/combined-blobs-vs-heads.txt: 7/7, 4/4, 14/14, 16/16, 15/15, 41/41).
worktree $SP/wt-int-all (sparse, non-cone /* !/briefs/, .lake/packages -> /home/user/tcslib/.lake/packages): at S6 for the build,
  S7 for the #324 rebuild, the axioms probe, Rule 10 of ../gate37-le/, tree check and lint, then at each solo merge. Clean at the
  end (checks/worktree-status.txt: only the ignored .lake/); removed (`git worktree remove --force`), pruned.

build set (order/ at S6; order-final/ at S7, identical sets and queue):
  downorder.py vs eff2dcd0 (the olean snapshot's base): changed 169 = 72 base-delta modules since eff2dcd0 (order/basedelta-
  modules.txt: int-313-323-324's 68 + #313's 5, minus SeedMajority, which #326 also changes) + the 97 PR modules; down 694; order
  1332 (imports-first); 377 Mathlib roots. buildset.py (seeds = the 97): down-seed 661 (incl. root TCSlib, audits/garg-ch1-3/Checks,
  audits/pass-shelat/Checks), build set 694 = down-seed + 33 base-delta modules they need, excluded 0; build-queue.txt 694 modules,
  imports-first (asserted per edge). (The expected "700 or more": 694.)
  downstream counts (order-final/bothdown.out, bothdownN.py at S7): #318 10, #319 68, #323 322, #324 19, #326 585, #327 65,
  union 661. Downstream of both, per pair: 318&319 1, 318&323 6, 318&324 3, 318&326 10, 318&327 1, 319&323 37, 319&324 1,
  319&326 57, 319&327 2, 323&324 16, 323&326 273, 323&327 41, 324&326 16, 324&327 1, 326&327 52; modules downstream of 1/2/3/4/6 PRs:
  353/214/90/3/1 (only root TCSlib is downstream of all six; order-final/merge-multi.tsv). With the old #324 head (order/
  bothdown.out) 323&324 was 3 and #323's downstream 309: G37-01's CommitmentLemmas import makes ComposeSecurity/Machines (hence
  the 16 #324 modules) downstream of #323's DAGCircuit.

Mathlib overlay (build-mathlib-extra/; the derand reviewer's method, derand-r1 PROVENANCE "environment"): the shared pinned Mathlib
  build lacks Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.olean, imported by Derandomization/RootSchedule (the only
  Mathlib module imported by the queue and missing). tools-used/mloverlay.sh put 3346 symlinks to the pinned Mathlib oleans in
  dl-oleans/Mathlib (our tree only; nothing under /home/user/tcslib written) and mathlibextra.sh compiled that one module from the
  pinned source (mathlib 029db123, source SHA-256 b371bf48...) with plain `lean -o`: rc 0, olean c0a9cff04c67... = the derand
  review's. Removed at restore.

olean tree $SP/dl-oleans:
  pre: tree/snapshot-pre.txt (snapshot.py): 1230 files, 0 empty dirs, SHA-256
    457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = the required value (byte-equal to int-313-323-324's
    snapshot-post). Before the build the 561 base oleans the queue overwrites were copied aside ($SP/dl-intall-backup;
    tree/backed-up.txt with hashes = snapshot-pre; copies verified 561/561) and the 133 new ones listed (tree/new-oleans.txt).

build (build/; runner.py $SP/wt-int-all order/build-queue.txt $SP/dl-oleans build, at S6; runner rc 0):
  build/summary.txt: 694/694 rc 0; errors 0 (G26-N1); substring "error" 0; 56 sorry warnings; 417 warnings; 5650 s of module time,
  2026-11-16T01:42:54 - 03:17:06 UTC (1 h 34 min wall), max RSS 4.52 GB; slowest DetMod 1447 s, CookLevin/Hardness 329 s,
  NARMProb 214 s, audits/pass-shelat/Checks 136 s, SequentialZK 117 s. build/per-module.tsv (permod.py): per module rc,
  err_colon (`error:`), err_paren (`error(`), combined, error_substr, sorry, warnings: totals error: 0, error( 0; every log hash =
  its record. The 97 PR modules: rc 0, 0 errors both forms; sorry 0 except Yao 2 (yaoHybrid_polyTime, yaoHybrid_simulators:
  tip admissions, sc-yao); warnings 20 = IterateFind 12 (derand E1 copy of the base linter lines, disclosed), Classes 2 (lines
  586/1302, unchanged code), Universal 1 (unused hc, canonizer), SequentialZK 1 (unused hQ, disclosed), SliceParser 1 and
  NestedBounds 1 (SG-F06), Yao 2 (the sorries). Other sorry warnings only in admitted non-PR modules (TQBF 21, RAMSimulation/
  Classes 9, UniqueGames 8, Hierarchy 4, WordSize 3, MaxCutAlgorithm 2, Simulation 2, NTimeDiagonalizer 2, NonUniform 1,
  NDNormalForm 1, Savitch 1).
  build-324/ (after LE-gate37; worktree at S7; order-final/rebuild324-queue.txt = down(#324) at S7 + both audits Checks, 21
    modules, imports-first): 21/21 rc 0, 0 errors both forms, 0 sorry, 0 warnings, 204 s (03:24:21-03:27:44). build-324-attempt1/:
    the same queue at the superseded b4900559 merge: Runs.lean 5 errors (the splitCoins name clash, ../gate37-le/), stopped there.
  Records of the final tree: admissions/records-final.jsonl = int-317's base records (admissions/base-records-from-int-317.jsonl,
    = int-313-323-324's and gate36-le's copy) + build/ + build-324/; build/results-final.jsonl = build/ + build-324/.

admissions (admissions/):
  tip (tip-census-b0ebd475.txt, tipcensus.py over the base records, int-313-323-324, gate36-le build/rerun/trial, sc-garble and
    sc-compose builds; 1253 modules matched, 0 disagreeing; 34 modules outside root TCSlib's closure have no record, as at gate36):
    215 sorry warnings tree-wide (= gate36-le's 654323f2 census, per module identical).
  combined (merge-census-639d16d9.txt, tipcensus.py over records-final.jsonl at S7; 1332 modules matched): 194.
  tip-count.txt / tip-vs-merge-census.diff: 194 = 215 - 2 (sc-ot: ObliviousTransfer 2->0) - 1 (canonizer: Universal 1->0) - 7
    (sc-garble: SpecialEncryptionSecurity 3->0, Garbling 1->0, GarblingSecurity 1->0, SpecialEncryptionMulti 1->0, Yao 3->2) - 3
    (sc-compose: ComposeSecurity 3->0) - 3 (derand: SeedMajority 2->0, Derandomization 1->0) - 5 (seq-zk: SequentialZK 5->0);
    no other count changes; every new PR module 0.
  pr-modules-sorry.txt: the 97 PR modules have 0 sorry warnings and 0 `sorry`/`admit` tokens in code except Yao (2 warnings,
    2 code tokens = the two tip admissions; 3 with its docstring's mention). No PR module gained an admission.

axioms (axioms/; AxiomsAll.lean.txt run as IntProbe/AxiomsAll in the worktree at S7 with runner_full.py: rc 0, 0 errors,
  0 warnings, no olean written; source removed afterwards; probe-runs/, AxiomsAll.log, axioms-summary.txt): 67 #print axioms =
  each unit's census / integration list: sc-ot (gate34-le census: otProtocol_polyTime, otProtocol_simulators, otProtocol_hbcSecure
  and 8 OT helpers), canonizer (int-319 census: exists_canonizerExp, exists_polyCanonizer, ... 11), learning/sc-garble/sc-compose
  (int-313-323-324 probe: 2 + 8 + 4), derand (review census: the 3 targets, E1-E3, inBPP_iff, ... 18), seq-zk (review census: the
  5 targets, PerfectZK.seqRep, PerfectZKAbort.seqRep, ... 11), plus yaoHybrid_hbcSecure and yaoProtocol_hbcSecure. Result: 63
  [propext, Classical.choice, Quot.sound]; Turing.oneTapeFormat_serialize_decode [propext, Quot.sound] (as in int-319);
  OT.pairSndD_nil' no axioms; yaoHybrid_hbcSecure and yaoProtocol_hbcSecure [propext, sorryAx, Classical.choice, Quot.sound].
  Dependency trace (the sc-garble review's DepTrace logic, unchanged): the admitted declarations (direct sorryAx) in the closure of
  yaoProtocol_hbcSecure (18264 constants) are exactly yaoHybrid_polyTime and yaoHybrid_simulators (sc-yao); of
  yaoHybrid_hbcSecure (9418) the same two. otProtocol_polyTime / otProtocol_simulators and hbcSecure_compose are gone.

refcmp (build/; refunion2.py over build/results-final.jsonl):
  references: 24 build runs (rc-0 records), copied to build/refs/jsonl/ and each byte-equal to its entry in its evidence's
    SHA256SUMS (refs/refs-hash-check.txt 24/24); the zips (refs/refs-zip-check.txt) extracted into fresh directories and checked
    against their records evidence-SHA256SUMS, path sets exact: fills/sc-ot/final-r1/review-evidence.zip (aa3bcfc3..., 810/810;
    build, build-r2, build-r3, edit-build, lereuse-trial), fills/canonizer/final-r1 (2b52982f..., 838/838; build, build-r3),
    fills/sc-garble/final-r1 (5a121c02..., 1200/1200; build, edit-build, base-build), fills/sc-compose/final-r1 (c11ce8bb...,
    850/850; build, edit-build, base-build), fills/derand/final-r1 (ef0776d5..., 1317/1317; build, build-retry, base-build),
    fills/seq-zk/final-r1 (f9c39479..., 1106/1106; build), gates/34-sc-ot/landing-r1/gate34-le (145d5574..., 459/459; build),
    gates/35-canonizer/integration/int-319 (830395f8..., 299/299; build, build-combined), gates/36-sc-garble/landing-r1/gate36-le
    (f77628dd..., 628/628; build, build-rerun, trial/build), gates/37-sc-compose/integration/int-313-323-324 (3917cc1e..., 527/527;
    build). (Only the Rule 10 seal/control runs were deleted from the extracts after the check, to save disk.)
  build/refunion.txt, refunion-matrix.tsv, refunion-per-ref.txt: 660 of 694 modules byte-identical in source and olean to at least
    one reference.
  - NO reference with the same source: 34 modules = exactly the files edited in this job (build/edited-this-job.txt; each has
    references with a different source): derand LE-doc Classes; seq-zk LE-doc Defs + 22 SequentialZK files; LE-gate37's 10
    ComposeSecurity files. Their sources are new here (docstrings are stored in the olean). No module has no reference at all.
  - same source, different olean: 1, SpecialEncryptionMulti/SliceReduction vs int-313-323-324 and the sc-garble review; it is
    byte-identical to gate36-le build and build-rerun. Explained by gate36-le: LE-gate36 (#323's head 8c3f3e3f) edited SliceParser's
    imports (+BlockEncryptor, +FromPRG), changing SliceReduction's import closure; gate36's rerun showed the new olean deterministic.
  - build/both-modules-refmatch.txt: of the 308 modules downstream of two or more PRs, 278 are byte-identical to a reference; the
    other 30 are among the 34 edited files. Root TCSlib, both audits Checks, SecureComputation and Randomness match 11-18 references.
tree check (tree/tree-check-merge.txt; treecheck_ml.py, order-final/order.txt 1332 modules, records-final.jsonl, rev S7, run after
  the probes; tree/snapshot-merge.txt): every module rc 0 at the S7 source, every olean = its record, none missing, no stray olean,
  no empty dir: RESULT OK (4710 files = 1332 + 31 PFR + the 3347 Mathlib overlay entries, attributed).
lint (lint/; campaign_style_lint.py --check8b in the worktree at S7 and in a git-archive export of the tip, removed afterwards):
  Cryptography 92 FAIL / 101 WARN at the tip and at the merge; linediff-Cryptography-tip-vs-combined.txt: only ZeroKnowledge/Defs'
  check-8 list loses StatZK (#327's StatZK_iff). Complexity 25/391 at the tip, 25/390 at the merge; the line set changes only by
  the disclosed ones: DAGCircuit check-8 loses IsFaninTwo (#323), DTIME's check-8 WARN removed (#326 E3), Classes 1403 -> 1415
  lines and check-8 loses InBPP (#326 SR-01), CodeFormat check-8 loses oneTapeFormat and CodeSimulator 9126 -> 9133 lines and
  loses oneTapeMachineFormat (#319). No new FAIL. No PR file has a new FAIL.

solo coverage (solo/; summary.txt): each PR alone on the tip, scratch merges solo/solo-merges.txt (all rc 0, clean; tree = tip + the
  PR's files exactly): #318 bae29c92, #319 5e5a4f6c, #323 4ebf36f9, #324 bcf945e8 (old head), #326 af5c9d44, #327 e3d2c3e4.
  solocheck.py compares every module of the solo merge's build order (pr*/order/, downorder + buildset at the solo merge) with the
  full record set its own integration build left; differ.txt = source differs or no record; rebuild.txt = their downstream.
  - #319 (own build int-319 at 05d26fe5, records-B = base + job A + build/): differ = #313's 5 Learning modules; rebuild 7 =
    Learning x5, Randomness, root TCSlib (the expected "Randomness and TCSlib" plus #313's own 5).
  - #318 (own build gate34-le at 05d26fe5): the same 7.
  - #323 (own build gate36-le, LE-gate36 on 654323f2, = the current code): 0 differ, 0 to rebuild.
  - #326 (own build the derand review at d34fbf09 / 6ce4658d, logs/records-head.jsonl): differ Classes (LE-doc) + Learning x5;
    rebuild 89 (Classes' downstream and Learning's).
  - #327 (own build the seq-zk review at 05d26fe5): differ the 23 LE-doc files + Learning x5; rebuild 63.
  - #324: its own builds (int-313-323-324, gate36 trial) predate LE-gate37; not re-checked alone (see below).
  Separate tip+PR checks were run for all of #318, #319, #326, #327 (sets 7, 7, 89, 63), after the combined analysis, in the same
  tree (solorun.sh): soloenv.py takes, for every module of the import closure of the rebuild set outside it, the olean its own
  build recorded (same source and import-closure sources, so it is the expected one) and checks the tree: OK if present, RESTORE
  from the base-snapshot backup if that is it, MISSING otherwise (rebuilt first, must reproduce the recorded hash); then the queue
  (missing + set, imports-first) is built at the solo merge. soloverify.py, pr*/verify.txt:
    #319: env OK 1230 / RESTORE 13 / MISSING 2 (tip SeedMajority, tip SpecialEncryptionMulti: rebuilt, = recorded hashes); 9/9 rc 0,
      0 errors, 125 s; the 7 byte-identical to references (Learning to gate36-le/int-313-323-324/combined; Randomness, TCSlib to
      14-19 builds). RESULT OK.
    #318: OK 1246 / RESTORE 3 / MISSING 1 (ObliviousTransfer, = recorded); 8/8 rc 0, 127 s; RESULT OK.
    #327: OK 1227 / RESTORE 1; 63/63 rc 0, 0 errors, 0 sorry, 548 s; every module byte-identical to a reference (the 23 LE-doc
      modules to the combined build). RESULT OK.
    #326: OK 1170 / RESTORE 2 / MISSING 2 (DTIME, IterateFind, = recorded); 91/91 rc 0, 0 errors, 0 sorry, 871 s; every module
      byte-identical to a reference. RESULT OK.
  So each of #318, #319, #323, #326, #327 is covered merging first onto the tip, and the combined tree covers all six together.
  #324 at 4bd2d80b alone on the tip was not built: its rebuild set is small (down(#324) = 19 modules), but its environment needs
  tip-state oleans for the #323/#326-downstream modules those 19 import, and no record of such a state exists (the closest
  builds include #323 or the old #324), so it would mean a ~280-module solo build. The combined build covers it with all PRs; its
  old head was covered alone-with-#323 by gate36's trial.

restore (restore/): the 561 backups copied back, each hash checked (restore-log.txt: 561 restored, 0 failed); the Mathlib overlay
  deleted (3346 symlinks + the NthRootLemmas olean c0a9cff0..., logged); restoreplan.py --delete against tree/snapshot-pre.txt:
  133 extra files (= tree/new-oleans.txt; restore/extra-vs-new-oleans.txt empty) deleted with 17 emptied directories
  (deleted-dirs.txt); 0 changed, 0 missing. The solo checks' restores and rebuilds are covered by the same backups (changed 0).
  post: tree/snapshot-post.txt: 1230 files, 0 empty dirs, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f,
  byte-identical to tree/snapshot-pre.txt. Backups removed afterwards.
cleanup: the worktree removed and pruned; the backup directory, the tip export and the reference extracts removed after zipping.
SHA256SUMS: every file here except itself (paths without "./"); ../int-all-open-evidence.zip holds exactly these paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/37-sc-compose/pack.md =====

# Gate 37 · The semi-honest composition theorem (`sc-compose`, [Gol04, §7.3.1, Theorem 7.3.3])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324) at
  `a6eaebd78c48e7fdfd06263edb84b70bc00ec593` (branch `land/pass-shelat-sc-compose`, tree
  `0758162eb040b2de2513719910edaa4ab37e7b73`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `6ce4658db08a1dc2a03a149987197660db078011` (the merge base; the records tip after #311, #312 and #314–#317).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. The 16 PR paths are byte-identical at the issue
    base and at `6ce4658d` (`pack-checks/rebase.txt`); in particular the owned file's blob is `3041d93f` at `eff2dcd0`,
    `107f1e8c` and the base. The Lean delta between them is #307, #311, #312 and #314–#317 (29 files; the only
    `SecureComputation` file is `SpecialEncryptionMulti`), and the review's build covers it.
  - The records tip is now `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`; it is records only since `6ce4658d`.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...a6eaebd7`, which equals `6ce4658d..a6eaebd7`
    byte for byte (16 paths, 4580 insertions, 60 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #313, #318, #319 and #323 is
    clean in each case, and no path is shared (`pack-checks/mergetrees.txt`). **Pending merge condition** (not an audit
    item): #324's own integration rebuild at the head (below, *The build and LE-prose*), and, for whichever of #324 and
    each open PR with a shared downstream merges second, an integration rebuild on the merged tip; the maintainer runs
    these builds (question 7).
- **Commits:** 14, all authored and committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Claude worker's 12 commits (job `sc-compose`), applied with `git am` with the delivered committer data. The 12
    worker hashes (`a3cb219d` … `d3f405d4`) reproduce only with the environment's signing on (SC-F05; `COMMITS.tsv` has
    no signing column, which this brief did not ask for). They were rebased onto `6ce4658d` without conflict, author
    kept: `git range-diff 107f1e8c..d3f405d4 6ce4658d..f3036c69` is 12/12 `=`. At `f3036c69` the 16 files are
    byte-identical to the worker's `src/` (exchange `bdfdcb76`).
  - Landing edit **LE-doc** `f61ce08fa74401660345f1f50c36dffb37588391`: formulas for 70 new public declarations,
    docstrings only.
  - Landing edit **LE-prose** `a6eaebd78c48e7fdfd06263edb84b70bc00ec593` (the head; SC-F03): one sentence of the frozen
    prose of `polyTime_compose`, under Seyoon's prose-only exception.
- **Scope:** a **proof audit**. The job proves the admitted `HybridProtocol.composeP_efficient`,
  `HybridProtocol.composeV_efficient` and `HybridProtocol.hbcSecure_compose` [Gol04, §7.3.1, Theorem 7.3.3] (used
  unstated by [PS10, Theorem 163.7]). The statements passed the prong B statement phase and Gate 06B and are frozen.
  Their consumer `polyTime_compose` (unchanged, proved at the base from the three) now uses only the standard axioms.
- **Brief:** `fills/sc-compose/issued-r1/brief.md` on the records branch. Three checkpoints (the efficiency pair;
  `hbcSecure_compose` steps 1–2; steps 3–5). The owned file plus `SecureComputation/ComposeSecurity/` only, with two
  named extra imports for helpers; every other file frozen. The binding duplication rule with an `## Overlap and
  reuse` section; Rule 10 with the projection-coercion ruling and seals with `PolyExpr.eval` both excluded and sealed;
  the docstring and sketch rules; the G26-N1 error count; the evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/`; `CS/` is `ComposeSecurity/`. The PR touches 16 Lean files:
the owned file (382 → 449 lines) and 15 new helpers (`source-head.json`; every line at most 100 characters, every
file at most 632 lines):

| Helpers (lines) | Role |
|---|---|
| `CS/Machines` (260), `CS/Efficiency` (596) | checkpoint 1: polynomial-time machines on encoded histories; the composed parties as functions of the layout |
| `CS/Probability` (126), `CS/Reductions` (106), `CS/Accept` (198) | the statistical switch, fixing coordinates, negligible × polynomial; advice-dependent pre/post-processing; coin splittings and acceptance |
| `CS/Assembly` (292), `CS/Runs` (632), `CS/Bounds` (96), `CS/Sim` (257), `CS/Correct` (208) | the assembled view; the coins run by run and `GoodRuns`; lengths; `Φ` and the simulator; correctness and the union bound |
| `CS/Chain` (263), `CS/Template` (191), `CS/Lengths` (303), `CS/SideA` (470), `CS/SideB` (455) | the hybrid argument over the runs; the worst-case template as advice; polynomial bounds on the template words; the two sides |

The owned file imports the 15 helpers and gets a `## Contents` list; after #305 no facade edit is needed, and none was
made.

**The proof** (REPORT § *The proof of `hbcSecure_compose`*; review § *Content*; the targets' sketches were rewritten
to describe the delivered proof, the statement prose is unchanged apart from LE-prose):
- **`composeP_efficient`, `composeV_efficient`** (checkpoint 1): `composePW`/`composeVW` on the raw layout are
  polynomial-time (`polyTimeComputable_composePW/VW` from `runW`, `ansW`, `mainW` and
  `polyTimeComputable_flatMap_range`: the indices from `|hist|`, the call inputs from `H.PolyTime`, the run tapes cut
  from `r`, one `ρ` activation or `L(n)` of them for the answers, one `main` activation); the strategy equals it
  (`composeP_next_eq_composePW`); `GI.efficient_of_polyTime`.
- **`hbcSecure_compose`**: `hbcSecure_iff` with `polyTime_compose`; simulators `exists_simA`/`exists_simB`; and **for
  each `D`, `ε = ε_A + ε_B`**, the sum of the two sides' negligible bounds (each nonnegative, since it bounds a
  `distAdv`). Each side follows the five-step sketch:
  1. **Simulator** (`ComposeSim.exists_simulator`): `S_A^H` post-processed by `Φ = phiV`, which recomputes the call
     inputs from the simulated `main`-view, runs `S_A^ρ` on each with its answer block and a fresh coin block, and
     assembles the view (`asmView`).
  2. **Output clause and switch** (`exists_correct`, `uprob_not_goodRuns_le`, `distAdv_le_uprob_of_eq`,
     `realA_compose_sampleA`): with the worst-case inputs as advice of a test machine, each `ρ`-output is wrong with
     probability `≤ ε_c(n)`; off `¬GoodRuns` (probability `≤ L(n) ε_c(n)`) the real sample is
     `sampleA m (real run views)`.
  3. **Hybrids over the runs** (`ComposeProb.abs_chain_le`, `exists_hyb_step`, `exists_gapA`, `exists_gap_le`): hybrid
     `i` has the runs `< i` simulated; one step reduces to one `ρ`-sample by `D ∘ hybW` with the worst instance's
     template as advice (polynomial by `exists_tmplA_bound`); each step `≤ ε₂(n)`, the chain `≤ L(n) ε₂(n)`.
  4. **The hybrid model** (`acceptProb_realA_dPhi`, `ComposeProb.acceptProb_post_pre`, `exists_dPhi`): with all runs
     simulated the sample is `D ∘ Φ` on `H.realA F n x y`, and `D` on `S_A` is `D ∘ Φ` on `F.idealA S_A^H`;
     `H.HBCSecure F` gives `ε₃(n)`.
  5. **Total** `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` (the brief's `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)`, with `ε_c` the correctness
     bound), negligible by `negligible_polyExpr_mul` and `Negligible.add`.
- `hM` is used in `realA_compose_eq`/`realB_compose_eq`. Bob's side (`CS/SideB`) is symmetric, with `ρ.V`'s coins and
  the leading fillers.

The brief's edge cases: `L(n) = 0` (no hybrid step; the instance type of `exists_gap_le` is empty there, the advice
`[]`, the union bound `0`); `ρ.rounds(n) = 0` (empty run chunks); `hM`; the fillers and leading fillers (`segW`,
`asmView`); the tape cut lengths (exact on real views: `padTo_of_length`); `padFin` readback
(`answersRealA_eq_answersA`); Bob's side.

**Statements.** decls2 from the issue base (and from `6ce4658d`) to the head gives **185 ADDED, 0 CHANGED, 0 REMOVED**
(review `statements/head-le/decls2-vs-base.tsv`; re-checked, `pack-checks/decls2-*.tsv`; 0 rows for LE-doc
`f3036c69..f61ce08f` and for LE-prose `f61ce08f..a6eaebd7`).
- The frozen check (`frozencheck.py`, at LE-doc) compares the owned file's **11** base declarations: kind, name,
  order, header bytes and statement prose. It finds **0 differences** (`landing/frozen-check.txt`). Its controls (the
  headers of `hbcSecure_compose` and `composeP_efficient`, the prose of `composeV_efficient`, the removal of the private
  `exists_ofFn_eq`) each report exactly one difference; the `polyTime_compose` prose control is a harness artifact (its
  docstring has no sketch, so the changed character was the closing `-/`; noted in `statements/frozen/controls-summary.txt`).
- `touched`: 3 CHANGED (the targets: proofs and sketches only), 8 UNCHANGED, 186 in new files.
- Re-checked for this pack from git objects (`pack-checks/headers.txt`): the 11 base headers byte-identical at the
  head, in order; docstrings changed only for the three targets (their sketches) and `polyTime_compose` (LE-prose).

## Rulings and records in force

1. **DL-49 (Seyoon, 2026-11-15): "ledger" — SC-F01.** Helpers under `CS/` restate public lemmas because the worker read
   the brief's two extra imports as exhaustive (disclosed in the checkpoint REPORTs): a third `negligible_polyExpr_mul`
   (`EnsemblesLemmas.lean:377`); `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`);
   and `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`,
   `msgAt_encodeMsgs` and the `padTo` family (from `ZeroKnowledge/ThreeColoring/Machines.lean`). Re-pointed in the
   cleanup. **Not a finding:** any item DL-49 lists.
2. **SC-F03 (Seyoon, 2026-11-15): a prose-only exception.** The frozen prose of `polyTime_compose` still called the
   efficiency theorems `sorry`s. LE-prose changes exactly that sentence:

   ```text
   - The two strategies are PPT (`composeP_efficient`, `composeV_efficient`; `sorry`s under their
   - sketches), and the messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
   + The two strategies are PPT (`composeP_efficient`, `composeV_efficient`, proved), and the
   + messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
   ```

   Re-checked (`pack-checks/leprose.txt`): one file, +2/−2; identical with doc comments deleted; one docstring
   (`polyTime_compose`) changed and no header; the prose at LE-doc equals the issue base's.
3. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical; the strict variant is run and its differences
   attributed.
4. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A** is canonical; seal B is run and reported.
   So **coe-A is the canonical variant**.
5. **The facade-completeness lint fix, #305.** The baseline is **92 FAIL / 101 WARN** (Cryptography).
6. **LE-doc (the maintainer's landing edit): docstrings only** (SC-F04). For the 70 new public declarations the
   review's docaudit flagged NO-FORMULA, the declaration's own Lean conclusion (for a `def` whose type is no relation,
   its `_eq`/`_iff` reader's) is added as a backticked formula at the end of the statement prose; 15 long conclusions
   are cut at 240 characters with " …" (`landing/le-doc-plan.tsv` in the review ZIP). Re-checked (`pack-checks/lecheck.txt`):
   `f3036c69..f61ce08f` touches 13 files, each identical with doc comments deleted, 70 docstrings changed, every line
   within 100 characters.
7. **The landing edits are the maintainer's** (the ext-nosrc … sc-ot, sc-garble precedents).

## What is frozen

- **The three targets' statements** (quoted in the brief), the 8 other pre-existing declarations of
  `ComposeSecurity.lean` and their statement prose (`polyTime_compose`'s apart from the SC-F03 sentence), in particular
  `exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`, `compose_msg_bound` and `polyTime_compose`.
- **Every file outside** `ComposeSecurity.lean` and `ComposeSecurity/`, in particular `SecureComputation/Defs.lean`,
  `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `YaoReal.lean`, `Yao.lean`, `Garbling*.lean`, the `FromPRF*`
  files, `Pseudorandom/*` and `Games/*`.
- **The landing edits:** LE-doc 70 docstrings; LE-prose one sentence.

## Questions for the audit

**1. Correctness against [Gol04, §7.3.1, Theorem 7.3.3]**
- **The efficiency pair:** do `composePW`/`composeVW` compute the composed parties' next-message functions on every
  history (the indices from `|hist|`, the call inputs, the run tapes cut from `r`, the answer activations, the `main`
  activation; `composeP_next_eq_composePW`)? Are they polynomial-time from `H.PolyTime F` and `G.PolyTime ρ`, with
  `GI.efficient_of_polyTime` the right extraction?
- **`hbcSecure_compose`:** does the proof follow the **five-step sketch** above, with `ε = ε_A + ε_B` for every `D`?
  - Is `Φ` right (call inputs recomputed from the simulated `main`-view, `S_A^ρ` per call on its answer block and a
    fresh coin block, `asmView`)?
  - Is the switch "agree off `¬GoodRuns`" sound, with `Pr[¬GoodRuns] ≤ L(n) ε_c(n)` from the worst-case-input test
    machine?
  - Is the hybrid chain over the runs right (`abs_chain_le`, `exists_hyb_step`; the coordinate fixing
    `exists_abs_sub_le_sections`; the worst instance's template as advice, polynomially long by `exists_tmplA_bound`),
    each step at most `ε₂(n)`?
  - Is the step to the hybrid model right (`acceptProb_realA_dPhi`, `exists_dPhi`, `H.HBCSecure F` giving `ε₃`)?
  - Is the total `L(n)(ε_c + ε₂) + ε₃` negligible, and is Bob's side really symmetric (`ρ.V`'s coins, the leading
    fillers)?
- Are the brief's edge cases covered (`L(n) = 0`, `ρ.rounds(n) = 0`, `hM` and its counterexample, the fillers, the cut
  lengths, `padFin` readback, Bob's side)? Do the rewritten sketches describe the delivered proof?

**2. Frozen-statement integrity**
- Are the three targets' headers and the other 8 pre-existing declarations byte-identical (`landing/frozen-check.txt`,
  `statements/frozen/`, `pack-checks/headers.txt`)? Is decls2 **185 ADDED / 0 CHANGED / 0 REMOVED**?
- In the owned file, did only the imports, the title, `## Contents`, `## Main results`, the three proofs and their
  sketches change, plus the LE-prose sentence (`statements/frozen/owned.diff`)?

**3. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's tables (the final REPORT's `## Overlap and reuse` and the two checkpoint REPORTs it says stand,
  `worker/cp1/REPORT.md` and `worker/cp2/REPORT.md`) and **DL-49**? SC-F01 is ruled ledger debt (DL-49). **Anything
  further is a major.** The recent majors of this class are G23-01, G24-01, prf-mac F-01, learning (`uprob_eq_point`),
  G29-01, G29-02, sc-ot F-01 and G34-01.
- Search in particular:
  - the hybrid argument (`multicopyHybrid`, `multicopyRed`, `exists_multicopyRed_ge`, `abs_sub_le_sum_hybrids`,
    `exists_hybrid_gap`) against `hybV`, `plugV`, `exists_hyb_step`, `abs_chain_le`;
  - argmax advice (`Finset.exists_max_image` patterns in `PublicKey/Hybrid.lean:295`, `NextBit.lean:411`,
    `Commitment.lean:317`) against `tmplW`, `hybW`, `exists_gap_le`;
  - probability and acceptance (`uprob_*`, `uexp_*`, `acceptProb_*`, `distAdv_*`, `StatClose`,
    `distAdv_le_of_statClose`, `pushesUniform_*`);
  - coin splittings and blocks (`coinsEquiv`, `splitCoins`, `blocks`, `coinBlock_flatten`, `FunFamily.ofFn_blocks_symm`);
  - history machinery (`Strategy.encodeMsgs`, `pairFstD`/`pairSndD`, `GI.iterate_pairSndD_encodeMsgs`, the
    `ThreeColoring/Machines` and `GI` layout helpers, `padFin`, `padTo`);
  - list readings (`getD`, `getElem?_ofFn`, `headD_drop_ofFn`; `pack-checks/dupscan.txt` lists the 9 added lines that
    use a getD/`getElem_ofFn` reading lemma: `msgAt_encodeMsgs` and the `padTo` family are DL-49 items; the others,
    `coinBlock_blocksCoins`, `runTape_ofFn_splitCoins`, `getD_filter_map_mover`, `getD_plug` and the two side lemmas,
    read coin blocks and word lists, not `(List.ofFn f).getD i d = f i`. Is that reading right?);
  - lengths (`length_answersA/B` against the owned file's `length_answersRealA/B`; the private `exists_ofFn_eq` of
    `CS/Lengths`, restated from the owned file's private one and disclosed).
- Are the disclosed relations accurate and their "why not reused" reasons valid (in particular "not importable" for
  `getD_plug` and the hybrid-chain lemmas)?

**4. Rule 10**
- Do the seals cover every touched declaration of the 16 files over the full closure, at the base and the head, in all
  four variants, run with `-DmaxErrors=0` (`tools/runner_full.py`) and install/EOF records? Requests 561–1192 per file
  (`logs/mkseals-*.log`); the base phase rebuilt the base owned file in its own closure.
- With **coe-A canonical**, does every file pass? The review has **64/64 head probes rc 0** (A and B, strict and coe, all
  16 files) and **4/4 at the base** (670/671/669/670 requests = the worker's); 0 new failing declarations; strict =
  coe (`logs/seal-table-seals{,-coe}.txt`).
- Do the paired controls bite? Rows: `PolyExpr.eval` (B), the `FinDist` CoeFun instance, `HybridProtocol.answersA`
  (frozen `Hybrid.lean`), `ComposeMachines.padTo`, `ComposeSim.tmplW`. Coe (canonical): 14 probes, 16 sealed
  negatives, `logs/ctlcheck.log` ALL_OK. Strict: 16 probes, 24 sealed negatives; every sealed negative fails exactly
  once, and only `ctlCoeReader` fails in the 8 strict sealed probes (the harness effect of sc-ot F-09;
  `logs/controls-strict-attribution.txt`).
- Explicit-unfold scan at the head (LE-doc): 1189 items, 1036 theorems, 2 owned definitions, 151 local or unresolved,
  **0 foreign** (`logs/scan2-head.log`). Does any proof read a foreign definition other than through a published
  reader (`Compose`, `ComposePhases`, `Hybrid`, `Defs`: `composeP`/`composeV`, `slotMsgs`, `runTape`, `answersA/B`,
  `realA/B`, `idealA/B`, `Protocol.transcript`, `acceptProb`, `distAdv`; the `NUPPT` layer; one helper's definitions
  read from another)?

**5. The landing edits, and the build**
- **LE-doc (ruling 6):** does each of the 70 new formulas state what its declaration says, in Lean argument order
  (`landing/le-doc.diff`, `landing/le-doc-doconly.txt`)? Are the 15 cut conclusions acceptable? Is it docstrings only?
- **LE-prose (ruling 2):** is it exactly the SC-F03 sentence, docstring only, with the header and code identical?
- **The build ran at LE-doc `f61ce08f`, not at the head.** The review built 279/279 modules and then the 18 modules
  LE-doc touches and their dependants, all at `f61ce08f`; its seals, controls, scan and census ran at `f61ce08f` too.
  **LE-prose `a6eaebd7` was checked doc-only, by stripping doc comments; it was not rebuilt.** Of the 279 built
  sources, 278 equal their blobs at the head; the one that differs is `ComposeSecurity.lean`, by the LE-prose docstring
  (`pack-checks/srcequality.txt`). The rebuild at the head is part of #324's integration build, which the maintainer
  runs before #324 merges (question 7). Is the doc-only check sufficient for this audit?

**6. The docstring and sketch rules**
- Does every new public declaration's docstring state its formula, with arguments in the Lean order and a source tag
  where it comes from the source? The review's docaudit after LE-doc (`statements/head-le/docaudit.tsv`) has 145 OK,
  29 LABEL (all state their equation) and 14 NO-FORMULA: the frozen prose of `composeP_efficient` and
  `composeV_efficient`, and 12 `PolyTimeComputable …` Prop formulas without a relation symbol, which the tool does not
  accept. Are those 12 acceptable?
- Does every proof of 15 lines or more carry a `**Proof sketch.**`? `statements/head-le/sketchaudit.txt` has 37
  theorems and 3 flagged: `runW_eq`, `composePW_eq`, `composeVW_eq`, `:= rfl` readers under long statements (a tool
  artifact). Do the long proofs (`exists_gapA`/`B`, `exists_simA`/`B`, `abs_chain_le`, the efficiency proofs) have
  step comments? A misstated formula or sketch is a minor.
- Does every new public `def` land with its `_eq` reader (lint check 8)? Is nothing new `@[simp]`, an instance or an
  abbreviation? The census has none; its 3 "abbrev" rows are compiler match auxiliaries (`…match_1_1`).

**7. The merge interaction**
- `git merge-tree --write-tree a6eaebd7 <x>` is clean, and no path is shared (`pack-checks/mergetrees.txt`):

  | `<x>` | head | merged tree | downstream of both (`pack-checks/downstream.txt`) |
  |---|---|---|---|
  | the tip | `540bac18` | `a5944f88` | none (records only since the base) |
  | #313 (learning) | `2b6c2981` | `828d6685` | root `TCSlib` |
  | #318 (sc-ot) | `f62a25b3` | `8da059d7` | `YaoReal`, `SecureComputation`, root `TCSlib` |
  | #319 (canonizer) | `6421ac16` | `6ceb6246` | root `TCSlib` |
  | #323 (sc-garble) | `cd9a4843` | `e6911ef7` | `YaoReal`, `SecureComputation`, root `TCSlib` |

- No open PR changes a module of the unit's closure (98 modules). None of the 185 new short names is declared in a file
  another PR changes (`pack-checks/namecheck.txt`); the review's name-clash scan has 0 exact clashes (the private
  `exists_ofFn_eq` of `CS/Lengths` shares its short name with the owned file's private one, disclosed).
- **Pending merge conditions (not audit items).** The combined trees are **not** built.
  - **#324's integration rebuild at the head:** the review build is at LE-doc `f61ce08f`; the maintainer rebuilds
    `ComposeSecurity` and its downstream (`YaoReal`, `SecureComputation`, root `TCSlib`) at `a6eaebd7`, on the merged
    tip, before #324 merges.
  - Whichever of #324 and #313, #318, #319 or #323 merges second needs an integration rebuild of the shared downstream
    on the merged tip before it merges; the maintainer runs that build.
  - Treat these as conditions on the merge, not as something for this audit to establish. What you can raise: a
    concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **SC-F02** (info): the final REPORT's overlap section relies on the checkpoint tables; copies are in the evidence
  (`worker/cp1/`, `worker/cp2/`). **SC-F04** (info): the 70 missing formulas, fixed by LE-doc. **SC-F05** (info):
  `COMMITS.tsv` has no signing column; the hashes reproduce only with the environment's deterministic SSH signing
  (`logs/git-am-integrity*.log`), as sc-ot F-05.
- **The PR description** reports the build (279/279) without saying that it ran at LE-doc; this pack states it.
- **`yaoProtocol_hbcSecure` keeps `sorryAx`**, now only through `otProtocol_*` (#318) and `yaoHybrid_*` (sc-yao);
  `hbcSecure_compose` is no longer among its admissions (review DepTrace).
- **Admissions:** 31 in 14 modules → 28 in 13; only `ComposeSecurity` changes (3 → 0). Outside the issued order only
  `SeedMajority` (#312) and `SpecialEncryptionMulti` (#311) differ, both base delta (`logs/sorry-census.txt`).
- **The worker's promotion requests** (the FP/history toolkit of `CS/Machines`, `Efficient.exists_polyTime`,
  `polyTimeComputable_slots`, `negligible_polyExpr_mul`, the coin splittings, the acceptance lemmas, `abs_chain_le`/
  `exists_hyb_step` beside the multicopy lemma, the argmax-advice pattern) are for the deferred cleanup.

## Also check

**Axioms**
- At LE-doc, `composeP_efficient`, `composeV_efficient`, `hbcSecure_compose`, `polyTime_compose`, `exists_simA/B` and
  the helper endpoints each print `[propext, Classical.choice, Quot.sound]` (`landing/census-head.log`). At the base
  the three targets and `polyTime_compose` had `sorryAx`.
- The census has **258** stored constants (= the worker's); the axiom union is the standard three, with no `sorryAx`,
  `@[simp]` or instance. Against the base: removed 0, type-changed 0, axioms-changed 4 (the targets and
  `polyTime_compose`, `sorryAx` dropped; `logs/census-base-vs-head.tsv`).

**Sizes and widths:** the owned file 449 lines, the largest helper 632 (`CS/Runs`), every line at most 100 characters
(`source-head.json`).

**Build:** at LE-doc `f61ce08f`, **279/279 modules rc 0, 0 errors in both diagnostic forms** (G26-N1; substring
"error" 0): the downstream of every module changed since `eff2dcd0` (85 = 69 base delta + 16 unit) through root
`TCSlib` and `audits/pass-shelat/Checks` (`landing/root-checks.jsonl`, at the pre-edit head `f3036c69`), then 18/18
for LE-doc (`landing/edit-build-results.jsonl`). The 16 unit modules have 0 warnings and 0 sorries. Whole-tree check
at `f61ce08f`: 1264 modules, RESULT OK (`landing/tree-check-head.txt`). Restore: `dl-oleans` back at `457ba704…`.
**Not rebuilt at the head** (question 5).

**Lint:** 92 FAIL / 101 WARN at the tip and at the landing head before LE-doc, with identical line sets; LE-doc and
LE-prose only edit docstrings.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (SC-F01–SC-F05).
- **`verification.zip`** (121 entries): every file the review cites and the pack uses, as byte-identical originals.
  Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/sc-compose/final-r1/`, SHA-256 `c11ce8bb…`) and `review-evidence-SHA256SUMS`, its
    manifest: 917 entries, 66 directories and 851 files, exactly the 850 manifest paths plus `SHA256SUMS`
    (byte-identical to the manifest; no top folder); every hash verifies;
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `records/` (12): the issue package `fills/sc-compose/issued-r1/`, the duplication ledger (DL-49), the decision log
    (the SC-F01 and SC-F03 rulings) and the secure-computation plan (§ 2.11–2.12), at records
    `540bac18ce13cb8ef37b7dc41d97de5d2deaf661`;
  - `evidence/` (70): byte copies of the ZIP entries this pack cites;
  - `worker/` (13): byte copies from exchange (`inbox/fills/sc-compose/`): at the final
    `bdfdcb76d0d78bedd61025b33cb7382b26ee7c70`, `COMMITS.tsv`, the census and sorry diffs, the lint diff, the axioms,
    `git am` check, header check and control, sketch and width checks and the control results; and the two checkpoint
    REPORTs at `419c4ceb` and `f1ba0b1a` (`worker/cp1/REPORT.md`, `worker/cp2/REPORT.md`; 10 of the 13 also
    byte-identical to the review's `logs/delivery-extracts/`);
  - `pack-checks/` (21): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `bdfdcb76`, under `inbox/fills/sc-compose/`. Its top `SHA256SUMS`
  lists 1062 files and `evidence/SHA256SUMS` 1031, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`), `build-summary.txt`,
  `edit-build-results.jsonl`, `edit-build-summary.txt`, `census-head.log` (= `probe-runs/mods/PlProbe_H_CensusHead.log`),
  `frozen-check.txt` (= `statements/head-le/frozen-check.txt`) and `tree-check-head.txt`.
- **`worker-report.md`:** the worker's final `REPORT.md`, at exchange `bdfdcb76`.
- **`pr-description.md`:** the PR #324 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (16 paths, 4580 insertions, 60 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 16 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 98 files.
- **The bundle** adds, as context at the head: `SecureComputation/Hybrid.lean` (`HybridProtocol`, `PolyTime`,
  `HBCSecure` and readers), `SecureComputation/Compose.lean` and `SecureComputation/ComposePhases.lean` (the composed
  protocol and its phase lemmas).

## Findings delivery

Return `gate37-sc-compose-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-49, or necessary evidence that
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

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Machines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Cryptography.SecureComputation.Compose
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time machines on encoded histories

The machine infrastructure behind the efficiency of the composed parties
(`HybridProtocol.composeP_efficient`, `composeV_efficient`) [Gol04, §7.3.1, the protocol of
Theorem 7.3.3]: a party of `H.compose ρ` reads its history `encodeMsgs hist` at interleaved
positions (the messages of one run of `ρ` sit at every other pair, `Compose.slotMsgs`), and maps
`ρ`'s next-message function over the `L(n)` runs. Both are loops over a data-dependent range of
the unary FP toolkit (`ZeroKnowledge/EncodingMachines.lean`) and the peeling loops of
`GraphIsomorphism/EfficiencyRep.lean`.

## Main definitions

* `ComposeMachines.padTo`: zero padding, the string form of `padFin`.

## Main results

* `ComposeMachines.polyTimeComputable_flatMap_range`: concatenating a polynomial-time chunk over
  a data-dependent range is polynomial-time.
* `ComposeMachines.iterSnd_poly`, `msgAt_encodeMsgs`: the `i`-th message of an encoded history.
* `ComposeMachines.encodeMsgs_append`, `encodeMsgs_eq_flatMap`, `encodeMsgs_slotMsgs`: the
  history encoding as a concatenation of chunks, and the interleaved slots of a history.
* `ComposeMachines.polyTimeComputable_slots`: **the interleaved-slot map**: the encoded messages
  `slotMsgs sel off p hist` are a polynomial-time function of the encoded history, for a
  polynomial-time selector and unary offset and count.
* `ComposeMachines.Efficient.exists_polyTime`: an efficient strategy's next-message function is
  a polynomial-time function of the machine layout `GI.ilayout` (the converse of
  `GI.efficient_of_polyTime`).
* `ComposeMachines.ofFn_padFin`, `padTo_poly`: `padFin` as a polynomial-time string map.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines and their time complexity, pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! ### Loops over a data-dependent range -/

/-- Emitting `E i` at the indices `i < L` of `List.range N` gives the concatenation of the
`E i` over `i < min N L`:
`(range N).flatMap (fun i => if i < L then E i else []) = (range (min N L)).flatMap E`. -/
theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
      (List.range (min N L)).flatMap E
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite E L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]

/-- **Concatenating a chunk over a data-dependent range**: if the chunk `E z i` is a
polynomial-time function of `⟨1^i, z⟩` and the count `n z` is a unary function, then
`z ↦ E z 0 ++ ⋯ ++ E z (n z − 1)` is polynomial-time.
`PolyTimeComputable fun z => (List.range (n z)).flatMap (E z)`.

**Proof sketch.** An instance of `Complexity.polyTimeComputable_iterateEmit` on the counter step
`EncodingMachines.cstep` from `⟨[], z⟩`, whose `i`-th iterate is `⟨1^i, z⟩` (`cstep_iterate`),
emitting `E z i` while `i < n z` (`flatMap_range_ite`); the number of rounds is the polynomial
bound of the unary count (`PolyTimeComputable.output_length_le`). -/
theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
  obtain ⟨C, c, hC⟩ := hn.output_length_le
  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD)
      (hn.comp polyTimeComputable_pairSndD)
  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  refine (hL.comp hpre).congr fun z => ?_
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]

/-! ### Reading an encoded history -/

/-- **The iterated second projection** `pairSndD^[i z] (s z)` is polynomial-time for a
polynomial-time `s` and a unary count `i`.
`PolyTimeComputable fun z => pairSndD^[i z] (s z)`.

**Proof sketch.** `GI.iterUnary_poly` with the step `⟨x₀, s⟩ ↦ pairSndD s` on
`⟨1^{i z}, s z⟩`; peeling never lengthens a word (`GI.length_iterate_le`,
`GI.length_pairSndD_le`), so the orbit is bounded by the input length. -/
theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
  have hstep : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hclosed : ∀ x₀ k, (fun t => pairSndD (pairSndD (pairEncode x₀ t)))^[k] (pairSndD x₀) =
      pairSndD^[k] (pairSndD x₀) := by
    intro x₀ k
    congr 1
    funext t
    rw [pairSndD_pairEncode]
  have hit := GI.iterUnary_poly hstep .var fun x₀ k _ => by
    rw [hclosed, PolyExpr.eval_var]
    exact (GI.length_iterate_le GI.length_pairSndD_le _ k).trans (GI.length_pairSndD_le x₀)
  refine (hit.comp (hi.pairEncode hs)).congr fun z => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- **The `i`-th message of an encoded history**: `pairFstD (pairSndD^[i] (encodeMsgs hist)) =
hist.getD i []` (`GI.iterate_pairSndD_encodeMsgs`, `Strategy.pairFstD_encodeMsgs`). -/
theorem msgAt_encodeMsgs (hist : List (List Bool)) (i : ℕ) :
    pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) = hist.getD i [] := by
  rw [GI.iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD]

/-- **The history encoding is a concatenation**:
`encodeMsgs (a ++ b) = encodeMsgs a ++ encodeMsgs b` (`pairEncode_nil_append`).
It is the public `CommitmentLemmas.encodeMsgs_append` (`ZeroKnowledge/CommitmentLemmas.lean`). -/
theorem encodeMsgs_append (a b : List (List Bool)) :
    Strategy.encodeMsgs (a ++ b) = Strategy.encodeMsgs a ++ Strategy.encodeMsgs b :=
  TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append a b

/-- **The history encoding chunk by chunk**: `encodeMsgs l = l.flatMap fun m => ⟨m, []⟩`. -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap fun m => pairEncode m [] := by
  induction l with
  | nil => rw [Strategy.encodeMsgs_nil, List.flatMap_nil]
  | cons m l ih =>
    rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ← ih, BinArith.pairEncode_nil_append]

/-- **The encoded slots of a history**: the encoding of `slotMsgs sel off p hist` is the
concatenation over `q < p` of the chunk `⟨hist[off + q], []⟩` when `sel q`, read from the
encoded history (`msgAt_encodeMsgs`):
`encodeMsgs (slotMsgs sel off p hist) = (range p).flatMap fun q =>
if sel q then ⟨pairFstD (pairSndD^[off + q] (encodeMsgs hist)), []⟩ else []`. -/
theorem encodeMsgs_slotMsgs (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) :
    Strategy.encodeMsgs (Compose.slotMsgs sel off p hist) =
      (List.range p).flatMap fun q =>
        if sel q then pairEncode (pairFstD (pairSndD^[off + q] (Strategy.encodeMsgs hist))) []
        else [] := by
  rw [Compose.slotMsgs_eq, encodeMsgs_eq_flatMap, List.flatMap_map]
  induction p with
  | zero => simp only [List.range_zero, List.filter_nil, List.flatMap_nil]
  | succ p ih =>
    rw [List.range_succ, List.filter_append, List.flatMap_append, List.flatMap_append, ih,
      List.flatMap_singleton]
    congr 1
    cases h : sel p
    · rw [List.filter_singleton, h, cond_false, List.flatMap_nil, if_neg Bool.false_ne_true]
    · rw [List.filter_singleton, h, cond_true, List.flatMap_singleton, if_pos rfl,
        msgAt_encodeMsgs]

/-- **The interleaved-slot map**: for a selector `sel z q` that is a polynomial-time test of
`⟨1^q, z⟩`, unary offset `off z` and count `p z`, and a polynomial-time word `M z`, the word
`(range (p z)).flatMap fun q => if sel z q then ⟨pairFstD (pairSndD^[off z + q] (M z)), []⟩
else []` is polynomial-time; on `M z = encodeMsgs hist` it is
`encodeMsgs (slotMsgs (sel z) (off z) (p z) hist)` (`encodeMsgs_slotMsgs`).

**Proof sketch.** `polyTimeComputable_flatMap_range` with the chunk built from the test, the
iterated projection at the unary count `off z + q` (`iterSnd_poly`, `unaryAdd_poly`) and
`pairEncode`. -/
theorem polyTimeComputable_slots {sel : List Bool → ℕ → Bool}
    (hsel : PolyTimeComputable fun w => [sel (pairSndD w) (pairFstD w).length])
    {off p : List Bool → ℕ} (hoff : PolyTimeComputable fun z => List.replicate (off z) true)
    (hp : PolyTimeComputable fun z => List.replicate (p z) true)
    {M : List Bool → List Bool} (hM : PolyTimeComputable M) :
    PolyTimeComputable fun z => (List.range (p z)).flatMap fun q =>
      if sel z q then pairEncode (pairFstD (pairSndD^[off z + q] (M z))) [] else [] := by
  have hcnt : PolyTimeComputable fun w =>
      List.replicate (off (pairSndD w) + (pairFstD w).length) true :=
    unaryAdd_poly (hoff.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have hmsg := polyTimeComputable_pairFstD.comp
    (iterSnd_poly (hM.comp polyTimeComputable_pairSndD) hcnt)
  exact polyTimeComputable_flatMap_range
    (polyTimeComputable_ite hsel (hmsg.pairEncode (polyTimeComputable_const []))
      (polyTimeComputable_const [])) hp

/-! ### Strategies as functions of the machine layout -/

/-- **An efficient strategy is a polynomial-time function of the layout** (the converse of
`GI.efficient_of_polyTime`): if `S.Efficient`, there is a polynomial-time `F` with
`S.next x z r hist = F (GI.ilayout x z hist r)` (the output
function of the uniform machine, `NUPPT.polyTimeComputable_output`; its advice is empty). -/
theorem Efficient.exists_polyTime {S : Strategy} (h : S.Efficient) :
    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ x z r hist, S.next x z r hist = F (GI.ilayout x z hist r) := by
  obtain ⟨A, hA, -, hnext⟩ := (Strategy.efficient_iff S).1 h
  refine ⟨A.output, A.polyTimeComputable_output, fun x z r hist => ?_⟩
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA,
    GI.ilayout_def]

/-! ### Zero padding -/

/-- **Zero padding** to length `L` (and truncation to `L`): `padTo L w = (w ++ 0^L).take L`, the
string form of `padFin L w` (`ofFn_padFin`). -/
def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- The defining equation of `padTo`: `padTo L w = (w ++ 0^L).take L`. -/
theorem padTo_eq (L : ℕ) (w : List Bool) : padTo L w = (w ++ List.replicate L false).take L :=
  rfl

/-- Padding to a unary length is polynomial-time (`EncodingMachines.truncate_poly`, the zeros
`GI.zeros_poly` of the unary string).
`PolyTimeComputable fun x => padTo (L x) (s x)`. -/
theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => padTo (L x) (s x) :=
  truncate_poly (hs.append ((GI.zeros_poly.comp' hL).congr fun x => by
    rw [List.length_replicate])) hL

/-- The padded word has length `L`: `|padTo L w| = L`. -/
theorem length_padTo (L : ℕ) (w : List Bool) : (padTo L w).length = L := by
  rw [padTo_eq, List.length_take, List.length_append, List.length_replicate]
  omega

/-- **`padFin` as a string**: `List.ofFn (padFin L w) = padTo L w`. -/
theorem ofFn_padFin (L : ℕ) (w : List Bool) : List.ofFn (padFin L w) = padTo L w := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_ofFn, padTo_eq, List.getElem?_take]
  by_cases hi : i < L
  · rw [dif_pos hi, if_pos hi, padFin_apply, Fin.val_mk, List.getD_eq_getElem?_getD,
      List.getElem?_append]
    split_ifs with h
    · rw [List.getElem?_eq_getElem h, Option.getD_some]
    · rw [List.getElem?_eq_none_iff.2 (by omega), Option.getD_none,
        List.getElem?_replicate, if_pos (by omega)]
  · rw [dif_neg hi, if_neg hi]

end TCSlib.Cryptography.SecureComputation.ComposeMachines

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Bounds.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial length bounds

The advice of a non-uniform reduction has polynomially bounded length (`NUPPT.advice_length`). The
reductions of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] hard-wire views and
outputs of executions, so their lengths must be bounded by a polynomial in `n`. This file collects
the lengths of the encodings (`encodeMsgs`, the machine layouts), of the transcripts, and of the
outputs of machines and efficient strategies.

## Main results

* `ComposeBound.length_encodeMsgs_le`, `length_transcriptWith_fst_le`, `_snd_le`.
* `ComposeBound.length_runAt_le`, `Efficient.length_next_le`, `length_ilayout`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform PPT machines, Definition 26.8) and §4.4 (time complexity of interactive
  machines).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeBound

open Complexity Turing

/-! ### Lengths of encodings and outputs -/

/-- **A transcript has at most `rounds` messages per party**:
`|(π.transcriptWith P' x y z r).1| ≤ π.rounds(|x|)` (`Compose.exec_eq_map`). -/
theorem length_transcriptWith_fst_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).1.length ≤ π.rounds.eval x.length := by
  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- The verifier's half: `|(π.transcriptWith P' x y z r).2| ≤ π.rounds(|x|)`. -/
theorem length_transcriptWith_snd_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) : (π.transcriptWith P' x y z r).2.length ≤ π.rounds.eval x.length := by
  rw [Protocol.transcriptWith_eq, Compose.exec_eq_map, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- **The length of an encoded history**: if every message has at most `c` bits,
`|encodeMsgs l| ≤ |l| (2c + 2)` (`encodeMsgs_eq_flatMap`, `BinArith.length_encWords_le`).
It is the public `CommitmentLemmas.length_encodeMsgs_le` (`ZeroKnowledge/CommitmentLemmas.lean`). -/
theorem length_encodeMsgs_le (l : List (List Bool)) (c : ℕ) (h : ∀ w ∈ l, w.length ≤ c) :
    (Strategy.encodeMsgs l).length ≤ l.length * (2 * c + 2) :=
  TCSlib.Cryptography.CommitmentLemmas.length_encodeMsgs_le l c h

/-- **The length of a machine layout**:
`|layout u y α r| = 2(2(2|u| + 2 + |y|) + 2 + |α|) + 2 + |r|`
(`NUPPT.layout_eq`, `length_pairEncode`). -/
theorem length_layout (u y α r : List Bool) :
    (NUPPT.layout u y α r).length = 2 * (2 * (2 * u.length + 2 + y.length) + 2 + α.length) + 2 +
      r.length := by
  rw [NUPPT.layout_eq, length_pairEncode, length_pairEncode, length_pairEncode]

/-- **The output of a machine is polynomially long**:
`|A.runAt n y r| ≤ A.Ct (|layout 1^n y (A.advice n) ⟦r⟧| + 1)^A.ct`
(`NUPPT.output_length_le`, `NUPPT.runAtL_eq_output_layout`). -/
theorem length_runAt_le (A : NUPPT) (n : ℕ) (y : List Bool) (r : A.Coins n) :
    (A.runAt n y r).length ≤ A.Ct * (2 * (2 * (2 * n + 2 + y.length) + 2 +
      (A.advice n).length) + 2 + A.coinLen n + 1) ^ A.ct := by
  have h := A.output_length_le (NUPPT.layout (List.replicate n true) y (A.advice n) (List.ofFn r))
  rw [NUPPT.timeBound_def, length_layout, List.length_replicate, List.length_ofFn] at h
  rw [NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]
  exact h

/-- **The next message of an efficient strategy is polynomially long** in the length of its
activation's layout: for some `C, c`, `|S.next x z r hist| ≤ C (|GI.ilayout x z hist r| + 1)^c`
(`ComposeMachines.Efficient.exists_polyTime`, `PolyTimeComputable.output_length_le`). -/
theorem Efficient.length_next_le {S : Strategy} (h : S.Efficient) :
    ∃ C c : ℕ, ∀ x z r hist, (S.next x z r hist).length ≤
      C * ((GI.ilayout x z hist r).length + 1) ^ c := by
  obtain ⟨F, hF, hnext⟩ := ComposeMachines.Efficient.exists_polyTime h
  obtain ⟨C, c, hC⟩ := hF.output_length_le
  exact ⟨C, c, fun x z r hist => by rw [hnext]; exact hC _⟩

/-- **The length of a strategy layout**: `|GI.ilayout x z hist r| =
2(2(2|x| + 2 + (2(2|x| + 2 + |z|) + 2 + |encodeMsgs hist|)) + 2) + 2 + |r|`. -/
theorem length_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    (GI.ilayout x z hist r).length =
      2 * (2 * (2 * x.length + 2 + (2 * (2 * x.length + 2 + z.length) + 2 +
        (Strategy.encodeMsgs hist).length)) + 2) + 2 + r.length := by
  rw [GI.ilayout_def, length_layout, List.length_replicate, length_pairEncode, length_pairEncode,
    List.length_nil, Nat.add_zero]

end TCSlib.Cryptography.SecureComputation.ComposeBound

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Runs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposePhases
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The real samples of the composed protocol, run by run

Step 2 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]: the coins
of an honest execution of `H.compose ρ` on `1^n` are the `main`-tapes `m` and one pair of
`ρ`-tapes `t j` per call (`composeCoins`), and when every run's outputs are the ideal answers
(`GoodRuns`), the real sample of either side is the assembled view (`ComposeSim.asmView`) of the
real views of the runs (`realViewA`, `realViewB`), with the main phase and the other party's output
those of the hybrid execution on the `main`-tapes (`realA_compose_eq`, `realB_compose_eq`, using
`hM`).

## Main definitions

* `ComposeSim.splitCoins`: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for `m = a + q·b`.
* `HybridProtocol.composeCoins`: the coins of `H.compose ρ` as `main`-tapes and run tapes.
* `HybridProtocol.inA`, `inB`: the call inputs as strings.
* `HybridProtocol.realViewA`, `realViewB`: the encoded views of a party in the honest runs.
* `HybridProtocol.GoodRuns`: every run's outputs are the ideal answers.

## Main results

* `ComposeSim.ofFn_splitCoins`, `HybridProtocol.ofFn_composeCoins_fst`, `_snd`.
* `HybridProtocol.answersRealA_eq_answersA`, `answersRealB_eq_answersB`: under `GoodRuns` the honest
  answers are the ideal ones.
* `HybridProtocol.realA_compose_eq`, `realB_compose_eq`: the real samples under `GoodRuns`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim Compose

namespace ComposeSim

/-- **A tape and `q` blocks as one string**: `{0,1}^a × ({0,1}^b)^q ≃ {0,1}^m` for
`m = a + q·b`, the tape followed by the blocks in order (`Fin.appendEquiv`, `FunFamily.blocks`). -/
def splitCoins {m a q b : ℕ} (h : m = a + q * b) :
    (Fin a → Bool) × (Fin q → Fin b → Bool) ≃ (Fin m → Bool) :=
  ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
    ((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))

/-- The defining equation of `splitCoins` (see `splitCoins`).
`splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
((Fin.appendEquiv a (q * b)).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool)))`. -/
theorem splitCoins_eq {m a q b : ℕ} (h : m = a + q * b) :
    splitCoins h = ((Equiv.refl (Fin a → Bool)).prodCongr (FunFamily.blocks q b).symm).trans
      ((Fin.appendEquiv a (q * b)).trans
        (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))) := rfl

/-- The blocks as one string: `⟦(blocks q b).symm t⟧ = ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`.

**Proof sketch.** `List.ofFn_mul` writes `⟦v⟧` for `v : Fin (q·b) → Bool` as the concatenation
of `q` blocks of `b` bits, entry `j` of block `i` being `v (i·b + j)`; by
`FunFamily.blocks_symm_apply` that is `t i j`, since `(i·b + j) / b = i` and
`(i·b + j) % b = j` for `j < b`. -/
theorem ofFn_blocks_symm (q b : ℕ) (t : Fin q → Fin b → Bool) :
    List.ofFn ((FunFamily.blocks q b).symm t) = (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => List.ofFn_inj.2 (funext fun j => ?_))
  rw [FunFamily.blocks_symm_apply]
  have hj := j.2
  have hb : 0 < b := by omega
  congr 1
  · refine Fin.ext ?_
    rw [Fin.coe_divNat]
    show ((i : ℕ) * b + j) / b = i
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]
  · refine Fin.ext ?_
    rw [Fin.coe_modNat]
    show ((i : ℕ) * b + j) % b = j
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **The split coins as a string**: `⟦splitCoins h (u, t)⟧ = ⟦u⟧ ++ ⟦t 0⟧ ++ ⋯ ++ ⟦t (q − 1)⟧`. -/
theorem ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) :
    List.ofFn (splitCoins h (u, t)) =
      List.ofFn u ++ (List.ofFn fun j => List.ofFn (t j)).flatten := by
  rw [splitCoins_eq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr]
  show List.ofFn (Fin.append u ((FunFamily.blocks q b).symm t)) = _
  rw [List.ofFn_fin_append, ofFn_blocks_symm]

/-- The first `a` bits of `splitCoins h (u, t)` are `u`.
`(List.ofFn (splitCoins h (u, t))).take a = List.ofFn u`. -/
theorem take_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) : (List.ofFn (splitCoins h (u, t))).take a = List.ofFn u := by
  rw [ofFn_splitCoins, List.take_left' List.length_ofFn]

/-- Block `j < q` of `splitCoins h (u, t)` is `t j`:
`runTape a b j ⟦splitCoins h (u, t)⟧ = ⟦t j⟧` (`Compose.runTape_eq`). -/
theorem runTape_ofFn_splitCoins {m a q b : ℕ} (h : m = a + q * b) (u : Fin a → Bool)
    (t : Fin q → Fin b → Bool) (j : Fin q) :
    runTape a b j (List.ofFn (splitCoins h (u, t))) = List.ofFn (t j) := by
  rw [runTape_eq, ofFn_splitCoins, ← List.drop_drop, List.drop_left' List.length_ofFn]
  have hblk := coinBlock_flatten (B := b) (List.ofFn fun j => List.ofFn (t j))
    (fun c hc => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact j.2)
  rw [coinBlock_eq] at hblk
  rw [hblk, List.getElem_ofFn]

/-- **A concatenation over `L·R` indices in `L` blocks of `R`**:
`(range (L·R)).flatMap f = (range L).flatMap fun j => (range R).flatMap fun p => f (R·j + p)`. -/
theorem flatMap_range_mul (f : ℕ → List Bool) (R : ℕ) : ∀ L,
    (List.range (L * R)).flatMap f =
      (List.range L).flatMap fun j => (List.range R).flatMap fun p => f (R * j + p)
  | 0 => by rw [Nat.zero_mul, List.range_zero, List.flatMap_nil, List.flatMap_nil]
  | L + 1 => by
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, flatMap_range_mul f R L,
      List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_map,
      Nat.mul_comm L R]

end ComposeSim

namespace HybridProtocol

/-! ### Coins of the composed protocol -/

section Coins

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- Alice's composed coin length at `1^n` is `main.P.coins + calls(n)·ρ.P.coins`.
`(H.compose ρ).P.coinLen (List.replicate n true).length = H.main.P.coinLen (List.replicate n
true).length + H.calls.eval n * ρ.P.coinLen (List.replicate n true).length`. -/
theorem composeP_coinLen_eq (n : ℕ) :
    (H.compose ρ).P.coinLen (List.replicate n true).length =
      H.main.P.coinLen (List.replicate n true).length +
        H.calls.eval n * ρ.P.coinLen (List.replicate n true).length := by
  rw [compose_P_coinLen, List.length_replicate]

/-- Bob's composed coin length at `1^n` is `main.V.coins + calls(n)·ρ.V.coins`.
`(H.compose ρ).V.coinLen (List.replicate n true).length = H.main.V.coinLen (List.replicate n
true).length + H.calls.eval n * ρ.V.coinLen (List.replicate n true).length`. -/
theorem composeV_coinLen_eq (n : ℕ) :
    (H.compose ρ).V.coinLen (List.replicate n true).length =
      H.main.V.coinLen (List.replicate n true).length +
        H.calls.eval n * ρ.V.coinLen (List.replicate n true).length := by
  rw [compose_V_coinLen, List.length_replicate]

/-- **The coins of `H.compose ρ` at `1^n`** as the `main`-tapes and one pair of `ρ`-tapes per
call: Alice's tape is her `main`-tape followed by her `ρ`-tapes, Bob's likewise.
`H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃ (H.compose
ρ).ExecCoins (H.compose ρ).P (List.replicate n true)`. -/
def composeCoins (n : ℕ) :
    H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) ≃
      (H.compose ρ).ExecCoins (H.compose ρ).P (List.replicate n true) :=
  ((Equiv.refl (H.Coins n)).prodCongr (Equiv.arrowProdEquivProdArrow _ _ _)).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans
      ((ComposeSim.splitCoins (H.composeP_coinLen_eq ρ n)).prodCongr
        (ComposeSim.splitCoins (H.composeV_coinLen_eq ρ n))))

/-- Alice's composed tape is `splitCoins` of her `main`-tape and her run tapes.
`(H.composeCoins ρ n (m, t)).1 = splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1)`. -/
theorem composeCoins_fst (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    (H.composeCoins ρ n (m, t)).1 =
      ComposeSim.splitCoins (H.composeP_coinLen_eq ρ n) (m.1, fun j => (t j).1) :=
  rfl

/-- Bob's composed tape is `splitCoins` of his `main`-tape and his run tapes.
`(H.composeCoins ρ n (m, t)).2 = splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2)`. -/
theorem composeCoins_snd (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    (H.composeCoins ρ n (m, t)).2 =
      ComposeSim.splitCoins (H.composeV_coinLen_eq ρ n) (m.2, fun j => (t j).2) :=
  rfl

/-- Alice's composed tape: `⟦(composeCoins (m, t)).1⟧ = ⟦m.1⟧ ++ ⟦(t 0).1⟧ ++ ⋯`. -/
theorem ofFn_composeCoins_fst (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    List.ofFn (H.composeCoins ρ n (m, t)).1 =
      List.ofFn m.1 ++ (List.ofFn fun j => List.ofFn (t j).1).flatten :=
  ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 fun j => (t j).1

/-- Bob's composed tape: `⟦(composeCoins (m, t)).2⟧ = ⟦m.2⟧ ++ ⟦(t 0).2⟧ ++ ⋯`. -/
theorem ofFn_composeCoins_snd (n : ℕ) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    List.ofFn (H.composeCoins ρ n (m, t)).2 =
      List.ofFn m.2 ++ (List.ofFn fun j => List.ofFn (t j).2).flatten :=
  ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 fun j => (t j).2

end Coins

/-! ### The runs of an honest execution -/

section Runs

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice's input to call `j`** as a string: `⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`, `[]`
otherwise. -/
def inA (n : ℕ) (zA rA : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else []

/-- The defining equation of `inA`: `inA n zA rA j = ⟦callA(n, zA, rA, j)⟧` for `j < calls(n)`,
`[]` otherwise. -/
theorem inA_eq (n : ℕ) (zA rA : List Bool) (j : ℕ) :
    H.inA n zA rA j =
      if h : j < H.calls.eval n then List.ofFn (H.callA n zA rA ⟨j, h⟩) else [] := rfl

/-- **Bob's input to call `j`** as a string: `⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`, `[]`
otherwise. -/
def inB (n : ℕ) (zB rB : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else []

/-- The defining equation of `inB`: `inB n zB rB j = ⟦callB(n, zB, rB, j)⟧` for `j < calls(n)`,
`[]` otherwise. -/
theorem inB_eq (n : ℕ) (zB rB : List Bool) (j : ℕ) :
    H.inB n zB rB j =
      if h : j < H.calls.eval n then List.ofFn (H.callB n zB rB ⟨j, h⟩) else [] := rfl

/-- The call inputs do not depend on how the parameter is written:
`N = n → ⟦callA(N, zA, rA, j)⟧ = ⟦callA(n, zA, rA, j)⟧`. -/
theorem ofFn_callA_congr {N n : ℕ} (hN : N = n) (zA rA : List Bool) (j : ℕ)
    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
    List.ofFn (H.callA N zA rA ⟨j, h₁⟩) = List.ofFn (H.callA n zA rA ⟨j, h₂⟩) := by
  subst hN
  rfl

/-- The call inputs do not depend on how the parameter is written:
`N = n → ⟦callB(N, zB, rB, j)⟧ = ⟦callB(n, zB, rB, j)⟧`. -/
theorem ofFn_callB_congr {N n : ℕ} (hN : N = n) (zB rB : List Bool) (j : ℕ)
    (h₁ : j < H.calls.eval N) (h₂ : j < H.calls.eval n) :
    List.ofFn (H.callB N zB rB ⟨j, h₁⟩) = List.ofFn (H.callB n zB rB ⟨j, h₂⟩) := by
  subst hN
  rfl

/-- **The run inputs of `H.compose ρ` at `1^n` are the call inputs**: for `j < calls(n)`,
`runInputA 1^n zA ⟦(composeCoins (m, t)).1⟧ j = inA n zA ⟦m.1⟧ j`
(`runInputA_of_lt`, `take_ofFn_splitCoins`). -/
theorem runInputA_composeCoins (n : ℕ) (zA : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j =
      H.inA n zA (List.ofFn m.1) j := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [inA_eq]
  by_cases hj : j < H.calls.eval n
  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
    rw [dif_pos hj, H.runInputA_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
      composeCoins_fst, take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n)]
    exact H.ofFn_callA_congr hN _ _ j hj' hj
  · rw [dif_neg hj, H.runInputA_of_ge _ _ _ (by rw [hN]; omega)]

/-- Bob's run inputs at `1^n` are his call inputs (as `runInputA_composeCoins`).
`H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j = H.inB n zB
(List.ofFn m.2) j`. -/
theorem runInputB_composeCoins (n : ℕ) (zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j =
      H.inB n zB (List.ofFn m.2) j := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [inB_eq]
  by_cases hj : j < H.calls.eval n
  · have hj' : j < H.calls.eval (List.replicate n true).length := by rw [hN]; exact hj
    rw [dif_pos hj, H.runInputB_of_lt _ _ _ hj', ← Strategy.coinLen_eq,
      composeCoins_snd, take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]
    exact H.ofFn_callB_congr hN _ _ j hj' hj
  · rw [dif_neg hj, H.runInputB_of_ge _ _ _ (by rw [hN]; omega)]

/-- **The honest run `j` at `1^n` is `ρ`'s execution on the call inputs and the run tapes**:
`runExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ j k = exec ρ.P ρ.V vF 1^n (inA j) (inB j) ⟦(t j).1⟧ ⟦(t j).2⟧ k`
for `c = composeCoins (m, t)` (`runExec_eq`, `runTape_ofFn_splitCoins`). -/
theorem runExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
    (k : ℕ) :
    H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) j k =
      exec ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) k := by
  rw [runExec_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
    composeCoins_snd,
    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]

/-- The message of `ρ`'s move `p` in the honest run `j` at `1^n` is the move of `ρ`'s execution on
the call inputs and the run tapes (`runMsg_eq`, as `runExec_composeCoins`).
`H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn
(H.composeCoins ρ n (m, t)).2) j p = moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA
n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2)
p`. -/
theorem runMsg_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : Fin (H.calls.eval n))
    (p : ℕ) :
    H.runMsg ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) j p =
      moveMsg ρ.P ρ.V ρ.verifierFirst (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (List.ofFn (t j).1) (List.ofFn (t j).2) p := by
  rw [runMsg_eq, runInputA_composeCoins, runInputB_composeCoins, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq, composeCoins_fst,
    composeCoins_snd,
    runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1) j,
    runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2) j]

/-- **Every run gives the ideal answers**: for every call `j`, Alice's and Bob's `ρ`-outputs in
the run on the call inputs and the tapes `t j` are `⟦f_A(callA_j, callB_j)⟧` and
`⟦f_B(callA_j, callB_j)⟧`.
`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧ ρ.outV ρ.P (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).2`. -/
def GoodRuns (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) : Prop :=
  ∀ j : Fin (H.calls.eval n),
    ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j)
        (t j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
    ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
        (H.inB n zB (List.ofFn m.2) j) (t j) =
      List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2

/-- The defining property of `GoodRuns` (see `GoodRuns`).
`H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n), ρ.outP (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧ ρ.outV ρ.P (List.replicate n true) (H.inA n zA
(List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t j) = List.ofFn (G.f n (H.callA n zA (List.ofFn
m.1) j) (H.callB n zB (List.ofFn m.2) j)).2`. -/
theorem goodRuns_iff (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.GoodRuns ρ n zA zB m t ↔ ∀ j : Fin (H.calls.eval n),
      ρ.outP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t j) =
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1 ∧
      ρ.outV ρ.P (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t j) =
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2 :=
  Iff.rfl

/-- **Under `GoodRuns`, Alice's honest answers are the ideal ones**:
`answersRealA 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersA n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.

**Proof sketch.** Both are concatenations over the calls `j < L` (`flatten_ofFn_eq_flatMap_range`;
`1^n` has length `n`). Block `j` of the honest answers is `padFin` of Alice's output of the run
on the call inputs and the run tapes (`runInputA_composeCoins`, `runExec_composeCoins`), which is
`ρ.outP` of that run (`Protocol.outP_eq`, `Protocol.transcriptWith_eq`), i.e. `⟦f_A(…)⟧` by
`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
`padTo_of_length`). -/
theorem answersRealA_eq_answersA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) :
    H.answersRealA ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
      H.answersA n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [answersRealA_eq, answersA_eq, flatten_ofFn_eq_flatMap_range (fun j =>
      List.ofFn (padFin (G.outA.eval (List.replicate n true).length)
        (ρ.P.next (List.replicate n true)
          (H.runInputA (List.replicate n true) zA (List.ofFn (H.composeCoins ρ n (m, t)).1) j)
          (runTape (H.main.P.coins.eval (List.replicate n true).length)
            (ρ.P.coins.eval (List.replicate n true).length) j
            (List.ofFn (H.composeCoins ρ n (m, t)).1))
          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
            (ρ.rounds.eval (List.replicate n true).length)).1))),
    show (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).1
        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).1 else [] by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
    flatMap_range_congr (by rw [hN])]
  refine List.flatMap_congr fun j hj => ?_
  have hjn : j < H.calls.eval n := List.mem_range.1 hj
  rw [dif_pos hjn, runInputA_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
    composeCoins_fst, runTape_ofFn_splitCoins (H.composeP_coinLen_eq ρ n) m.1 (fun j => (t j).1)
      ⟨j, hjn⟩, ← composeCoins_fst, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
    ← Protocol.transcriptWith_eq, ← Protocol.outP_eq, (hg ⟨j, hjn⟩).1, ofFn_padFin,
    padTo_of_length (by rw [List.length_ofFn, hN])]

/-- **Under `GoodRuns`, Bob's honest answers are the ideal ones**:
`answersRealB 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ = answersB n zA zB ⟦m.1⟧ ⟦m.2⟧` for `c = composeCoins (m, t)`.

**Proof sketch.** As `answersRealA_eq_answersA`: block `j` of Bob's honest answers is `padFin` of
his output in run `j` on the call inputs and the run tapes (`runInputB_composeCoins`,
`runExec_composeCoins`), which is `ρ.outV` of that run (`Protocol.outV_eq`), i.e. `⟦f_B(…)⟧` by
`GoodRuns`; padding a word of the right length is the identity (`ofFn_padFin`,
`padTo_of_length`). -/
theorem answersRealB_eq_answersB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) :
    H.answersRealB ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) =
      H.answersB n zA zB (List.ofFn m.1) (List.ofFn m.2) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  rw [answersRealB_eq, answersB_eq, flatten_ofFn_eq_flatMap_range (fun j =>
      List.ofFn (padFin (G.outB.eval (List.replicate n true).length)
        (ρ.V.next (List.replicate n true)
          (H.runInputB (List.replicate n true) zB (List.ofFn (H.composeCoins ρ n (m, t)).2) j)
          (runTape (H.main.V.coins.eval (List.replicate n true).length)
            (ρ.V.coins.eval (List.replicate n true).length) j
            (List.ofFn (H.composeCoins ρ n (m, t)).2))
          (H.runExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
            (List.ofFn (H.composeCoins ρ n (m, t)).2) j
            (ρ.rounds.eval (List.replicate n true).length)).2))),
    show (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) j) (H.callB n zB (List.ofFn m.2) j)).2
        ).flatten = (List.range (H.calls.eval n)).flatMap fun i => if h : i < H.calls.eval n then
          List.ofFn (G.f n (H.callA n zA (List.ofFn m.1) ⟨i, h⟩)
            (H.callB n zB (List.ofFn m.2) ⟨i, h⟩)).2 else [] by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2])),
    flatMap_range_congr (by rw [hN])]
  refine List.flatMap_congr fun j hj => ?_
  have hjn : j < H.calls.eval n := List.mem_range.1 hj
  rw [dif_pos hjn, runInputB_composeCoins, ← Strategy.coinLen_eq, ← Strategy.coinLen_eq,
    composeCoins_snd, runTape_ofFn_splitCoins (H.composeV_coinLen_eq ρ n) m.2 (fun j => (t j).2)
      ⟨j, hjn⟩, ← composeCoins_snd, runExec_composeCoins H ρ n zA zB m t ⟨j, hjn⟩,
    ← Protocol.transcriptWith_eq (π := ρ) (P' := ρ.P), ← Protocol.outV_eq, (hg ⟨j, hjn⟩).2,
    ofFn_padFin, padTo_of_length (by rw [List.length_ofFn, hN])]

/-- **Under `GoodRuns`, the main phase is the hybrid execution on the `main`-tapes**:
`mainExec 1^n zA zB ⟦c.1⟧ ⟦c.2⟧ k = exec main.P main.V vF 1^n (privA n zA zB ⟦m.1⟧ ⟦m.2⟧)
(privB …) ⟦m.1⟧ ⟦m.2⟧ k` (`mainExec_eq`, the answers, `take_ofFn_splitCoins`). -/
theorem mainExec_composeCoins (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n zA zB m t) (k : ℕ) :
    H.mainExec ρ (List.replicate n true) zA zB (List.ofFn (H.composeCoins ρ n (m, t)).1)
        (List.ofFn (H.composeCoins ρ n (m, t)).2) k =
      exec H.main.P H.main.V H.main.verifierFirst (List.replicate n true)
        (H.privA n zA zB (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n zA zB (List.ofFn m.1) (List.ofFn m.2)) (List.ofFn m.1) (List.ofFn m.2) k := by
  rw [mainExec_eq, H.answersRealA_eq_answersA ρ n zA zB m t hg,
    H.answersRealB_eq_answersB ρ n zA zB m t hg, privA_eq, privB_eq, ← Strategy.coinLen_eq,
    ← Strategy.coinLen_eq, composeCoins_fst, composeCoins_snd,
    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n),
    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n)]

/-- **Alice's encoded views of the honest runs**: for `j < calls(n)`, her view of `ρ` on the call
inputs `inA j`, `inB j` and the tapes `t j`; `[]` otherwise. -/
def realViewA (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then
    (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
  else []

/-- The defining equation of `realViewA` (see `realViewA`).
`H.realViewA ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewP (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
theorem realViewA_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.realViewA ρ n zA zB m t j =
      if h : j < H.calls.eval n then
        (ρ.viewP (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
      else [] := rfl

/-- **Bob's encoded views of the honest runs** (as `realViewA`, with `ρ.viewV`).
`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
def realViewB (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval n then
    (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
      (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
  else []

/-- The defining equation of `realViewB` (see `realViewB`).
`H.realViewB ρ n zA zB m t j = if h : j < H.calls.eval n then (ρ.viewV (List.replicate n true)
(H.inA n zA (List.ofFn m.1) j) (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode else []`. -/
theorem realViewB_eq (n : ℕ) (zA zB : List Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) (j : ℕ) :
    H.realViewB ρ n zA zB m t j =
      if h : j < H.calls.eval n then
        (ρ.viewV (List.replicate n true) (H.inA n zA (List.ofFn m.1) j)
          (H.inB n zB (List.ofFn m.2) j) (t ⟨j, h⟩)).encode
      else [] := rfl

/-- **The real sample of Alice's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
`F.realA (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.P`'s coins,
Bob's moves read, no leading filler) of Alice's real run views, her input, her `main`-tape and
the hybrid main phase, paired with Bob's output in the hybrid execution on the `main`-tapes.

**Proof sketch.** `compose_viewP` and `compose_outV` (with `hM`) give the view and Bob's output.
Her tape is her `main`-tape followed by the run tapes (`ofFn_composeCoins_fst`), which are the
tapes of the run views, of exact length (`padTo_of_length`). Her messages are Bob's run messages
at the pairs, `L` blocks of `R` (`encodeMsgs_eq_flatMap`, `flatMap_range_mul`, `slotFromB_mul_add`),
which are the chunks `segW` of the received messages of the run views (`runExec_composeCoins`,
`exec_eq_map`, `segW_encodeMsgs`), followed by the main phase, the hybrid one under `GoodRuns`
(`mainExec_composeCoins`). -/
theorem realA_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
          (List.replicate n true) (List.ofFn x) (List.ofFn m.1)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1)
          (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
  -- the tape: the `main`-tape followed by the run tapes
  have htape : List.ofFn (H.composeCoins ρ n (m, t)).1 = List.ofFn m.1 ++
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        padTo (ρ.P.coins.eval (List.replicate n true).length)
          (pairFstD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    have hT0 : (List.ofFn fun j => List.ofFn (t j).1).flatten =
        (List.range (H.calls.eval n)).flatMap fun j =>
          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).1 else [] := by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
    rw [ofFn_composeCoins_fst, hT0, flatMap_range_congr hL.symm]
    congr 1
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [dif_pos hjn, realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk,
      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
        rw [List.length_ofFn, Strategy.coinLen_eq])]
  -- Bob's run messages at the pairs: the chunks of the received messages of Alice's run views
  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length)).map
        (H.slotFromB ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        segW ρ.verifierFirst true (ρ.rounds.eval (List.replicate n true).length)
          (pairSndD (pairSndD (H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [realViewA_eq, dif_pos hjn, Protocol.viewP_eq, View.encode_mk, pairSndD_pairEncode,
      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (moverIsV ρ.verifierFirst) =
        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun q => moverIsV ρ.verifierFirst q == true) from
        List.filter_congr fun q _ => (beq_true _).symm, segW_encodeMsgs]
    refine List.flatMap_congr fun p hp => ?_
    rw [slotFromB_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp), beq_true,
      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
    (H.main.rounds.eval (List.replicate n true).length)
  rw [Functionality.realA_eq, compose_viewP, compose_outV H ρ _ _ _ _ (hM _), View.encode_mk,
    asmView_eq, encodeMsgs_append, hmsgs, hmain, H.answersRealB_eq_answersB ρ n _ _ m t hg, htape,
    List.replicate_zero, Strategy.encodeMsgs_nil, List.append_nil,
    Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq, Protocol.outV_eq,
    Protocol.transcriptWith_eq, privB_eq, ← Strategy.coinLen_eq H.main.V, composeCoins_snd,
    take_ofFn_splitCoins (H.composeV_coinLen_eq ρ n), ← privB_eq]

/-- **The real sample of Bob's side under `GoodRuns`**: with `c = composeCoins (m, t)`,
`F.realB (H.compose ρ) n x y c` is the assembled view (`ComposeSim.asmView` with `ρ.V`'s coins,
Alice's moves read, `lead` leading fillers) of Bob's real run views, his input, his `main`-tape
and the hybrid main phase, paired with Alice's output in the hybrid execution.

**Proof sketch.** As `realA_compose_eq`, with `compose_viewV`, `compose_outP`, the second
components, `slotFromA_mul_add` and the leading fillers between the runs and the main phase. -/
theorem realB_compose_eq {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
          (List.replicate n true) (List.ofFn y) (List.ofFn m.2)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2)
          (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m) := by
  have hN : (List.replicate n true).length = n := List.length_replicate
  have hL : H.calls.eval (List.replicate n true).length = H.calls.eval n := by rw [hN]
  -- the tape: the `main`-tape followed by the run tapes
  have htape : List.ofFn (H.composeCoins ρ n (m, t)).2 = List.ofFn m.2 ++
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        padTo (ρ.V.coins.eval (List.replicate n true).length)
          (pairFstD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    have hT0 : (List.ofFn fun j => List.ofFn (t j).2).flatten =
        (List.range (H.calls.eval n)).flatMap fun j =>
          if h : j < H.calls.eval n then List.ofFn (t ⟨j, h⟩).2 else [] := by
      rw [← flatten_ofFn_eq_flatMap_range]
      exact congrArg List.flatten (List.ofFn_inj.2 (funext fun j => by rw [dif_pos j.2]))
    rw [ofFn_composeCoins_snd, hT0, flatMap_range_congr hL.symm]
    congr 1
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [dif_pos hjn, realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk,
      pairSndD_pairEncode, pairFstD_pairEncode, padTo_of_length (by
        rw [List.length_ofFn, Strategy.coinLen_eq])]
  -- Alice's run messages at the pairs: the chunks of the received messages of Bob's run views
  have hmsgs : Strategy.encodeMsgs ((List.range (H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length)).map
        (H.slotFromA ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
          (List.ofFn (H.composeCoins ρ n (m, t)).1) (List.ofFn (H.composeCoins ρ n (m, t)).2))) =
      (List.range (H.calls.eval (List.replicate n true).length)).flatMap fun j =>
        segW ρ.verifierFirst false (ρ.rounds.eval (List.replicate n true).length)
          (pairSndD (pairSndD (H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t j))) := by
    rw [encodeMsgs_eq_flatMap, List.flatMap_map, flatMap_range_mul]
    refine List.flatMap_congr fun j hj => ?_
    have hjn : j < H.calls.eval n := by rw [← hL]; exact List.mem_range.1 hj
    rw [realViewB_eq, dif_pos hjn, Protocol.viewV_eq, View.encode_mk, pairSndD_pairEncode,
      pairSndD_pairEncode, Protocol.transcriptWith_eq, exec_eq_map,
      show (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun i => !moverIsV ρ.verifierFirst i) =
        (List.range (ρ.rounds.eval (List.replicate n true).length)).filter
          (fun q => moverIsV ρ.verifierFirst q == false) from
        List.filter_congr fun q _ => (beq_false _).symm, segW_encodeMsgs]
    refine List.flatMap_congr fun p hp => ?_
    rw [slotFromA_mul_add H ρ _ _ _ _ _ (List.mem_range.1 hp),
      runMsg_composeCoins H ρ n _ _ m t ⟨j, hjn⟩ p]
    cases moverIsV ρ.verifierFirst p <;> rfl
  have hmain := H.mainExec_composeCoins ρ n (List.ofFn x) (List.ofFn y) m t hg
    (H.main.rounds.eval (List.replicate n true).length)
  rw [Functionality.realB_eq, compose_viewV, compose_outP H ρ _ _ _ _ (hM _), View.encode_mk,
    asmView_eq, encodeMsgs_append, encodeMsgs_append, hmsgs, hmain,
    H.answersRealA_eq_answersA ρ n _ _ m t hg, htape, Protocol.transcript_eq_transcriptWith,
    Protocol.transcriptWith_eq, Protocol.outP_eq, Protocol.transcriptWith_eq, privA_eq,
    ← Strategy.coinLen_eq H.main.P, composeCoins_fst,
    take_ofFn_splitCoins (H.composeP_coinLen_eq ρ n), ← privA_eq]

end Runs

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Assembly.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Assembling a view of the composed protocol from views of the runs

The post-processing of the simulators and reductions of the composition theorem
[Gol04, §7.3.1, proof of Theorem 7.3.3]: a party's view of `H.compose ρ` is its common input, its
input, its tape (the `main`-tape followed by one `ρ`-tape per run) and its received messages
(the other party's run messages at the pairs, with fillers, the leading fillers and the main
phase). Given a word `V j` per run that reads as an encoded view of `ρ`
(`⟨⟨x, z⟩, ⟨r, encodeMsgs received⟩⟩`, `View.encode`), `asmView` assembles such a view: the run
tapes are cut or padded to `ρ`'s coin length, and the received run messages are placed at the
pairs where the other party moves (the `k`-th message received at the `k`-th such pair, `p / 2`).

## Main definitions

* `ComposeSim.segW`: the pair chunks of one run, from the run's encoded received messages.
* `ComposeSim.asmView`: the assembled encoded view; `ComposeSim.asmW` its word form.

## Main results

* `ComposeSim.moverIsV_beq_iff`, `length_filter_mover`, `getD_filter_map_mover`: the parity of
  the pairs at which a party moves, and the position of a run message among them.
* `ComposeSim.polyTimeComputable_asmW`: the assembly is polynomial-time.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

/-! ### The pairs at which a party moves -/

/-- **The mover test is a parity**: `moverIsV vF q == b` iff `q % 2 = (if vF == b then 0 else 1)`
(`moverIsV_def`). -/
theorem moverIsV_beq_iff (vF b : Bool) (q : ℕ) :
    (moverIsV vF q == b) = true ↔ q % 2 = (if vF == b then 0 else 1) := by
  rw [moverIsV_def]
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> cases vF <;> cases b <;> simp [h]

/-- The number of `q < p` with `q % 2 = d` (for `d ≤ 1`) is `(p + 1 − d) / 2`. -/
theorem length_filter_mod_two {d : ℕ} (hd : d ≤ 1) :
    ∀ p, ((List.range p).filter fun q => q % 2 == d).length = (p + 1 - d) / 2
  | 0 => by
    rw [List.range_zero, List.filter_nil, List.length_nil]
    omega
  | p + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_mod_two hd p,
      List.filter_singleton]
    by_cases h : p % 2 = d
    · rw [show (p % 2 == d) = true from beq_iff_eq.2 h, cond_true, List.length_singleton]
      omega
    · rw [show (p % 2 == d) = false from beq_eq_false_iff_ne.2 h, cond_false, List.length_nil]
      omega

/-- **The number of moves of a party before its move `p`** is `p / 2`: if
`moverIsV vF p == b`, then `|{q < p : moverIsV vF q == b}| = p / 2` (`moverIsV_beq_iff`,
`length_filter_mod_two`). -/
theorem length_filter_mover (vF b : Bool) {p : ℕ} (hp : (moverIsV vF p == b) = true) :
    ((List.range p).filter fun q => moverIsV vF q == b).length = p / 2 := by
  have hd : (if vF == b then 0 else 1) ≤ 1 := by split_ifs <;> omega
  have hpar := (moverIsV_beq_iff vF b p).1 hp
  have hfilt : ((List.range p).filter fun q => moverIsV vF q == b) =
      (List.range p).filter fun q => q % 2 == (if vF == b then 0 else 1) := by
    refine List.filter_congr fun q _ => ?_
    rw [Bool.eq_iff_iff, moverIsV_beq_iff]
    exact beq_iff_eq.symm
  rw [hfilt, length_filter_mod_two hd]
  split_ifs at hpar ⊢ <;> omega

/-- **A run message at its position**: for `p < R` with `moverIsV vF p == b`, entry `p / 2` of
the messages `f q` at the `q < R` with `moverIsV vF q == b` is `f p`
(`length_filter_mover`). -/
theorem getD_filter_map_mover (vF b : Bool) (f : ℕ → List Bool) {R p : ℕ} (hpR : p < R)
    (hp : (moverIsV vF p == b) = true) :
    (((List.range R).filter fun q => moverIsV vF q == b).map f).getD (p / 2) [] = f p := by
  obtain ⟨d, rfl⟩ : ∃ d, R = p + 1 + d := ⟨R - (p + 1), by omega⟩
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append,
    List.filter_singleton, hp, cond_true, List.map_append, List.map_append, List.map_singleton,
    List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by
      rw [List.length_map, length_filter_mover vF b hp]), List.length_map,
    length_filter_mover vF b hp, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero,
    Option.getD_some]

/-- Padding a word of the right length is the identity: `|w| = L → padTo L w = w`. -/
theorem padTo_of_length {L : ℕ} {w : List Bool} (h : w.length = L) : padTo L w = w := by
  rw [padTo_eq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- A concatenation over `range a` is one over `range b` when `a = b` (no rewriting inside the
chunks): `a = b → (range a).flatMap f = (range b).flatMap f`. -/
theorem flatMap_range_congr {a b : ℕ} (h : a = b) (f : ℕ → List Bool) :
    (List.range a).flatMap f = (List.range b).flatMap f := by
  subst h
  rfl

/-! ### One run's chunks -/

/-- **The pair chunks of one run**, from the encoded received messages `e` of the run's view:
for `p < R`, the chunk `⟨m_p, []⟩` with `m_p` the message received at the `p / 2`-th of the pairs
where the other party moves (`moverIsV vF p == b`) and `[]` (a filler) at the others:
`segW vF b R e = (range R).flatMap fun p =>
⟨if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else [], []⟩`. -/
def segW (vF b : Bool) (R : ℕ) (e : List Bool) : List Bool :=
  (List.range R).flatMap fun p =>
    pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) []

/-- The defining equation of `segW` (see `segW`).
`segW vF b R e = (List.range R).flatMap fun p => pairEncode (if moverIsV vF p == b then pairFstD
(pairSndD^[p / 2] e) else []) []`. -/
theorem segW_eq (vF b : Bool) (R : ℕ) (e : List Bool) :
    segW vF b R e = (List.range R).flatMap fun p =>
      pairEncode (if moverIsV vF p == b then pairFstD (pairSndD^[p / 2] e) else []) [] := rfl

/-- **`segW` on a real run**: if the run's received messages are the messages `f q` at the
`q < R` with `moverIsV vF q == b`, the chunks are `⟨f p, []⟩` at those pairs and `⟨[], []⟩` at
the others:
`segW vF b R (encodeMsgs (filter … (range R)).map f) =
(range R).flatMap fun p => ⟨if moverIsV vF p == b then f p else [], []⟩`
(`msgAt_encodeMsgs`, `getD_filter_map_mover`). -/
theorem segW_encodeMsgs (vF b : Bool) (R : ℕ) (f : ℕ → List Bool) :
    segW vF b R (Strategy.encodeMsgs (((List.range R).filter fun q => moverIsV vF q == b).map f)) =
      (List.range R).flatMap fun p =>
        pairEncode (if moverIsV vF p == b then f p else []) [] := by
  rw [segW_eq]
  refine List.flatMap_congr fun p hp => ?_
  by_cases h : (moverIsV vF p == b) = true
  · rw [if_pos h, if_pos h, msgAt_encodeMsgs, getD_filter_map_mover vF b f (List.mem_range.1 hp) h]
  · rw [if_neg h, if_neg h]

/-! ### The assembled view -/

/-- **The assembled encoded view** of a party of `H.compose ρ` (`n = |x₁|`, `L = calls(n)`,
`R = rounds(n)`, `c = cρ(n)`), from its common input `x₁`, input `xin`, `main`-tape `mt`, encoded
main-phase messages `me`, the number `lead` of leading fillers it receives, and one word `V j`
per run read as an encoded `ρ`-view: the view `⟨⟨x₁, xin⟩, ⟨mt ++ τ, E⟩⟩` with the tape
`τ = (range L).flatMap fun j => padTo c (tape of V j)` and the messages
`E = (range L).flatMap (fun j => segW vF b R (messages of V j)) ++ encodeMsgs [[]]^lead ++ me`. -/
def asmView (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (x₁ xin mt me : List Bool)
    (V : ℕ → List Bool) : List Bool :=
  pairEncode (pairEncode x₁ xin)
    (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
      ((List.range (calls.eval x₁.length)).flatMap (fun j =>
          segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
        Strategy.encodeMsgs (List.replicate lead []) ++ me))

/-- The defining equation of `asmView` (see `asmView`).
`asmView calls rounds cρ vF b lead x₁ xin mt me V = pairEncode (pairEncode x₁ xin) (pairEncode (mt
++ (List.range (calls.eval x₁.length)).flatMap fun j => padTo (cρ.eval x₁.length) (pairFstD
(pairSndD (V j)))) ((List.range (calls.eval x₁.length)).flatMap (fun j => segW vF b (rounds.eval
x₁.length) (pairSndD (pairSndD (V j)))) ++ Strategy.encodeMsgs (List.replicate lead []) ++ me))`. -/
theorem asmView_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me : List Bool) (V : ℕ → List Bool) :
    asmView calls rounds cρ vF b lead x₁ xin mt me V =
      pairEncode (pairEncode x₁ xin)
        (pairEncode (mt ++ (List.range (calls.eval x₁.length)).flatMap fun j =>
            padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j))))
          ((List.range (calls.eval x₁.length)).flatMap (fun j =>
              segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) ++
            Strategy.encodeMsgs (List.replicate lead []) ++ me)) := rfl

/-- `asmView` depends on the run words only below `L`: if `V j = V' j` for `j < calls(|x₁|)`, the
assembled views agree. -/
theorem asmView_congr (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me : List Bool) {V V' : ℕ → List Bool}
    (h : ∀ j < calls.eval x₁.length, V j = V' j) :
    asmView calls rounds cρ vF b lead x₁ xin mt me V =
      asmView calls rounds cρ vF b lead x₁ xin mt me V' := by
  have h₁ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
      padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V j)))) =
      (List.range (calls.eval x₁.length)).flatMap fun j =>
        padTo (cρ.eval x₁.length) (pairFstD (pairSndD (V' j))) :=
    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
  have h₂ : ((List.range (calls.eval x₁.length)).flatMap fun j =>
      segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V j)))) =
      (List.range (calls.eval x₁.length)).flatMap fun j =>
        segW vF b (rounds.eval x₁.length) (pairSndD (pairSndD (V' j))) :=
    List.flatMap_congr fun j hj => by rw [h j (List.mem_range.1 hj)]
  rw [asmView_eq, asmView_eq, h₁, h₂]

/-- **The assembly in word form**: on `w = ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩`, `asmView` with the run
words `V j = pairFstD (pairSndD^[j] VL)` (the entries of an encoded list,
`msgAt_encodeMsgs`). -/
def asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) : List Bool :=
  asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
    (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
    (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w))

/-- The defining equation of `asmW` (see `asmW`).
`asmW calls rounds cρ vF b lead w = asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD
w))) (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w))) (pairSndD (pairSndD
(pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w))`. -/
theorem asmW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (w : List Bool) :
    asmW calls rounds cρ vF b lead w =
      asmView calls rounds cρ vF b lead (pairFstD (pairFstD (pairFstD w)))
        (pairSndD (pairFstD (pairFstD w))) (pairFstD (pairSndD (pairFstD w)))
        (pairSndD (pairSndD (pairFstD w))) fun j => pairFstD (pairSndD^[j] (pairSndD w)) := rfl

/-- `asmW` on its word: `asmW … ⟨⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩, VL⟩ =
asmView … x₁ xin mt me (fun j => pairFstD (pairSndD^[j] VL))`. -/
theorem asmW_pairEncode (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (x₁ xin mt me VL : List Bool) :
    asmW calls rounds cρ vF b lead
        (pairEncode (pairEncode (pairEncode x₁ xin) (pairEncode mt me)) VL) =
      asmView calls rounds cρ vF b lead x₁ xin mt me fun j => pairFstD (pairSndD^[j] VL) := by
  rw [asmW_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- **`segW` is polynomial-time** on `⟨1^R, e⟩` words given by polynomial-time maps
(`polyTimeComputable_flatMap_range` over `p < R`, the mover test `polyTimeComputable_moverW`,
`p / 2` by `divNum_poly`, the message by `iterSnd_poly`). -/
theorem polyTimeComputable_segW (vF b : Bool) {R : List Bool → ℕ} {e : List Bool → List Bool}
    (hR : PolyTimeComputable fun z => List.replicate (R z) true) (he : PolyTimeComputable e) :
    PolyTimeComputable fun z => segW vF b (R z) (e z) := by
  have hhalf : PolyTimeComputable fun v => List.replicate ((pairFstD v).length / 2) true :=
    (divNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2)).congr
      fun v => by rw [divNum_eq]
  have hmsg := polyTimeComputable_pairFstD.comp'
    (iterSnd_poly (he.comp' polyTimeComputable_pairSndD) hhalf)
  have hchunk : PolyTimeComputable fun v =>
      pairEncode (if moverIsV vF (pairFstD v).length == b then
        pairFstD (pairSndD^[(pairFstD v).length / 2] (e (pairSndD v))) else []) [] :=
    (polyTimeComputable_ite ((polyTimeComputable_moverW vF b).congr fun v => moverW_eq vF b v)
      hmsg (polyTimeComputable_const [])).pairEncode (polyTimeComputable_const [])
  exact (polyTimeComputable_flatMap_range hchunk hR).congr fun z => (segW_eq vF b (R z) (e z)).symm

/-- **The assembly is polynomial-time**: `PolyTimeComputable (asmW calls rounds cρ vF b lead)`.

**Proof sketch.** The components `x₁`, `xin`, `mt`, `me` are projections. The tape part and the
message part are concatenations over the unary count `calls(|x₁|)`
(`polyTimeComputable_flatMap_range`) of a padded tape (`padTo_poly`) and of `segW`
(`polyTimeComputable_segW`) of the run word `pairFstD (pairSndD^[j] VL)` (`iterSnd_poly`),
followed by constant fillers and `me`; the word is `asmView` of these (`asmW_eq`,
`asmView_eq`). -/
theorem polyTimeComputable_asmW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
    PolyTimeComputable (asmW calls rounds cρ vF b lead) := by
  have hx₁ : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
  have hxin : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD)
  have hmt : PolyTimeComputable fun w => pairFstD (pairSndD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  have hme : PolyTimeComputable fun w => pairSndD (pairSndD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
  -- the run word `V j` from `v = ⟨1^j, w⟩`
  have hV : PolyTimeComputable fun v =>
      pairFstD (pairSndD^[(pairFstD v).length] (pairSndD (pairSndD v))) :=
    polyTimeComputable_pairFstD.comp' (iterSnd_poly
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD))
  have hn : PolyTimeComputable fun v =>
      List.replicate (pairFstD (pairFstD (pairFstD (pairSndD v)))).length true :=
    unaryLength_poly (hx₁.comp' polyTimeComputable_pairSndD)
  have htape : PolyTimeComputable fun v =>
      padTo (cρ.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
        (pairFstD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
          (pairSndD (pairSndD v)))))) :=
    padTo_poly ((polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).comp' hV)
      (unaryPolyOf_poly cρ hn)
  have hseg : PolyTimeComputable fun v =>
      segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD (pairSndD v)))).length)
        (pairSndD (pairSndD (pairFstD (pairSndD^[(pairFstD v).length]
          (pairSndD (pairSndD v)))))) :=
    polyTimeComputable_segW vF b (unaryPolyOf_poly rounds hn)
      ((polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD).comp' hV)
  have hL := unaryPolyOf_poly calls (unaryLength_poly hx₁)
  have hT := polyTimeComputable_flatMap_range (E := fun w j =>
    padTo (cρ.eval (pairFstD (pairFstD (pairFstD w))).length)
      (pairFstD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) htape hL
  have hS := polyTimeComputable_flatMap_range (E := fun w j =>
    segW vF b (rounds.eval (pairFstD (pairFstD (pairFstD w))).length)
      (pairSndD (pairSndD (pairFstD (pairSndD^[j] (pairSndD w)))))) hseg hL
  exact (((hx₁.pairEncode hxin).pairEncode ((hmt.append hT).pairEncode
    ((hS.append (polyTimeComputable_const _)).append hme)))).congr fun w => by
      rw [asmW_eq, asmView_eq]

end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composed parties as polynomial-time functions of the machine layout

The efficiency half of the composition theorem [Gol04, §7.3.1, the protocol of Theorem 7.3.3]:
Alice's and Bob's next-message functions in `H.compose ρ` (`HybridProtocol.composeP`,
`composeV`) are polynomial-time functions of the machine layout
`GI.ilayout x z hist r = ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, encodeMsgs hist⟩⟩, []⟩, r⟩`, when `main`'s and `ρ`'s
strategies are efficient and the call inputs are polynomial-time (`HybridProtocol.PolyTime`,
`Functionality.PolyTime`).

The pieces are shared by the two parties and generic in the strategies:
* `ComposeMachines.runW`: one activation of a `ρ`-party in run `j` after `p` pairs of the run,
  on the call input (recomputed from the `main`-tape), the run tape cut from the coins and the
  run's messages read from the history at the interleaved pairs (`polyTimeComputable_slots`);
* `ComposeMachines.ansW`: the `L(n)` run outputs, each padded to the answer length, concatenated;
* `ComposeMachines.mainW`: one activation of a `main`-party on its input paired with the answers,
  its `main`-tape and the messages after the runs.

## Main definitions

* `ComposeMachines.runW`, `ansW`, `mainW`, `moverW`: the shared pieces.
* `HybridProtocol.composePW`, `composeVW`: the two parties on the layout.

## Main results

* `ComposeMachines.runW_ilayout`, `ansW_ilayout`, `mainW_ilayout`: the pieces on a layout.
* `ComposeMachines.polyTimeComputable_runW`, `polyTimeComputable_ansW`,
  `polyTimeComputable_mainW`: the pieces are polynomial-time.
* `HybridProtocol.composeP_next_eq_composePW`, `composeV_next_eq_composeVW`: the composed
  parties are the layout functions.
* `HybridProtocol.polyTimeComputable_composePW`, `polyTimeComputable_composeVW`: and these are
  polynomial-time.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the composed protocol of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines and their time complexity, pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

namespace ComposeMachines

/-! ### The mover test -/

/-- **The mover test in unary**: `moverW vF b w = [moverIsV vF |fst w| = b]` (whether the
party moving at position `|fst w|` of `ρ` is the verifier, compared with `b`). -/
def moverW (vF b : Bool) (w : List Bool) : List Bool :=
  [moverIsV vF (pairFstD w).length == b]

/-- The defining equation of `moverW`: `moverW vF b w = [moverIsV vF |fst w| == b]`. -/
theorem moverW_eq (vF b : Bool) (w : List Bool) :
    moverW vF b w = [moverIsV vF (pairFstD w).length == b] := rfl

/-- The mover test is polynomial-time: the parity of the unary length `|fst w|`
(`EncodingMachines.modNum_poly`, `eqTest_poly`), compared with constants
(`Complexity.polyTimeComputable_ite`).
`PolyTimeComputable (moverW vF b)`. -/
theorem polyTimeComputable_moverW (vF b : Bool) : PolyTimeComputable (moverW vF b) := by
  have hpar : PolyTimeComputable fun w =>
      [decide (modNum (pairFstD w).length 2 = (if vF then 0 else 1))] :=
    eqTest_poly (modNum_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 2))
      (unaryConst_poly _)
  have h := polyTimeComputable_ite hpar (polyTimeComputable_const [b])
    (polyTimeComputable_const [!b])
  refine h.congr fun w => ?_
  rw [moverW_eq, moverIsV_def, modNum_eq]
  rcases Nat.mod_two_eq_zero_or_one (pairFstD w).length with hp | hp <;>
    cases vF <;> cases b <;> simp [hp]

/-! ### One activation of a `ρ`-party in a run -/

/-- **One `ρ`-activation in run `j` after `p` pairs of the run**, on the word
`u = ⟨1^j, ⟨1^p, w⟩⟩` with `w` a layout (common input `x`, input `z`, messages `M`, coins `r`,
`n = |x|`): the `ρ`-party's machine `Fρ` on the layout with common input `x`, input
`fcall ⟨1^n, ⟨z, ⟨r_{<c₀(n)}, 1^j⟩⟩⟩` (the call input from the `main`-tape), the messages
of the run read at the pairs `R(n)·j + q`, `q < p`, selected by `moverIsV vF q = b`, and the run
tape `r[c₀(n) + j·c(n), c₀(n) + (j + 1)·c(n))`. -/
def runW (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (u : List Bool) : List Bool :=
  Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
    (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
        (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
          (pairEncode (GI.argZ (pairSndD (pairSndD u)))
            (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
                (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
              (List.replicate (pairFstD u).length true))))))
      ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
        if moverIsV vF q == b then
          pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
            (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
        else []))
    []
    (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
        (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
          (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
      (c.eval (GI.argX (pairSndD (pairSndD u))).length)))

/-- The defining equation of `runW` (see `runW`).
`runW Fρ fcall c₀ c R vF b u = Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD
u))).length true) (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u))) (fcall (pairEncode
(List.replicate (GI.argX (pairSndD (pairSndD u))).length true) (pairEncode (GI.argZ (pairSndD
(pairSndD u))) (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take (c₀.eval (GI.argX (pairSndD
(pairSndD u))).length)) (List.replicate (pairFstD u).length true)))))) ((List.range (pairFstD
(pairSndD u)).length).flatMap fun q => if moverIsV vF q == b then pairEncode (pairFstD
(pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length * (pairFstD u).length + q] (GI.argM
(pairSndD (pairSndD u))))) [] else [])) [] (((NUPPT.inCoins (pairSndD (pairSndD u))).drop (c₀.eval
(GI.argX (pairSndD (pairSndD u))).length + (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD
u))).length)).take (c.eval (GI.argX (pairSndD (pairSndD u))).length)))`. -/
theorem runW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (u : List Bool) :
    runW Fρ fcall c₀ c R vF b u =
      Fρ (NUPPT.layout (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
        (pairEncode (pairEncode (GI.argX (pairSndD (pairSndD u)))
            (fcall (pairEncode (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
              (pairEncode (GI.argZ (pairSndD (pairSndD u)))
                (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
                    (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
                  (List.replicate (pairFstD u).length true))))))
          ((List.range (pairFstD (pairSndD u)).length).flatMap fun q =>
            if moverIsV vF q == b then
              pairEncode (pairFstD (pairSndD^[R.eval (GI.argX (pairSndD (pairSndD u))).length *
                (pairFstD u).length + q] (GI.argM (pairSndD (pairSndD u))))) []
            else []))
        []
        (((NUPPT.inCoins (pairSndD (pairSndD u))).drop
            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
              (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length)).take
          (c.eval (GI.argX (pairSndD (pairSndD u))).length))) := rfl

/-- **`runW` on a layout**: on `⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩` it is `Fρ` on the layout of
the run activation: `runW … ⟨1^j, ⟨1^p, GI.ilayout x z hist r⟩⟩ =
Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩) (slotMsgs sel (R·j) p hist)
(runTape c₀ c j r))` with `sel q = (moverIsV vF q == b)` (`encodeMsgs_slotMsgs`). -/
theorem runW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R : PolyExpr) (vF b : Bool)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) (j p : ℕ) :
    runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
        (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) =
      Fρ (GI.ilayout x (fcall (pairEncode (List.replicate x.length true)
          (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
        (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j) p hist)
        (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r)) := by
  rw [runW_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
    pairFstD_pairEncode, List.length_replicate, List.length_replicate, GI.argX_ilayout,
    GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout, GI.ilayout_def, encodeMsgs_slotMsgs,
    Compose.runTape_eq]

/-- **`runW` is polynomial-time** when `Fρ` and `fcall` are.
`PolyTimeComputable (runW Fρ fcall c₀ c R vF b)`.

**Proof sketch.** The layout is assembled (`NUPPT.polyTimeComputable_layout`) from the slot
projections, the unary polynomials `c₀(n)`, `c(n)`, `R(n)` (`unaryPoly_comp`), the call input
(`fcall` after `pairEncode`), the typed cuts of the coins (`EncodingMachines.truncate_poly`,
`Complexity.polyTimeComputable_pairDropPoly` at the unary count `c₀(n) + j·c(n)`) and the
interleaved-slot map at the offset `R(n)·j` (`polyTimeComputable_slots`). -/
theorem polyTimeComputable_runW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
    (hcall : PolyTimeComputable fcall) (c₀ c R : PolyExpr) (vF b : Bool) :
    PolyTimeComputable (runW Fρ fcall c₀ c R vF b) := by
  have hw : PolyTimeComputable fun u => pairSndD (pairSndD u) :=
    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have hx := GI.argX_poly.comp' hw
  have hn : PolyTimeComputable fun u =>
      List.replicate (GI.argX (pairSndD (pairSndD u))).length true := unaryLength_poly hx
  have hj : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hp : PolyTimeComputable fun u => List.replicate (pairFstD (pairSndD u)).length true :=
    unaryLength_poly (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD)
  have hr := NUPPT.polyTimeComputable_inCoins.comp' hw
  have hc₀ := unaryPoly_comp c₀ hx
  have hc := unaryPoly_comp c hx
  have hR := unaryPoly_comp R hx
  have hinp : PolyTimeComputable fun u => fcall (pairEncode
      (List.replicate (GI.argX (pairSndD (pairSndD u))).length true)
      (pairEncode (GI.argZ (pairSndD (pairSndD u)))
        (pairEncode ((NUPPT.inCoins (pairSndD (pairSndD u))).take
            (c₀.eval (GI.argX (pairSndD (pairSndD u))).length))
          (List.replicate (pairFstD u).length true)))) :=
    hcall.comp' (hn.pairEncode ((GI.argZ_poly.comp' hw).pairEncode
      ((truncate_poly hr hc₀).pairEncode hj)))
  have hsel : PolyTimeComputable fun w' => [moverIsV vF (pairFstD w').length == b] :=
    (polyTimeComputable_moverW vF b).congr fun w' => moverW_eq vF b w'
  have hslots := polyTimeComputable_slots (sel := fun _ q => moverIsV vF q == b)
    (off := fun u => R.eval (GI.argX (pairSndD (pairSndD u))).length * (pairFstD u).length)
    (p := fun u => (pairFstD (pairSndD u)).length)
    hsel
    (unaryMul_poly hR hj) hp (GI.argM_poly.comp' hw)
  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD (pairSndD u))).drop
      (c₀.eval (GI.argX (pairSndD (pairSndD u))).length +
        (pairFstD u).length * c.eval (GI.argX (pairSndD (pairSndD u))).length) :=
    ((polyTimeComputable_pairDropPoly .var).comp'
      ((unaryAdd_poly hc₀ (unaryMul_poly hj hc)).pairEncode hr)).congr fun u => by
        rw [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
          List.length_replicate]
  exact (hFρ.comp' (NUPPT.polyTimeComputable_layout hn ((hx.pairEncode hinp).pairEncode hslots)
    (polyTimeComputable_const []) (truncate_poly hdrop hc))).congr fun u => by
      rw [runW_eq]

/-! ### The answers -/

/-- **The answers on the layout**: the `L(n)` run outputs of the `ρ`-party (`runW` with
`p = R(n)`), each padded to `out(n)` bits, concatenated:
`ansW … w = (range L(n)).flatMap fun j => padTo out(n) (runW … ⟨1^j, ⟨1^{R(n)}, w⟩⟩)`. -/
def ansW (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (w : List Bool) : List Bool :=
  (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
    padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
      (pairEncode (List.replicate j true)
        (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w)))

/-- The defining equation of `ansW` (see `ansW`).
`ansW Fρ fcall c₀ c R L out vF b w = (List.range (L.eval (GI.argX w).length)).flatMap fun j => padTo
(out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b (pairEncode (List.replicate j true)
(pairEncode (List.replicate (R.eval (GI.argX w).length) true) w)))`. -/
theorem ansW_eq (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (w : List Bool) :
    ansW Fρ fcall c₀ c R L out vF b w =
      (List.range (L.eval (GI.argX w).length)).flatMap fun j =>
        padTo (out.eval (GI.argX w).length) (runW Fρ fcall c₀ c R vF b
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate (R.eval (GI.argX w).length) true) w))) := rfl

/-- **The answers are polynomial-time** (`polyTimeComputable_flatMap_range` over the unary count
`L(n)`, with the chunk `padTo_poly` of `polyTimeComputable_runW`).
`PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b)`. -/
theorem polyTimeComputable_ansW {Fρ fcall : List Bool → List Bool} (hFρ : PolyTimeComputable Fρ)
    (hcall : PolyTimeComputable fcall) (c₀ c R L out : PolyExpr) (vF b : Bool) :
    PolyTimeComputable (ansW Fρ fcall c₀ c R L out vF b) := by
  have hw := polyTimeComputable_pairSndD
  have hx := GI.argX_poly.comp' hw
  have hchunk : PolyTimeComputable fun v =>
      padTo (out.eval (GI.argX (pairSndD v)).length) (runW Fρ fcall c₀ c R vF b
        (pairEncode (List.replicate (pairFstD v).length true)
          (pairEncode (List.replicate (R.eval (GI.argX (pairSndD v)).length) true)
            (pairSndD v)))) :=
    padTo_poly ((polyTimeComputable_runW hFρ hcall c₀ c R vF b).comp
      ((unaryLength_poly polyTimeComputable_pairFstD).pairEncode
        ((unaryPoly_comp R hx).pairEncode hw))) (unaryPoly_comp out hx)
  exact (polyTimeComputable_flatMap_range hchunk (unaryPoly_comp L GI.argX_poly)).congr
    fun w => rfl

/-! ### One activation of a `main`-party -/

/-- **One `main`-activation on the layout**: the `main`-party's machine `Fm` on the layout with
common input `x`, input `⟨z, ans w⟩`, the messages after the first `d w` (`pairSndD^[d w] M`)
and the `main`-tape `r_{<c₀(n)}`. -/
def mainW (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr) (w : List Bool) :
    List Bool :=
  Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
    (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
      (pairSndD^[d w] (GI.argM w)))
    [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))

/-- The defining equation of `mainW` (see `mainW`).
`mainW Fm ans d c₀ w = Fm (NUPPT.layout (List.replicate (GI.argX w).length true) (pairEncode
(pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w))) (pairSndD^[d w] (GI.argM w))) []
((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length)))`. -/
theorem mainW_eq (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
    (w : List Bool) :
    mainW Fm ans d c₀ w =
      Fm (NUPPT.layout (List.replicate (GI.argX w).length true)
        (pairEncode (pairEncode (GI.argX w) (pairEncode (GI.argZ w) (ans w)))
          (pairSndD^[d w] (GI.argM w)))
        [] ((NUPPT.inCoins w).take (c₀.eval (GI.argX w).length))) := rfl

/-- **`mainW` on a layout**: `mainW Fm ans d c₀ (GI.ilayout x z hist r) =
Fm (GI.ilayout x ⟨z, ans (GI.ilayout x z hist r)⟩ (hist.drop (d …)) r_{<c₀})`
(`GI.iterate_pairSndD_encodeMsgs`). -/
theorem mainW_ilayout (Fm ans : List Bool → List Bool) (d : List Bool → ℕ) (c₀ : PolyExpr)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    mainW Fm ans d c₀ (GI.ilayout x z hist r) =
      Fm (GI.ilayout x (pairEncode z (ans (GI.ilayout x z hist r)))
        (hist.drop (d (GI.ilayout x z hist r))) (r.take (c₀.eval x.length))) := by
  rw [mainW_eq, GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout,
    GI.iterate_pairSndD_encodeMsgs, GI.ilayout_def, GI.ilayout_def]

/-- **`mainW` is polynomial-time** when `Fm`, the answers and the unary drop count are
(`iterSnd_poly`, `EncodingMachines.truncate_poly`).
`PolyTimeComputable (mainW Fm ans d c₀)`. -/
theorem polyTimeComputable_mainW {Fm ans : List Bool → List Bool} (hFm : PolyTimeComputable Fm)
    (hans : PolyTimeComputable ans) {d : List Bool → ℕ}
    (hd : PolyTimeComputable fun w => List.replicate (d w) true) (c₀ : PolyExpr) :
    PolyTimeComputable (mainW Fm ans d c₀) :=
  (hFm.comp' (NUPPT.polyTimeComputable_layout (unaryLength_poly GI.argX_poly)
    ((GI.argX_poly.pairEncode (GI.argZ_poly.pairEncode hans)).pairEncode
      (iterSnd_poly GI.argM_poly hd))
    (polyTimeComputable_const [])
    (truncate_poly NUPPT.polyTimeComputable_inCoins (unaryPoly_comp c₀ GI.argX_poly)))).congr
    fun w => by rw [mainW_eq]


/-- **`ansW` on a layout**: the concatenation over `j < L(|x|)` of the padded run outputs
`padTo out(|x|) (Fρ (GI.ilayout x (fcall ⟨1^{|x|}, ⟨z, ⟨r_{<c₀}, 1^j⟩⟩⟩)
(slotMsgs sel (R·j) R hist) (runTape c₀ c j r)))` (`runW_ilayout`). -/
theorem ansW_ilayout (Fρ fcall : List Bool → List Bool) (c₀ c R L out : PolyExpr) (vF b : Bool)
    (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    ansW Fρ fcall c₀ c R L out vF b (GI.ilayout x z hist r) =
      (List.range (L.eval x.length)).flatMap fun j =>
        padTo (out.eval x.length) (Fρ (GI.ilayout x
          (fcall (pairEncode (List.replicate x.length true)
            (pairEncode z (pairEncode (r.take (c₀.eval x.length)) (List.replicate j true)))))
          (Compose.slotMsgs (fun q => moverIsV vF q == b) (R.eval x.length * j)
            (R.eval x.length) hist)
          (Compose.runTape (c₀.eval x.length) (c.eval x.length) j r))) := by
  rw [ansW_eq, GI.argX_ilayout]
  refine List.flatMap_congr fun j _ => ?_
  rw [runW_ilayout]

/-- **A concatenation over `Fin L` as a concatenation over `range L`**:
`(List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E`. -/
theorem flatten_ofFn_eq_flatMap_range (E : ℕ → List Bool) (L : ℕ) :
    (List.ofFn fun j : Fin L => E j).flatten = (List.range L).flatMap E := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange, List.flatMap_map, List.flatMap_def]

end ComposeMachines

/-! ### The composed parties on the layout -/

namespace HybridProtocol

open ComposeMachines

section Parties

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice of `H.compose ρ` on the layout** [Gol04, §7.3.1], given machines `Fρ` for `ρ.P`,
`Fm` for `main.P` and `fcall` for her call inputs: with `k` the number of messages received
(`GI.msgCount`), `n = |x|`, `L = calls(n)`, `R = ρ.rounds(n)`:
- if `k < L·R`: `[]` if `ρ`'s mover `k % R` is Bob, else her `ρ`-move in run `k / R` after
  `k % R` pairs (`runW`, reading Bob's moves);
- else, if `main`'s verifier moves first and `k = L·R`: the leading filler `[]`;
- else her `main`-move on `⟨z, her answers⟩` (`ansW`) and the messages after the first `L·R`
  (`mainW`). -/
def composePW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide (GI.msgCount (GI.argM w) <
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
    if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) then []
    else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
      (pairEncode
        (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
        (pairEncode
          (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
  else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
  else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
      ρ.verifierFirst true)
    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) H.main.P.coins w

/-- The defining equation of `composePW` (see `composePW`).
`H.composePW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) < H.calls.eval (GI.argX w).length
* ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) %
ρ.rounds.eval (GI.argX w).length) then [] else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds
ρ.verifierFirst true (pairEncode (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX
w).length) true) (pairEncode (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX
w).length) true) w)) else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) = H.calls.eval
(GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then [] else mainW Fm (ansW Fρ fcall
H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA ρ.verifierFirst true) (fun w => H.calls.eval
(GI.argX w).length * ρ.rounds.eval (GI.argX w).length) H.main.P.coins w`. -/
theorem composePW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
    H.composePW ρ Fρ Fm fcall w =
      if decide (GI.msgCount (GI.argM w) <
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
        if moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)
        then []
        else runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
          (pairEncode
            (List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true)
            (pairEncode
              (List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true) w))
      else if (H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)) then []
      else mainW Fm (ansW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds H.calls G.outA
          ρ.verifierFirst true)
        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)
        H.main.P.coins w := rfl

/-- **Bob of `H.compose ρ` on the layout**, given machines `Fρ` for `ρ.V`, `Fm` for `main.V` and
`fcall` for his call inputs: with `c` the number of messages received and `k = c − 1`:
- if `k < L·R`: his `ρ`-move in run `k / R` after `k % R` pairs if `ρ`'s mover `k % R` is Bob
  (`runW`, reading Alice's moves), else `[]`;
- else his `main`-move on `⟨z, his answers⟩` and the messages after the first `L·R + lead`. -/
def composeVW (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) : List Bool :=
  if decide (GI.msgCount (GI.argM w) - 1 <
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
    if moverIsV ρ.verifierFirst ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
    then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
      (pairEncode
        (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
        (pairEncode
          (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
            true) w))
    else []
  else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
      ρ.verifierFirst false)
    (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
    H.main.V.coins w

/-- The defining equation of `composeVW` (see `composeVW`).
`H.composeVW ρ Fρ Fm fcall w = if decide (GI.msgCount (GI.argM w) - 1 < H.calls.eval (GI.argX
w).length * ρ.rounds.eval (GI.argX w).length) then if moverIsV ρ.verifierFirst ((GI.msgCount
(GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) then runW Fρ fcall H.main.V.coins ρ.V.coins
ρ.rounds ρ.verifierFirst false (pairEncode (List.replicate ((GI.msgCount (GI.argM w) - 1) /
ρ.rounds.eval (GI.argX w).length) true) (pairEncode (List.replicate ((GI.msgCount (GI.argM w) - 1) %
ρ.rounds.eval (GI.argX w).length) true) w)) else [] else mainW Fm (ansW Fρ fcall H.main.V.coins
ρ.V.coins ρ.rounds H.calls G.outB ρ.verifierFirst false) (fun w => H.calls.eval (GI.argX w).length *
ρ.rounds.eval (GI.argX w).length + H.lead) H.main.V.coins w`. -/
theorem composeVW_eq (Fρ Fm fcall : List Bool → List Bool) (w : List Bool) :
    H.composeVW ρ Fρ Fm fcall w =
      if decide (GI.msgCount (GI.argM w) - 1 <
          H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length) then
        if moverIsV ρ.verifierFirst
          ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
        then runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
          (pairEncode
            (List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true)
            (pairEncode
              (List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)
                true) w))
        else []
      else mainW Fm (ansW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds H.calls G.outB
          ρ.verifierFirst false)
        (fun w => H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length + H.lead)
        H.main.V.coins w := rfl

/-- **Alice of `H.compose ρ` is `composePW`**: if `Fρ`, `Fm` compute `ρ.P` and `main.P` on the
layout and `fcall` computes Alice's call inputs (the `callA` clause of `HybridProtocol.PolyTime`),
then `(H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.

**Proof sketch.** Unfold both sides (`composeP_next`, `composePW_eq`); the number of messages
read from the layout is `|hist|` (`GI.msgCount_encodeMsgs`). In a run branch `j = k / R < L`, so
the call input is `runInputA` (`runInputA_of_lt`) and `runW` is `runNextA` (`runW_ilayout`,
`runNextA_eq`). In the main branch `mainW` is `main.P.next` on the answers read by `ansW`, which
are `answersFromA` (`ansW_ilayout`, `answersFromA_eq`, `ofFn_padFin`). -/
theorem composeP_next_eq_composePW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : ∀ x z r hist, ρ.P.next x z r hist = Fρ (GI.ilayout x z hist r))
    (hFm : ∀ x z r hist, H.main.P.next x z r hist = Fm (GI.ilayout x z hist r))
    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
      fcall (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
    (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeP ρ).next x z r hist = H.composePW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
  have hrun : ∀ j p, j < H.calls.eval x.length →
      H.runNextA ρ x z r hist j p =
        runW Fρ fcall H.main.P.coins ρ.P.coins ρ.rounds ρ.verifierFirst true
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
    intro j p hj
    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputA_of_lt x z r hj, ← hFρ,
      runNextA_eq]
    congr 2
    funext q
    rw [beq_true]
  rw [composeP_next, composePW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  by_cases hk : hist.length < H.calls.eval x.length * ρ.rounds.eval x.length
  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
      rw [h, Nat.mul_zero] at hk
      omega
    have hj : hist.length / ρ.rounds.eval x.length < H.calls.eval x.length :=
      (Nat.div_lt_iff_lt_mul hR).2 hk
    rw [if_pos hk, if_pos hk]
    by_cases hm : moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) = true
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm, hrun _ _ hj]
  · rw [if_neg hk, if_neg hk]
    by_cases hl : H.main.verifierFirst = true ∧
        hist.length = H.calls.eval x.length * ρ.rounds.eval x.length
    · rw [if_pos hl, if_pos hl]
    · rw [if_neg hl, if_neg hl, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromA_eq,
        ansW_ilayout,
        flatten_ofFn_eq_flatMap_range
          (fun j => List.ofFn (padFin (G.outA.eval x.length)
            (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length))))]
      congr 2
      refine List.flatMap_congr fun j hj => ?_
      rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]

/-- **Bob of `H.compose ρ` is `composeVW`**: if `Fρ`, `Fm` compute `ρ.V` and `main.V` on the
layout and `fcall` computes Bob's call inputs, then
`(H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r)`.

**Proof sketch.** As `composeP_next_eq_composePW`, with `k = |hist| − 1`, `runNextB`,
`runInputB_of_lt`, the selector `!moverIsV` (`beq_false`), `answersFromB` and the drop count
`L·R + lead`. -/
theorem composeV_next_eq_composeVW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : ∀ x z r hist, ρ.V.next x z r hist = Fρ (GI.ilayout x z hist r))
    (hFm : ∀ x z r hist, H.main.V.next x z r hist = Fm (GI.ilayout x z hist r))
    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
      fcall (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
    (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeV ρ).next x z r hist = H.composeVW ρ Fρ Fm fcall (GI.ilayout x z hist r) := by
  have hrun : ∀ j p, j < H.calls.eval x.length →
      H.runNextB ρ x z r hist j p =
        runW Fρ fcall H.main.V.coins ρ.V.coins ρ.rounds ρ.verifierFirst false
          (pairEncode (List.replicate j true)
            (pairEncode (List.replicate p true) (GI.ilayout x z hist r))) := by
    intro j p hj
    rw [runW_ilayout, hcall x.length z _ ⟨j, hj⟩, ← H.runInputB_of_lt x z r hj, ← hFρ,
      runNextB_eq]
    congr 2
    funext q
    rw [beq_false]
  rw [composeV_next, composeVW_eq, GI.argM_ilayout, GI.argX_ilayout, GI.msgCount_encodeMsgs]
  simp only [decide_eq_true_eq]
  by_cases hk : hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length
  · have hR : 0 < ρ.rounds.eval x.length := Nat.pos_of_ne_zero fun h => by
      rw [h, Nat.mul_zero] at hk
      omega
    have hj : (hist.length - 1) / ρ.rounds.eval x.length < H.calls.eval x.length :=
      (Nat.div_lt_iff_lt_mul hR).2 hk
    rw [if_pos hk, if_pos hk]
    by_cases hm : moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) = true
    · rw [if_pos hm, if_pos hm, hrun _ _ hj]
    · rw [if_neg hm, if_neg hm]
  · rw [if_neg hk, if_neg hk, mainW_ilayout, GI.argX_ilayout, ← hFm, answersFromB_eq, ansW_ilayout,
      flatten_ofFn_eq_flatMap_range
        (fun j => List.ofFn (padFin (G.outB.eval x.length)
          (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length))))]
    congr 2
    refine List.flatMap_congr fun j hj => ?_
    rw [ofFn_padFin, hrun _ _ (List.mem_range.1 hj), runW_ilayout]

/-- **`composePW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
`PolyTimeComputable (H.composePW ρ Fρ Fm fcall)`.

**Proof sketch.** Three branches (`Complexity.polyTimeComputable_ite`) on unary tests of the
message count (`GI.msgCount_poly`) against `L(n)·R(n)` (`ltTest_poly`, `eqTest_poly`), the
mover test at `k % R` (`polyTimeComputable_moverW`, `modNum_poly`), and the pieces
`polyTimeComputable_runW` (at `k / R`, `divNum_poly`), `polyTimeComputable_ansW` and
`polyTimeComputable_mainW`. -/
theorem polyTimeComputable_composePW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composePW ρ Fρ Fm fcall) := by
  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w)) true :=
    GI.msgCount_poly.comp' GI.argM_poly
  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
  have hdiv : PolyTimeComputable fun w =>
      List.replicate (GI.msgCount (GI.argM w) / ρ.rounds.eval (GI.argX w).length) true :=
    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
  have hmod : PolyTimeComputable fun w =>
      List.replicate (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length) true :=
    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
  have hmv : PolyTimeComputable fun w =>
      [moverIsV ρ.verifierFirst (GI.msgCount (GI.argM w) % ρ.rounds.eval (GI.argX w).length)] :=
    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
  have hrun := (polyTimeComputable_runW hFρ hcall H.main.P.coins ρ.P.coins ρ.rounds
    ρ.verifierFirst true).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.P.coins
    ρ.P.coins ρ.rounds H.calls G.outA ρ.verifierFirst true) hLR H.main.P.coins
  have hlead : PolyTimeComputable fun w =>
      [H.main.verifierFirst && decide (GI.msgCount (GI.argM w) =
      H.calls.eval (GI.argX w).length * ρ.rounds.eval (GI.argX w).length)] :=
    polyTimeComputable_and (polyTimeComputable_const [H.main.verifierFirst]) (eqTest_poly hk hLR)
  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
    (polyTimeComputable_ite hmv (polyTimeComputable_const []) hrun)
    (polyTimeComputable_ite hlead (polyTimeComputable_const []) hmain)).congr
    fun w => (H.composePW_eq ρ Fρ Fm fcall w).symm

/-- **`composeVW` is polynomial-time** when `Fρ`, `Fm` and `fcall` are.
`PolyTimeComputable (H.composeVW ρ Fρ Fm fcall)`.

**Proof sketch.** As `polyTimeComputable_composePW`, with the count `k − 1` (`unarySub_poly`),
two branches in the run phase and the drop count `L(n)·R(n) + lead` (`unaryAdd_poly`). -/
theorem polyTimeComputable_composeVW {Fρ Fm fcall : List Bool → List Bool}
    (hFρ : PolyTimeComputable Fρ) (hFm : PolyTimeComputable Fm)
    (hcall : PolyTimeComputable fcall) : PolyTimeComputable (H.composeVW ρ Fρ Fm fcall) := by
  have hk : PolyTimeComputable fun w => List.replicate (GI.msgCount (GI.argM w) - 1) true :=
    unarySub_poly (GI.msgCount_poly.comp' GI.argM_poly) (unaryConst_poly 1)
  have hR := unaryPoly_comp ρ.rounds GI.argX_poly
  have hLR := unaryMul_poly (unaryPoly_comp H.calls GI.argX_poly) hR
  have hdiv : PolyTimeComputable fun w =>
      List.replicate ((GI.msgCount (GI.argM w) - 1) / ρ.rounds.eval (GI.argX w).length) true :=
    (divNum_poly hk hR).congr fun w => by rw [divNum_eq]
  have hmod : PolyTimeComputable fun w =>
      List.replicate ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length) true :=
    (modNum_poly hk hR).congr fun w => by rw [modNum_eq]
  have hmv : PolyTimeComputable fun w =>
      [moverIsV ρ.verifierFirst
        ((GI.msgCount (GI.argM w) - 1) % ρ.rounds.eval (GI.argX w).length)] :=
    ((polyTimeComputable_moverW ρ.verifierFirst true).comp'
      (hmod.pairEncode polyTimeComputable_id)).congr fun w => by
        rw [moverW_eq, pairFstD_pairEncode, List.length_replicate, beq_true]
  have hrun := (polyTimeComputable_runW hFρ hcall H.main.V.coins ρ.V.coins ρ.rounds
    ρ.verifierFirst false).comp' (hdiv.pairEncode (hmod.pairEncode polyTimeComputable_id))
  have hmain := polyTimeComputable_mainW hFm (polyTimeComputable_ansW hFρ hcall H.main.V.coins
    ρ.V.coins ρ.rounds H.calls G.outB ρ.verifierFirst false)
    (unaryAdd_poly hLR (unaryConst_poly H.lead)) H.main.V.coins
  exact (polyTimeComputable_ite (ltTest_poly hk hLR)
    (polyTimeComputable_ite hmv hrun (polyTimeComputable_const [])) hmain).congr
    fun w => (H.composeVW_eq ρ Fρ Fm fcall w).symm

end Parties

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Lengths.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial bounds on the words of the hybrid-step templates

The templates of the reductions of the composition theorem [Gol04, §7.3.1, proof of
Theorem 7.3.3] hold the hybrid main phase, the other party's output in `main`, real views of
`ρ` and simulator outputs. Each has a length bounded by a polynomial in `n`, uniformly over the
inputs and coins:
* the encoded messages of the main phase on the ideal answers (`H.PolyTime` bounds `main`'s
  messages for any answers of the hybrid lengths) and the parties' outputs in `main` (efficient
  strategies on a polynomially long layout);
* the encoded views of `ρ` on inputs of `G`'s lengths (`G.PolyTime ρ`);
* the outputs of a machine on polynomially long arguments.

## Main results

* `HybridProtocol.exists_main_msgs_le`, `exists_main_outV_le`, `exists_main_outP_le`.
* `ComposeBound.exists_viewP_le`, `exists_viewV_le`, `exists_runAt_le`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (Definition 26.8) and §4.4 (time complexity of interactive machines).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography ComposeBound

/-- A list of length `c` is the encoding of a `c`-bit string. -/
private theorem exists_ofFn_eq {c : ℕ} {l : List Bool} (h : l.length = c) :
    ∃ t : Fin c → Bool, List.ofFn t = l := by
  subst h
  exact ⟨fun i => l[i.1], List.ofFn_getElem l⟩

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G)

/-- Alice's ideal answers have `calls(n) · G.outA(n)` bits.
`(H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n`. -/
theorem length_answersA (n : ℕ) (x y rA rB : List Bool) :
    (H.answersA n x y rA rB).length = H.calls.eval n * G.outA.eval n := by
  rw [answersA_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- Bob's ideal answers have `calls(n) · G.outB(n)` bits.
`(H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n`. -/
theorem length_answersB (n : ℕ) (x y rA rB : List Bool) :
    (H.answersB n x y rA rB).length = H.calls.eval n * G.outB.eval n := by
  rw [answersB_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- **The encoded main phase is polynomially long**: for some polynomial `E`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, both halves of the encoded transcript of
`main` on the ideal answers have at most `E(n)` bits.
`∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n (List.ofFn x)
(List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn
m.1) (List.ofFn m.2)) m).1).length ≤ E.eval n ∧ (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
(H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2).length ≤ E.eval n`.

**Proof sketch.** The ideal answers are strings of the hybrid lengths (`length_answersA`,
`length_answersB`), so `H.PolyTime` bounds every message by `B(n)`; each half of the transcript
has at most `rounds(n)` messages (`length_transcriptWith_fst_le`), so its encoding has at most
`E(n) = rounds(n) (2B(n) + 2)` bits (`length_encodeMsgs_le`). -/
theorem exists_main_msgs_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ E : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1).length ≤
          E.eval n ∧
        (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2).length ≤
          E.eval n := by
  obtain ⟨-, -, -, -, B, hB⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  refine ⟨.mul H.main.rounds (.add (.mul (.const 2) B) (.const 2)), fun n x y m => ?_⟩
  obtain ⟨aA, haA⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outA.eval n)
    (l := H.answersA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.length_answersA n _ _ _ _)
  obtain ⟨aB, haB⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outB.eval n)
    (l := H.answersB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.length_answersB n _ _ _ _)
  have hmsg := hB n x y aA aB m
  rw [haA, haB, ← privA_eq, ← privB_eq, Protocol.transcript_eq_transcriptWith] at hmsg
  rw [Protocol.transcript_eq_transcriptWith]
  have h₁ := length_transcriptWith_fst_le H.main H.main.P (List.replicate n true)
    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
  have h₂ := length_transcriptWith_snd_le H.main H.main.P (List.replicate n true)
    (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
    (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m
  have hR : H.main.rounds.eval (List.replicate n true).length = H.main.rounds.eval n := by
    rw [List.length_replicate]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
  exact ⟨(length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_left _ hw)).trans
      (Nat.mul_le_mul_right _ (h₁.trans hR.le)),
    (length_encodeMsgs_le _ (B.eval n) fun w hw => hmsg w (List.mem_append_right _ hw)).trans
      (Nat.mul_le_mul_right _ (h₂.trans hR.le))⟩

/-- **Bob's output in `main` is polynomially long**: for some polynomial `O`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, Bob's output in the hybrid execution has at
most `O(n)` bits.
`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (H.main.outV H.main.P (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn
m.1) (List.ofFn m.2)) (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
m).length ≤ O.eval n`.

**Proof sketch.** The output is `main.V.next` on `1^n`, Bob's private input, the messages he
received and his `main`-tape (`Protocol.outV_eq`), at most `C (|layout| + 1)^c` bits
(`Efficient.length_next_le`). The layout's length (`length_ilayout`) is linear in `n`, in his
private input's `2 F.inB(n) + 2 + calls(n) G.outB(n)` bits (`length_answersB`), in the encoded
messages (`exists_main_msgs_le`) and in his coin length; take `O = C (I + 1)^c` for that linear
bound `I`. -/
theorem exists_main_outV_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (H.main.outV H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
        O.eval n := by
  obtain ⟨-, hV, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hV
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  -- the layout: `1^n`, Bob's private input, the main phase and his `main`-tape
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
      (.add (.add (.mul (.const 2) .var) (.const 2))
        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
          (.add (.add (.mul (.const 2) F.inB) (.const 2)) (.mul H.calls G.outB)))) (.const 2)) E)))
      (.const 2))) (.const 2)) H.main.V.coins
  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
  have hI : (GI.ilayout (List.replicate n true)
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
      (H.main.transcriptWith H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).2
      (List.ofFn m.2)).length ≤ I.eval n := by
    have h₁ := (hE n x y m).2
    rw [Protocol.transcript_eq_transcriptWith] at h₁
    have hpB : (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
        2 * F.inB.eval n + 2 + H.calls.eval n * G.outB.eval n := by
      rw [privB_eq, length_pairEncode, H.length_answersB, List.length_ofFn]
    have hc : (List.ofFn m.2).length = H.main.V.coins.eval n := by
      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
    have hu : (List.replicate n true).length = n := List.length_replicate
    rw [length_ilayout, hpB, hc]
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  rw [Protocol.outV_eq]
  refine (hC _ _ _ _).trans ?_
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

/-- **Alice's output in `main` is polynomially long**: for some polynomial `O`, on common input
`1^n`, inputs of `F`'s lengths and any `main`-tapes, Alice's output in the hybrid execution has
at most `O(n)` bits.
`∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins
n), (H.main.outP (List.replicate n true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1)
(List.ofFn m.2)) (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
O.eval n`.

**Proof sketch.** As `exists_main_outV_le`, with `main.P.next` on her private input
(`length_answersA`), the messages she received and her `main`-tape (`Protocol.outP_eq`). -/
theorem exists_main_outP_le {F : Functionality} (hH : H.PolyTime F) :
    ∃ O : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (m : H.Coins n),
      (H.main.outP (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).length ≤
        O.eval n := by
  obtain ⟨hP, -, -, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨C, c, hC⟩ := Efficient.length_next_le hP
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.mul (.const 2)
      (.add (.add (.mul (.const 2) .var) (.const 2))
        (.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
          (.add (.add (.mul (.const 2) F.inA) (.const 2)) (.mul H.calls G.outA)))) (.const 2)) E)))
      (.const 2))) (.const 2)) H.main.P.coins
  refine ⟨.mul (.const C) (.pow (.add I (.const 1)) c), fun n x y m => ?_⟩
  have hI : (GI.ilayout (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
      (H.main.transcriptWith H.main.P (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)) m).1
      (List.ofFn m.1)).length ≤ I.eval n := by
    have h₁ := (hE n x y m).1
    rw [Protocol.transcript_eq_transcriptWith] at h₁
    have hpA : (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn m.1) (List.ofFn m.2)).length =
        2 * F.inA.eval n + 2 + H.calls.eval n * G.outA.eval n := by
      rw [privA_eq, length_pairEncode, H.length_answersA, List.length_ofFn]
    have hc : (List.ofFn m.1).length = H.main.P.coins.eval n := by
      rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
    have hu : (List.replicate n true).length = n := List.length_replicate
    rw [length_ilayout, hpA, hc]
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  rw [Protocol.outP_eq]
  refine (hC _ _ _ _).trans ?_
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

end HybridProtocol

namespace ComposeBound

/-- **Alice's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
`1^n` and inputs of `G`'s lengths, `|encode (viewP)| ≤ V(n)`.

**Proof sketch.** The encoded view is `⟨⟨1^n, x⟩, ⟨tape, encodeMsgs received⟩⟩` (`View.encode_mk`,
`length_pairEncode`): her tape has `ρ.P.coins(n)` bits, and she receives at most `rounds(n)`
messages (`length_transcriptWith_fst_le`) of at most `B(n)` bits each, `B` the bound of
`G.PolyTime ρ` (`length_encodeMsgs_le`); the sum is linear in these. -/
theorem exists_viewP_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
      (ρ.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
        V.eval n := by
  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inA))
      (.const 2)) (.add (.add (.mul (.const 2) ρ.P.coins) (.const 2))
        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
  have h₁ := length_transcriptWith_fst_le ρ ρ.P (List.replicate n true) (List.ofFn x)
    (List.ofFn y) t
  have hb := hB n x y t
  rw [Protocol.transcript_eq_transcriptWith] at hb
  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
    hb w (List.mem_append_left _ hw)).trans (Nat.mul_le_mul_right _ h₁)
  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
    rw [List.length_replicate]
  rw [hR] at h₂
  have hu : (List.replicate n true).length = n := List.length_replicate
  have hz : (List.ofFn x).length = G.inA.eval n := List.length_ofFn
  have ht : (List.ofFn t.1).length = ρ.P.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  rw [Protocol.viewP_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
    ht]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Bob's encoded `ρ`-views are polynomially long**: for some polynomial `V`, on common input
`1^n` and inputs of `G`'s lengths, `|encode (viewV)| ≤ V(n)`.

**Proof sketch.** As `exists_viewP_le`, with `ρ.V`'s tape and the messages he receives
(`length_transcriptWith_snd_le`). -/
theorem exists_viewV_le {G : Functionality} {ρ : Protocol} (hρ : G.PolyTime ρ) :
    ∃ V : PolyExpr, ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool)
      (t : ρ.ExecCoins ρ.P (List.replicate n true)),
      (ρ.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) t).encode.length ≤
        V.eval n := by
  obtain ⟨-, -, B, hB⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2)) G.inB))
      (.const 2)) (.add (.add (.mul (.const 2) ρ.V.coins) (.const 2))
        (.mul ρ.rounds (.add (.mul (.const 2) B) (.const 2)))), fun n x y t => ?_⟩
  have h₁ := length_transcriptWith_snd_le ρ ρ.P (List.replicate n true) (List.ofFn x)
    (List.ofFn y) t
  have hb := hB n x y t
  rw [Protocol.transcript_eq_transcriptWith] at hb
  have h₂ := (length_encodeMsgs_le _ (B.eval n) fun w hw =>
    hb w (List.mem_append_right _ hw)).trans (Nat.mul_le_mul_right _ h₁)
  have hR : ρ.rounds.eval (List.replicate n true).length = ρ.rounds.eval n := by
    rw [List.length_replicate]
  rw [hR] at h₂
  have hu : (List.replicate n true).length = n := List.length_replicate
  have hz : (List.ofFn y).length = G.inB.eval n := List.length_ofFn
  have ht : (List.ofFn t.2).length = ρ.V.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  rw [Protocol.viewV_eq, View.encode_mk, length_pairEncode, length_pairEncode, length_pairEncode,
    ht]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **A machine's outputs on polynomially long arguments are polynomially long**: for an `NUPPT`
`S` and a polynomial `k` there is a polynomial `O` with `|S.runAt n w s| ≤ O(n)` whenever
`|w| ≤ k(n)` (`length_runAt_le`, `NUPPT.advice_length`). -/
theorem exists_runAt_le (S : NUPPT) (k : PolyExpr) :
    ∃ O : PolyExpr, ∀ n (w : List Bool) (s : S.Coins n), w.length ≤ k.eval n →
      (S.runAt n w s).length ≤ O.eval n := by
  let I : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2)
    (.add (.add (.mul (.const 2) .var) (.const 2)) k)) (.const 2)) S.adv)) (.const 2)) S.coins
  refine ⟨.mul (.const S.Ct) (.pow (.add I (.const 1)) S.ct), fun n w s hw => ?_⟩
  refine (length_runAt_le S n w s).trans ?_
  have ha := S.advice_length n
  have hI : 2 * (2 * (2 * n + 2 + w.length) + 2 + (S.advice n).length) + 2 + S.coinLen n ≤
      I.eval n := by
    simp only [I, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
      NUPPT.coinLen_eq]
    omega
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  gcongr

end ComposeBound

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem: Alice's side

Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
Alice's real and ideal samples of `H.compose ρ`. On the `main`-tapes `m`, a run word `V j` per
call and the sample `sampleA m V` (the assembled view of `V`, her input, her `main`-tape and the
hybrid main phase, paired with Bob's output in `main`):
1. under `GoodRuns` the real sample is `sampleA m (real views)` (`realA_compose_sampleA`); the
   bad event has probability at most `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
2. the hybrid argument replaces the real views by `ρ`'s simulator, at most `ε₂(n)` per run
   (`exists_gapA`: the reduction `exists_gap_le` with a polynomially long template,
   `exists_tmplA_bound`; `abs_chain_le`);
3. `sampleA m (simulated views)` is `D ∘ Φ` on the hybrid real sample, and `D` on the simulator
   `S_A` is `D ∘ Φ` on the hybrid ideal sample (`acceptProb_realA_dPhi`, `acceptProb_post_pre`),
   so `H.HBCSecure F` bounds the rest (`exists_simA`).

## Main definitions

* `HybridProtocol.viewRunA`, `simRunA`: Alice's real and simulated run words.
* `HybridProtocol.sampleA`: Alice's sample from run words.

## Main results

* `HybridProtocol.realA_compose_sampleA`, `exists_tmplA_bound`, `exists_gapA`,
  `acceptProb_realA_dPhi`.
* `HybridProtocol.exists_simA`: Alice's side of `hbcSecure_compose`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1.
-/

namespace TCSlib.Cryptography.SecureComputation

open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
  ComposeBound

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Alice's real run word** for call `j`: her encoded view of `ρ` on the call inputs
`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
def viewRunA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
  (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
    (H.inB n ys (List.ofFn m.2) j) t).encode

/-- The defining equation of `viewRunA` (see `viewRunA`).
`H.viewRunA ρ n xs ys m j t = (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
theorem viewRunA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunA ρ n xs ys m j t =
      (ρ.viewP (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl

/-- **Alice's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on her call
input and her ideal answer `⟦f_A(callA_j, callB_j)⟧`, with coins `s`.
`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
def simRunA (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (s : S.Coins n) : List Bool :=
  S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s

/-- The defining equation of `simRunA` (see `simRunA`).
`H.simRunA S n xs ys m j s = S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1)) s`. -/
theorem simRunA_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
    H.simRunA S n xs ys m j s =
      S.runAt n (pairEncode (H.inA n xs (List.ofFn m.1) j)
        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).1))
        s := rfl

/-- **Alice's sample from run words**: the assembled view (`asmView` with `ρ.P`'s coins, Bob's
moves read, no leading filler) of the words `V`, her input `xs`, her `main`-tape and the hybrid
main phase on the ideal answers, paired with Bob's output in that hybrid execution.
`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn
m.2)) m).1) V) (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1)
(List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
def sampleA (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
  pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0 (List.replicate n true)
      xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
        (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
    (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)

/-- The defining equation of `sampleA` (see `sampleA`).
`H.sampleA ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
(List.replicate n true) xs (List.ofFn m.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n
true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn
m.2)) m).1) V) (H.main.outV H.main.P (List.replicate n true) (H.privA n xs ys (List.ofFn m.1)
(List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
theorem sampleA_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
    H.sampleA ρ n xs ys m V =
      pairEncode (asmView H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
          (List.replicate n true) xs (List.ofFn m.1)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).1) V)
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl

/-- **The real sample under `GoodRuns`** (step 2):
`F.realA (H.compose ρ) n x y (composeCoins (m, t)) = sampleA m (j ↦ viewRunA m j (t j))`
(`realA_compose_eq`, `realViewA_eq`). -/
theorem realA_compose_sampleA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realA (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      H.sampleA ρ n (List.ofFn x) (List.ofFn y) m fun j =>
        if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
          (t ⟨j, h⟩) else [] := by
  have hV : H.realViewA ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
      if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
        (t ⟨j, h⟩) else [] :=
    funext fun j => by rw [realViewA_eq]; rfl
  rw [H.realA_compose_eq ρ hM n x y m t hg, hV, sampleA_eq]

/-- **The templates of Alice's hybrid steps are polynomially long**: for some polynomial `q`, for
all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
`⟨⟨1^n, ⟦x⟧⟩, ⟨⟦m.1⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
Bob's output in `main` has at most `q(n)` bits.
`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
S.Coins n)), (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn x)) (pairEncode
(List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n
(List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n (List.ofFn x) (List.ofFn
y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1))) ((List.range i).map (hybV (H.viewRunA ρ n
(List.ofFn x) (List.ofFn y)) (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a)) ((List.range
(H.calls.eval n - (i + 1))).map fun k => hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
(H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)) (H.main.outV H.main.P (List.replicate n
true) (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n
(List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤ q.eval n`.

**Proof sketch.** The main phase and Bob's output are polynomially long (`exists_main_msgs_le`,
`exists_main_outV_le`); every run word is a real view (`exists_viewP_le`), a simulator output on
an argument of `2 G.inA(n) + 2 + G.outA(n)` bits (`exists_runAt_le`) or empty; at most `L(n)` of
them are encoded (`length_encodeMsgs_le`); the rest is `length_pairEncode`. -/
theorem exists_tmplA_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
    (S : NUPPT) :
    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
        ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
          (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))
        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
          hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
        q.eval n := by
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  obtain ⟨O, hO⟩ := H.exists_main_outV_le hH
  obtain ⟨V, hV⟩ := exists_viewP_le hρ
  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inA) (.const 2)) G.outA)
  -- every run word has at most `V(n) + Sv(n)` bits
  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (j : ℕ),
      (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
    intro n x y i a j
    rw [hybV_eq]
    split_ifs with h₁ h₂
    · rw [simRunA_eq]
      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
      rw [length_pairEncode, inA_val, List.length_ofFn, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
    · rw [viewRunA_eq, inA_val, inB_val]
      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
    · exact Nat.zero_le _
  -- the encoded word lists
  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
      (Strategy.encodeMsgs (l.map (hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
      fun n x y i a l hl => ?_⟩
    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
      exact hw n x y i a j
    · rw [List.length_map]
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.mul_le_mul_right _ hl
  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
    F.inA)) (.const 2)) (.add (.add (.mul (.const 2) H.main.P.coins) (.const 2)) E)
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
      hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
      (by rw [List.length_map, List.length_range]; omega)
    rwa [List.map_map] at h
  have h₃ := (hE n x y a.1).1
  have h₄ := hO n x y a.1
  have hc : (List.ofFn a.1.1).length = H.main.P.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  have hu : (List.replicate n true).length = n := List.length_replicate
  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Alice's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT
`D` there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
`|Pr_t[D(sampleA a.1 (plugV i a (viewRunA a.1 i t)))] −
Pr_s[D(sampleA a.1 (plugV i a (simRunA a.1 i s)))]| ≤ ε₂(n)`.

**Proof sketch.** `exists_gap_le` with `ρ`'s Alice-side samplers, the instances
`(x, y, i, a)`, the call inputs of `a.1` at `i`, and the template of `exists_tmplA_bound`. The
filled template is the sample: `asmW_pairEncode`, `msgAt_encodeMsgs` and `getD_plug` turn it into
`asmView` of `plugV`, and the first component of `ρ`'s real (ideal) sample is the real
(simulated) run word (`Functionality.realA_eq`, `idealA_eq`, `inA_val`, `inB_val`). -/
theorem exists_gapA {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realA ρ n x y) (G.idealA S n x y) (D.distinguisherL n) ≤ ε n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      |acceptProb (fun t => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
            (H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
        acceptProb (fun s => H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a
            (H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
        ε₂ n := by
  obtain ⟨q, hq⟩ := H.exists_tmplA_bound ρ hH hρ S
  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
    (Sc := fun n => S.Coins n) (fun n => G.realA ρ n) (fun n => G.idealA S n) hS H.calls
    ρ.rounds ρ.P.coins ρ.verifierFirst true 0
    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
      Fin (H.calls.eval n) ×
      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.1))
      (pairEncode (List.ofFn θ.2.2.2.1.1) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true)
        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2))
        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).1)))
    (fun n θ => H.main.outV H.main.P (List.replicate n true)
      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2))
      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
      (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
      hybV (H.viewRunA ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
        (H.simRunA S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
  -- the filled template is the sample with run `i` replaced
  have hfill : ∀ v : List Bool, H.sampleA ρ n (List.ofFn x) (List.ofFn y) a.1
      (plugV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a v) =
      pairEncode (asmW H.calls ρ.rounds ρ.P.coins ρ.verifierFirst true 0
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn x))
          (pairEncode (List.ofFn a.1.1) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).1)))
          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunA ρ n (List.ofFn x)
            (List.ofFn y)) (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a) ++
            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
              hybV (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
                (H.simRunA S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
    intro v
    rw [sampleA_eq, asmW_pairEncode]
    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
    rw [List.length_replicate] at hj
    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
  have hreal : ∀ t, H.viewRunA ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
      pairFstD (G.realA ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
    rw [Functionality.realA_eq, pairFstD_pairEncode, viewRunA_eq, inA_val, inB_val]
  have hsim : ∀ s, H.simRunA S n (List.ofFn x) (List.ofFn y) a.1 i s =
      pairFstD (G.idealA S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
    rw [Functionality.idealA_eq, pairFstD_pairEncode, simRunA_eq, inA_val]
  simp only [hfill, hreal, hsim]
  exact h n (x, y, i, a)

/-- **The simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
reduction of `exists_dPhi` (coins `calls · S.coins + D.coins`), then
`Pr[DΦ(H.realA F n x y)] = Pr_{(m, s)}[D(sampleA m (j ↦ simRunA m j (s j)))]`.

**Proof sketch.** Unfold `DΦ` (`acceptProb_pre`) and read its extra coins as one block of
`S.coins(n)` bits per call (`blocksCoins`). On `H.realA`, `phiD` keeps Bob's output and applies
`phiV` to Alice's view of `main`, whose private input is `⟨⟦x⟧, answers⟩` (`phiD_pairEncode`,
`phiV_view`): run `j` is `S`'s output on the call input (`hcall`, `inA_val`), the `j`-th
answer block (`coinBlock_flatten`) and the `j`-th coin block (`coinBlock_blocksCoins`), i.e.
`simRunA` (`NUPPT.runAtL_eq_output_layout`). -/
theorem acceptProb_realA_dPhi {F : Functionality} (S D DΦ : NUPPT) {fA : List Bool → List Bool}
    (hcall : ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
      fA (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callA n x r j))
    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
    (hD : ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    acceptProb (H.realA F n x y) (DΦ.distinguisherL n) =
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunA S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
  rw [acceptProb_pre (H.realA F n x y) DΦ D (.mul H.calls S.coins) n
    (fun w e => phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
    (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  show phiD S fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
        (pairEncode (H.realA F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
  rw [realA_eq, phiD_pairEncode, Protocol.viewP_eq, View.encode_mk, privA_eq, phiV_view,
    sampleA_eq, privA_eq, Protocol.transcript_eq_transcriptWith]
  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
  rw [List.length_replicate] at hj
  rw [dif_pos hj, simRunA_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
    hcall n (List.ofFn x) (List.ofFn z.1.1) ⟨j, hj⟩, inA_val, ← NUPPT.coinLen_eq,
    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersA_eq,
    coinBlock_flatten _ (fun c hc' => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]

/-- **Alice's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there
is a non-uniform PPT `S_A` such that every non-uniform PPT `D` has a negligible `ε` with
`distAdv (F.realA (H.compose ρ) n x y) (F.idealA S_A n x y) D ≤ ε(n)` for all `n`, `x`, `y`.

**Proof sketch.** `S_A` post-processes the hybrid simulator by `Φ` (`exists_simulator`). For `D`:
1. relabel the coins (`composeCoins`); the real sample is `sampleA` of the real views except
   on `¬ GoodRuns` (`realA_compose_sampleA`, `distAdv_le_uprob_of_eq`), of probability at most
   `L(n) ε_c(n)` (`uprob_not_goodRuns_le`, `exists_correct`);
2. the real and simulated views are within `L(n) ε₂(n)` (`abs_chain_le`, `exists_gapA`);
3. `D` on the simulated views is `DΦ` on `H.realA` (`acceptProb_realA_dPhi`), and `D` on
   `S_A` is `DΦ` on `S_A^H` (`acceptProb_post_pre`, `phiD_pairEncode`), so `H.HBCSecure F`
   bounds this distance by `ε₃(n)`.
The total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` is negligible (`negligible_polyExpr_mul`). -/
theorem exists_simA {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
    ∃ SA : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        distAdv (F.realA (H.compose ρ) n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n := by
  obtain ⟨hHpt, SH, SHB, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
  obtain ⟨-, -, ⟨fA, hfA, hcallA⟩, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
  obtain ⟨SA, hSAc, hSA⟩ := exists_simulator SρA H.calls ρ.rounds ρ.P.coins G.outA
    ρ.verifierFirst true 0 SH hfA
  refine ⟨SA, fun D => ?_⟩
  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapA ρ hHpt hρpt SρA (fun D => by
    obtain ⟨ε, hε, h⟩ := hρs D
    exact ⟨ε, hε, fun n x y => (h n x y).1⟩) D
  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst
    true 0 D hfA
  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
    fun n x y => ?_⟩
  -- step 1: the statistical switch
  have s1 : |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realA (H.compose ρ) n x y)]
    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
      (fun z hz => H.realA_compose_sampleA ρ hM n x y z.1 z.2 (not_not.1 hz))
    rw [distAdv_def] at h
    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
  -- step 2: the hybrid argument over the runs
  have s2 := abs_chain_le (H.viewRunA ρ n (List.ofFn x) (List.ofFn y))
    (H.simRunA SρA n (List.ofFn x) (List.ofFn y)) (H.sampleA ρ n (List.ofFn x) (List.ofFn y))
    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
  -- step 3: the hybrid model
  have hid : ∀ S : NUPPT, F.idealA S n x y = fun s =>
      pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
        (List.ofFn (F.f n x y).2) := fun S => funext (Functionality.idealA_eq F S n x y)
  have e3 : acceptProb (F.idealA SA n x y) (D.distinguisherL n) =
      acceptProb (F.idealA SH n x y) (DΦ.distinguisherL n) := by
    rw [hid SA, hid SH]
    exact acceptProb_post_pre SA SH DΦ D (.mul H.calls SρA.coins) n
      (fun hv e => phiV SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode hv e)))
      (fun w e => phiD SρA fA H.calls ρ.rounds ρ.P.coins G.outA ρ.verifierFirst true 0
        (pairEncode (pairEncode (List.replicate n true) (SρA.advice n)) (pairEncode w e)))
      (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) (List.ofFn (F.f n x y).2) hSAc
      (hSA n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
        H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
      acceptProb (F.idealA SA n x y) (D.distinguisherL n)| ≤ ε₃ n := by
    rw [← H.acceptProb_realA_dPhi ρ SρA D DΦ hcallA hDΦc hDΦ n x y, e3]
    have h := (h₃ n x y).1
    rwa [distAdv_def] at h
  rw [distAdv_def]
  calc |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
        acceptProb (F.idealA SA n x y) (D.distinguisherL n)|
      ≤ |acceptProb (F.realA (H.compose ρ) n x y) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunA ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρA.Coins n) =>
            H.sampleA ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunA SρA n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (F.idealA SA n x y) (D.distinguisherL n)| :=
        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
    _ ≤ _ := add_le_add (add_le_add s1 s2) s3

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/SideB.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem: Bob's side

Steps 1–5 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3] for
Bob's real and ideal samples of `H.compose ρ`, as for Alice's (`ComposeSecurity/SideA.lean`). On
the `main`-tapes `m`, a run word `V j` per call and the sample `sampleB m V` (the assembled view of
`V`, his input, his `main`-tape, the leading fillers and the hybrid main phase, paired with
Alice's output in `main`):
1. under `GoodRuns` the real sample is `sampleB m (real views)` (`realB_compose_sampleB`);
2. the hybrid argument replaces his real views by `ρ`'s simulator (`exists_gapB`,
   `exists_tmplB_bound`, `abs_chain_le`);
3. `sampleB m (simulated views)` is `D ∘ Φ` on the hybrid real sample (`acceptProb_realB_dPhi`),
   and `H.HBCSecure F` bounds the rest (`exists_simB`).

## Main definitions

* `HybridProtocol.viewRunB`, `simRunB`: Bob's real and simulated run words.
* `HybridProtocol.sampleB`: Bob's sample from run words.

## Main results

* `HybridProtocol.realB_compose_sampleB`, `exists_tmplB_bound`, `exists_gapB`,
  `acceptProb_realB_dPhi`.
* `HybridProtocol.exists_simB`: Bob's side of `hbcSecure_compose`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1.
-/

namespace TCSlib.Cryptography.SecureComputation

open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
  ComposeBound

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **Bob's real run word** for call `j`: his encoded view of `ρ` on the call inputs
`inA n xs ⟦m.1⟧ j`, `inB n ys ⟦m.2⟧ j` and the tapes `t`.
`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
def viewRunB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) : List Bool :=
  (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
    (H.inB n ys (List.ofFn m.2) j) t).encode

/-- The defining equation of `viewRunB` (see `viewRunB`).
`H.viewRunB ρ n xs ys m j t = (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j) (H.inB
n ys (List.ofFn m.2) j) t).encode`. -/
theorem viewRunB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (t : ρ.ExecCoins ρ.P (List.replicate n true)) :
    H.viewRunB ρ n xs ys m j t =
      (ρ.viewV (List.replicate n true) (H.inA n xs (List.ofFn m.1) j)
        (H.inB n ys (List.ofFn m.2) j) t).encode := rfl

/-- **Bob's simulated run word** for call `j`: the output of `ρ`'s simulator `S` on his call
input and his ideal answer `⟦f_B(callA_j, callB_j)⟧`, with coins `s`.
`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
def simRunB (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (j : Fin (H.calls.eval n))
    (s : S.Coins n) : List Bool :=
  S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
    (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s

/-- The defining equation of `simRunB` (see `simRunB`).
`H.simRunB S n xs ys m j s = S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j) (List.ofFn (G.f n
(H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2)) s`. -/
theorem simRunB_eq (S : NUPPT) (n : ℕ) (xs ys : List Bool) (m : H.Coins n)
    (j : Fin (H.calls.eval n)) (s : S.Coins n) :
    H.simRunB S n xs ys m j s =
      S.runAt n (pairEncode (H.inB n ys (List.ofFn m.2) j)
        (List.ofFn (G.f n (H.callA n xs (List.ofFn m.1) j) (H.callB n ys (List.ofFn m.2) j)).2))
        s := rfl

/-- **Bob's sample from run words**: the assembled view (`asmView` with `ρ.V`'s coins, Alice's
moves read, `lead` leading fillers) of the words `V`, his input `ys`, his `main`-tape and the
hybrid main phase on the ideal answers, paired with Alice's output in that hybrid execution.
`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys
(List.ofFn m.1) (List.ofFn m.2)) m).2) V) (H.main.outP (List.replicate n true) (H.privA n xs ys
(List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
def sampleB (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) : List Bool :=
  pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
      (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
        (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
    (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
      (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)

/-- The defining equation of `sampleB` (see `sampleB`).
`H.sampleB ρ n xs ys m V = pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false
H.lead (List.replicate n true) ys (List.ofFn m.2) (Strategy.encodeMsgs (H.main.transcript
(List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys
(List.ofFn m.1) (List.ofFn m.2)) m).2) V) (H.main.outP (List.replicate n true) (H.privA n xs ys
(List.ofFn m.1) (List.ofFn m.2)) (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m)`. -/
theorem sampleB_eq (n : ℕ) (xs ys : List Bool) (m : H.Coins n) (V : ℕ → List Bool) :
    H.sampleB ρ n xs ys m V =
      pairEncode (asmView H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
          (List.replicate n true) ys (List.ofFn m.2)
          (Strategy.encodeMsgs (H.main.transcript (List.replicate n true)
            (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
            (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m).2) V)
        (H.main.outP (List.replicate n true) (H.privA n xs ys (List.ofFn m.1) (List.ofFn m.2))
          (H.privB n xs ys (List.ofFn m.1) (List.ofFn m.2)) m) := rfl

/-- **Bob's real sample under `GoodRuns`** (step 2): `F.realB (H.compose ρ) n x y (composeCoins
(m, t)) = sampleB m (j ↦ viewRunB m j (t j))` (`realB_compose_eq`, `realViewB_eq`). -/
theorem realB_compose_sampleB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (m : H.Coins n)
    (t : Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true))
    (hg : H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) m t) :
    F.realB (H.compose ρ) n x y (H.composeCoins ρ n (m, t)) =
      H.sampleB ρ n (List.ofFn x) (List.ofFn y) m fun j =>
        if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
          (t ⟨j, h⟩) else [] := by
  have hV : H.realViewB ρ n (List.ofFn x) (List.ofFn y) m t = fun j =>
      if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) m ⟨j, h⟩
        (t ⟨j, h⟩) else [] :=
    funext fun j => by rw [realViewB_eq]; rfl
  rw [H.realB_compose_eq ρ hM n x y m t hg, hV, sampleB_eq]

/-- **The templates of Bob's hybrid steps are polynomially long**: for some polynomial `q`, for
all inputs, run indices `i` and coordinates `a`, the template (`ComposeSim.tmplW`) of the header
`⟨⟨1^n, ⟦y⟧⟩, ⟨⟦m.2⟧, main phase⟩⟩`, the run words of hybrid `i` before and after run `i`, and
Alice's output in `main` has at most `q(n)` bits.
`∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : Fin
(H.calls.eval n)) (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
S.Coins n)), (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn y)) (pairEncode
(List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript (List.replicate n true) (H.privA n
(List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n (List.ofFn x) (List.ofFn
y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2))) ((List.range i).map (hybV (H.viewRunB ρ n
(List.ofFn x) (List.ofFn y)) (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a)) ((List.range
(H.calls.eval n - (i + 1))).map fun k => hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
(H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)) (H.main.outP (List.replicate n true)
(H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) (H.privB n (List.ofFn x)
(List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤ q.eval n`.

**Proof sketch.** As `exists_tmplA_bound`, with Bob's half of the main phase
(`exists_main_msgs_le`), Alice's output (`exists_main_outP_le`), Bob's views (`exists_viewV_le`)
and simulator outputs on arguments of `2 G.inB(n) + 2 + G.outB(n)` bits (`exists_runAt_le`). -/
theorem exists_tmplB_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ)
    (S : NUPPT) :
    ∃ q : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      (tmplW (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
        ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
          (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))
        ((List.range (H.calls.eval n - (i + 1))).map fun k =>
          hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1)).length ≤
        q.eval n := by
  obtain ⟨E, hE⟩ := H.exists_main_msgs_le hH
  obtain ⟨O, hO⟩ := H.exists_main_outP_le hH
  obtain ⟨V, hV⟩ := exists_viewV_le hρ
  obtain ⟨Sv, hSv⟩ := exists_runAt_le S (.add (.add (.mul (.const 2) G.inB) (.const 2)) G.outB)
  -- every run word has at most `V(n) + Sv(n)` bits
  have hw : ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (j : ℕ),
      (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a j).length ≤ V.eval n + Sv.eval n := by
    intro n x y i a j
    rw [hybV_eq]
    split_ifs with h₁ h₂
    · rw [simRunB_eq]
      refine (hSv n _ _ ?_).trans (Nat.le_add_left _ _)
      rw [length_pairEncode, inB_val, List.length_ofFn, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, le_refl]
    · rw [viewRunB_eq, inA_val, inB_val]
      exact (hV n _ _ _).trans (Nat.le_add_right _ _)
    · exact Nat.zero_le _
  -- the encoded word lists
  obtain ⟨P, hP⟩ : ∃ P : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : ℕ)
      (a : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) ×
        S.Coins n)) (l : List ℕ), l.length ≤ H.calls.eval n →
      (Strategy.encodeMsgs (l.map (hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a))).length ≤ P.eval n := by
    refine ⟨.mul H.calls (.add (.mul (.const 2) (.add V Sv)) (.const 2)),
      fun n x y i a l hl => ?_⟩
    refine (length_encodeMsgs_le _ (V.eval n + Sv.eval n) fun w hw' => ?_).trans ?_
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw'
      exact hw n x y i a j
    · rw [List.length_map]
      simp only [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.mul_le_mul_right _ hl
  let Hd : PolyExpr := .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) .var) (.const 2))
    F.inB)) (.const 2)) (.add (.add (.mul (.const 2) H.main.V.coins) (.const 2)) E)
  refine ⟨.add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) Hd) (.const 2)) P))
    (.const 2)) (.add (.add (.mul (.const 2) P) (.const 2)) O), fun n x y i a => ?_⟩
  have h₁ := hP n x y i a (List.range i) (by rw [List.length_range]; exact i.2.le)
  have h₂ : (Strategy.encodeMsgs ((List.range (H.calls.eval n - (i + 1))).map fun k =>
      hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k))).length ≤ P.eval n := by
    have h := hP n x y i a ((List.range (H.calls.eval n - (i + 1))).map fun k => i + 1 + k)
      (by rw [List.length_map, List.length_range]; omega)
    rwa [List.map_map] at h
  have h₃ := (hE n x y a.1).2
  have h₄ := hO n x y a.1
  have hc : (List.ofFn a.1.2).length = H.main.V.coins.eval n := by
    rw [List.length_ofFn, Strategy.coinLen_eq, List.length_replicate]
  have hu : (List.replicate n true).length = n := List.length_replicate
  rw [tmplW_eq, length_pairEncode, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, length_pairEncode, hc, List.length_ofFn]
  simp only [Hd, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Bob's hybrid steps are bounded by `ρ`'s security** (step 3): for every non-uniform PPT `D`
there is a negligible `ε₂` with, for all `n`, inputs, run indices `i` and coordinates `a`,
`|Pr_t[D(sampleB a.1 (plugV i a (viewRunB a.1 i t)))] −
Pr_s[D(sampleB a.1 (plugV i a (simRunB a.1 i s)))]| ≤ ε₂(n)`.

**Proof sketch.** As `exists_gapA`: `exists_gap_le` with `ρ`'s Bob-side samplers and the
template of `exists_tmplB_bound`; the first component of `ρ`'s real (ideal) Bob sample is the
real (simulated) run word (`Functionality.realB_eq`, `idealB_eq`, `inA_val`, `inB_val`). -/
theorem exists_gapB {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) (S : NUPPT)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (G.realB ρ n x y) (G.idealB S n x y) (D.distinguisherL n) ≤ ε n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (x : Fin (F.inA.eval n) → Bool)
      (y : Fin (F.inB.eval n) → Bool) (i : Fin (H.calls.eval n))
      (a : H.Coins n ×
        (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)),
      |acceptProb (fun t => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
            (H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t))) (D.distinguisherL n) -
        acceptProb (fun s => H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
          (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
            (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a
            (H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s))) (D.distinguisherL n)| ≤
        ε₂ n := by
  obtain ⟨q, hq⟩ := H.exists_tmplB_bound ρ hH hρ S
  obtain ⟨ε₂, hε₂, h⟩ := exists_gap_le (T := fun n => ρ.ExecCoins ρ.P (List.replicate n true))
    (Sc := fun n => S.Coins n) (fun n => G.realB ρ n) (fun n => G.idealB S n) hS H.calls
    ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
    (Θ := fun n => (Fin (F.inA.eval n) → Bool) × (Fin (F.inB.eval n) → Bool) ×
      Fin (H.calls.eval n) ×
      (H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true) × S.Coins n)))
    (fun n θ => H.callA n (List.ofFn θ.1) (List.ofFn θ.2.2.2.1.1) θ.2.2.1)
    (fun n θ => H.callB n (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.2) θ.2.2.1)
    (fun n θ => pairEncode (pairEncode (List.replicate n true) (List.ofFn θ.2.1))
      (pairEncode (List.ofFn θ.2.2.2.1.2) (Strategy.encodeMsgs (H.main.transcript
        (List.replicate n true)
        (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2))
        (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
          (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1).2)))
    (fun n θ => H.main.outP (List.replicate n true)
      (H.privA n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2))
      (H.privB n (List.ofFn θ.1) (List.ofFn θ.2.1) (List.ofFn θ.2.2.2.1.1)
        (List.ofFn θ.2.2.2.1.2)) θ.2.2.2.1)
    (fun n θ => (List.range θ.2.2.1).map (hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
      (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2))
    (fun n θ => (List.range (H.calls.eval n - (θ.2.2.1 + 1))).map fun k =>
      hybV (H.viewRunB ρ n (List.ofFn θ.1) (List.ofFn θ.2.1))
        (H.simRunB S n (List.ofFn θ.1) (List.ofFn θ.2.1)) θ.2.2.1 θ.2.2.2 (θ.2.2.1 + 1 + k))
    q (fun n θ => hq n θ.1 θ.2.1 θ.2.2.1 θ.2.2.2) D
  refine ⟨ε₂, hε₂, fun n x y i a => ?_⟩
  -- the filled template is the sample with run `i` replaced
  have hfill : ∀ v : List Bool, H.sampleB ρ n (List.ofFn x) (List.ofFn y) a.1
      (plugV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
        (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a v) =
      pairEncode (asmW H.calls ρ.rounds ρ.V.coins ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn y))
          (pairEncode (List.ofFn a.1.2) (Strategy.encodeMsgs (H.main.transcript
            (List.replicate n true)
            (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
            (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1).2)))
          (Strategy.encodeMsgs ((List.range i).map (hybV (H.viewRunB ρ n (List.ofFn x)
            (List.ofFn y)) (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a) ++
            v :: (List.range (H.calls.eval n - (i + 1))).map fun k =>
              hybV (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
                (H.simRunB S n (List.ofFn x) (List.ofFn y)) i a (i + 1 + k)))))
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn a.1.1) (List.ofFn a.1.2)) a.1) := by
    intro v
    rw [sampleB_eq, asmW_pairEncode]
    refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
    rw [List.length_replicate] at hj
    rw [msgAt_encodeMsgs, getD_plug _ _ i.2 hj, plugV_eq]
  have hreal : ∀ t, H.viewRunB ρ n (List.ofFn x) (List.ofFn y) a.1 i t =
      pairFstD (G.realB ρ n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) t) := fun t => by
    rw [Functionality.realB_eq, pairFstD_pairEncode, viewRunB_eq, inA_val, inB_val]
  have hsim : ∀ s, H.simRunB S n (List.ofFn x) (List.ofFn y) a.1 i s =
      pairFstD (G.idealB S n (H.callA n (List.ofFn x) (List.ofFn a.1.1) i)
        (H.callB n (List.ofFn y) (List.ofFn a.1.2) i) s) := fun s => by
    rw [Functionality.idealB_eq, pairFstD_pairEncode, simRunB_eq, inB_val]
  simp only [hfill, hreal, hsim]
  exact h n (x, y, i, a)

/-- **Bob's simulated sample is `D ∘ Φ` on the hybrid real sample** (step 4): if `DΦ` is the
reduction of `exists_dPhi` for Bob's post-processing (coins `calls · S.coins + D.coins`), then
`Pr[DΦ(H.realB F n x y)] = Pr_{(m, s)}[D(sampleB m (j ↦ simRunB m j (s j)))]`.

**Proof sketch.** As `acceptProb_realA_dPhi`, with Bob's view of `main`, whose private input is
`⟨⟦y⟧, answers⟩`, his call inputs (`hcall`, `inB_val`) and his answer blocks. -/
theorem acceptProb_realB_dPhi {F : Functionality} (S D DΦ : NUPPT) {fB : List Bool → List Bool}
    (hcall : ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
      fB (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
        (List.replicate j true)))) = List.ofFn (H.callB n y r j))
    (hc : DΦ.coins = .add (.mul H.calls S.coins) D.coins)
    (hD : ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (S.advice n))
          (pairEncode y (r.take ((PolyExpr.mul H.calls S.coins).eval n)))))
        (r.drop ((PolyExpr.mul H.calls S.coins).eval n)))
    (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    acceptProb (H.realB F n x y) (DΦ.distinguisherL n) =
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → S.Coins n) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunB S n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) := by
  have hlen : (PolyExpr.mul H.calls S.coins).eval n = H.calls.eval n * S.coinLen n := by
    rw [PolyExpr.eval_mul, NUPPT.coinLen_eq]
  rw [acceptProb_pre (H.realB F n x y) DΦ D (.mul H.calls S.coins) n
    (fun w e => phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
      (pairEncode (pairEncode (List.replicate n true) (S.advice n)) (pairEncode w e))) hc (hD n)]
  refine (acceptProb_comp_equiv ((Equiv.refl (H.Coins n)).prodCongr (blocksCoins hlen)) _
    (D.distinguisherL n)).symm.trans ?_
  refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
  show phiD S fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
      (pairEncode (pairEncode (List.replicate n true) (S.advice n))
        (pairEncode (H.realB F n x y z.1) (List.ofFn (blocksCoins hlen z.2)))) = _
  rw [realB_eq, phiD_pairEncode, Protocol.viewV_eq, View.encode_mk, privB_eq, phiV_view,
    sampleB_eq, privB_eq, Protocol.transcript_eq_transcriptWith]
  refine congrArg (fun w => pairEncode w _) (asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_)
  rw [List.length_replicate] at hj
  rw [dif_pos hj, simRunB_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout,
    hcall n (List.ofFn y) (List.ofFn z.1.2) ⟨j, hj⟩, inB_val, ← NUPPT.coinLen_eq,
    coinBlock_blocksCoins hlen z.2 ⟨j, hj⟩, answersB_eq,
    coinBlock_flatten _ (fun c hc' => by
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.1 hc'
      exact List.length_ofFn) j (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]

/-- **Bob's side of the composition theorem**: from `H.HBCSecure F` and `HBCSecure ρ G`, there is
a non-uniform PPT `S_B` such that every non-uniform PPT `D` has a negligible `ε` with
`distAdv (F.realB (H.compose ρ) n x y) (F.idealB S_B n x y) D ≤ ε(n)` for all `n`, `x`, `y`.

**Proof sketch.** As `exists_simA`, with Bob's simulator post-processed by Bob's `Φ`
(`exists_simulator` with `ρ.V`'s coins, Alice's moves read and `lead` fillers), his real sample
(`realB_compose_sampleB`), the same bad event, the hybrid argument over his views
(`exists_gapB`, `abs_chain_le`) and the hybrid model (`acceptProb_realB_dPhi`,
`acceptProb_post_pre`). -/
theorem exists_simB {F : Functionality} (hM : ∀ n, 0 < H.main.rounds.eval n)
    (hH : H.HBCSecure F) (hρ : SecureComputation.HBCSecure ρ G) :
    ∃ SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
        distAdv (F.realB (H.compose ρ) n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  obtain ⟨hHpt, SHA, SH, hHs⟩ := (HybridProtocol.hbcSecure_iff H F).mp hH
  obtain ⟨hρpt, SρA, SρB, hρs⟩ := (SecureComputation.hbcSecure_iff ρ G).mp hρ
  obtain ⟨-, -, -, ⟨fB, hfB, hcallB⟩, -⟩ := (HybridProtocol.polyTime_iff H F).mp hHpt
  obtain ⟨SB, hSBc, hSB⟩ := exists_simulator SρB H.calls ρ.rounds ρ.V.coins G.outB
    ρ.verifierFirst false H.lead SH hfB
  refine ⟨SB, fun D => ?_⟩
  obtain ⟨εc, hεc, hc⟩ := exists_correct SρA SρB hρs
  obtain ⟨ε₂, hε₂, h₂⟩ := H.exists_gapB ρ hHpt hρpt SρB (fun D => by
    obtain ⟨ε, hε, h⟩ := hρs D
    exact ⟨ε, hε, fun n x y => (h n x y).2⟩) D
  obtain ⟨DΦ, hDΦc, hDΦ⟩ := exists_dPhi SρB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst
    false H.lead D hfB
  obtain ⟨ε₃, hε₃, h₃⟩ := hHs DΦ
  refine ⟨fun n => (H.calls.eval n : ℝ) * εc n + (H.calls.eval n : ℝ) * ε₂ n + ε₃ n,
    ((negligible_polyExpr_mul hεc H.calls).add (negligible_polyExpr_mul hε₂ H.calls)).add hε₃,
    fun n x y => ?_⟩
  -- step 1: the statistical switch
  have s1 : |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
      acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
          ρ.ExecCoins ρ.P (List.replicate n true)) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1 ⟨j, h⟩
            (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| ≤ H.calls.eval n * εc n := by
    rw [← acceptProb_comp_equiv (H.composeCoins ρ n) (F.realB (H.compose ρ) n x y)]
    have h := distAdv_le_uprob_of_eq _ _ (D.distinguisherL n)
      (fun z : H.Coins n × (Fin (H.calls.eval n) → ρ.ExecCoins ρ.P (List.replicate n true)) =>
        ¬ H.GoodRuns ρ n (List.ofFn x) (List.ofFn y) z.1 z.2)
      (fun z hz => H.realB_compose_sampleB ρ hM n x y z.1 z.2 (not_not.1 hz))
    rw [distAdv_def] at h
    exact h.trans (H.uprob_not_goodRuns_le ρ n _ _ (εc n) (hc n))
  -- step 2: the hybrid argument over the runs
  have s2 := abs_chain_le (H.viewRunB ρ n (List.ofFn x) (List.ofFn y))
    (H.simRunB SρB n (List.ofFn x) (List.ofFn y)) (H.sampleB ρ n (List.ofFn x) (List.ofFn y))
    (D.distinguisherL n) (ε₂ n) (fun i a => h₂ n x y i a)
  -- step 3: the hybrid model
  have hid : ∀ S : NUPPT, F.idealB S n x y = fun s =>
      pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
        (List.ofFn (F.f n x y).1) := fun S => funext (Functionality.idealB_eq F S n x y)
  have e3 : acceptProb (F.idealB SB n x y) (D.distinguisherL n) =
      acceptProb (F.idealB SH n x y) (DΦ.distinguisherL n) := by
    rw [hid SB, hid SH]
    exact acceptProb_post_pre SB SH DΦ D (.mul H.calls SρB.coins) n
      (fun hv e => phiV SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode hv e)))
      (fun w e => phiD SρB fB H.calls ρ.rounds ρ.V.coins G.outB ρ.verifierFirst false H.lead
        (pairEncode (pairEncode (List.replicate n true) (SρB.advice n)) (pairEncode w e)))
      (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) (List.ofFn (F.f n x y).1) hSBc
      (hSB n _) hDΦc (hDΦ n) (fun hv e => phiD_pairEncode _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have s3 : |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
        H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
          if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
            ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
      acceptProb (F.idealB SB n x y) (D.distinguisherL n)| ≤ ε₃ n := by
    rw [← H.acceptProb_realB_dPhi ρ SρB D DΦ hcallB hDΦc hDΦ n x y, e3]
    have h := (h₃ n x y).2
    rwa [distAdv_def] at h
  rw [distAdv_def]
  calc |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
        acceptProb (F.idealB SB n x y) (D.distinguisherL n)|
      ≤ |acceptProb (F.realB (H.compose ρ) n x y) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) →
            ρ.ExecCoins ρ.P (List.replicate n true)) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.viewRunB ρ n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n)| +
        |acceptProb (fun z : H.Coins n × (Fin (H.calls.eval n) → SρB.Coins n) =>
            H.sampleB ρ n (List.ofFn x) (List.ofFn y) z.1 fun j =>
              if h : j < H.calls.eval n then H.simRunB SρB n (List.ofFn x) (List.ofFn y) z.1
                ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) (D.distinguisherL n) -
          acceptProb (F.idealB SB n x y) (D.distinguisherL n)| :=
        (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
    _ ≤ _ := add_le_add (add_le_add s1 s2) s3

end HybridProtocol

end TCSlib.Cryptography.SecureComputation

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Sim.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The post-processing `Φ` and the simulators of the composed protocol

Steps 1 and 4 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
party's simulator for `H.compose ρ` runs the hybrid simulator `S^H` and post-processes its output
`hv`, read as a view of `main` with private input `⟨x, a⟩`, `main`-tape `mt` and messages `me`:
for each call `j < L(n)` it recomputes the call input `fcall ⟨1^n, ⟨x, ⟨mt, 1^j⟩⟩⟩`, runs `ρ`'s
simulator `S^ρ` on it and on the `j`-th block of `a`, with the `j`-th block of fresh coins, and
assembles the view of `H.compose ρ` (`ComposeSim.asmView`). The same post-processing applied to
the hybrid real sample gives the last hybrid of the proof, and applied before a distinguisher it
gives the reduction to the hybrid model's security (`exists_dPhi`).

## Main definitions

* `ComposeSim.simV`: one simulated run, `ComposeSim.vlW`: their encoded list.
* `ComposeSim.phiV`: the post-processing of a view; `ComposeSim.phiD`: of a sample `⟨view, out⟩`.

## Main results

* `ComposeSim.phiV_view`: `phiV` on an encoded view of `main` with input `1^n` is the assembled
  view of the simulated runs.
* `ComposeSim.polyTimeComputable_phiV`, `polyTimeComputable_phiD`.
* `ComposeSim.exists_simulator`, `ComposeSim.exists_dPhi`: the simulator and the reduction as
  non-uniform PPT machines.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

variable (Sρ : NUPPT) (fcall : List Bool → List Bool) (calls rounds cρ out : PolyExpr)
  (vF b : Bool) (lead : ℕ)

/-- **One simulated run**: on `v = ⟨1^j, ⟨⟨u, α⟩, ⟨hv, s⟩⟩⟩` (`u = 1^n`, `α` the advice of
`S^ρ`, `hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩` a view, `s` the fresh coins), `S^ρ`'s output on the
call input `fcall ⟨u, ⟨xin, ⟨mt, 1^j⟩⟩⟩` and the answer block `coinBlock out(n) j a`, with
advice `α` and coins `coinBlock Sρ.coins(n) j s`. -/
def simV (v : List Bool) : List Bool :=
  Sρ.output (NUPPT.layout (pairFstD (pairFstD (pairSndD v)))
    (pairEncode
      (fcall (pairEncode (pairFstD (pairFstD (pairSndD v)))
        (pairEncode (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))
          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v))))) (pairFstD v)))))
      (coinBlock (out.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
        (pairSndD (pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v))))))))
    (pairSndD (pairFstD (pairSndD v)))
    (coinBlock (Sρ.coins.eval (pairFstD (pairFstD (pairSndD v))).length) (pairFstD v).length
      (pairSndD (pairSndD (pairSndD v)))))

/-- `simV` on its word: with `w = ⟨⟨1^n, α⟩, ⟨⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩`,
`simV ⟨1^j, w⟩ = Sρ.output (layout 1^n ⟨fcall ⟨1^n, ⟨xin, ⟨mt, 1^j⟩⟩⟩, coinBlock out(n) j a⟩ α
(coinBlock Sρ.coins(n) j s))`. -/
theorem simV_pairEncode (n j : ℕ) (α x₁ xin a mt me s : List Bool) :
    simV Sρ fcall out (pairEncode (List.replicate j true)
        (pairEncode (pairEncode (List.replicate n true) α)
          (pairEncode (pairEncode (pairEncode x₁ (pairEncode xin a)) (pairEncode mt me)) s))) =
      Sρ.output (NUPPT.layout (List.replicate n true)
        (pairEncode (fcall (pairEncode (List.replicate n true)
            (pairEncode xin (pairEncode mt (List.replicate j true)))))
          (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
  simp only [simV, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **The encoded list of the simulated runs** on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩`:
`vlW w = (range calls(n)).flatMap fun j => ⟨simV ⟨1^j, w⟩, []⟩`. -/
def vlW (w : List Bool) : List Bool :=
  (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
    pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []

/-- The defining equation of `vlW` (see `vlW`).
`vlW Sρ fcall calls out w = (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j
=> pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []`. -/
theorem vlW_eq (w : List Bool) :
    vlW Sρ fcall calls out w =
      (List.range (calls.eval (pairFstD (pairFstD w)).length)).flatMap fun j =>
        pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) [] := rfl

/-- **The post-processing of a view** (`Φ` on views): on `w = ⟨⟨1^n, α⟩, ⟨hv, s⟩⟩` with
`hv = ⟨⟨x₁, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩`, the assembled view (`asmW`) of `x₁`, `xin`, `mt`, `me` and the
simulated runs (`vlW`). -/
def phiV (w : List Bool) : List Bool :=
  asmW calls rounds cρ vF b lead
    (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
        (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
      (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
        (pairSndD (pairSndD (pairFstD (pairSndD w))))))
      (vlW Sρ fcall calls out w))

/-- The defining equation of `phiV` (see `phiV`).
`phiV Sρ fcall calls rounds cρ out vF b lead w = asmW calls rounds cρ vF b lead (pairEncode
(pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w)))) (pairFstD (pairSndD (pairFstD
(pairFstD (pairSndD w)))))) (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w)))) (pairSndD
(pairSndD (pairFstD (pairSndD w)))))) (vlW Sρ fcall calls out w))`. -/
theorem phiV_eq (w : List Bool) :
    phiV Sρ fcall calls rounds cρ out vF b lead w =
      asmW calls rounds cρ vF b lead
        (pairEncode (pairEncode (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD w))))
            (pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w))))))
          (pairEncode (pairFstD (pairSndD (pairFstD (pairSndD w))))
            (pairSndD (pairSndD (pairFstD (pairSndD w))))))
          (vlW Sρ fcall calls out w)) := rfl

/-- **`phiV` on a view of `main` with common input `1^n`**: on
`⟨⟨1^n, α⟩, ⟨⟨⟨1^n, ⟨xin, a⟩⟩, ⟨mt, me⟩⟩, s⟩⟩` it is
`asmView … 1^n xin mt me V` with `V j = S^ρ`'s output on the call input and the answer block
`j`, with the coin block `j` (`asmW_pairEncode`, `asmView_congr`, `msgAt_encodeMsgs`). -/
theorem phiV_view (n : ℕ) (α xin a mt me s : List Bool) :
    phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) α)
          (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
            (pairEncode mt me)) s)) =
      asmView calls rounds cρ vF b lead (List.replicate n true) xin mt me fun j =>
        Sρ.output (NUPPT.layout (List.replicate n true)
          (pairEncode (fcall (pairEncode (List.replicate n true)
              (pairEncode xin (pairEncode mt (List.replicate j true)))))
            (coinBlock (out.eval n) j a)) α (coinBlock (Sρ.coins.eval n) j s)) := by
  rw [phiV_eq, vlW_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [asmW_pairEncode]
  refine asmView_congr _ _ _ _ _ _ _ _ _ _ fun j hj => ?_
  rw [List.length_replicate] at hj ⊢
  rw [← List.flatMap_map (fun j => simV Sρ fcall out (pairEncode (List.replicate j true)
      (pairEncode (pairEncode (List.replicate n true) α)
        (pairEncode (pairEncode (pairEncode (List.replicate n true) (pairEncode xin a))
          (pairEncode mt me)) s)))) (fun m => pairEncode m []),
    ← encodeMsgs_eq_flatMap, msgAt_encodeMsgs, Compose.getD_map_range hj, simV_pairEncode]

/-- **The post-processing of a sample** (`Φ` on samples `⟨view, out⟩`): on
`w = ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩`, `phiD w = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
def phiD (w : List Bool) : List Bool :=
  pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
      (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
        (pairSndD (pairSndD w)))))
    (pairSndD (pairFstD (pairSndD w)))

/-- `phiD` on its word: `phiD ⟨⟨u, α⟩, ⟨⟨hv, o⟩, s⟩⟩ = ⟨phiV ⟨⟨u, α⟩, ⟨hv, s⟩⟩, o⟩`. -/
theorem phiD_pairEncode (u α hv o s : List Bool) :
    phiD Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode u α) (pairEncode (pairEncode hv o) s)) =
      pairEncode (phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode u α) (pairEncode hv s))) o := by
  simp only [phiD, pairFstD_pairEncode, pairSndD_pairEncode]

variable {fcall}

/-- **`simV` is polynomial-time** when `fcall` is: `PolyTimeComputable (simV Sρ fcall out)`.

**Proof sketch.** The components `1^n`, `α`, `xin`, `a`, `mt`, `s` of the word are projections;
the call input is `fcall` on a pairing of them; the answer block and the coin block are
`coinSlice`s (`GI.coinSlice_poly`); and `S^ρ`'s output on the assembled layout is polynomial-time
(`NUPPT.polyTimeComputable_output`, `NUPPT.polyTimeComputable_layout`). -/
theorem polyTimeComputable_simV (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (simV Sρ fcall out) := by
  have hw := polyTimeComputable_pairSndD
  have hu : PolyTimeComputable fun v => pairFstD (pairFstD (pairSndD v)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp' hw)
  have hhv : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have hz : PolyTimeComputable fun v => pairSndD (pairFstD (pairFstD (pairSndD (pairSndD v)))) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)))
  have hxin := polyTimeComputable_pairFstD.comp' hz
  have ha := polyTimeComputable_pairSndD.comp' hz
  have hmt : PolyTimeComputable fun v => pairFstD (pairSndD (pairFstD (pairSndD (pairSndD v)))) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hhv)
  have hs : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have hα : PolyTimeComputable fun v => pairSndD (pairFstD (pairSndD v)) :=
    polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp' hw)
  have hin := hcall.comp' (hu.pairEncode (hxin.pairEncode (hmt.pairEncode
    polyTimeComputable_pairFstD)))
  exact (Sρ.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
    (hin.pairEncode (GI.coinSlice_poly out hu polyTimeComputable_pairFstD ha)) hα
    (GI.coinSlice_poly Sρ.coins hu polyTimeComputable_pairFstD hs))).congr fun v => rfl

/-- **`vlW` is polynomial-time** (`ComposeMachines.polyTimeComputable_flatMap_range` of
`polyTimeComputable_simV` over the unary count `calls(n)`).
`PolyTimeComputable (vlW Sρ fcall calls out)`. -/
theorem polyTimeComputable_vlW (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (vlW Sρ fcall calls out) := by
  have hchunk : PolyTimeComputable fun v =>
      pairEncode (simV Sρ fcall out (pairEncode (List.replicate (pairFstD v).length true)
        (pairSndD v))) [] :=
    ((polyTimeComputable_simV Sρ out hcall).comp' ((unaryLength_poly
      polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)).pairEncode
      (polyTimeComputable_const [])
  exact (polyTimeComputable_flatMap_range (E := fun w j =>
      pairEncode (simV Sρ fcall out (pairEncode (List.replicate j true) w)) []) hchunk
    (unaryPolyOf_poly calls (unaryLength_poly (polyTimeComputable_pairFstD.comp'
      polyTimeComputable_pairFstD)))).congr fun w => (vlW_eq Sρ fcall calls out w).symm

/-- **`phiV` is polynomial-time** (`polyTimeComputable_asmW` after projections and `vlW`).
`PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead)`. -/
theorem polyTimeComputable_phiV (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (phiV Sρ fcall calls rounds cρ out vF b lead) := by
  have hhv : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  have hv1 := polyTimeComputable_pairFstD.comp' hhv
  have hv2 := polyTimeComputable_pairSndD.comp' hhv
  exact ((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
    ((((polyTimeComputable_pairFstD.comp' hv1).pairEncode (polyTimeComputable_pairFstD.comp'
      (polyTimeComputable_pairSndD.comp' hv1))).pairEncode
      ((polyTimeComputable_pairFstD.comp' hv2).pairEncode
        (polyTimeComputable_pairSndD.comp' hv2))).pairEncode
      (polyTimeComputable_vlW Sρ calls out hcall))).congr fun w => rfl

/-- **`phiD` is polynomial-time** (`polyTimeComputable_phiV` after re-pairing).
`PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead)`. -/
theorem polyTimeComputable_phiD (hcall : PolyTimeComputable fcall) :
    PolyTimeComputable (phiD Sρ fcall calls rounds cρ out vF b lead) := by
  have hsmp : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  exact (((polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall).comp'
    (polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairFstD.comp' hsmp).pairEncode
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)))).pairEncode
    (polyTimeComputable_pairSndD.comp' hsmp)).congr fun w => rfl

/-- **The simulator of the composed protocol** (step 1): for a hybrid simulator `SH`, there is a
non-uniform PPT `S` with coins `SH.coins + calls · Sρ.coins` such that
`S(1^n, y; r) = phiV ⟨⟨1^n, Sρ.advice n⟩, ⟨SH(1^n, y; r_{<SH.coins(n)}), r_{≥SH.coins(n)}⟩⟩`
(`exists_post`). -/
theorem exists_simulator (SH : NUPPT) (hcall : PolyTimeComputable fcall) :
    ∃ S : NUPPT, S.coins = .add SH.coins (.mul calls Sρ.coins) ∧ ∀ n y r, S.runAtL n y r =
      phiV Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
          (pairEncode (SH.runAtL n y (r.take (SH.coinLen n))) (r.drop (SH.coinLen n)))) :=
  exists_post SH (polyTimeComputable_phiV Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
    Sρ.advice_length (.mul calls Sρ.coins)

/-- **The reduction to the hybrid model** (step 4): for a distinguisher `D`, there is a non-uniform
PPT `DΦ` with coins `calls · Sρ.coins + D.coins` such that
`DΦ(1^n, w; r) = D(1^n, phiD ⟨⟨1^n, Sρ.advice n⟩, ⟨w, r_{<p(n)}⟩⟩; r_{≥p(n)})`,
`p = calls · Sρ.coins` (`exists_pre`). -/
theorem exists_dPhi (D : NUPPT) (hcall : PolyTimeComputable fcall) :
    ∃ DΦ : NUPPT, DΦ.coins = .add (.mul calls Sρ.coins) D.coins ∧ ∀ n y r, DΦ.runAtL n y r =
      D.runAtL n (phiD Sρ fcall calls rounds cρ out vF b lead
        (pairEncode (pairEncode (List.replicate n true) (Sρ.advice n))
          (pairEncode y (r.take ((PolyExpr.mul calls Sρ.coins).eval n)))))
        (r.drop ((PolyExpr.mul calls Sρ.coins).eval n)) :=
  exists_pre D (polyTimeComputable_phiD Sρ calls rounds cρ out vF b lead hcall) Sρ.advice Sρ.adv
    Sρ.advice_length (.mul calls Sρ.coins)

end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/SecureComputation/ComposeSecurity/Template.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction of one hybrid step to the sub-protocol

Step 3 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3]. A
distinguisher between neighbouring hybrids, at fixed inputs, run index and other coordinates,
becomes a distinguisher for one sample of `ρ`: the reduction holds as advice a **template**
(`tmplW`): the header `⟨⟨x₁, xin⟩, ⟨mt, me⟩⟩` of the assembled view, the encoded words of the
runs before and after the run under attack, and the other party's output. On a `ρ`-sample `w`
it inserts the view `pairFstD w` between them, assembles the view (`asmW`) and pairs it with the
output (`hybW`). The template is chosen at each `n` for the worst-case instance, so one
non-uniform machine serves every `n` (`exists_gap_le`).

## Main definitions

* `ComposeSim.tmplW`: the template; `ComposeSim.hybW`: the reduction's pre-processing.

## Main results

* `ComposeSim.hybW_tmplW`: the pre-processing on a template.
* `ComposeSim.polyTimeComputable_hybW`.
* `ComposeSim.exists_gap_le`: the worst-case gap over the instances of each `n` is at most the
  sub-protocol's negligible bound.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeSim

open Finset Complexity Turing TCSlib.Cryptography ComposeProb ComposeMachines

/-- **The template of a hybrid step**: `⟨⟨hdr, encodeMsgs pre⟩, ⟨encodeMsgs suf, out⟩⟩` for the
header `hdr`, the words `pre` of the runs before the attacked one, the words `suf` of those
after it and the output `out`.
`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
(Strategy.encodeMsgs suf) out)`. -/
def tmplW (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) : List Bool :=
  pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
    (pairEncode (Strategy.encodeMsgs suf) out)

/-- The defining equation of `tmplW` (see `tmplW`).
`tmplW hdr pre suf out = pairEncode (pairEncode hdr (Strategy.encodeMsgs pre)) (pairEncode
(Strategy.encodeMsgs suf) out)`. -/
theorem tmplW_eq (hdr : List Bool) (pre suf : List (List Bool)) (out : List Bool) :
    tmplW hdr pre suf out =
      pairEncode (pairEncode hdr (Strategy.encodeMsgs pre))
        (pairEncode (Strategy.encodeMsgs suf) out) := rfl

/-- **The pre-processing of the hybrid-step reduction**: on `z = ⟨⟨u, β⟩, ⟨w, r⟩⟩` with
`β = ⟨⟨hdr, P⟩, ⟨Q, out⟩⟩`, the pair of `asmW ⟨hdr, P ++ ⟨pairFstD w, Q⟩⟩` and `out`. -/
def hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) : List Bool :=
  pairEncode (asmW calls rounds cρ vF b lead
      (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
        (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
          pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
            (pairFstD z)))))))
    (pairSndD (pairSndD (pairSndD (pairFstD z))))

/-- The defining equation of `hybW` (see `hybW`).
`hybW calls rounds cρ vF b lead z = pairEncode (asmW calls rounds cρ vF b lead (pairEncode (pairFstD
(pairFstD (pairSndD (pairFstD z)))) (pairSndD (pairFstD (pairSndD (pairFstD z))) ++ pairEncode
(pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD (pairFstD z))))))) (pairSndD
(pairSndD (pairSndD (pairFstD z))))`. -/
theorem hybW_eq (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) (z : List Bool) :
    hybW calls rounds cρ vF b lead z =
      pairEncode (asmW calls rounds cρ vF b lead
          (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD z))))
            (pairSndD (pairFstD (pairSndD (pairFstD z))) ++
              pairEncode (pairFstD (pairFstD (pairSndD z))) (pairFstD (pairSndD (pairSndD
                (pairFstD z)))))))
        (pairSndD (pairSndD (pairSndD (pairFstD z)))) := rfl

/-- **The pre-processing on a template**: `hybW ⟨⟨u, tmplW hdr pre suf out⟩, ⟨w, r⟩⟩ =
⟨asmW ⟨hdr, encodeMsgs (pre ++ pairFstD w :: suf)⟩, out⟩` (`encodeMsgs_append`). -/
theorem hybW_tmplW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ)
    (u hdr out w r : List Bool) (pre suf : List (List Bool)) :
    hybW calls rounds cρ vF b lead (pairEncode (pairEncode u (tmplW hdr pre suf out))
        (pairEncode w r)) =
      pairEncode (asmW calls rounds cρ vF b lead
        (pairEncode hdr (Strategy.encodeMsgs (pre ++ pairFstD w :: suf)))) out := by
  rw [hybW_eq, tmplW_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- **The pre-processing is polynomial-time** (`polyTimeComputable_asmW` after projections,
`append` and `pairEncode`).
`PolyTimeComputable (hybW calls rounds cρ vF b lead)`. -/
theorem polyTimeComputable_hybW (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) :
    PolyTimeComputable (hybW calls rounds cρ vF b lead) := by
  have hβ : PolyTimeComputable fun z => pairSndD (pairFstD z) :=
    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD
  have h1 := polyTimeComputable_pairFstD.comp' hβ
  have h2 := polyTimeComputable_pairSndD.comp' hβ
  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (pairSndD z)) :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp'
      polyTimeComputable_pairSndD)
  exact (((polyTimeComputable_asmW calls rounds cρ vF b lead).comp'
    ((polyTimeComputable_pairFstD.comp' h1).pairEncode
      ((polyTimeComputable_pairSndD.comp' h1).append
        (hw.pairEncode (polyTimeComputable_pairFstD.comp' h2))))).pairEncode
    (polyTimeComputable_pairSndD.comp' h2)).congr fun z => rfl

/-- **The worst-case hybrid step is bounded by the sub-protocol's security.** Let `rs n x y` and
`is n x y` be samplers of `ρ` on inputs of `G`'s lengths, indistinguishable with a negligible
bound uniform over the inputs (`hS`). Let `Θ n` be finite sets of instances, each with inputs
`xA θ`, `yB θ` of `ρ` and a template whose length is at most `q(n)`. Then for every non-uniform
PPT `D` there is a negligible `ε₂` with, for all `n` and `θ : Θ n`,
`|Pr_t[D(K θ (pairFstD (rs t)))] − Pr_s[D(K θ (pairFstD (is s)))]| ≤ ε₂(n)`, where
`K θ v = ⟨asmW ⟨hdr θ, encodeMsgs (pre θ ++ v :: suf θ)⟩, out θ⟩` (the template filled with `v`).

**Proof sketch.** At each `n` with instances, take the instance `θ*` with the largest gap
(`Finset.exists_max_image`) and give its template as advice (length at most `q(n)`). The
machine `D ∘ hybW` with no extra coins (`exists_pre`) accepts a sample `w` as `D` accepts
`K θ* (pairFstD w)` (`acceptProb_pre`, `hybW_tmplW`, `acceptProb_fst`), so its advantage
between `rs` and `is` at the inputs of `θ*` is the gap at `θ*`, at most `ε₂(n)` by `hS`, and
every gap at `n` is at most the gap at `θ*`. -/
theorem exists_gap_le {G : Functionality} {T Sc : ℕ → Type} [∀ n, Fintype (T n)]
    [∀ n, Fintype (Sc n)]
    (rs : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → T n → List Bool)
    (is : ∀ n, (Fin (G.inA.eval n) → Bool) → (Fin (G.inB.eval n) → Bool) → Sc n → List Bool)
    (hS : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (G.inA.eval n) → Bool) (y : Fin (G.inB.eval n) → Bool),
        distAdv (rs n x y) (is n x y) (D.distinguisherL n) ≤ ε n)
    (calls rounds cρ : PolyExpr) (vF b : Bool) (lead : ℕ) {Θ : ℕ → Type} [∀ n, Fintype (Θ n)]
    (xA : ∀ n, Θ n → Fin (G.inA.eval n) → Bool) (yB : ∀ n, Θ n → Fin (G.inB.eval n) → Bool)
    (hdr out : ∀ n, Θ n → List Bool) (pre suf : ∀ n, Θ n → List (List Bool)) (q : PolyExpr)
    (hq : ∀ n θ, (tmplW (hdr n θ) (pre n θ) (suf n θ) (out n θ)).length ≤ q.eval n)
    (D : NUPPT) :
    ∃ ε₂ : ℕ → ℝ, Negligible ε₂ ∧ ∀ n (θ : Θ n),
      |acceptProb (fun t => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
            (Strategy.encodeMsgs (pre n θ ++ pairFstD (rs n (xA n θ) (yB n θ) t) :: suf n θ))))
            (out n θ)) (D.distinguisherL n) -
        acceptProb (fun s => pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
            (Strategy.encodeMsgs (pre n θ ++ pairFstD (is n (xA n θ) (yB n θ) s) :: suf n θ))))
            (out n θ)) (D.distinguisherL n)| ≤ ε₂ n := by
  classical
  -- the gap of an instance
  let K : ∀ n, Θ n → List Bool → List Bool := fun n θ v =>
    pairEncode (asmW calls rounds cρ vF b lead (pairEncode (hdr n θ)
      (Strategy.encodeMsgs (pre n θ ++ v :: suf n θ)))) (out n θ)
  let gap : ∀ n, Θ n → ℝ := fun n θ =>
    |acceptProb (fun t => K n θ (pairFstD (rs n (xA n θ) (yB n θ) t))) (D.distinguisherL n) -
      acceptProb (fun s => K n θ (pairFstD (is n (xA n θ) (yB n θ) s))) (D.distinguisherL n)|
  have hmax : ∀ n, Nonempty (Θ n) → ∃ θs : Θ n, ∀ θ, gap n θ ≤ gap n θs := fun n hn => by
    obtain ⟨θs, -, h⟩ := exists_max_image univ (gap n) univ_nonempty
    exact ⟨θs, fun θ => h θ (mem_univ θ)⟩
  -- the advice: the template of the worst instance
  let β : ℕ → List Bool := fun n => if h : Nonempty (Θ n) then
    tmplW (hdr n (Classical.choose (hmax n h))) (pre n (Classical.choose (hmax n h)))
      (suf n (Classical.choose (hmax n h))) (out n (Classical.choose (hmax n h))) else []
  have hβ : ∀ n, (β n).length ≤ q.eval n := fun n => by
    by_cases h : Nonempty (Θ n)
    · simp only [β, dif_pos h]
      exact hq n _
    · simp only [β, dif_neg h, List.length_nil]
      exact Nat.zero_le _
  obtain ⟨Dh, hc, hDh⟩ := exists_pre D (polyTimeComputable_hybW calls rounds cρ vF b lead) β q hβ
    (.const 0)
  obtain ⟨ε, hε, hbound⟩ := hS Dh
  refine ⟨ε, hε, fun n θ => ?_⟩
  have hn : Nonempty (Θ n) := ⟨θ⟩
  have hθs := Classical.choose_spec (hmax n hn)
  -- `Dh` accepts a sample as `D` accepts the filled template of the worst instance
  have key : ∀ {σ : Type} [Fintype σ] (X : σ → List Bool),
      acceptProb X (Dh.distinguisherL n) =
        acceptProb (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s)))
          (D.distinguisherL n) := by
    intro σ _ X
    rw [acceptProb_pre X Dh D (.const 0) n (fun w e => hybW calls rounds cρ vF b lead
      (pairEncode (pairEncode (List.replicate n true) (β n)) (pairEncode w e))) hc (hDh n)]
    refine Eq.trans ?_ (acceptProb_fst (τ := Fin ((PolyExpr.const 0).eval n) → Bool)
      (fun s => K n (Classical.choose (hmax n hn)) (pairFstD (X s))) (D.distinguisherL n))
    refine congrArg (fun f => acceptProb f (D.distinguisherL n)) (funext fun z => ?_)
    simp only [β, dif_pos hn]
    rw [hybW_tmplW]
  have h := hbound n (xA n (Classical.choose (hmax n hn))) (yB n (Classical.choose (hmax n hn)))
  rw [distAdv_def, key, key] at h
  exact (hθs θ).trans h

end TCSlib.Cryptography.SecureComputation.ComposeSim

## ===== TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the commitment theorems

The machine constructions and probability bookkeeping behind the theorems of
`TCSlib.Cryptography.ZeroKnowledge.Commitment` [PS10, §4.7.1]: multi-value hiding of a
commitment scheme (Claim-126.a), the hiding of the bitwise scheme of Theorem 126.4
(Claim-127.d) and the polynomial-time evaluator of its `Com` (Alg-127.a). Nothing here mentions
the commitment definitions themselves; the file supplies

* **averaging over a coin factor** (`exists_fixCoins`): for a distinguisher whose coins split as
  `κ × ρ`, some fixed value `c₀` of the first factor has at least the advantage of the
  distinguisher. This is the non-uniform way to run the coordinatewise hybrid reduction
  `pairRed` of Claim-126.a without any sampler: the randomness of the other coordinates is
  hard-wired as advice, so neither hiding theorem needs an efficient evaluator of the scheme
  (the text's "simple hybrid argument" tacitly uses the non-uniformity of [PS10, Definition 126.3]);
* **coin transport** (`acceptProb_distinguisher_of_runAtL`, `acceptProb_distinguisherL_of_runAtL`):
  a machine with `D`'s coins whose activation is `D` on a pre-processed input has the acceptance
  probabilities of the pre-processed distinguisher;
* **splitting a tuple at a position** (`ofFn_update_eq`, `ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update`): the block string, respectively the message encoding
  `Strategy.encodeMsgs`, of a tuple with one position replaced by a challenge `z` is a fixed
  prefix, then `z` (respectively the pair `⟨z, ·⟩`), then a fixed suffix;
* **the splice machines** (`exists_spliceRed`, `exists_pairSpliceRed`): the `NUPPT`s that
  plant their argument between two hard-wired strings and call `D` once
  (`Complexity.NUPPT.exists_comp`, `Complexity.NUPPT.exists_withAdvice`);
* **the bitwise commitment loop** (`ComLoop`): the state loop evaluating
  `Com(v, (r_i)_i) = (F ⟨1^n, r_i⟩ ‖ (v_i ⊕ H ⟨1^n, r_i⟩))_i` from evaluators `F`, `H` of `f`, `h`
  (`Complexity.polyTimeComputable_iterateEmit`), with the closed form of its emissions.

## Main definitions

* `TCSlib.Cryptography.CommitmentLemmas.spliceFun`, `pairSpliceFun` — the splice pre-processings.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.step`, `ComLoop.emit`, `ComLoop.loopOut`,
  `ComLoop.init` — the bitwise commitment loop.

## Main results

* `TCSlib.Cryptography.CommitmentLemmas.exists_fixCoins` — averaging over a coin factor.
* `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisher_of_runAtL`,
  `acceptProb_distinguisherL_of_runAtL` — coin transport.
* `TCSlib.Cryptography.CommitmentLemmas.ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update` — splitting a tuple at a position.
* `TCSlib.Cryptography.CommitmentLemmas.exists_spliceRed`, `exists_pairSpliceRed` — the
  splice machines.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.loopOut_poly`, `ComLoop.emit_init_of_lt`,
  `ComLoop.emit_init_of_le` — the loop is polynomial-time and its emissions are the one-bit
  commitments.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.1: Definition 126.3, Theorem 126.4; §3.1.1: Lemma 71.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.3 (the multicopy hybrid argument).
-/

namespace TCSlib.Cryptography.CommitmentLemmas

open Complexity Turing Finset

/-! ### Averaging over a coin factor -/

/-- Some point of a finite nonempty type carries at least the absolute value of the average:
`|E f| ≤ |f c₀|` for some `c₀` (`Finset.exists_le_of_sum_le` against the constant `|E f|`). -/
theorem exists_abs_uexp_le {κ : Type*} [Fintype κ] [Nonempty κ] (f : κ → ℝ) :
    ∃ c₀, |uexp f| ≤ |f c₀| := by
  have hcard : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hsum : ∑ _c : κ, |uexp f| ≤ ∑ c, |f c| := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uexp_def, abs_div, abs_of_pos hcard,
      mul_div_cancel₀ _ hcard.ne']
    exact Finset.abs_sum_le_sum_abs _ _
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨c₀, hc₀⟩

/-- The acceptance probability of a distinguisher with coins `κ × ρ` is the average over the
first coin factor of the acceptance probabilities with that factor fixed (`uprob_prod` after
regrouping the sample space). -/
theorem acceptProb_eq_uexp_fst {σ γ κ ρ : Type*} [Fintype σ] [Fintype κ] [Fintype ρ]
    (X : σ → γ) (D : γ → κ × ρ → Bool) :
    acceptProb X D = uexp fun c₀ => acceptProb X fun z c => D z (c₀, c) := by
  simp only [acceptProb_def]
  refine ((uprob_comp_equiv (EnsembleLemmas.swapAux κ σ ρ)
    fun z : σ × (κ × ρ) => D (X z.1) z.2 = true).symm.trans ?_)
  rw [uprob_prod]
  rfl

/-- **Averaging over a coin factor**: for a distinguisher `D` whose coins split as `κ × ρ`,
some fixed value `c₀` of the first factor does at least as well as `D` itself,
`distAdv X Y D ≤ distAdv X Y (D(·, (c₀, ·)))`. This is how a non-uniform reduction hard-wires
the randomness of the other coordinates of a hybrid argument instead of sampling them
([PS10, Definition 26.8], advice).

**Proof sketch.** Both acceptance probabilities are averages over `c₀`
(`acceptProb_eq_uexp_fst`), so the advantage is `|E_{c₀}[a(c₀) − b(c₀)]|`, and some `c₀` has
`|a(c₀) − b(c₀)|` at least the average (`exists_abs_uexp_le`). -/
theorem exists_fixCoins {σ τ γ κ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [Fintype ρ]
    [Nonempty κ] (X : σ → γ) (Y : τ → γ) (D : γ → κ × ρ → Bool) :
    ∃ c₀ : κ, distAdv X Y D ≤ distAdv X Y fun z c => D z (c₀, c) := by
  obtain ⟨c₀, hc₀⟩ := exists_abs_uexp_le fun c₀ : κ =>
    acceptProb X (fun z c => D z (c₀, c)) - acceptProb Y (fun z c => D z (c₀, c))
  refine ⟨c₀, ?_⟩
  simp only [distAdv_def]
  rw [acceptProb_eq_uexp_fst X D, acceptProb_eq_uexp_fst Y D]
  convert hc₀ using 2
  rw [uexp_def, uexp_def, uexp_def, ← sub_div, Finset.sum_sub_distrib]

/-- The distinguishing advantage is symmetric in the two distributions. -/
theorem distAdv_comm {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : distAdv X Y D = distAdv Y X D :=
  abs_sub_comm _ _

/-! ### Coin transport -/

/-- A machine `B` with `D`'s coins whose activation on `y` is `D`'s on `g y` has, as a typed
distinguisher, the acceptance probabilities of the distinguisher `D(1^n, g ·)` (the coin types
correspond along `B.coins = D.coins`). -/
theorem acceptProb_distinguisher_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n m : ℕ} (X : σ → Fin m → Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisher n m) =
      acceptProb X fun z c => D.distinguisherL n (g (List.ofFn z)) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen_eq, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hrun]

/-- As `acceptProb_distinguisher_of_runAtL`, for untyped samples. -/
theorem acceptProb_distinguisherL_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n : ℕ} (X : σ → List Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisherL n) = acceptProb X fun z c => D.distinguisherL n (g z) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen_eq, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hrun]

/-! ### Splitting a tuple at a position -/

/-- Splitting `List.ofFn F` at position `j`: the first `j` entries, the entry `j`, the rest
(`List.ext_getElem` with `List.getElem_append`, `List.getElem_cons`; private copy of
`ofFn_eq_append_cons` of `Encryption/PublicKey/HybridMachine.lean`, which this file does not import). -/
theorem ofFn_eq_append_cons {α : Type*} {N : ℕ} (F : Fin N → α) (j : Fin N) :
    List.ofFn F = (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
      F j :: List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro t h1 h2
    rw [List.getElem_append]
    simp only [List.length_ofFn]
    split_ifs with h
    · simp only [List.getElem_ofFn]
      congr 1
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)

/-- `List.ofFn (update W k z)` is the entries before `k`, then `z`, then the entries after `k`.

**Proof sketch.** `ofFn_eq_append_cons` splits `List.ofFn (update W k z)` at `k`; the entry at
`k` is `z` (`Function.update_self`) and the entries before and after `k` are those of `W`
(`Function.update_of_ne`, the indices `castLE i < k` and `k + 1 + i` differing from `k`). -/
theorem ofFn_update_eq {α : Type*} {N : ℕ} (W : Fin N → α) (k : Fin N) (z : α) :
    List.ofFn (Function.update W k z) = (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
      z :: List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩ := by
  rw [ofFn_eq_append_cons (Function.update W k z) k, Function.update_self]
  have h₁ : ∀ i : Fin k, Function.update W k z (Fin.castLE k.2.le i) = W (Fin.castLE k.2.le i) := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    have hi := i.2
    simp only [Fin.coe_castLE] at hv
    omega
  have h₂ : ∀ i : Fin (N - k - 1),
      Function.update W k z ⟨k + 1 + i, by omega⟩ = W ⟨k + 1 + i, by omega⟩ := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  simp only [h₁, h₂]

/-- The concatenation of `j` strings of `L` bits has `j · L` bits. -/
theorem length_flatten_ofFn {j L : ℕ} (f : Fin j → Fin L → Bool) :
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L := by
  simp [List.length_flatten, List.sum_ofFn]

/-- The block string of a tuple with block `k` replaced by `z`: the blocks before `k`, then
`z`, then the blocks after `k` (`FunFamily.ofFn_blocks_symm`, `ofFn_update_eq`). -/
theorem ofFn_blocks_symm_update {q ℓ : ℕ} (W : Fin q → Fin ℓ → Bool) (k : Fin q)
    (z : Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks q ℓ).symm (Function.update W k z)) =
      (List.ofFn fun i : Fin k => List.ofFn (W (Fin.castLE k.2.le i))).flatten ++ List.ofFn z ++
        (List.ofFn fun i : Fin (q - k - 1) => List.ofFn (W ⟨k + 1 + i, by omega⟩)).flatten := by
  rw [FunFamily.ofFn_blocks_symm]
  have h2 : (fun i => List.ofFn (Function.update W k z i)) =
      Function.update (fun i => List.ofFn (W i)) k (List.ofFn z) := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [h2, ofFn_update_eq, List.flatten_append, List.flatten_cons, List.append_assoc]

/-- The encoding of a concatenated history is the concatenation of the encodings
(`pairEncode a (b ++ c) = pairEncode a b ++ c`). -/
theorem encodeMsgs_append (L M : List (List Bool)) :
    Strategy.encodeMsgs (L ++ M) = Strategy.encodeMsgs L ++ Strategy.encodeMsgs M := by
  induction L with
  | nil => rfl
  | cons m L ih => simp [ih, pairEncode_eq, List.append_assoc]

/-- The encoding of a history of messages of length `≤ M` has length at most
`|L| · (2M + 2)` (`length_pairEncode`). -/
theorem length_encodeMsgs_le (L : List (List Bool)) (M : ℕ) (hM : ∀ m ∈ L, m.length ≤ M) :
    (Strategy.encodeMsgs L).length ≤ L.length * (2 * M + 2) := by
  induction L with
  | nil => simp
  | cons m L ih =>
    have h1 := hM m (by simp)
    have h2 := ih fun m' hm' => hM m' (by simp [hm'])
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The encoding of a tuple with position `k` replaced by `z`: the encoding of the entries
before `k`, then the pair `⟨z, ·⟩` around the encoding of the entries after `k`
(`ofFn_update_eq`, `encodeMsgs_append`). -/
theorem encodeMsgs_ofFn_update {N : ℕ} (W : Fin N → List Bool) (k : Fin N) (z : List Bool) :
    Strategy.encodeMsgs (List.ofFn (Function.update W k z)) =
      Strategy.encodeMsgs (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
        pairEncode z (Strategy.encodeMsgs
          (List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩)) := by
  rw [ofFn_update_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]

/-- Chunks that are empty from index `n` on do not contribute: the concatenation over
`range m` equals the one over `range n` for `n ≤ m`. -/
theorem flatMap_range_eq_of_nil (F : ℕ → List Bool) {n m : ℕ} (hnm : n ≤ m)
    (hF : ∀ i, n ≤ i → F i = []) : (List.range m).flatMap F = (List.range n).flatMap F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have h : (List.range d).flatMap (fun a => F (n + a)) = [] :=
    List.flatMap_eq_nil_iff.2 fun x _ => hF _ (Nat.le_add_right n x)
  rw [h, List.append_nil]

/-! ### The splice machines -/

/-- The splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ z ++ suf`. -/
def spliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairFstD y ++ pairSndD (pairSndD y)

/-- The splice pre-processing is polynomial-time. -/
theorem spliceFun_poly : PolyTimeComputable spliceFun :=
  ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    polyTimeComputable_pairFstD).append
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The splice pre-processing on a well-formed argument. -/
@[simp] theorem spliceFun_pairEncode (z pre suf : List Bool) :
    spliceFun (pairEncode z (pairEncode pre suf)) = pre ++ z ++ suf := by
  simp [spliceFun]

/-- The pair-splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ ⟨z, suf⟩`. -/
def pairSpliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairEncode (pairFstD y) (pairSndD (pairSndD y))

/-- The pair-splice pre-processing is polynomial-time. -/
theorem pairSpliceFun_poly : PolyTimeComputable pairSpliceFun :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The pair-splice pre-processing on a well-formed argument. -/
@[simp] theorem pairSpliceFun_pairEncode (z pre suf : List Bool) :
    pairSpliceFun (pairEncode z (pairEncode pre suf)) = pre ++ pairEncode z suf := by
  simp [pairSpliceFun]

/-- **The splice machine**: for an `NUPPT` `D` and polynomially bounded strings `pre n`, `suf n`
there is an `NUPPT` `B` with `D`'s coins computing `D(1^n, pre n ++ y ++ suf n; r)`
(`Complexity.NUPPT.exists_comp` with `spliceFun`, then `Complexity.NUPPT.exists_withAdvice`
hard-wiring `⟨pre n, suf n⟩`). -/
theorem exists_spliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧ ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ y ++ suf n) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp spliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, spliceFun_pairEncode]
  rfl

/-- **The pair-splice machine**: as `exists_spliceRed`, computing
`D(1^n, pre n ++ ⟨y, suf n⟩; r)` (the argument planted as a message of an encoded history). -/
theorem exists_pairSpliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧
      ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ pairEncode y (suf n)) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp pairSpliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, pairSpliceFun_pairEncode]
  rfl

/-! ### The bitwise commitment loop -/

namespace ComLoop

/-- The unary parameter slot `u` of the state word `⟨u, ⟨vs, rs⟩⟩`. -/
def p₁ (w : List Bool) : List Bool := pairFstD w

/-- The remaining value bits `vs` of the state word. -/
def p₂ (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The remaining randomness `rs` of the state word. -/
def p₃ (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The state word `⟨u, ⟨vs, rs⟩⟩`. -/
def st (u vs rs : List Bool) : List Bool := pairEncode u (pairEncode vs rs)

/-- Reading the parameter slot. -/
@[simp] theorem p₁_st (u vs rs : List Bool) : p₁ (st u vs rs) = u := by simp [p₁, st]

/-- Reading the value bits. -/
@[simp] theorem p₂_st (u vs rs : List Bool) : p₂ (st u vs rs) = vs := by simp [p₂, st]

/-- Reading the randomness. -/
@[simp] theorem p₃_st (u vs rs : List Bool) : p₃ (st u vs rs) = rs := by simp [p₃, st]

/-- The projections are polynomial-time. -/
theorem p₁_poly : PolyTimeComputable p₁ := polyTimeComputable_pairFstD

/-- The projections are polynomial-time. -/
theorem p₂_poly : PolyTimeComputable p₂ :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The projections are polynomial-time. -/
theorem p₃_poly : PolyTimeComputable p₃ :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Assembling a state word from three polynomial-time components is polynomial-time. -/
theorem st_poly {f₁ f₂ f₃ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) :
    PolyTimeComputable fun z => st (f₁ z) (f₂ z) (f₃ z) :=
  h₁.pairEncode (h₂.pairEncode h₃)

/-- The evaluators' argument at a state word: `⟨u, rs.take |u|⟩`, i.e. `⟨1^n, r_i⟩` for the
current randomness block. -/
def arg (w : List Bool) : List Bool := pairEncode (p₁ w) ((p₃ w).take (p₁ w).length)

/-- The argument is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` on
`⟨u, rs⟩`). -/
theorem arg_poly : PolyTimeComputable arg := by
  convert p₁_poly.pairEncode
    ((polyTimeComputable_pairTakePoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [arg]

/-- The step: drop the first value bit and the first `|u|` randomness bits. -/
def step (w : List Bool) : List Bool := st (p₁ w) (p₂ w).tail ((p₃ w).drop (p₁ w).length)

/-- The step is polynomial-time (`Complexity.polyTimeComputable_tail`,
`Complexity.polyTimeComputable_pairDropPoly` on `⟨u, rs⟩`). -/
theorem step_poly : PolyTimeComputable step := by
  convert st_poly p₁_poly ((polyTimeComputable_tail.congr fun _ => List.drop_one).comp p₂_poly)
    ((polyTimeComputable_pairDropPoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [step]

/-- One step grows a word by at most four symbols (the pairing overhead; both components
only shrink). -/
theorem length_step_le (w : List Bool) : (step w).length ≤ w.length + 4 := by
  have h₁ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le w
  have h₂ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le (pairSndD w)
  simp only [step, st, length_pairEncode, List.length_tail, List.length_drop, p₁, p₂, p₃]
  omega

/-- The orbit of any word grows at most linearly in the number of rounds. -/
theorem length_iterate_step_le (w : List Bool) (i : ℕ) :
    (step^[i] w).length ≤ w.length + 4 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := length_step_le (step^[i] w)
    omega

/-- The closed form of the orbit from `⟨u, ⟨vs, rs⟩⟩`: after `i` rounds the state word is
`⟨u, ⟨vs.drop i, rs.drop (i · |u|)⟩⟩`. -/
theorem iterate_step (u vs rs : List Bool) (i : ℕ) :
    step^[i] (st u vs rs) = st u (vs.drop i) (rs.drop (i * u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, p₁_st, p₂_st, p₃_st, List.tail_drop, List.drop_drop]
    congr 2
    ring

variable (F H : List Bool → List Bool)

/-- The emission at a state word: nothing once the value bits are exhausted, else the one-bit
commitment `F ⟨u, r_i⟩ ++ [v_i ⊕ H ⟨u, r_i⟩]` of the current value bit with the current block
(Alg-127.a). -/
def emit (w : List Bool) : List Bool :=
  if p₂ w = [] then [] else F (arg w) ++ [xor ((p₂ w).headD false) ((H (arg w)).headD false)]

/-- The emission is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
`polyTimeComputable_isNil`, `polyTimeComputable_headD`, `BinArith.polyTimeComputable_xor`,
`PolyTimeComputable.append`). -/
theorem emit_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (emit F H) := by
  convert polyTimeComputable_ite (polyTimeComputable_isNil.comp p₂_poly)
      (polyTimeComputable_const []) ((hF.comp arg_poly).append
        (BinArith.polyTimeComputable_xor (polyTimeComputable_headD.comp p₂_poly)
      (polyTimeComputable_headD.comp (hH.comp arg_poly)))) using 1
  funext w
  simp [emit]

/-- The loop output: the emissions along the `|x| + 1` rounds from `x`, concatenated. -/
def loopOut (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => emit F H (step^[i] x)

/-- The loop output is polynomial-time (`Complexity.polyTimeComputable_iterateEmit` with the
orbit bound `|x| + 4 |x| = 5 |x|`). -/
theorem loopOut_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (loopOut F H) := by
  unfold loopOut
  refine polyTimeComputable_iterateEmit step_poly (emit_poly F H hF hH) .var (.mul (.const 5) .var)
    fun x i hi => ?_
  have := length_iterate_step_le x i
  simp only [PolyExpr.eval_var] at hi
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- The initial state from the argument `⟨v, r⟩`: `⟨1^{|v|}, ⟨v, padL (|v|²) r⟩⟩` (the
randomness padded or cut to `|v|²` bits, as `padFin` does). -/
def init (w : List Bool) : List Bool :=
  st (List.replicate (pairFstD w).length true) (pairFstD w)
    (EnsembleLemmas.padL ((pairFstD w).length * (pairFstD w).length) (pairSndD w))

/-- The initial state is polynomial-time (`Complexity.polyTimeComputable_unary`,
`EnsembleLemmas.polyTimeComputable_padL`). -/
theorem init_poly : PolyTimeComputable init := by
  convert st_poly (polyTimeComputable_unary.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairFstD (EnsembleLemmas.polyTimeComputable_padL (.mul .var .var)
      polyTimeComputable_pairFstD polyTimeComputable_pairSndD) using 1

/-- The initial state only depends on the two components of the argument. -/
theorem init_eq (w : List Bool) : init w = init (pairEncode (pairFstD w) (pairSndD w)) := by
  simp [init]

/-- Once the value bits are exhausted (round `i ≥ |v|`), the loop emits nothing. -/
theorem emit_init_of_le {v r : List Bool} {i : ℕ} (hi : v.length ≤ i) :
    emit F H (step^[i] (init (pairEncode v r))) = [] := by
  simp [init, iterate_step, emit, List.drop_eq_nil_of_le hi]

/-- At round `i < |v|` the loop emits the one-bit commitment of the bit `v[i]` with the `i`-th
block of the padded randomness: `F ⟨1^n, r_i⟩ ++ [v[i] ⊕ (H ⟨1^n, r_i⟩)[0]]` with
`r_i = blocks n n (padFin (n²) r) i`, `n = |v|` (`EnsembleLemmas.take_drop_ofFn_blocks`). -/
theorem emit_init_of_lt {v r : List Bool} {i : ℕ} (hi : i < v.length) :
    emit F H (step^[i] (init (pairEncode v r))) =
      F (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks v.length v.length
        (padFin (v.length * v.length) r) ⟨i, hi⟩))) ++
      [xor (v.getD i false) ((H (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks
        v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩)))).headD false)] := by
  have hne : v.drop i ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff]
    omega
  have hblock : ((EnsembleLemmas.padL (v.length * v.length) r).drop (i * v.length)).take v.length =
      List.ofFn (EnsembleLemmas.blocks v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩) :=
    EnsembleLemmas.take_drop_ofFn_blocks (padFin (v.length * v.length) r) i hi
  simp only [init, pairFstD_pairEncode, pairSndD_pairEncode, iterate_step, List.length_replicate,
    emit, arg, p₁_st, p₂_st, p₃_st, hne, if_false, hblock, NUPPT.advInput_eq, headD_drop]

end ComLoop

end TCSlib.Cryptography.CommitmentLemmas
