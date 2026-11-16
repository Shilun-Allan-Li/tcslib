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
