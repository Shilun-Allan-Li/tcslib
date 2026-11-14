# ext-nosrc · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** Two items are open before the PR is marked ready:
- **M1:** a Rule-10 ruling on `FinDist`'s `CoeFun` instance. It is asked of Seyoon.
- **M2:** the formula-docstring landing edit LE-doc. It is in progress.

## Delivery and landing branch

**The delivery**
- **Source:** Codex worker, exchange `a5da5cc3b2f37f8a8540cf74eb2762cd1e2a08d4` (`inbox/fills/ext-nosrc/`).
- **Worker head:** `7aa5cf51` (3 commits on the issue base `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`).
- **Target:** `Randomness.not_isExtractor_effSources`, [PS10, Theorem 183.6]. Brief: `../issued-r1/brief.md`, SHA-256 `30a0e02d…`.
- **Files:**
  - the owned file `Randomness/Extraction.lean`, at 322 lines;
  - new helpers `Randomness/Extraction/Rejection.lean` (481) and `Randomness/Extraction/Sampler.lean` (217);
  - the facade `Randomness.lean`, which gains two imports.
- **The facade imports** are a disclosed scope extension that Seyoon approved (decision log, 2026-11-14). The facade diff is exactly the two lines of the worker's `evidence/scope-request/facade-imports.patch`.

**The landing branch** is `land/pass-shelat-ext-nosrc`.
- **How it was built:** the 3 worker commits were applied with `git am` at the base, with authors kept, then rebased onto records tip `ba0adb6b1a69787805340d06cb5ce9216b6277a0`. The rebase had no conflict. The 7 commits between the base and that tip change only `PassShelatChapter5-8Plan.md` and `briefs/` (`landing/origin-delta-nonbriefs.txt`).
- **Commits:**
  - `6ba3a4ec221deeb40e535bacc1923609554a55c4`, `6fbfa12788b033420a900e56eff183c23b996966` and `a86ad95616fc488db3c75942655b302802ca52ed`, the worker's commits;
  - `653d6c1bd0514ca4225bb92db80a9b7754af60bb`, **LE-width** (tree `cc890fca133c7ebbaa2d925ae31f5c32525b6eb9`). It re-wraps one 102-character statement line of `chooseWord_flatten` (`Sampler.lean:105`) and changes whitespace only.
- **Authorship:** the worker committed under Seyoon's git identity, and that identity is kept.

**The evidence** is `review-evidence.zip`.
- SHA-256 `5bb2454b103f56056303664c41e3913384ec63cd89e2bf8d85e73baf82b3d7a8`, 352 entries.
- Its manifest is `evidence-SHA256SUMS`, and `unzip -Z1` lists exactly the manifest's paths.
- Extracts are in `landing/`, with the full provenance in `landing/PROVENANCE.txt`.

## Checks

**Integrity**
- The top-level `SHA256SUMS` verifies 846/846 and `evidence/SHA256SUMS` 837/837. In both, the delivered paths are exactly the manifest's paths.
- `git am` at the base gives rc 0 and tree `fd59faf0`.
- The 4 changed paths are byte-identical to `src/`.
- The worker's commit hashes cannot be reproduced, because the delivery records no committer metadata. The content is verified independently, so this is recorded only.

**Build**, on the full base tree `$SP/dl-oleans`
- The head modules were built: Rejection, Sampler, Extraction, the `Randomness` facade and root `TCSlib`. All have rc 0 and 0 errors, both before and after LE-width.
- At the final head, all 1201 modules plus 31 PFR modules have rc 0 at the head's source and olean hash.
- `audits/*/Checks` do not import Randomness.
- The tree was then restored to base: all 1199 modules match the base hashes (`landing/restore-base-check.txt`).

**Statements**
- decls2 from base to head: 73 ADDED, 0 CHANGED, 0 REMOVED.
- The target's header and the 7 other pre-existing declarations of `Extraction.lean` are byte-identical (`landing/header-bytes.txt`).
- `touched`: only the target changed, in its body and its sketch.

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`. At the base it also had `sorryAx`.
- All 108 stored constants use subsets of those three (`landing/axioms-summary.txt`).
- Nothing new carries `@[simp]` or is an instance, and there is no new hand-written `abbrev`.

**Admissions:** 21 → 20 in the issued modules; only the target was removed (`landing/sorry-census.txt`).

**Lint:** 216 FAIL / 102 WARN at the base and at the head, with no line differing (`landing/lint-diff.txt` is empty).

**Sizes and widths**
- File lengths: Extraction 322, Rejection 481, Sampler 217, facade 40.
- The one new over-width line is fixed by LE-width.

**Rule 10** (`landing/seal-table.txt`)
- **Strict harness** (the archived Gate 10 harness, which also seals instances):
  - Extraction, Sampler and the facade pass both variants.
  - **Rejection fails A and B: 18 errors in 16 declarations.** This is M1.
- **Harness with `FinDist`'s `CoeFun` instance treated as notation:** all 4 files pass A and B, at the head and at the base.
- **Paired controls** (coercion as notation): 12 probes over `padFin`, `PolyExpr.eval`, `FinDist.uniform`, `Rejection.mixture` and `Rejection.select`. Result: ALL_OK (`landing/ctlcheck.log`, `ctlcheck-le.log`).
- **Strict-control diagnostic:** sealing the instance also breaks the published readers `FinDist.uniform_apply` and `FinDist.coe_mk` when they are used through `p a` (`landing/superseded-DISPOSITION.txt`).
- **Explicit-unfold scan:** 215 items, 0 foreign definitions.

**Content.** The proof follows its sketch.
1. `U_n` is an `n`-source, hence an `(n−2)`-source. Extraction on it forces `q ≥ 1/4`.
2. The rejection sampler runs 10 trials, then a fallback, over 11 blocks of `n` coins. The blocks are read through `FunFamily.blocks`.
3. Its law is the mixture `(1−q)^10 U_n + (1−(1−q)^10) flat(S)`.
4. The flat point mass is at most `1/(2^n q) ≤ 2^{−(n−2)}`.
5. Then `Pr = 1−(1−q)^11 ≥ 1−(3/4)^11 > 1/4`, which contradicts the extractor bound.

The edge cases `n = 0`, `n ≤ 2`, `q = 1` and empty `Ext` output are handled.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| M1 | medium | **Rule 10, coercion.** 16 Rejection declarations read `FinDist`'s `CoeFun` instance `⟨FinDist.prob⟩`. The file mixes `p a` with `p.prob a`, and the strict seal masks the instance. The worker's harness does not mask instances. Base precedent: coercion reads already occur at the base, for example `Games/Probability.dist_apply` at Gates 20 and 21, and the Extractors replay of Gate 06. | **Ruling asked** (2026-11-14). Either treat a `CoeFun` instance whose body is a structure projection as notation, or have `FinDist` publish `coe_eq_prob : p a = p.prob a` and re-point the 16 declarations. |
| M2 | medium | **Policy, formula docstrings.** 44 of the 73 new public declarations have prose-only docstrings (`landing/docaudit.tsv`). | **Landing edit LE-doc**, docstrings only, as in the nm-sim precedent (#297). In progress. |
| 3 | low | 10 linter warnings in `Rejection.lean`: an unused `[Fintype α]` on 4 lemmas (which cascades), 4 unused `simp` arguments, and 2 unnecessary `<;>`. | Follow-up. The fix needs `omit … in` plus cascading edits. |
| 4 | low | `Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`. | Ledger **DL-39**. |
| 5 | low | Generic `FinDist` facts are local to `Rejection`: `sum_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource` and `uniform_probTrue`. The worker requests their promotion. No exact duplicate exists (`landing/duplication-grep.txt`). The nearest relatives are `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map` and `ProbComp.expect_map`, which works on `ProbComp`. | Ledger **DL-39**: promote them to `InformationTheory/FinDist` in a later job, since `FinDist` is frozen for this fill. |
| 6 | info | The worker's commit hashes cannot be reproduced, because no committer metadata is recorded. | Recorded. The content is verified. |
| 7 | info | The two facade imports. | Approved by Seyoon (2026-11-14). |
