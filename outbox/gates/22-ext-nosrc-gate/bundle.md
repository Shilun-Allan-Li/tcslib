## ===== briefs/pass-shelat-ch5-8/gates/22-ext-nosrc/pack.md =====

# Gate 22 · No efficient extractor for efficient sources (`ext-nosrc`, Theorem 183.6)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #303](https://github.com/Shilun-Allan-Li/tcslib/pull/303) at
  `e99a6055ff6b24cdf4b25993e83d045bd569028f` (branch `land/pass-shelat-ext-nosrc`, tree
  `962374efbcb153c8f696b96f74aae0cab4a2baff`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `ba0adb6b1a69787805340d06cb5ce9216b6277a0` (the merge base).
  - The fill was issued on `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, the merge of #299.
  - Every commit between the issue base, the PR base and the current records tip touches records only
    (`PassShelatChapter5-8Plan.md` and `briefs/`). The Lean sources of the base are those of the issue base.
- **Commits:** 5.
  - The Codex worker's 3 checkpoint commits (job `ext-nosrc`): `6ba3a4ec221deeb40e535bacc1923609554a55c4`,
    `6fbfa12788b033420a900e56eff183c23b996966`, `a86ad95616fc488db3c75942655b302802ca52ed`. They were applied with
    `git am` and rebased, with authors kept (the worker committed under Seyoon's git identity).
  - Landing edit **LE-width** `653d6c1bd0514ca4225bb92db80a9b7754af60bb`: whitespace only, re-wrapping one
    102-character statement line of `chooseWord_flatten` in `Sampler.lean`.
  - Landing edit **LE-doc** `e99a6055ff6b24cdf4b25993e83d045bd569028f` (the head): formula docstrings for 44 public
    declarations, docstrings only.
- **Scope:** a **proof audit**. The job proves the admitted `Randomness.not_isExtractor_effSources`
  [PS10, Theorem 183.6]. Its statement passed Gate 06 (prong D) and is frozen.
- **Brief:** `fills/ext-nosrc/issued-r1/brief.md` on the records branch (SHA-256 `30a0e02d…`; exchange pack
  `b436d19a`): three checkpoints following the docstring sketch, the owned file plus the helper directory
  `Randomness/Extraction/` only, and the evidence-completeness rule added after G20-01.

## What changed

All paths are under `TCSlib/Cryptography/`. The PR touches 4 Lean files: 2 modified and 2 new
(949 insertions, 6 deletions).

| File | Status | Lines |
|---|---|---:|
| `Randomness/Extraction.lean` | owned, modified | 127 → 339 |
| `Randomness/Extraction/Rejection.lean` | helper, new | 492 |
| `Randomness/Extraction/Sampler.lean` | helper, new | 237 |
| `Randomness.lean` | facade, modified | 38 → 40 |

- **`Extraction.lean`:** the target's proof and sketch, the module docstring (title, `## Contents`,
  `## Main results`) and the target-specific bridges (`uniform_acceptance_lower`, `rejection_mem_effSources`,
  `samplerLaw_rejection`).
- **`Rejection.lean`:** finite rejection laws, `FinDist` pushforward and product facts, and convex mixtures of
  sources.
- **`Sampler.lean`:** the uniform rejection machine, its `11n` coin blocks and its law.
- **`Randomness.lean`:** two imports, `…Extraction.Rejection` and `…Extraction.Sampler`.

The proof follows the sketch (REPORT, review § Content):
1. `U_n` is the law of the uniform PPT that outputs its coins. It is an `n`-source, hence an `(n − 2)`-source.
   Extraction on it forces `q = Pr[Ext(U_n) = 1] ≥ 1/4`.
2. The sampler uses `11n` coins: 10 trial blocks of `n` bits for `Ext(x) = 1`, then the 11th block as the
   fallback. It is built at the fixed `n` by ten applications of the polynomial-time conditional combinator, with
   constant coin polynomial and empty advice. The blocks are read through `FunFamily.blocks`.
3. Its law is the mixture `(1 − q)^{10} U_n + (1 − (1 − q)^{10}) flat(S)`, with `S = {x : Ext(x) = 1}`.
4. Each point of `flat(S)` has mass at most `1/(2^n q) ≤ 2^{−(n−2)}`. Mixtures preserve the bound.
5. `Pr[Ext(X) = 1] = 1 − (1 − q)^{11} ≥ 1 − (3/4)^{11} > 3/4`, which contradicts `1/4`-closeness to `U_1`.

The edge cases are `n = 0, 1, 2`, `q = 1` and an empty `Ext` output (read as `false`).

**Statements:** decls2 from the base to the head gives 73 ADDED, 0 CHANGED, 0 REMOVED. The target's header and
the 7 other pre-existing declarations of `Extraction.lean` are byte-identical.

## Rulings and records in force (2026-11-14)

1. **The two facade imports are an approved scope extension (Seyoon).** The brief froze every file outside the
   owned file and helper directory. The required lint flagged the facade `Randomness.lean` for not importing the
   new helpers, and the worker asked Seyoon in its chat. Seyoon approved exactly those two imports; the decision log
   confirms it. The facade diff is exactly `evidence/scope-request/facade-imports.patch` of the worker
   (`verification.zip`: `worker/scope-request/`). **Not a finding.**
2. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon).** This is
   `FinDist`'s `⟨FinDist.prob⟩`, treated like reducible abbreviations (ruling of 2026-10-26). It closes review item
   M1.
   - The **coe-variant seals are canonical**: there, all 4 files pass A and B at the head, and the 2 pre-existing
     files (`Extraction`, the facade) pass both at the base.
   - The **strict harness** (the archived Gate 10 harness, which also seals instances) is still run and its
     differences are attributed. `Rejection.lean` fails A and B: 18 errors in 16 declarations, all reads of the
     coercion `p a`. `Extraction`, `Sampler` and the facade pass both strict variants.
   - The attribution is the strict-control diagnostic (`superseded/DISPOSITION.txt`): under the strict mask the
     published readers `FinDist.uniform_apply` and `FinDist.coe_mk` also fail when used through `p a`, because
     `p a` elaborates to `CoeFun.coe p a`. So the strict failures come from sealing the notation, not from a read
     of `FinDist.prob`'s definition.
3. **LE-doc is docstrings only** (decision log, the PR #303 row). It is a maintainer landing edit fixing review item
   M2, under the nm-sim precedent (2026-11-13).
   - All 44 hunks lie inside `/-- -/` spans. With the docstrings blanked, the files at `653d6c1b` and `e99a6055`
     are byte-identical.
   - All 81 declaration headers of the 4 files are byte-identical; decls2 from `653d6c1b` is empty.
   - The target's docstring is untouched: it keeps its book-statement first line and its `[PS10, Theorem 183.6]`
     tag.

## What is frozen

- **The target's statement** (quoted in the brief), the 7 other pre-existing declarations of `Extraction.lean`, the
  statement prose and the global simp attributes.
- **Every file outside** `Randomness/Extraction.lean` and `Randomness/Extraction/`, except the two approved facade
  imports. That includes `InformationTheory/FinDist.lean` (which is why the generic `FinDist` facts stay local; see
  DL-39) and `Games/Efficiency.lean` (982 lines, untouched).
- **The landing edits:** LE-width changes whitespace only, and LE-doc changes docstrings only.

## Questions for the audit

**1. Correctness against [PS10, Theorem 183.6]**
- Does the proof establish the frozen statement for every `n`, including `n ≤ 2`, `q = 1` and an empty `Ext`
  output?
- Is the formal witness the book's `X` (sample until `Ext(x) = 1`, give up after 10 tries and output a fresh
  `x ← U_n`)? Is the `11n`-coin machine a uniform PPT in the sense of `effSources`, with its constant coin
  polynomial and empty advice legitimate because the witness is chosen after `n` is fixed?
- Does the final step use the extractor bound correctly: `1 − (3/4)^{11} > 3/4`, against `1/4`-closeness?
- Does the edited target sketch (steps 1–5) describe the delivered proof?

**2. The rejection-sampler law**
- Is `Rejection.law D t` the law of the bounded rejection sampler (`t` trials, then a fallback), and is
  `law_eq_mixture` (`(1 − q)^t U + (1 − (1 − q)^t) flat(S)`, for `q > 0`) correct for every `t`, including
  `q = 1`?
- Is `law_probTrue` (`1 − (1 − q)^{t+1}`) correct?
- Is `samplerLaw_rejection` (the machine's `samplerLaw` equals `Rejection.law … 10`) correct, including the coin
  split through `coinEquiv` and `FunFamily.blocks` at `n = 0`?
- Are `mixture_isSource` and `accepted_flat_isSource` correct, with the mass bound `1/(2^n q) ≤ 2^{−(n−2)}`?

**3. The coercion ruling (Rule 10)**
- Is every strict-harness failure in `Rejection.lean` a read of `FinDist`'s `CoeFun` instance, so that it falls
  under ruling 2? Is there any other read, of `FinDist.prob`'s definition or of another file's definition?
- Do the coe-variant seals cover every touched declaration of the 4 files over the full closure, at the base and
  at the head? Do the paired controls (12 probes over `padFin`, `PolyExpr.eval`, `FinDist.uniform`,
  `Rejection.mixture` and `Rejection.select`; ALL_OK) show that the seals bite?
- Explicit-unfold scan: 215 items, 0 foreign definitions.

**4. The facade imports**
- Is the facade change exactly the two approved import lines, with no other effect (no cycle, no change to what
  the facade's other imports export)?

**5. LE-doc formula accuracy**
- Does each of the 44 new formulas state what its declaration proves or defines (`landing-ledoc/0001-LE-doc.patch`;
  `docaudit-after.tsv` 73/73 OK)? A formula that misstates its declaration is a minor.
- Is LE-doc docstrings only, as ruling 3 records?

**6. Duplication**
- Does any new declaration duplicate a public TCSlib or Mathlib lemma beyond the disclosed items below?
- Is any private lemma of another file copied rather than re-derived from published readers? The worker reports
  **overlap: none**.
- Is any generic fact missing from the promotion list (DL-39)?

## Known dispositions (not findings)

- **DL-39** (duplication ledger, open, deferred): `Rejection.tupleEquiv` restates Mathlib's
  `(Fin.consEquiv _).symm`. The generic `FinDist` facts local to `Rejection.lean` (`sum_map`, `expect_map`,
  `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`,
  `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`) are to be promoted to
  `InformationTheory/FinDist` in a later job, since `FinDist` was frozen for this fill. No exact duplicate exists in
  TCSlib (`landing/duplication-grep.txt`). What you can raise: a copy outside DL-39, or a disagreement with it.
- **The linter warnings:** 10 in `Rejection.lean` (an unused `[Fintype α]` on 4 lemmas, which cascades; 4 unused
  `simp` arguments; 2 unnecessary `<;>`). They are a follow-up, because the fix needs `omit … in` and cascading
  edits. The 2 unused-variable warnings of `Extraction.lean` (`samplerLaw_apply`, `samplerLaw_prob`) are inherited
  from the base. The campaign lint is unchanged (216 FAIL / 102 WARN, no line differs).
- **`tupleEquiv` versus `Fin.consEquiv`:** recorded in DL-39, as above.
- **The worker's commit hashes** (`e0b0d226`, `406330fe`, `7aa5cf51`) cannot be reproduced, because the delivery
  records no committer metadata. The content is verified: `git am` at the base reproduces the 4 delivered files.
- **A slip in `review.md`:** its § Content step 5 reads "`≥ 1−(3/4)^11 > 1/4`". The proof shows
  `(3/4)^{11} < 1/4`, hence `Pr > 3/4`, as the brief, the REPORT and the target sketch state. The review record is
  frozen and is not edited.

## Also check

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`. At the base it also had `sorryAx`.
- All 108 stored constants of the 4 files use subsets of those three (census at `653d6c1b`; LE-doc changes no code).
- Nothing new is `@[simp]` or an instance, and there is no new hand-written `abbrev` (3 generated matchers only).

**Admissions:** 21 → 20 in the 11 issued modules; only the target is removed.

**Sizes and widths:** Extraction 339, Rejection 492, Sampler 237, facade 40 lines; 0 lines over 100 characters
(`source-head.json`).

**Build:** at `653d6c1b`, 1201 modules plus 31 PFR modules with rc 0 at the head's source and olean hashes. At
`e99a6055`, Rejection, Sampler, Extraction, the facade and root `TCSlib` were rebuilt with rc 0 at the head's
source hashes. `audits/*/Checks` do not import `Randomness`.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (M1 ruled, M2 fixed by
  LE-doc).
- **`verification.zip`** (SHA-256 `13b9b09caeacba30b2f2f9eb9f7f7c251fe404d117490519dc14c69a77c32a16`, 43 entries):
  every file the review cites, as byte-identical originals. Its `SHA256SUMS` lists every other entry, and
  `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/ext-nosrc/final-r1/`, SHA-256 `5bb2454b…`, 352 entries) and
    `review-evidence-SHA256SUMS`, its manifest; `unzip -Z1` lists exactly the manifest's paths. It covers:
    - integrity (846/846 and 837/837, `git am` replay);
    - the base and head builds, the full-tree check and the restore to base;
    - decls2, header bytes, `touched` and the docstring audit;
    - the census and axioms;
    - the strict and coe-variant seals at the base and the head, the LE-width re-seals and the superseded strict
      controls;
    - the paired controls;
    - the scan;
    - lint, sizes and the duplication grep;
  - `ledoc-evidence.zip` (SHA-256 `c425d689…`, 53 entries) and `ledoc-evidence-SHA256SUMS`: the LE-doc patch,
    the docstring-only checks, the build at the head, lint and the restore;
  - `landing/` and `landing-ledoc/`: the review's extracts, each a byte copy of an entry of the matching ZIP;
  - `records/`: the issued brief, the duplication ledger and the decision log, at records
    `083d928faf2d1dc109cdd466969f5b1004bf641f`;
  - `worker/scope-request/`: the worker's approval record, request, `facade-imports.patch` and lint logs.
- **The worker's own evidence:** on the exchange at `a5da5cc3b2f37f8a8540cf74eb2762cd1e2a08d4`, under
  `inbox/fills/ext-nosrc/evidence/`. Its `SHA256SUMS` lists 837 files, all delivered.
- **`landing/`:** at the final head.
  - `root-checks.jsonl`: Rejection, Sampler, Extraction, the facade and root `TCSlib` at `e99a6055`, rc 0, each
    `source_sha256` matching `source-head.json` (= `build/results.jsonl` of `ledoc-evidence.zip`).
  - `final-tree-check.txt`: 1201/1201 modules with rc 0 at `653d6c1b`'s source and olean hashes
    (= `final-r1/landing/final-tree-check-head.txt`; LE-doc changes docstrings only).
  - `axioms-head.txt`: the census and target axioms at `653d6c1b` (= `final-r1/landing/axioms-summary.txt`).
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `a5da5cc3`.
- **`pr.diff.txt`:** `git diff` from the base to the head (4 paths, 949 insertions, 6 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 4 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 203 files.

## Findings delivery

Return `gate22-ext-nosrc-findings.md` as a Markdown file in this chat. If you have several evidence files, return
a ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation beyond the approved facade imports.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the coercion
  ruling, an undisclosed copied private lemma, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/22-ext-nosrc/review.md =====

# ext-nosrc · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** Both medium items are closed:
- **M1** by Seyoon's ruling of 2026-11-14: a `CoeFun` instance whose body is a structure projection is notation.
- **M2** by landing edit **LE-doc** `e99a6055ff6b24cdf4b25993e83d045bd569028f` (tree `962374efbcb153c8f696b96f74aae0cab4a2baff`).

The landing head is `e99a6055`, pushed as `land/pass-shelat-ext-nosrc`.

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
| M1 | medium | **Rule 10, coercion.** 16 Rejection declarations read `FinDist`'s `CoeFun` instance `⟨FinDist.prob⟩`. The file mixes `p a` with `p.prob a`, and the strict seal masks the instance. The worker's harness does not mask instances. Base precedent: coercion reads already occur at the base, for example `Games/Probability.dist_apply` at Gates 20 and 21, and the Extractors replay of Gate 06. | **Ruled notation (Seyoon, 2026-11-14):** a `CoeFun` instance whose body is a structure projection is notation, like a reducible abbreviation. Every file passes A and B under this reading. Not a finding. |
| M2 | medium | **Policy, formula docstrings.** 44 of the 73 new public declarations have prose-only docstrings (`landing/docaudit.tsv`). | **Fixed by LE-doc** `e99a6055`. See below. |
| 3 | low | 10 linter warnings in `Rejection.lean`: an unused `[Fintype α]` on 4 lemmas (which cascades), 4 unused `simp` arguments, and 2 unnecessary `<;>`. | Follow-up. The fix needs `omit … in` plus cascading edits. |
| 4 | low | `Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`. | Ledger **DL-39**. |
| 5 | low | Generic `FinDist` facts are local to `Rejection`: `sum_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource` and `uniform_probTrue`. The worker requests their promotion. No exact duplicate exists (`landing/duplication-grep.txt`). The nearest relatives are `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map` and `ProbComp.expect_map`, which works on `ProbComp`. | Ledger **DL-39**: promote them to `InformationTheory/FinDist` in a later job, since `FinDist` is frozen for this fill. |
| 6 | info | The worker's commit hashes cannot be reproduced, because no committer metadata is recorded. | Recorded. The content is verified. |
| 7 | info | The two facade imports. | Approved by Seyoon (2026-11-14). |

## LE-doc · formula docstrings (`e99a6055`)

The evidence is `ledoc-evidence.zip`.
- SHA-256 `c425d6893d8590c476368edb2475939df1e253e6d7160ae5516af8fcd66f8b28`, 53 entries.
- Its manifest is `ledoc-evidence-SHA256SUMS`.
- Extracts are in `landing-ledoc/`.

**What changed**
- 44 docstrings gain a formula: Rejection 15, Sampler 15, Extraction 14.
- The target's docstring is untouched, as instructed. It keeps its book-statement first line and its `[PS10, Theorem 183.6]` tag.

**Checks**
- **Docaudit:** 73/73 new declarations are OK.
- **Docstrings only:**
  - All 44 hunks lie inside `/-- -/` spans.
  - With docstrings blanked, the old and new files are byte-identical.
  - All 81 headers are byte-identical, and decls2 against `653d6c1b` is empty.
- **Widths:** at most 99 characters, by Python `len`.
- **Lengths:** Rejection 492, Sampler 237, Extraction 339 lines.
- **Lint:** FAIL and WARN lines are identical.
- **Build:** Rejection, Sampler, Extraction, the facade and root `TCSlib` all give rc 0 and 0 errors on the full tree. Each module is built at the head's source hash.
- **Restore:** `$SP/dl-oleans` is back at base. A whole-tree file snapshot is byte-identical before and after (`landing-ledoc/tree-check-post.txt`).

## ===== briefs/pass-shelat-ch5-8/gates/22-ext-nosrc/worker-report.md =====

# ext-nosrc · final delivery

The frozen `TCSlib.Cryptography.Randomness.not_isExtractor_effSources` is proved. The complete
owned module and all required checks pass. The only admission removed is the target.

## Provenance and scope

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4`.
Local proof branch: `fill/ext-nosrc`, head `7aa5cf513f964ddfe32c1282673329f2187b42fc`. It has never been pushed.
Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`; all seven pack checksums and
all 201 issued source hashes passed. Lean pin: 4.25.0. Mathlib pin:
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

Only the owned Extraction module and its two permitted helper modules were initially edited.
The required lint exposed two direct-import findings in frozen `Randomness.lean`. Seyoon
explicitly approved exactly those two imports in this chat. The approval, exact two-line patch,
original findings and successful overlay are preserved under `evidence/scope-request/`.
No other frozen source file is changed. All original non-target declarations and their prose,
the target signature/statement prose and global simp attributes are preserved.

| Changed or new source | Lines |
|---|---:|
| `TCSlib/Cryptography/Randomness.lean` | 40 |
| `TCSlib/Cryptography/Randomness/Extraction.lean` | 322 |
| `TCSlib/Cryptography/Randomness/Extraction/Rejection.lean` | 481 |
| `TCSlib/Cryptography/Randomness/Extraction/Sampler.lean` | 216 |

## Proof and sketch changes

At the fixed parameter n, the uniform PPT outputs its n coin bits. Its law is U_n, an n-source
and hence an (n−2)-source. Assuming extraction yields q≥1/4 for the first output bit on U_n.
The uniform rejection machine uses exactly 11n coins: ten independent n-bit trial blocks and
an eleventh fallback. Ten applications of the published polynomial-time conditional combinator
prove efficiency. Its constant coin polynomial is legitimate because the witness is chosen
after fixing n; it has empty advice at every activation parameter.

A generic finite-law calculation identifies its distribution with
`(1−q)^10 U_n + (1−(1−q)^10) flat(S)`. Uniform is an (n−2)-source. Each flat-source point has
mass at most `1/(2^n q) ≤ 4/2^n = 2^(-(n−2))`, so the flat component is one too. Convex mixtures
preserve that bound. The exact acceptance probability is `1−(1−q)^11`, which is at least
`1−(3/4)^11 > 3/4`, contradicting the assumed quarter-closeness to a fair bit.

The formulas work unchanged for n=0,1,2 and q=1; division is only by positive q, never by 1−q.
An empty extractor output reads false through padFin and is already contradicted by q≥1/4.
The canonical coin/block equivalence proves the exact 11n split, including n=0.

The owned module drops the statement-phase title, updates Main results, adds Contents and
updates sketch step 3 to describe the checked finite conditional construction. The frozen
statement and its mathematical meaning are unchanged.

## Declarations, reuse and promotion requests

The final three proof modules contain 108 stored constants,
versus 10 at base: 98
new stored constants, including compiler-generated definitions. Full names, module ownership
and every axiom set are in `evidence/logs/declaration-inventory.json` and the raw census logs.
The approved facade contains zero stored constants, verified by its separate censuses.

`evidence/rejection-review.md` lists the public probability/expectation, pushforward/product,
tuple, rejection-law and convex-mixture declarations for promotion to the InformationTheory
and sampling layers. `evidence/sampler-review.md` lists the machine/list promotion requests;
in particular `take_poly` belongs in ClassNP/PolyTimePrefix and the bounded sampler interface
can be promoted to a shared sampler layer. `uniform_one_probTrue` is a probability-layer
promotion request, and `uniform_card_div_quarter` is a bit-source entropy arithmetic request.
The target-specific membership and machine-law bridges stay with Extraction. The complete
uniform-machine family and an existing block-reader relocation request are also listed in
`evidence/promotion-requests.md`, which consolidates all promotion requests.

Searches are recorded in those reviews and `evidence/logs/rejection-duplication-search.log`.
Public lemmas/readers were imported and used. **Overlap: none.** No private foreign proof was
copied or re-derived from its implementation. No missing-reader request remains.

## Environment and bootstrap

Preflight raw evidence is `evidence/logs/preflight.log`: Darwin/macOS, 12 logical CPUs,
19,327,352,832 physical bytes (18 GiB), native memory-pressure headroom estimate 8,890,582,302
bytes and APFS available space 273,209,647,104 bytes. The 4 GiB memory and 12 GiB disk floors
passed. Linux nproc/proc/cgroups and GNU df flags are unavailable on this host; their failed
queries and native sysctl/vm_stat/memory_pressure/statvfs/mount alternatives are explicit.
All clone, scratch and olean directories are disk-backed. No dependency tree or another
session's object store was copied, merged, moved or reused.

All present packages match the manifest. The package verifier's final line is
`PACKAGES MATCH: all present packages match manifest`. doc-gen4, UnicodeBasic, BibtexQuery and
MD4Lean are ABSENT and are not imported by the issued order. Only the 80 supplied Mathlib roots
were requested. The narrowed cache command exited 0 without failed downloads: no files needed
downloading and 2,125 files decompressed. The shared archive store already contained 32,667
files totaling 1,595,387,830 bytes, of unverified prior origin; these were not downloaded by
this session. The zero-size olean scan was empty and the root-import probe passed.

Bootstrap first checked the owned module's 32 initial prerequisites, then the additional 43
prerequisites for the sampler and the new helpers, always in dependency order. A full 203-module
pass then completed the remaining bootstrap (its historical logs are named sweep). A separate
203-module final sweep follows that completed bootstrap; its logs are named final-sweep. Development
errors and corrected successful rechecks are preserved. No project lake build or unfiltered cache get
was run. The cache tool's expected internal package build is allowed by the addendum. Every module/probe uses scripts/lean_check_tree.sh, one module per invocation, with
start/end time and native maximum-memory output. All Python commands use python3 -I.

Seyoon temporarily overrode host concurrency and then clarified a cap of three Lean jobs
across the whole Mac. The scheduler counts actual Lean executables before launching its one
job. It also honored the authorized reservation for dl-crh's bootstrap, releasing that reservation
after a read-only status confirmed the requesting chat had reached checkpoint packaging. External jobs sometimes
occupied or exceeded the cap, so this fill waited. The scheduler was deliberately restarted at
a completed module boundary to honor the reservation; only its Python controller was signaled,
no Lean check was interrupted. The verified completed prefix and all raw logs were preserved.
See concurrency-override.txt, resource-reservation.json and sweep-scheduler-reservation.log.

## Completed checks

The owned theorem module passed before the final sweep. The completed first full pass was
used as bootstrap, and a separate final sweep ran after all prerequisites existed, satisfying
the addendum sequencing requirement. Both passes have zero errors. The supplied 201-module order plus
two helpers gives 203 successful per-module checks, zero errors. The stable topological order
places Samples before Rejection, then Sampler before Extraction, preserving all supplied
modules and satisfying the new import edges. `admissions-comparison.json` records 21 base
admissions and 20 final admissions: exactly not_isExtractor_effSources removed, none added.
The current facade, including the approved imports, is checked in that sweep.

The target's axioms are exactly `Classical.choice`, `Quot.sound`, `propext`. Every stored
constant in all changed/new files has only a subset of these axioms. The facade's stored set
is empty. The raw censuses, probes, manifests and summaries are included.

Both whole-file seal variants pass for every changed/new file at base where present and at
final. Variant A exempts PolyExpr.eval as notation; variant B seals it. Full foreign TCSlib
import closures include definitions, instances, matchers, splitters and projections. Only
validated actually reducible abbreviation notation is exempted in both variants; semireducible
compiler-generated definitions remain sealed. Every requested name/home and active seal is
verified at installation and EOF. Rejection does not import PolyExpr.eval, so its A/B sets are
both 18 definitions; the other files and the eval controls test the eval distinction. No source
declaration fails any completed whole-file seal.

| Survey | Whole-file seal | Requested definitions | Errors |
|---|---|---:|---:|
| base-r2 | `SealA_Extraction` | 608 | 0 |
| base-r2 | `SealB_Extraction` | 609 | 0 |
| final | `SealA_Extraction` | 1046 | 0 |
| final | `SealB_Extraction` | 1047 | 0 |
| final | `SealA_Rejection` | 18 | 0 |
| final | `SealB_Rejection` | 18 | 0 |
| final | `SealA_Sampler` | 1034 | 0 |
| final | `SealB_Sampler` | 1035 | 0 |
| facade-base | `FacadeSealA` | 3365 | 0 |
| facade-base | `FacadeSealB` | 3366 | 0 |
| facade-final | `FacadeSealA` | 3382 | 0 |
| facade-final | `FacadeSealB` | 3383 | 0 |

The base facade uses the original Extraction snapshot, not its final olean; every other
foreign source is byte-identical to the pinned base. Both facade censuses explicitly verify
zero stored constants. Its controls reuse hash-verified matching sources/logs/results from
the completed control surveys. Every paired negative control passes unsealed and fails
exactly once sealed. The eval control passes in A and fails exactly once in B; reader controls
pass under both variants. Invalid early collector/preparation attempts are retained separately, including the quoted
snapshot-header parser repair used for the facade;
no dependent Lean seal was run against a failed census.

The census-backed explicit scan finds zero foreign-definition tactic rule heads across 92
argument lists. Its five nested lexical matches are ordinary theorem parameters or local
name shadowing, reviewed explicitly. Source scans and whole-file seals provide independent
evidence; lexical limitations are documented. The facade has imports only, no tactic bodies.

Required command: `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`.
Base and approved final each have 216 existing FAIL findings and 102 WARN: **zero new FAIL**.
The raw initial two-finding regression and the approved repair are both preserved.

The complete three-patch series replays at the issue base and reproduces all four src files
byte-for-byte (`patch-reproduction.log`). Full-library landing checks under TCSlib and
audits/pass-shelat/Checks remain the maintainer's landing step, as specified by the brief.

## Delivery and evidence completeness

Checkpoint 1: a0c36ef90. Checkpoint 2: dfec1f17d. Checkpoint 3: a2c2e1b2c. The final delivery
changes only inbox/fills/ext-nosrc on the exchange; every push is preceded by pull --rebase and
no force push is used. A checkpoint push race was resolved by rebasing and retrying.
The campaign proof branch stays local; maintainer landing is through a PR for Seyoon's approval.

patches contains the entire format-patch series from the pinned base; src contains its exact
final files. evidence contains every tool, probe/control/seal source, request/import manifest,
raw log and results.jsonl named by its SHA256SUMS. All development failures and successful
repairs are retained. The payload verifier checks that manifest paths are exactly delivered
paths and every digest matches. The chat ZIP has ext-nosrc/ at its root and the same payload.

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

## ===== briefs/pass-shelat-ch5-8/fills/ext-nosrc/issued-r1/brief.md =====

# Codex fill · no efficient one-bit extractor for efficient sources (`not_isExtractor_effSources`, Theorem 183.6)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `ext-nosrc`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `not_isExtractor_effSources` of [PS10, Theorem 183.6] in `TCSlib/Cryptography/Randomness/Extraction.lean`. The
statement passed Gate 06 (prong D, chapters 5–8 statements) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/ext-nosrc` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/ext-nosrc/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill ext-nosrc: checkpoint N` and `fill ext-nosrc: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `ext-nosrc/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem not_isExtractor_effSources (Ext : List Bool → List Bool) (hExt : PolyTimeComputable Ext)
    (n : ℕ) :
    ¬ IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n) := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Randomness`. There are no section variables. `effSources k n` is the set of laws `samplerLaw S n` of uniform PPT samplers that are `k(n)`-sources, `extBit Ext n` is the first output bit, and `IsExtractor` is the `ε`-closeness to `U_1` for every source of the class (`InformationTheory/Extractors.lean`).

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `samplerLaw`, `samplerLaw_apply`, `samplerLaw_prob`, `effSources_iff`, `extBit_eq` | owned file |
| `IsExtractor` and its readers, `abs_probTrue_sub_le_statDist` | `InformationTheory/Extractors.lean` |
| `FinDist.IsSource`, `isSource_uniform`, `IsSource.mono` (`Entropy.lean:154`) | `InformationTheory/Entropy.lean` |
| `FinDist` laws (`uniform`, `map`, `prob`), statistical distance | `InformationTheory/FinDist.lean`, `StatisticalDistance.lean` |
| `polyTimeComputable_ite`, `polyTimeComputable_iterateFind`; `NUPPT.ofPolyTimeUniform` and its `runAt`/uniform readers | `Complexity/ClassNP/PolyTimePairing.lean`, `Complexity/Randomized/Repetition.lean`, `Asymptotic/Adversary.lean` |
| `padFin`, `coinBlock`, `FunFamily.blocks`, `Foundations/BitLists` | `Games/BitCodec.lean`, `Asymptotic/Adversary.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the uniform witness (sketch steps 1–2).** Show that `U_n` is `samplerLaw` of the uniform PPT that outputs its coins and is an `(n − 2)`-source. If `extBit Ext n` is not `1/4`-close to `U_1` on it, conclude. Otherwise derive `q = Pr[Ext(U_n) = 1] ≥ 1/4`. Send this checkpoint.
2. **Checkpoint 2 · the rejection sampler (sketch steps 3–4).** Build the sampler with `11n` coins: try up to 10 `n`-bit blocks for `Ext(x) = 1`, else output the 11th block. Prove it is a uniform PPT, compute its law as the mixture `(1 − q)^{10} U_n + (1 − (1 − q)^{10}) flat(S)`, and show both components, hence the mixture, are `(n − 2)`-sources. Send this checkpoint.
3. **Final · the bound (sketch step 5).** `Pr[Ext(X) = 1] = 1 − (1 − q)^{11} ≥ 1 − (3/4)^{11} > 3/4`, so the distance from `U_1` exceeds `1/4`.

Check the edge cases: small `n` (`n = 0, 1, 2`, where `n − 2 ≤ 0` and `S` may be all or nothing); `q = 1`; `Ext` outputs of length `0` (`padFin 1` reads `false`); the `11n` coin split.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Randomness/Extraction.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Randomness/Extraction/`. The owned file imports them precisely and
  gets a `## Contents` list.
- **Size.** Keep every file below 1000 lines.
- **Frozen.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines and must be split before it grows. Do not add to it.
  - If a lemma belongs in an existing file, put it in your helper module and list it as a promotion request.
  - If a reader of another file's definition is missing, escalate: record the exact obligation and the reader you
    need, and push a checkpoint.
- **Parallel fills.** Four Codex fills (`ext-nosrc`, `dl-crh`, `hash-sign`, `lamport`) and one Claude fill
  (`cca2-ett`) run from the same base. Edit only your own owned file and helper directory.
- **Duplication (binding).**
  - Do not copy public lemmas: import them.
  - Do not copy private lemmas of another file. If you need one, re-derive it from published readers in your helper
    module, disclose it in `REPORT.md` as **"overlap: <file> <item>"**, and keep its statement general.
  - Any other generic probability, machine or list fact goes on your promotion list. Grep first, and report the
    searches.
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global simp
  attributes.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial
  (policy §3). Add no `@[simp]`. A new public `abbrev` needs an `_eq`/`_iff` lemma.
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections. Your helper modules count as foreign to each other and to the owned file. The owned file's
  definitions are foreign to your helpers.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` (201 modules) and the narrow `roots.txt` (80), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Never run
  `lake build` or an unfiltered cache get. Run Python as `python3 -I`. Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (21 declarations in 11 modules). The only change
    must be the removal of `not_isExtractor_effSources`.
- **Axioms.**
  - Print the axioms of `not_isExtractor_effSources`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final, and report every failing declaration.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`. It must show no new FAIL.
- **Report.** Give:
  - the base and the target's status;
  - the changed files and the sketch edits;
  - the new declarations;
  - the promotion and reader requests;
  - every "overlap" item;
  - the evidence.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**

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
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). |

## ===== briefs/pass-shelat-ch5-8/gates/22-ext-nosrc/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Randomness.lean b/TCSlib/Cryptography/Randomness.lean
index 9020b6d8a..a2e2c484e 100644
--- a/TCSlib/Cryptography/Randomness.lean
+++ b/TCSlib/Cryptography/Randomness.lean
@@ -3,6 +3,8 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Randomness.Extraction
+import TCSlib.Cryptography.Randomness.Extraction.Rejection
+import TCSlib.Cryptography.Randomness.Extraction.Sampler
 import TCSlib.Cryptography.Randomness.Learning
 import TCSlib.Cryptography.Randomness.BPPBridge
 import TCSlib.Cryptography.Randomness.Derandomization
diff --git a/TCSlib/Cryptography/Randomness/Extraction.lean b/TCSlib/Cryptography/Randomness/Extraction.lean
index 77cd11f44..f7bf668c8 100644
--- a/TCSlib/Cryptography/Randomness/Extraction.lean
+++ b/TCSlib/Cryptography/Randomness/Extraction.lean
@@ -5,13 +5,15 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.InformationTheory.Entropy
 import TCSlib.InformationTheory.Extractors
 import TCSlib.Cryptography.Asymptotic.Adversary
+import TCSlib.Cryptography.Randomness.Extraction.Rejection
+import TCSlib.Cryptography.Randomness.Extraction.Sampler
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# No efficient one-bit extractor for efficient sources (statement phase)
+# No efficient one-bit extractor for efficient sources
 
 [PS10, Theorem 183.6]: let `C` be the set of all efficiently computable `(n − 2)`-sources on
 `{0,1}^n`; then there is no 1-bit `1/4`-extractor for `C`.
@@ -38,6 +40,11 @@ because `Ext` is. And `Pr[Ext(X) = 1] ≥ 1 − (3/4)^{10} > 0.9`, so `Ext(X)` i
   trivial, since every distribution is a `(n − 2)`-source there (a point mass is a witness); the
   content is at `n ≥ 3`.
 
+## Contents
+
+* `Randomness.Extraction.Rejection`: finite rejection laws and source-preserving mixtures.
+* `Randomness.Extraction.Sampler`: the uniform machine and its consecutive coin blocks.
+
 ## Main definitions
 
 * `Randomness.samplerLaw`: the law of a machine's `n`-bit output.
@@ -46,8 +53,8 @@ because `Ext` is. And `Pr[Ext(X) = 1] ≥ 1 − (3/4)^{10} > 0.9`, so `Ext(X)` i
 
 ## Main results
 
-* `Randomness.not_isExtractor_effSources` (Thm 183.6, stated; a `sorry` under the source's
-  sketch).
+* `Randomness.not_isExtractor_effSources` (Thm 183.6): no efficient one-bit extractor for
+  efficiently samplable `(n−2)`-sources, proved by bounded rejection sampling.
 
 ## References
 
@@ -102,6 +109,188 @@ def extBit (Ext : List Bool → List Bool) (n : ℕ) : (Fin n → Bool) → (Fin
 theorem extBit_eq (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool) :
     extBit Ext n x = padFin 1 (Ext (List.ofFn x)) := rfl
 
+/-- The uniform sampler at the fixed width `n` outputs its `n` coin bits and has no advice:
+`(uniformSampler n).runAt n [] r = List.ofFn r` and `(uniformSampler n).coins = .const n`. -/
+noncomputable def uniformSampler (n : ℕ) : NUPPT :=
+  NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)
+
+/-- The uniform sampler uses the constant coin polynomial `n`:
+`(uniformSampler n).coins = .const n`. -/
+theorem uniformSampler_coins (n : ℕ) : (uniformSampler n).coins = .const n :=
+  NUPPT.coins_ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)
+
+/-- The uniform sampler has empty advice at every activation parameter:
+`(uniformSampler n).Uniform`, i.e. `∀ m, (uniformSampler n).advice m = []`. -/
+theorem uniformSampler_uniform (n : ℕ) : (uniformSampler n).Uniform :=
+  NUPPT.ofPolyTimeUniform_uniform polyTimeComputable_pairSndD (.const n)
+
+/-- The uniform sampler returns the encoding of its coin vector:
+`(uniformSampler n).runAt n [] r = List.ofFn r`. -/
+theorem uniformSampler_runAt (n : ℕ) (r : (uniformSampler n).Coins n) :
+    (uniformSampler n).runAt n [] r = List.ofFn r := by
+  rw [NUPPT.runAt_eq]
+  change (NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)).runAtL
+    n [] (List.ofFn r) = _
+  rw [NUPPT.runAtL_ofPolyTimeUniform, pairSndD_pairEncode]
+
+/-- The coins of the uniform sampler are canonically the `n`-bit vectors:
+`(uniformSampler n).Coins n ≃ (Fin n → Bool)`. -/
+noncomputable def uniformSamplerCoins (n : ℕ) :
+    (uniformSampler n).Coins n ≃ (Fin n → Bool) :=
+  (NUPPT.coinsEquivPoly (uniformSampler_coins n) n).trans
+    (Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool))
+
+/-- The canonical uniform-sampler coin equivalence is the composition of the published
+coin-polynomial identification with the constant-polynomial width equality:
+`uniformSamplerCoins n = e₁.trans e₂`, where `e₁ = NUPPT.coinsEquivPoly (uniformSampler_coins n) n`
+and `e₂ = Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool)`. -/
+theorem uniformSamplerCoins_eq (n : ℕ) : uniformSamplerCoins n =
+    (NUPPT.coinsEquivPoly (uniformSampler_coins n) n).trans
+      (Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool)) := rfl
+
+/-- The uniform sampler's coin equivalence preserves the encoded word:
+`List.ofFn (uniformSamplerCoins n r) = List.ofFn r`. -/
+theorem uniformSamplerCoins_ofFn (n : ℕ) (r : (uniformSampler n).Coins n) :
+    List.ofFn (uniformSamplerCoins n r) = List.ofFn r := by
+  rw [uniformSamplerCoins, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
+    NUPPT.coinsEquivPoly_ofFn]
+
+/-- The law of the sampler that returns its coins is the uniform law on `n`-bit strings:
+`samplerLaw (uniformSampler n) n = U_n`.
+The coin equivalence preserves encodings, and a bijection preserves uniformity. -/
+theorem samplerLaw_uniformSampler (n : ℕ) :
+    samplerLaw (uniformSampler n) n = FinDist.uniform (Fin n → Bool) := by
+  have hread : (fun r : (uniformSampler n).Coins n =>
+      padFin n ((uniformSampler n).runAt n [] r)) = uniformSamplerCoins n := by
+    funext r
+    rw [uniformSampler_runAt, ← uniformSamplerCoins_ofFn n r, padFin_ofFn]
+  rw [samplerLaw, hread]
+  exact Rejection.map_uniform_equiv (uniformSamplerCoins n)
+
+/-- Uniform `n`-bit strings form an efficiently samplable `(n−2)`-source:
+`U_n ∈ effSources (fun n => n - 2) n`. -/
+theorem uniform_mem_effSources (n : ℕ) :
+    FinDist.uniform (Fin n → Bool) ∈ effSources (fun n => (n : ℝ) - 2) n := by
+  have hu : FinDist.IsSource (n : ℝ) (FinDist.uniform (Fin n → Bool)) := by
+    simpa [Fintype.card_bool, Fintype.card_fin, Real.logb_pow] using
+      (FinDist.isSource_uniform (α := Fin n → Bool))
+  exact (effSources_iff _ _ _).2
+    ⟨uniformSampler n, uniformSampler_uniform n, (samplerLaw_uniformSampler n).symm,
+      hu.mono (by linarith)⟩
+
+/-- The first output bit read by `extBit` is the head of the extractor's output,
+with `false` for an empty output: `extBit Ext n x 0 = (Ext (List.ofFn x)).headD false`. -/
+theorem extBit_zero (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool) :
+    extBit Ext n x 0 = (Ext (List.ofFn x)).headD false := by
+  rw [extBit_eq, padFin_apply]
+  cases Ext (List.ofFn x) <;> rfl
+
+/-- A uniform one-bit word has its first bit true with probability `1/2`:
+`Pr_{U_1}[fun x => x 0] = 1/2`. -/
+theorem uniform_one_probTrue :
+    (FinDist.uniform (Fin 1 → Bool)).probTrue (fun x => x 0) = 1 / 2 := by
+  classical
+  rw [FinDist.probTrue_eq]
+  have hs : (Finset.univ : Finset (Fin 1 → Bool)).filter (fun x => x 0 = true) =
+      {fun _ => true} := by
+    ext x
+    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
+    constructor
+    · intro h
+      funext i
+      have hi : i = 0 := Subsingleton.elim _ _
+      simpa only [hi] using h
+    · rintro rfl
+      rfl
+  rw [hs, Finset.sum_singleton, FinDist.uniform_apply]
+  norm_num
+
+/-- If the candidate extractor succeeds on every efficient `(n−2)`-source, then its first
+bit on the uniform source is true with probability at least `1/4`:
+`IsExtractor (effSources (fun n => n - 2) n) (1/4) (extBit Ext n) →
+1/4 ≤ Pr_{U_n}[fun x => extBit Ext n x 0]`.
+The uniform source is efficient, so its output is within `1/4` of a fair bit. -/
+theorem uniform_acceptance_lower (Ext : List Bool → List Bool) (n : ℕ)
+    (h : IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n)) :
+    1 / 4 ≤ (FinDist.uniform (Fin n → Bool)).probTrue (fun x => extBit Ext n x 0) := by
+  have hclose := (isExtractor_iff.1 h) _ (uniform_mem_effSources n)
+  have hb := (abs_probTrue_sub_le_statDist
+    ((FinDist.uniform (Fin n → Bool)).map (extBit Ext n))
+    (FinDist.uniform (Fin 1 → Bool)) (fun x => x 0)).trans
+      (epsClose_iff_statDist_le.1 hclose)
+  rw [Rejection.probTrue_map, uniform_one_probTrue] at hb
+  have hl := (abs_le.1 hb).1
+  linarith
+
+/-- The bounded rejection machine's law at width `n` is the finite first-success law
+on `t` trials and an independent uniform fallback:
+`samplerLaw (RejectionSampler.machine hExt n t) n = Rejection.law D t`, where
+`D a = (Ext (List.ofFn a)).headD false`.
+
+**Proof sketch.** Its coin equivalence followed by the canonical block equivalence is a
+bijection onto independent uniform blocks. The machine reader identifies its output with
+the typed selector, whose pushforward is the rejection law. -/
+theorem samplerLaw_rejection {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t : ℕ) :
+    samplerLaw (RejectionSampler.machine hExt n t) n =
+      Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t := by
+  let D := fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false
+  let e := (RejectionSampler.coinEquiv hExt n t n).trans (FunFamily.blocks (t + 1) n)
+  have hread : (fun r : (RejectionSampler.machine hExt n t).Coins n =>
+      padFin n ((RejectionSampler.machine hExt n t).runAt n [] r)) =
+      (fun r => Rejection.select D t (e r)) := by
+    funext r
+    rw [RejectionSampler.machine_runAt, ← RejectionSampler.coinEquiv_ofFn hExt n t n r,
+      RejectionSampler.chooseWord_blocks, padFin_ofFn]
+    rfl
+  rw [samplerLaw, hread,
+    ← Rejection.map_map (FinDist.uniform ((RejectionSampler.machine hExt n t).Coins n))
+      e (Rejection.select D t), Rejection.map_uniform_equiv e]
+  exact Rejection.select_uniform_law D t
+
+/-- Dividing a uniform `n`-bit point mass by `1/4` gives the exact `(n−2)`-source bound,
+including `n=0,1,2`: `4 / 2^n = 2^(-(n-2))`. -/
+theorem uniform_card_div_quarter (n : ℕ) :
+    (Fintype.card (Fin n → Bool) : ℝ)⁻¹ / (1 / 4) =
+      (2 : ℝ) ^ (-((n : ℝ) - 2)) := by
+  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
+    Nat.cast_ofNat]
+  rw [show -((n : ℝ) - 2) = 2 - (n : ℝ) by ring,
+    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
+  norm_num
+  ring
+
+/-- When uniform acceptance is at least `1/4`, ten rejection trials and a fresh fallback
+produce an efficiently samplable `(n−2)`-source:
+`1/4 ≤ Pr_{U_n}[D] → Rejection.law D 10 ∈ effSources (fun n => n - 2) n`, where
+`D a = (Ext (List.ofFn a)).headD false`.
+
+**Proof sketch.** The accepted flat source has point mass at most `1/(2^n q) ≤ 4/2^n`,
+so it and the uniform law are `(n−2)`-sources. The exact convex mixture identity preserves
+that bound, and the uniform machine realizes the mixture with `11n` coins. -/
+theorem rejection_mem_effSources {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n : ℕ)
+    (hq : 1 / 4 ≤ (FinDist.uniform (Fin n → Bool)).probTrue
+      (fun a => (Ext (List.ofFn a)).headD false)) :
+    Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) 10 ∈
+      effSources (fun n => (n : ℝ) - 2) n := by
+  let D := fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false
+  have hqpos : 0 < (FinDist.uniform (Fin n → Bool)).probTrue D := by
+    dsimp only [D]
+    linarith
+  have hbound : (Fintype.card (Fin n → Bool) : ℝ)⁻¹ /
+      (FinDist.uniform (Fin n → Bool)).probTrue D ≤ (2 : ℝ) ^ (-((n : ℝ) - 2)) := by
+    calc _ ≤ (Fintype.card (Fin n → Bool) : ℝ)⁻¹ / (1 / 4) :=
+        div_le_div_of_nonneg_left (by positivity) (by norm_num) hq
+      _ = _ := uniform_card_div_quarter n
+  obtain ⟨_, _, _, hU⟩ := (effSources_iff _ _ _).1 (uniform_mem_effSources n)
+  have hflat := Rejection.accepted_flat_isSource D (Rejection.accepted_nonempty D hqpos)
+    ((n : ℝ) - 2) hbound
+  exact (effSources_iff _ _ _).2
+    ⟨RejectionSampler.machine hExt n 10, RejectionSampler.machine_uniform hExt n 10,
+      (samplerLaw_rejection hExt n 10).symm,
+      Rejection.law_isSource D hqpos 10 ((n : ℝ) - 2) hU hflat⟩
+
 /-- **Theorem 183.6: no efficient `1`-bit `1/4`-extractor for efficient `(n − 2)`-sources**
 [PS10, Theorem 183.6]: for every polynomial-time `Ext` and every `n`, `Ext` is not a
 `1/4`-extractor for the efficiently samplable `(n − 2)`-sources on `{0,1}^n`.
@@ -112,8 +301,9 @@ theorem extBit_eq (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool)
    it, `U_n` is the witness.
 2. Otherwise `q = Pr[Ext(U_n) = 1] ≥ 1/4`, so `S = {x : Ext(x) = 1}` has `|S| ≥ 2^{n−2}`.
 3. The sampler `X` with `11n` coins tries up to 10 `n`-bit blocks for `Ext(x) = 1`, else outputs
-   the 11th block. It is a uniform PPT because `Ext` is polynomial-time (`polyTimeComputable_ite`,
-   `polyTimeComputable_iterateFind`).
+   the 11th block. At this fixed `n`, ten applications of the polynomial-time conditional
+   combinator construct the sampler with constant coin polynomial `11n` and empty advice.
+   The canonical block equivalence identifies its coins with eleven independent uniform blocks.
 4. Its law is the mixture `(1 − q)^{10} U_n + (1 − (1 − q)^{10}) flat(S)` (rejection sampling).
    Both components are `(n − 2)`-sources, and min-entropy is preserved by mixtures (each point has
    probability at most `2^{−(n−2)}`).
@@ -122,6 +312,28 @@ theorem extBit_eq (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool)
 theorem not_isExtractor_effSources (Ext : List Bool → List Bool) (hExt : PolyTimeComputable Ext)
     (n : ℕ) :
     ¬ IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n) := by
-  sorry
+  intro h
+  have hq := uniform_acceptance_lower Ext n h
+  simp only [extBit_zero] at hq
+  have hsource := rejection_mem_effSources hExt n hq
+  have hclose := (isExtractor_iff.1 h) _ hsource
+  have hb := (abs_probTrue_sub_le_statDist
+    ((Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) 10).map
+      (extBit Ext n))
+    (FinDist.uniform (Fin 1 → Bool)) (fun x => x 0)).trans
+      (epsClose_iff_statDist_le.1 hclose)
+  rw [Rejection.probTrue_map, uniform_one_probTrue] at hb
+  simp only [extBit_zero] at hb
+  rw [Rejection.law_probTrue] at hb
+  have hq1 := Rejection.probTrue_le_one (FinDist.uniform (Fin n → Bool))
+    (fun a => (Ext (List.ofFn a)).headD false)
+  have hpow :
+      (1 - (FinDist.uniform (Fin n → Bool)).probTrue
+        (fun a => (Ext (List.ofFn a)).headD false)) ^ 11 ≤ (3 / 4 : ℝ) ^ 11 :=
+    pow_le_pow_left₀ (by linarith) (by linarith) 11
+  have hnum : (3 / 4 : ℝ) ^ 11 < 1 / 4 := by norm_num
+  have hu := (abs_le.1 hb).2
+  norm_num only [Nat.reduceAdd] at hu
+  linarith
 
 end TCSlib.Cryptography.Randomness
diff --git a/TCSlib/Cryptography/Randomness/Extraction/Rejection.lean b/TCSlib/Cryptography/Randomness/Extraction/Rejection.lean
new file mode 100644
index 000000000..397b447bb
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Extraction/Rejection.lean
@@ -0,0 +1,492 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.InformationTheory.Samples
+import TCSlib.InformationTheory.Entropy
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Finite rejection sampling
+
+The first accepted point among `t` independent trials is returned; a final independent point
+is returned when all trials fail. The resulting law and its acceptance probability are computed
+from the published finite-distribution readers.
+
+## Main definitions
+
+* `Rejection.select`: the first accepted point among the first `t` entries, otherwise entry `t`.
+* `Rejection.law`: the recursive distribution of this rejection sampler.
+
+## Main results
+
+* `Rejection.select_uniform_law`: the recursive law is the law of the finite tuple selector.
+* `Rejection.law_eq_mixture`: the law is a mixture of uniform and the accepted flat law.
+* `Rejection.law_probTrue`: its acceptance probability is `1-(1-q)^(t+1)`.
+* `Rejection.law_isSource`: the source bound is preserved by this mixture.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §8.3.2, Theorem 183.6.
+-/
+
+namespace TCSlib.Cryptography.Randomness.Rejection
+
+open TCSlib.InformationTheory Finset
+
+variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
+
+/-- Pushing the uniform distribution through a bijection preserves uniformity:
+`map e U_α = U_β`. -/
+theorem map_uniform_equiv [DecidableEq β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
+    (FinDist.uniform α).map e = FinDist.uniform β := by
+  classical
+  apply FinDist.ext
+  intro b
+  rw [FinDist.map_apply]
+  have hf : (univ : Finset α).filter (fun a => e a = b) = {e.symm b} := by
+    ext a
+    simp only [mem_filter, mem_univ, true_and, mem_singleton]
+    constructor
+    · intro h
+      exact e.injective (h.trans (e.apply_symm_apply b).symm)
+    · rintro rfl
+      exact e.apply_symm_apply b
+  rw [hf, sum_singleton, FinDist.uniform_apply, FinDist.uniform_apply,
+    Fintype.card_congr e]
+
+/-- Summing a function over a pushforward is summing its composite over the original law:
+`∑ b, map f p b · g b = ∑ a, p a · g (f a)`. The proof exchanges the two finite sums and
+uses the unique image `f a` of each input. -/
+theorem sum_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
+    (∑ b, (p.map f) b * g b) = ∑ a, p a * g (f a) := by
+  classical
+  simp only [FinDist.map_apply, sum_mul, sum_filter]
+  rw [sum_comm]
+  apply sum_congr rfl
+  intro a _
+  rw [sum_eq_single (f a)]
+  · simp
+  · intro b _ hba
+    simp only [if_neg (Ne.symm hba), zero_mul]
+  · intro h
+    exact False.elim (h (mem_univ _))
+
+/-- Expectation under a pushforward composes the test:
+`E_{map f p}[g] = E_p[g ∘ f]`. -/
+theorem expect_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
+    (p.map f).expect g = p.expect (fun a => g (f a)) := by
+  rw [FinDist.expect_eq, FinDist.expect_eq]
+  exact sum_map p f g
+
+/-- Acceptance under a pushforward composes the Boolean test:
+`Pr_{map f p}[D] = Pr_p[D ∘ f]`. -/
+theorem probTrue_map [DecidableEq β] (p : FinDist α) (f : α → β) (D : β → Bool) :
+    (p.map f).probTrue D = p.probTrue (fun a => D (f a)) := by
+  rw [FinDist.probTrue_eq_expect, expect_map, FinDist.probTrue_eq_expect]
+
+/-- A Boolean acceptance probability is nonnegative: `0 ≤ Pr_p[D]`. -/
+theorem probTrue_nonneg (p : FinDist α) (D : α → Bool) : 0 ≤ p.probTrue D := by
+  rw [FinDist.probTrue_eq]
+  exact sum_nonneg fun a _ => p.nonneg a
+
+/-- A Boolean acceptance probability is at most one: `Pr_p[D] ≤ 1`. -/
+theorem probTrue_le_one (p : FinDist α) (D : α → Bool) : p.probTrue D ≤ 1 := by
+  rw [FinDist.probTrue_eq, ← p.sum_prob]
+  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ => p.nonneg a)
+
+/-- A pushforward's mass at `b` is the expectation of its preimage indicator:
+`map f p b = E_p[1_{f(a)=b}]`. -/
+theorem map_apply_expect [DecidableEq β] (p : FinDist α) (f : α → β) (b : β) :
+    (p.map f) b = p.expect (fun a => if f a = b then 1 else 0) := by
+  classical
+  rw [FinDist.map_apply, FinDist.expect_eq, sum_filter]
+  apply sum_congr rfl
+  intro a _
+  split_ifs <;> simp
+
+/-- Successive pushforwards compose: `map g (map f p) = map (g ∘ f) p`. -/
+theorem map_map [DecidableEq β] [DecidableEq γ] (p : FinDist α) (f : α → β) (g : β → γ) :
+    (p.map f).map g = p.map (fun a => g (f a)) := by
+  classical
+  apply FinDist.ext
+  intro c
+  rw [map_apply_expect, expect_map, map_apply_expect]
+
+/-- Mapping only the second coordinate of an independent pair can be done before or after
+pairing: `map g (p × map f q) = map (fun (x,y) => g (x,f y)) (p × q)`. -/
+theorem map_prod_snd [DecidableEq β] [DecidableEq γ] {δ : Type*} [Fintype δ]
+    [DecidableEq δ] (p : FinDist α) (q : FinDist β) (f : β → γ) (g : α × γ → δ) :
+    (p.prod (q.map f)).map g = (p.prod q).map (fun z => g (z.1, f z.2)) := by
+  classical
+  apply FinDist.ext
+  intro d
+  rw [map_apply_expect, map_apply_expect, FinDist.expect_prod, FinDist.expect_prod]
+  congr 1
+  funext a
+  exact expect_map q f (fun c => if g (a, c) = d then 1 else 0)
+
+/-- The product of two uniform laws is the uniform law on pairs: `U_α × U_β = U_(α×β)`. -/
+theorem uniform_prod [Nonempty α] [Nonempty β] :
+    (FinDist.uniform α).prod (FinDist.uniform β) = FinDist.uniform (α × β) := by
+  apply FinDist.ext
+  intro z
+  rw [FinDist.prod_apply, FinDist.uniform_apply, FinDist.uniform_apply,
+    FinDist.uniform_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
+  ring
+
+/-- A nonempty tuple is equivalent to its first entry and its tail:
+`(Fin (t+1+1) → α) ≃ α × (Fin (t+1) → α)`. -/
+def tupleEquiv (t : ℕ) : (Fin (t + 1 + 1) → α) ≃ α × (Fin (t + 1) → α) where
+  toFun x := (x 0, fun i => x i.succ)
+  invFun z := Fin.cons z.1 z.2
+  left_inv x := by
+    funext i
+    refine Fin.cases ?_ (fun j => ?_) i
+    · simp
+    · simp
+  right_inv z := by
+    apply Prod.ext
+    · simp
+    · funext i
+      simp
+
+/-- The tuple equivalence reads the first entry and the tail:
+`tupleEquiv t x = (x 0, fun i => x i.succ)`. -/
+theorem tupleEquiv_apply (t : ℕ) (x : Fin (t + 1 + 1) → α) :
+    tupleEquiv t x = (x 0, fun i => x i.succ) := rfl
+
+/-- The inverse tuple equivalence prepends its first coordinate:
+`(tupleEquiv t).symm (a,x) = Fin.cons a x`. -/
+theorem tupleEquiv_symm_apply (t : ℕ) (z : α × (Fin (t + 1) → α)) :
+    (tupleEquiv t).symm z = Fin.cons z.1 z.2 := rfl
+
+/-- The first entry of the inverse tuple equivalence is the pair's first coordinate:
+`(tupleEquiv t).symm z 0 = z.1`. -/
+theorem tupleEquiv_symm_zero (t : ℕ) (z : α × (Fin (t + 1) → α)) :
+    (tupleEquiv t).symm z 0 = z.1 := by
+  rw [tupleEquiv_symm_apply]
+  simp
+
+/-- Each successor entry of the inverse tuple equivalence is the corresponding tail entry:
+`(tupleEquiv t).symm z i.succ = z.2 i`. -/
+theorem tupleEquiv_symm_succ (t : ℕ) (z : α × (Fin (t + 1) → α)) (i : Fin (t + 1)) :
+    (tupleEquiv t).symm z i.succ = z.2 i := by
+  rw [tupleEquiv_symm_apply]
+  simp
+
+/-- Select the first accepted entry among `t` trials; if all fail, return the final entry:
+`select D 0 x = x 0` and `select D (t+1) x = if D (x 0) then x 0 else select D t (x ∘ succ)`.
+There are `t+1` entries in total, so the fallback is always present. -/
+def select (D : α → Bool) : (t : ℕ) → (Fin (t + 1) → α) → α
+  | 0, x => x 0
+  | t + 1, x => if D (x 0) then x 0 else select D t (fun i => x i.succ)
+
+/-- With no rejection trials, the selector returns its sole entry: `select D 0 x = x 0`. -/
+theorem select_zero (D : α → Bool) (x : Fin 1 → α) : select D 0 x = x 0 := rfl
+
+/-- With one more rejection trial, accept the first entry if its test succeeds, otherwise
+select from the tail: `select D (t+1) x = if D (x 0) then x 0 else select D t (x ∘ succ)`. -/
+theorem select_succ (D : α → Bool) (t : ℕ) (x : Fin (t + 1 + 1) → α) :
+    select D (t + 1) x = if D (x 0) then x 0 else select D t (fun i => x i.succ) := rfl
+
+/-- The law of rejection sampling with `t` trials and an independent uniform fallback:
+`law D 0 = U_α` and `law D (t+1) = map (fun (x,y) => if D x then x else y) (U_α × law D t)`.
+At each trial, a fresh uniform point is accepted if its test succeeds. -/
+noncomputable def law [DecidableEq α] [Nonempty α] (D : α → Bool) : ℕ → FinDist α
+  | 0 => FinDist.uniform α
+  | t + 1 => ((FinDist.uniform α).prod (law D t)).map
+      (fun z => if D z.1 then z.1 else z.2)
+
+/-- With zero trials, the rejection law is uniform: `law D 0 = U_α`. -/
+theorem law_zero [DecidableEq α] [Nonempty α] (D : α → Bool) :
+    law D 0 = FinDist.uniform α := rfl
+
+/-- One more trial draws a fresh uniform point independently of the remaining sampler:
+`law D (t+1) = map (fun (x,y) => if D x then x else y) (U_α × law D t)`. -/
+theorem law_succ [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
+    law D (t + 1) = ((FinDist.uniform α).prod (law D t)).map
+      (fun z => if D z.1 then z.1 else z.2) := rfl
+
+/-- Selecting from `t+1` independent uniform entries has the recursive rejection law:
+`map (select D t) U_(α^(t+1)) = law D t`.
+
+**Proof sketch.** Split a tuple into its first entry and its tail. Uniformity is preserved by
+this bijection, and uniformity on pairs is the product of the two uniform laws. The induction
+hypothesis identifies the selected tail with the remaining rejection sampler. -/
+theorem select_uniform_law [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
+    (FinDist.uniform (Fin (t + 1) → α)).map (select D t) = law D t := by
+  classical
+  induction t with
+  | zero =>
+    rw [law_zero]
+    let e : (Fin 1 → α) ≃ α :=
+      { toFun := fun x => x 0
+        invFun := fun a _ => a
+        left_inv := by
+          intro x
+          funext i
+          have hi : i = 0 := Subsingleton.elim _ _
+          rw [hi]
+        right_inv := fun _ => rfl }
+    exact map_uniform_equiv e
+  | succ t ih =>
+    rw [law_succ, ← ih]
+    have hu : FinDist.uniform (Fin (t + 1 + 1) → α) =
+        (FinDist.uniform (α × (Fin (t + 1) → α))).map (tupleEquiv t).symm :=
+      (map_uniform_equiv (tupleEquiv (α := α) t).symm).symm
+    rw [hu, map_map, ← uniform_prod, map_prod_snd]
+    congr 1
+
+/-- Independent branching returns the first point on acceptance and the second on rejection:
+`map (fun (x,y) => if D x then x else y) (p × q) a = 1_{D(a)} p(a) + (1-Pr_p[D]) q(a)`.
+
+**Proof sketch.** Expand the map and product readers. For a fixed first point, the inner sum
+is either its whole mass or the mass of the second point at `a`. Split the outer sum into
+accepted and rejected first points. -/
+theorem branch_apply [DecidableEq α] (p q : FinDist α) (D : α → Bool) (a : α) :
+    ((p.prod q).map (fun z => if D z.1 then z.1 else z.2)) a =
+      (if D a then p a else 0) + (1 - p.probTrue D) * q a := by
+  classical
+  rw [FinDist.map_apply, sum_filter, Fintype.sum_prod_type]
+  simp only [FinDist.prod_apply]
+  have inner (x : α) :
+      (∑ y, if (if D x then x else y) = a then p x * q y else 0) =
+        if D x then (if x = a then p x else 0) else p x * q a := by
+    cases hd : D x
+    · simp [hd]
+    · by_cases hxa : x = a
+      · simp [hd, hxa, ← mul_sum, q.sum_prob]
+      · simp [hd, hxa]
+  simp_rw [inner]
+  have split (x : α) :
+      (if D x then (if x = a then p x else 0) else p x * q a) =
+        (if x = a then (if D a then p a else 0) else 0) +
+          (if !D x then p x * q a else 0) := by
+    by_cases hxa : x = a
+    · subst x
+      cases D a <;> simp
+    · cases hd : D x <;> simp [hd, hxa]
+  simp_rw [split]
+  rw [sum_add_distrib]
+  have hn : (∑ x, if !D x then p x * q a else 0) =
+      (1 - p.probTrue D) * q a := by
+    rw [← FinDist.probTrue_not, FinDist.probTrue_eq, sum_mul, sum_filter]
+  rw [hn]
+  simp
+
+/-- One rejection trial satisfies the point recurrence
+`law D (t+1) a = 1_{D(a)} / |α| + (1-q) law D t a`, where `q = Pr_{U_α}[D]`. -/
+theorem law_succ_apply [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) (a : α) :
+    law D (t + 1) a =
+      (if D a then (Fintype.card α : ℝ)⁻¹ else 0) +
+        (1 - (FinDist.uniform α).probTrue D) * law D t a := by
+  rw [law_succ, branch_apply, FinDist.uniform_apply]
+
+/-- The acceptance probabilities obey
+`Pr_{law D (t+1)}[D] = q + (1-q) Pr_{law D t}[D]`. -/
+theorem law_succ_probTrue [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
+    (law D (t + 1)).probTrue D =
+      (FinDist.uniform α).probTrue D +
+        (1 - (FinDist.uniform α).probTrue D) * (law D t).probTrue D := by
+  classical
+  rw [FinDist.probTrue_eq]
+  simp_rw [law_succ_apply]
+  rw [sum_add_distrib, ← mul_sum]
+  have hi : (∑ a ∈ (univ : Finset α).filter (fun a => D a = true),
+      if D a then (Fintype.card α : ℝ)⁻¹ else 0) = (FinDist.uniform α).probTrue D := by
+    rw [FinDist.probTrue_eq]
+    apply sum_congr rfl
+    intro a ha
+    simp [(mem_filter.1 ha).2, FinDist.uniform_apply]
+  rw [hi, ← FinDist.probTrue_eq (law D t) D]
+
+/-- The rejection sampler accepts with probability `1-(1-q)^(t+1)`, including the independent
+fallback's chance to accept. This formula also holds for `q=0` and `q=1`.
+
+**Proof sketch.** The zero-trial law has acceptance `q`. Each additional trial fails with
+probability `1-q`, multiplying the probability that the remaining sampler fails by that factor. -/
+theorem law_probTrue [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
+    (law D t).probTrue D = 1 - (1 - (FinDist.uniform α).probTrue D) ^ (t + 1) := by
+  induction t with
+  | zero => rw [law_zero]; ring
+  | succ t ih => rw [law_succ_probTrue, ih, pow_succ]; ring
+
+/-- For positive uniform acceptance `q = Pr_{U_α}[D] > 0`, the rejection law's point mass is
+`law D t a = (1-q)^t / |α| + 1_{D(a)} (1-(1-q)^t) / (|α| q)`.
+
+**Proof sketch.** Induct on the trial count using the point recurrence. On accepted points the
+geometric sum contributes `(1-(1-q)^t)/q`; on rejected points only the fallback contributes. -/
+theorem law_apply [DecidableEq α] [Nonempty α] (D : α → Bool)
+    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (a : α) :
+    law D t a =
+      (1 - (FinDist.uniform α).probTrue D) ^ t * (Fintype.card α : ℝ)⁻¹ +
+        (if D a then
+          (1 - (1 - (FinDist.uniform α).probTrue D) ^ t) *
+            (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D else 0) := by
+  have hq0 : (FinDist.uniform α).probTrue D ≠ 0 := ne_of_gt hq
+  induction t with
+  | zero => rw [law_zero, FinDist.uniform_apply]; simp
+  | succ t ih =>
+    rw [law_succ_apply, ih, pow_succ]
+    cases D a <;> simp
+    · ring
+    · field_simp [hq0]
+      <;> ring
+
+/-- Uniform acceptance is the cardinality of the accepted set divided by the whole cardinality:
+`Pr_{U_α}[D] = |{a : D a}| / |α|`. -/
+theorem uniform_probTrue [Nonempty α] (D : α → Bool) :
+    (FinDist.uniform α).probTrue D =
+      (((univ : Finset α).filter (fun a => D a = true)).card : ℝ) *
+        (Fintype.card α : ℝ)⁻¹ := by
+  classical
+  rw [FinDist.probTrue_eq]
+  simp only [FinDist.uniform_apply, sum_const, nsmul_eq_mul]
+
+/-- Positive uniform acceptance implies that the accepted set is nonempty:
+`0 < Pr_{U_α}[D] → {a : D a}.Nonempty`. -/
+theorem accepted_nonempty [Nonempty α] (D : α → Bool)
+    (hq : 0 < (FinDist.uniform α).probTrue D) :
+    ((univ : Finset α).filter (fun a => D a = true)).Nonempty := by
+  classical
+  by_contra h
+  have he := Finset.not_nonempty_iff_eq_empty.1 h
+  have hz : (FinDist.uniform α).probTrue D = 0 := by
+    rw [FinDist.probTrue_eq, he, sum_empty]
+  linarith
+
+/-- The flat law on the accepted set has point mass `1/(|α| q)` at accepted points and zero
+elsewhere, where `q=Pr_{U_α}[D]`. -/
+theorem accepted_flat_apply [DecidableEq α] [Nonempty α] (D : α → Bool)
+    (hs : ((univ : Finset α).filter (fun a => D a = true)).Nonempty) (a : α) :
+    FinDist.flat ((univ : Finset α).filter (fun a => D a = true)) hs a =
+      if D a then (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D else 0 := by
+  classical
+  rw [FinDist.flat_apply]
+  have hm : a ∈ (univ : Finset α).filter (fun a => D a = true) ↔ D a = true := by simp
+  simp only [hm]
+  by_cases hd : D a = true
+  · rw [if_pos hd, if_pos hd, uniform_probTrue]
+    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
+    have hs0 : ((((univ : Finset α).filter (fun a => D a = true)).card : ℕ) : ℝ) ≠ 0 :=
+      Nat.cast_ne_zero.2 hs.card_pos.ne'
+    field_simp [hc, hs0]
+  · rw [if_neg hd, if_neg hd]
+
+/-- The rejection law is the pointwise mixture
+`(1-q)^t U_α + (1-(1-q)^t) flat({a : D a})` for `q>0`. -/
+theorem law_apply_flat [DecidableEq α] [Nonempty α] (D : α → Bool)
+    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (a : α) :
+    law D t a =
+      (1 - (FinDist.uniform α).probTrue D) ^ t * (FinDist.uniform α) a +
+        (1 - (1 - (FinDist.uniform α).probTrue D) ^ t) *
+          FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
+            (accepted_nonempty D hq) a := by
+  rw [law_apply D hq, FinDist.uniform_apply, accepted_flat_apply]
+  cases D a <;> simp <;> ring
+
+/-- A mixture of `p` and `q` with weight `w∈[0,1]` gives mass
+`w p(a) + (1-w) q(a)` to each point. -/
+noncomputable def mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
+    (p q : FinDist α) : FinDist α where
+  prob a := w * p a + (1 - w) * q a
+  nonneg a := add_nonneg (mul_nonneg hw0 (p.nonneg a))
+    (mul_nonneg (sub_nonneg.2 hw1) (q.nonneg a))
+  sum_prob := by
+    rw [sum_add_distrib, ← mul_sum, ← mul_sum, p.sum_prob, q.sum_prob]
+    ring
+
+/-- The point probability of the mixture is its defining convex combination:
+`mixture w p q a = w p(a) + (1-w) q(a)`. -/
+theorem mixture_apply (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
+    (p q : FinDist α) (a : α) :
+    mixture w hw0 hw1 p q a = w * p a + (1 - w) * q a := rfl
+
+/-- Mixtures of two `k`-sources are `k`-sources:
+`IsSource k p → IsSource k q → IsSource k (mixture w p q)`. Their point probabilities share
+the same upper bound `2^(-k)`, which is preserved by a convex combination. -/
+theorem mixture_isSource (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
+    (p q : FinDist α) (k : ℝ) (hp : FinDist.IsSource k p) (hq : FinDist.IsSource k q) :
+    FinDist.IsSource k (mixture w hw0 hw1 p q) := by
+  have hp' := (FinDist.hasMinEntropy_iff p k).1
+    (FinDist.isSource_iff_hasMinEntropy.1 hp)
+  have hq' := (FinDist.hasMinEntropy_iff q k).1
+    (FinDist.isSource_iff_hasMinEntropy.1 hq)
+  apply FinDist.isSource_iff_hasMinEntropy.2
+  apply (FinDist.hasMinEntropy_iff _ _).2
+  intro a
+  rw [mixture_apply]
+  calc w * p a + (1 - w) * q a
+      ≤ w * (2 : ℝ) ^ (-k) + (1 - w) * (2 : ℝ) ^ (-k) :=
+        add_le_add (mul_le_mul_of_nonneg_left (hp' a) hw0)
+          (mul_le_mul_of_nonneg_left (hq' a) (sub_nonneg.2 hw1))
+    _ = (2 : ℝ) ^ (-k) := by ring
+
+/-- The probability `(1-q)^t` that all rejection trials fail is nonnegative:
+`0 ≤ (1-Pr_{U_α}[D])^t`. -/
+theorem failure_pow_nonneg [Nonempty α] (D : α → Bool) (t : ℕ) :
+    0 ≤ (1 - (FinDist.uniform α).probTrue D) ^ t :=
+  pow_nonneg (sub_nonneg.2 (probTrue_le_one _ _)) _
+
+/-- The probability `(1-q)^t` that all rejection trials fail is at most one:
+`(1-Pr_{U_α}[D])^t ≤ 1`. -/
+theorem failure_pow_le_one [Nonempty α] (D : α → Bool) (t : ℕ) :
+    (1 - (FinDist.uniform α).probTrue D) ^ t ≤ 1 := by
+  have hb0 : 0 ≤ 1 - (FinDist.uniform α).probTrue D :=
+    sub_nonneg.2 (probTrue_le_one _ _)
+  have hb1 : 1 - (FinDist.uniform α).probTrue D ≤ 1 := by
+    linarith [probTrue_nonneg (FinDist.uniform α) D]
+  induction t with
+  | zero => simp
+  | succ t ih =>
+    rw [pow_succ]
+    calc (1 - (FinDist.uniform α).probTrue D) ^ t *
+        (1 - (FinDist.uniform α).probTrue D) ≤ 1 * 1 := mul_le_mul ih hb1 hb0 zero_le_one
+      _ = 1 := one_mul _
+
+/-- The rejection law is exactly the convex mixture
+`law D t = mixture ((1-q)^t) U_α flat({a : D a})` for `q = Pr_{U_α}[D] > 0`, that is,
+`(1-q)^t U_α + (1-(1-q)^t) flat({a : D a})`. -/
+theorem law_eq_mixture [DecidableEq α] [Nonempty α] (D : α → Bool)
+    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) :
+    law D t = mixture ((1 - (FinDist.uniform α).probTrue D) ^ t)
+      (failure_pow_nonneg D t) (failure_pow_le_one D t) (FinDist.uniform α)
+      (FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
+        (accepted_nonempty D hq)) := by
+  apply FinDist.ext
+  intro a
+  rw [mixture_apply]
+  exact law_apply_flat D hq t a
+
+/-- If `1/(|α|q) ≤ 2^(-k)`, the flat law on the accepted set is a `k`-source. -/
+theorem accepted_flat_isSource [DecidableEq α] [Nonempty α] (D : α → Bool)
+    (hs : ((univ : Finset α).filter (fun a => D a = true)).Nonempty) (k : ℝ)
+    (hbound : (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D ≤ (2 : ℝ) ^ (-k)) :
+    FinDist.IsSource k (FinDist.flat ((univ : Finset α).filter (fun a => D a = true)) hs) := by
+  apply FinDist.isSource_iff_hasMinEntropy.2
+  apply (FinDist.hasMinEntropy_iff _ _).2
+  intro a
+  rw [accepted_flat_apply]
+  split_ifs
+  · exact hbound
+  · positivity
+
+/-- The rejection law is a `k`-source whenever its uniform and accepted-flat components are
+`k`-sources: `IsSource k U_α → IsSource k flat({a : D a}) → IsSource k (law D t)`.
+This follows from its exact mixture identity and convexity of the point bound. -/
+theorem law_isSource [DecidableEq α] [Nonempty α] (D : α → Bool)
+    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (k : ℝ)
+    (hU : FinDist.IsSource k (FinDist.uniform α))
+    (hflat : FinDist.IsSource k
+      (FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
+        (accepted_nonempty D hq))) :
+    FinDist.IsSource k (law D t) := by
+  rw [law_eq_mixture D hq t]
+  exact mixture_isSource _ _ _ _ _ _ hU hflat
+
+end TCSlib.Cryptography.Randomness.Rejection
diff --git a/TCSlib/Cryptography/Randomness/Extraction/Sampler.lean b/TCSlib/Cryptography/Randomness/Extraction/Sampler.lean
new file mode 100644
index 000000000..c0f49b816
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Extraction/Sampler.lean
@@ -0,0 +1,237 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Asymptotic.OneWay
+import TCSlib.Complexity.ClassP.BinaryArith.Basic
+import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
+import TCSlib.Cryptography.Randomness.Extraction.Rejection
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# A bounded rejection sampler on consecutive coin blocks
+
+The sampler used in [PS10, Theorem 183.6] reads a fixed number of blocks and returns the
+first whose extractor output starts with `true`, using the last block as a fallback.
+The security parameter at which the counterexample is needed is fixed before the sampler
+is chosen, so fixed block widths and a constant coin polynomial suffice. The resulting
+machine has no advice and is therefore uniform.
+
+## Main definitions
+
+* `RejectionSampler.chooseWord`: bounded first-success selection from a bit tape.
+* `RejectionSampler.machine`: the uniform PPT implementing the selection.
+* `RejectionSampler.coinEquiv`: its coins as a tape of exactly `(t + 1) * n` bits.
+
+## Main results
+
+* `RejectionSampler.chooseWord_poly`: fixed-width bounded selection is polynomial-time.
+* `RejectionSampler.chooseWord_blocks`: its typed interpretation is `Rejection.select`.
+* `RejectionSampler.machine_runAt_coinEquiv`: the machine implements that tape selection.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, §8.3.2, Theorem 183.6.
+-/
+
+namespace TCSlib.Cryptography.Randomness.RejectionSampler
+
+open Complexity Turing
+
+/-- Trying `t` blocks of width `n` and falling back to block `t` means returning the first
+block whose extractor output starts with `true`, or the final block if every test fails:
+`chooseWord Ext n 0 r = r.take n`, and `chooseWord Ext n (t+1) r = r.take n` if
+`(Ext (r.take n)).headD false`, otherwise
+`chooseWord Ext n (t+1) r = chooseWord Ext n t (r.drop n)`.
+[PS10, Theorem 183.6]. Short input tapes are truncated by `List.take`. -/
+def chooseWord (Ext : List Bool → List Bool) (n : ℕ) : ℕ → List Bool → List Bool
+  | 0, r => r.take n
+  | t + 1, r =>
+      if (Ext (r.take n)).headD false then r.take n else chooseWord Ext n t (r.drop n)
+
+/-- With no trials, `chooseWord` returns the first `n` bits: `chooseWord Ext n 0 r = r.take n`.
+-/
+theorem chooseWord_zero (Ext : List Bool → List Bool) (n : ℕ) (r : List Bool) :
+    chooseWord Ext n 0 r = r.take n := rfl
+
+/-- One additional trial tests the first block, returning it on acceptance and otherwise
+running the remaining trials on the tape with that block dropped:
+`chooseWord Ext n (t+1) r = if (Ext (r.take n)).headD false then r.take n else
+chooseWord Ext n t (r.drop n)`. -/
+theorem chooseWord_succ (Ext : List Bool → List Bool) (n t : ℕ) (r : List Bool) :
+    chooseWord Ext n (t + 1) r =
+      if (Ext (r.take n)).headD false then r.take n else chooseWord Ext n t (r.drop n) := rfl
+
+/-- Taking any fixed number `n` of input bits is polynomial-time computable:
+`PolyTimeComputable (fun r : List Bool => r.take n)`.
+
+**Proof sketch.** Pair a constant unary word of length `n` with the input and apply the
+published length-gated prefix machine. -/
+theorem take_poly (n : ℕ) : PolyTimeComputable (fun r : List Bool => r.take n) := by
+  have henc : PolyTimeComputable fun r => pairEncode (List.replicate n true) r :=
+    (polyTimeComputable_const (List.replicate n true)).pairEncode polyTimeComputable_id
+  have h := polyTimeComputable_takePrefixByLength.comp henc
+  convert h using 1
+  funext r
+  change r.take n = PrefixByLength.take (pairEncode (List.replicate n true) r)
+  rw [PrefixByLength.take_def, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- If `Ext` is polynomial-time, the fixed-width sampler with any fixed number of trials is
+polynomial-time: `PolyTimeComputable Ext → PolyTimeComputable (chooseWord Ext n t)`.
+[PS10, Theorem 183.6, the efficiency claim].
+
+**Proof sketch.** Induct on the fixed number of trials. The head-bit test composes the
+extractor with a fixed prefix, and the conditional combinator joins that prefix with the
+inductively constructed sampler on the fixed-width suffix. -/
+theorem chooseWord_poly {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t : ℕ) : PolyTimeComputable (chooseWord Ext n t) := by
+  induction t with
+  | zero =>
+    convert take_poly n using 1
+  | succ t ih =>
+    have htest : PolyTimeComputable fun r => [(Ext (r.take n)).headD false] :=
+      polyTimeComputable_headD.comp (hExt.comp (take_poly n))
+    have h := polyTimeComputable_ite htest (take_poly n)
+      (ih.comp (BinArith.polyTimeComputable_drop n))
+    convert h using 1
+
+/-- On a concatenated tuple of `n`-bit blocks, string selection encodes typed selection:
+`chooseWord Ext n t (flatten (ofFn (ofFn ∘ x))) = ofFn (select D t x)`, where
+`D a = (Ext (ofFn a)).headD false`.
+
+**Proof sketch.** At each successor trial, `take n` reads the first encoded block and
+`drop n` leaves the concatenation of the remaining blocks. Both selectors therefore make
+the same branch choice; induction identifies the remaining trials. -/
+theorem chooseWord_flatten (Ext : List Bool → List Bool) (n t : ℕ)
+    (x : Fin (t + 1) → Fin n → Bool) :
+    chooseWord Ext n t (List.ofFn fun i => List.ofFn (x i)).flatten =
+      List.ofFn
+        (Rejection.select (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t x) := by
+  induction t with
+  | zero =>
+    rw [Rejection.select_zero, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
+      List.flatten_nil, List.append_nil, chooseWord_zero]
+    exact List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
+  | succ t ih =>
+    have hflat : (List.ofFn fun i : Fin (t + 1 + 1) => List.ofFn (x i)).flatten =
+        List.ofFn (x 0) ++ (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten := by
+      rw [List.ofFn_succ, List.flatten_cons]
+    have ht : (List.ofFn (x 0) ++
+        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten).take n =
+        List.ofFn (x 0) := List.take_left' List.length_ofFn
+    have hd : (List.ofFn (x 0) ++
+        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten).drop n =
+        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten :=
+      List.drop_left' List.length_ofFn
+    rw [hflat, chooseWord_succ, ht, hd, Rejection.select_succ]
+    split_ifs
+    · rfl
+    · exact ih (fun i => x i.succ)
+
+/-- On `(t + 1) * n` uniform coin bits, `chooseWord` encodes typed first-success selection
+from the canonical `(t + 1)` blocks. This includes `n = 0`. -/
+theorem chooseWord_blocks (Ext : List Bool → List Bool) (n t : ℕ)
+    (r : Fin ((t + 1) * n) → Bool) :
+    chooseWord Ext n t (List.ofFn r) =
+      List.ofFn (Rejection.select (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t
+        (FunFamily.blocks (t + 1) n r)) := by
+  have h := FunFamily.ofFn_blocks_symm (t + 1) n (FunFamily.blocks (t + 1) n r)
+  rw [Equiv.symm_apply_apply] at h
+  rw [h]
+  exact chooseWord_flatten Ext n t _
+
+/-- The bounded rejection machine on `(t + 1) * n` coins has empty advice and runs
+`chooseWord Ext n t` on its coin tape: `(machine hExt n t).runAtL m y r = chooseWord Ext n t r`
+and `(machine hExt n t).coins = .const ((t + 1) * n)`. [PS10, Theorem 183.6]. -/
+noncomputable def machine {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t : ℕ) : NUPPT :=
+  NUPPT.ofPolyTimeUniform ((chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD)
+    (.const ((t + 1) * n))
+
+/-- The rejection machine packages the polynomial-time coin function with constant coin
+polynomial `(t + 1) * n` and empty advice:
+`machine hExt n t = NUPPT.ofPolyTimeUniform f (.const ((t + 1) * n))`, where `f` is
+`(chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD`. -/
+theorem machine_eq {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext) (n t : ℕ) :
+    machine hExt n t =
+      NUPPT.ofPolyTimeUniform ((chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD)
+        (.const ((t + 1) * n)) := rfl
+
+/-- The bounded rejection machine is uniform: it has empty advice at every parameter,
+`(machine hExt n t).Uniform`, i.e. `∀ m, (machine hExt n t).advice m = []`. -/
+theorem machine_uniform {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t : ℕ) : (machine hExt n t).Uniform := by
+  rw [machine_eq]
+  exact NUPPT.ofPolyTimeUniform_uniform _ _
+
+/-- The rejection machine's coin polynomial is the constant `(t + 1) * n`:
+`(machine hExt n t).coins = .const ((t + 1) * n)`. -/
+theorem machine_coins {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t : ℕ) : (machine hExt n t).coins = .const ((t + 1) * n) := by
+  rw [machine_eq, NUPPT.coins_ofPolyTimeUniform]
+
+/-- On an untyped coin tape `r`, at every activation parameter and argument, the rejection
+machine returns `chooseWord Ext n t r`: `(machine hExt n t).runAtL m y r = chooseWord Ext n t r`.
+-/
+theorem machine_runAtL {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) (y r : List Bool) :
+    (machine hExt n t).runAtL m y r = chooseWord Ext n t r := by
+  rw [machine_eq, NUPPT.runAtL_ofPolyTimeUniform]
+  change chooseWord Ext n t (pairSndD (pairEncode (pairEncode (NUPPT.advInput m y) []) r)) = _
+  rw [pairSndD_pairEncode]
+
+/-- On typed coins, the rejection machine runs `chooseWord` on the coin string:
+`(machine hExt n t).runAt m y r = chooseWord Ext n t (List.ofFn r)`. -/
+theorem machine_runAt {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) (y : List Bool) (r : (machine hExt n t).Coins m) :
+    (machine hExt n t).runAt m y r = chooseWord Ext n t (List.ofFn r) := by
+  rw [NUPPT.runAt_eq, machine_runAtL]
+
+/-- At every activation parameter, the rejection machine uses exactly `(t + 1) * n` bits:
+`(machine hExt n t).coinLen m = (t + 1) * n`. -/
+theorem machine_coinLen {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) : (machine hExt n t).coinLen m = (t + 1) * n := by
+  rw [NUPPT.coinLen_eq, machine_coins, PolyExpr.eval_const]
+
+/-- The rejection machine's coins are canonically the bit tape of length `(t + 1) * n`,
+independently of its activation parameter:
+`(machine hExt n t).Coins m ≃ (Fin ((t + 1) * n) → Bool)`. -/
+noncomputable def coinEquiv {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) : (machine hExt n t).Coins m ≃ (Fin ((t + 1) * n) → Bool) :=
+  Equiv.arrowCongr (finCongr (machine_coinLen hExt n t m)) (Equiv.refl Bool)
+
+/-- The canonical rejection-coin equivalence is the arrow equivalence induced by the
+published equality `coinLen m = (t + 1) * n`. -/
+theorem coinEquiv_eq {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) : coinEquiv hExt n t m =
+      Equiv.arrowCongr (finCongr (machine_coinLen hExt n t m)) (Equiv.refl Bool) := rfl
+
+/-- The canonical rejection-coin equivalence preserves the encoded coin string:
+`List.ofFn (coinEquiv hExt n t m r) = List.ofFn r`. -/
+theorem coinEquiv_ofFn {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) (r : (machine hExt n t).Coins m) :
+    List.ofFn (coinEquiv hExt n t m r) = List.ofFn r :=
+  (List.ofFn_congr (machine_coinLen hExt n t m) r).symm
+
+/-- The inverse canonical rejection-coin equivalence preserves the encoded coin string:
+`List.ofFn ((coinEquiv hExt n t m).symm r) = List.ofFn r`. -/
+theorem coinEquiv_symm_ofFn {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) (r : Fin ((t + 1) * n) → Bool) :
+    List.ofFn ((coinEquiv hExt n t m).symm r) = List.ofFn r := by
+  rw [← coinEquiv_ofFn hExt n t m, Equiv.apply_symm_apply]
+
+/-- Running the rejection machine on a tape transported through `coinEquiv` is precisely
+`chooseWord Ext n t` on that tape:
+`(machine hExt n t).runAt m y ((coinEquiv hExt n t m).symm r) = chooseWord Ext n t (List.ofFn r)`.
+-/
+theorem machine_runAt_coinEquiv {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
+    (n t m : ℕ) (y : List Bool) (r : Fin ((t + 1) * n) → Bool) :
+    (machine hExt n t).runAt m y ((coinEquiv hExt n t m).symm r) =
+      chooseWord Ext n t (List.ofFn r) := by
+  rw [machine_runAt, coinEquiv_symm_ofFn]
+
+end TCSlib.Cryptography.Randomness.RejectionSampler

## ===== TCSlib/Cryptography/Randomness/Extraction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Entropy
import TCSlib.InformationTheory.Extractors
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Randomness.Extraction.Rejection
import TCSlib.Cryptography.Randomness.Extraction.Sampler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# No efficient one-bit extractor for efficient sources

[PS10, Theorem 183.6]: let `C` be the set of all efficiently computable `(n − 2)`-sources on
`{0,1}^n`; then there is no 1-bit `1/4`-extractor for `C`.

**The source's proof.** Suppose `Ext` is a `1/4`-extractor for `C`. Since `U_n ∈ C`,
`Pr[Ext(U_n) = 1] ≥ 1/4`, so `S = {x : Ext(x) = 1}` has at least `2^{n−2}` elements. The source
`X` samples `x ← U_n` until `Ext(x) = 1`, giving up after 10 tries with a fresh `x ← U_n`. It is a
mixture of `U_n` and the flat source on `S`, both `(n − 2)`-sources, so it is one. It is efficient
because `Ext` is. And `Pr[Ext(X) = 1] ≥ 1 − (3/4)^{10} > 0.9`, so `Ext(X)` is not `1/4`-close to
`U_1`.

**Source gap (inventory Thm-183.6).** "`X` is computable in polynomial time since `Ext` is" needs
`Ext` to be efficient, so the theorem is stated for polynomial-time `Ext`.

**The formal reading.**
- A source at `n` is efficient when it is the law of `padFin n (S(1^n))` for a uniform PPT `S`,
  over `S`'s uniform coins (`samplerLaw`).
- The class `C` at `n` is the set of efficient laws that are `(n − 2)`-sources (`effSources`).
- The extractor property is P0's `IsExtractor` ([PS10, Def 181.2]).
- The theorem is stated at **every** `n`: for every polynomial-time `Ext` and every `n`, the
  `1`-bit function `Ext` induces on `n`-bit strings is not a `1/4`-extractor for `C` at `n`. The
  witness depends on `n`: `U_n` if `Ext` fails on it, and otherwise the source's `X`. This is
  stronger than the source's "there is no extractor", which needs only one `n`. For `n ≤ 2` it is
  trivial, since every distribution is a `(n − 2)`-source there (a point mass is a witness); the
  content is at `n ≥ 3`.

## Contents

* `Randomness.Extraction.Rejection`: finite rejection laws and source-preserving mixtures.
* `Randomness.Extraction.Sampler`: the uniform machine and its consecutive coin blocks.

## Main definitions

* `Randomness.samplerLaw`: the law of a machine's `n`-bit output.
* `Randomness.effSources`: the efficiently samplable `k`-sources at `n`.
* `Randomness.extBit`: the `1`-bit function induced on `n`-bit strings by a string function.

## Main results

* `Randomness.not_isExtractor_effSources` (Thm 183.6): no efficient one-bit extractor for
  efficiently samplable `(n−2)`-sources, proved by bounded rejection sampling.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.2, Definition 183.5 and Theorem 183.6 (book pp. 183–184).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity TCSlib.Cryptography TCSlib.InformationTheory

/-- **The law of a sampler's `n`-bit output**: the distribution of `padFin n (S(1^n; r))` for
uniform coins `r`. -/
noncomputable def samplerLaw (S : NUPPT) (n : ℕ) : FinDist (Fin n → Bool) :=
  (FinDist.uniform (S.Coins n)).map fun r => padFin n (S.runAt n [] r)

/-- The probability of an `n`-bit word under `samplerLaw S n` is the sum of the uniform
coin probabilities over tapes whose padded sampler output is that word. -/
theorem samplerLaw_apply (S : NUPPT) (n : ℕ) (x : Fin n → Bool) :
    (samplerLaw S n).prob x =
      ∑ r ∈ (Finset.univ : Finset (S.Coins n)).filter
        (fun r => padFin n (S.runAt n [] r) = x), (Fintype.card (S.Coins n) : ℝ)⁻¹ := by
  rw [samplerLaw, FinDist.map_apply]
  simp only [FinDist.uniform_apply]

/-- The probability field of `samplerLaw S n` maps each word to the sum of the uniform
coin probabilities over its preimage under the padded sampler output. -/
theorem samplerLaw_prob (S : NUPPT) (n : ℕ) :
    (samplerLaw S n).prob = fun x =>
      ∑ r ∈ (Finset.univ : Finset (S.Coins n)).filter
        (fun r => padFin n (S.runAt n [] r) = x), (Fintype.card (S.Coins n) : ℝ)⁻¹ :=
  funext (samplerLaw_apply S n)

/-- **The efficiently samplable `k(n)`-sources at `n`** [PS10, Theorem 183.6, "efficiently
computable sources"]: the laws of uniform PPT samplers that are `k(n)`-sources. -/
def effSources (k : ℕ → ℝ) (n : ℕ) : Set (FinDist (Fin n → Bool)) :=
  {X | ∃ S : NUPPT, S.Uniform ∧ X = samplerLaw S n ∧ FinDist.IsSource (k n) X}

/-- A distribution belongs to `effSources k n` exactly when it is the law of a uniform PPT
sampler and is a `k(n)`-source. -/
theorem effSources_iff (k : ℕ → ℝ) (n : ℕ) (X : FinDist (Fin n → Bool)) :
    X ∈ effSources k n ↔
      ∃ S : NUPPT, S.Uniform ∧ X = samplerLaw S n ∧ FinDist.IsSource (k n) X := Iff.rfl

/-- The `1`-bit function induced on `n`-bit strings by a string function: the first bit of its
output (`padFin 1`). -/
def extBit (Ext : List Bool → List Bool) (n : ℕ) : (Fin n → Bool) → (Fin 1 → Bool) :=
  fun x => padFin 1 (Ext (List.ofFn x))

/-- On an `n`-bit input `x`, `extBit Ext n` is the one-bit padding of `Ext (List.ofFn x)`:
`extBit Ext n x = padFin 1 (Ext (List.ofFn x))`. -/
theorem extBit_eq (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool) :
    extBit Ext n x = padFin 1 (Ext (List.ofFn x)) := rfl

/-- The uniform sampler at the fixed width `n` outputs its `n` coin bits and has no advice:
`(uniformSampler n).runAt n [] r = List.ofFn r` and `(uniformSampler n).coins = .const n`. -/
noncomputable def uniformSampler (n : ℕ) : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)

/-- The uniform sampler uses the constant coin polynomial `n`:
`(uniformSampler n).coins = .const n`. -/
theorem uniformSampler_coins (n : ℕ) : (uniformSampler n).coins = .const n :=
  NUPPT.coins_ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)

/-- The uniform sampler has empty advice at every activation parameter:
`(uniformSampler n).Uniform`, i.e. `∀ m, (uniformSampler n).advice m = []`. -/
theorem uniformSampler_uniform (n : ℕ) : (uniformSampler n).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform polyTimeComputable_pairSndD (.const n)

/-- The uniform sampler returns the encoding of its coin vector:
`(uniformSampler n).runAt n [] r = List.ofFn r`. -/
theorem uniformSampler_runAt (n : ℕ) (r : (uniformSampler n).Coins n) :
    (uniformSampler n).runAt n [] r = List.ofFn r := by
  rw [NUPPT.runAt_eq]
  change (NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD (.const n)).runAtL
    n [] (List.ofFn r) = _
  rw [NUPPT.runAtL_ofPolyTimeUniform, pairSndD_pairEncode]

/-- The coins of the uniform sampler are canonically the `n`-bit vectors:
`(uniformSampler n).Coins n ≃ (Fin n → Bool)`. -/
noncomputable def uniformSamplerCoins (n : ℕ) :
    (uniformSampler n).Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsEquivPoly (uniformSampler_coins n) n).trans
    (Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool))

/-- The canonical uniform-sampler coin equivalence is the composition of the published
coin-polynomial identification with the constant-polynomial width equality:
`uniformSamplerCoins n = e₁.trans e₂`, where `e₁ = NUPPT.coinsEquivPoly (uniformSampler_coins n) n`
and `e₂ = Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool)`. -/
theorem uniformSamplerCoins_eq (n : ℕ) : uniformSamplerCoins n =
    (NUPPT.coinsEquivPoly (uniformSampler_coins n) n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_const n n)) (Equiv.refl Bool)) := rfl

/-- The uniform sampler's coin equivalence preserves the encoded word:
`List.ofFn (uniformSamplerCoins n r) = List.ofFn r`. -/
theorem uniformSamplerCoins_ofFn (n : ℕ) (r : (uniformSampler n).Coins n) :
    List.ofFn (uniformSamplerCoins n r) = List.ofFn r := by
  rw [uniformSamplerCoins, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquivPoly_ofFn]

/-- The law of the sampler that returns its coins is the uniform law on `n`-bit strings:
`samplerLaw (uniformSampler n) n = U_n`.
The coin equivalence preserves encodings, and a bijection preserves uniformity. -/
theorem samplerLaw_uniformSampler (n : ℕ) :
    samplerLaw (uniformSampler n) n = FinDist.uniform (Fin n → Bool) := by
  have hread : (fun r : (uniformSampler n).Coins n =>
      padFin n ((uniformSampler n).runAt n [] r)) = uniformSamplerCoins n := by
    funext r
    rw [uniformSampler_runAt, ← uniformSamplerCoins_ofFn n r, padFin_ofFn]
  rw [samplerLaw, hread]
  exact Rejection.map_uniform_equiv (uniformSamplerCoins n)

/-- Uniform `n`-bit strings form an efficiently samplable `(n−2)`-source:
`U_n ∈ effSources (fun n => n - 2) n`. -/
theorem uniform_mem_effSources (n : ℕ) :
    FinDist.uniform (Fin n → Bool) ∈ effSources (fun n => (n : ℝ) - 2) n := by
  have hu : FinDist.IsSource (n : ℝ) (FinDist.uniform (Fin n → Bool)) := by
    simpa [Fintype.card_bool, Fintype.card_fin, Real.logb_pow] using
      (FinDist.isSource_uniform (α := Fin n → Bool))
  exact (effSources_iff _ _ _).2
    ⟨uniformSampler n, uniformSampler_uniform n, (samplerLaw_uniformSampler n).symm,
      hu.mono (by linarith)⟩

/-- The first output bit read by `extBit` is the head of the extractor's output,
with `false` for an empty output: `extBit Ext n x 0 = (Ext (List.ofFn x)).headD false`. -/
theorem extBit_zero (Ext : List Bool → List Bool) (n : ℕ) (x : Fin n → Bool) :
    extBit Ext n x 0 = (Ext (List.ofFn x)).headD false := by
  rw [extBit_eq, padFin_apply]
  cases Ext (List.ofFn x) <;> rfl

/-- A uniform one-bit word has its first bit true with probability `1/2`:
`Pr_{U_1}[fun x => x 0] = 1/2`. -/
theorem uniform_one_probTrue :
    (FinDist.uniform (Fin 1 → Bool)).probTrue (fun x => x 0) = 1 / 2 := by
  classical
  rw [FinDist.probTrue_eq]
  have hs : (Finset.univ : Finset (Fin 1 → Bool)).filter (fun x => x 0 = true) =
      {fun _ => true} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using h
    · rintro rfl
      rfl
  rw [hs, Finset.sum_singleton, FinDist.uniform_apply]
  norm_num

/-- If the candidate extractor succeeds on every efficient `(n−2)`-source, then its first
bit on the uniform source is true with probability at least `1/4`:
`IsExtractor (effSources (fun n => n - 2) n) (1/4) (extBit Ext n) →
1/4 ≤ Pr_{U_n}[fun x => extBit Ext n x 0]`.
The uniform source is efficient, so its output is within `1/4` of a fair bit. -/
theorem uniform_acceptance_lower (Ext : List Bool → List Bool) (n : ℕ)
    (h : IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n)) :
    1 / 4 ≤ (FinDist.uniform (Fin n → Bool)).probTrue (fun x => extBit Ext n x 0) := by
  have hclose := (isExtractor_iff.1 h) _ (uniform_mem_effSources n)
  have hb := (abs_probTrue_sub_le_statDist
    ((FinDist.uniform (Fin n → Bool)).map (extBit Ext n))
    (FinDist.uniform (Fin 1 → Bool)) (fun x => x 0)).trans
      (epsClose_iff_statDist_le.1 hclose)
  rw [Rejection.probTrue_map, uniform_one_probTrue] at hb
  have hl := (abs_le.1 hb).1
  linarith

/-- The bounded rejection machine's law at width `n` is the finite first-success law
on `t` trials and an independent uniform fallback:
`samplerLaw (RejectionSampler.machine hExt n t) n = Rejection.law D t`, where
`D a = (Ext (List.ofFn a)).headD false`.

**Proof sketch.** Its coin equivalence followed by the canonical block equivalence is a
bijection onto independent uniform blocks. The machine reader identifies its output with
the typed selector, whose pushforward is the rejection law. -/
theorem samplerLaw_rejection {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) :
    samplerLaw (RejectionSampler.machine hExt n t) n =
      Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t := by
  let D := fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false
  let e := (RejectionSampler.coinEquiv hExt n t n).trans (FunFamily.blocks (t + 1) n)
  have hread : (fun r : (RejectionSampler.machine hExt n t).Coins n =>
      padFin n ((RejectionSampler.machine hExt n t).runAt n [] r)) =
      (fun r => Rejection.select D t (e r)) := by
    funext r
    rw [RejectionSampler.machine_runAt, ← RejectionSampler.coinEquiv_ofFn hExt n t n r,
      RejectionSampler.chooseWord_blocks, padFin_ofFn]
    rfl
  rw [samplerLaw, hread,
    ← Rejection.map_map (FinDist.uniform ((RejectionSampler.machine hExt n t).Coins n))
      e (Rejection.select D t), Rejection.map_uniform_equiv e]
  exact Rejection.select_uniform_law D t

/-- Dividing a uniform `n`-bit point mass by `1/4` gives the exact `(n−2)`-source bound,
including `n=0,1,2`: `4 / 2^n = 2^(-(n-2))`. -/
theorem uniform_card_div_quarter (n : ℕ) :
    (Fintype.card (Fin n → Bool) : ℝ)⁻¹ / (1 / 4) =
      (2 : ℝ) ^ (-((n : ℝ) - 2)) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [show -((n : ℝ) - 2) = 2 - (n : ℝ) by ring,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  norm_num
  ring

/-- When uniform acceptance is at least `1/4`, ten rejection trials and a fresh fallback
produce an efficiently samplable `(n−2)`-source:
`1/4 ≤ Pr_{U_n}[D] → Rejection.law D 10 ∈ effSources (fun n => n - 2) n`, where
`D a = (Ext (List.ofFn a)).headD false`.

**Proof sketch.** The accepted flat source has point mass at most `1/(2^n q) ≤ 4/2^n`,
so it and the uniform law are `(n−2)`-sources. The exact convex mixture identity preserves
that bound, and the uniform machine realizes the mixture with `11n` coins. -/
theorem rejection_mem_effSources {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n : ℕ)
    (hq : 1 / 4 ≤ (FinDist.uniform (Fin n → Bool)).probTrue
      (fun a => (Ext (List.ofFn a)).headD false)) :
    Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) 10 ∈
      effSources (fun n => (n : ℝ) - 2) n := by
  let D := fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false
  have hqpos : 0 < (FinDist.uniform (Fin n → Bool)).probTrue D := by
    dsimp only [D]
    linarith
  have hbound : (Fintype.card (Fin n → Bool) : ℝ)⁻¹ /
      (FinDist.uniform (Fin n → Bool)).probTrue D ≤ (2 : ℝ) ^ (-((n : ℝ) - 2)) := by
    calc _ ≤ (Fintype.card (Fin n → Bool) : ℝ)⁻¹ / (1 / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hq
      _ = _ := uniform_card_div_quarter n
  obtain ⟨_, _, _, hU⟩ := (effSources_iff _ _ _).1 (uniform_mem_effSources n)
  have hflat := Rejection.accepted_flat_isSource D (Rejection.accepted_nonempty D hqpos)
    ((n : ℝ) - 2) hbound
  exact (effSources_iff _ _ _).2
    ⟨RejectionSampler.machine hExt n 10, RejectionSampler.machine_uniform hExt n 10,
      (samplerLaw_rejection hExt n 10).symm,
      Rejection.law_isSource D hqpos 10 ((n : ℝ) - 2) hU hflat⟩

/-- **Theorem 183.6: no efficient `1`-bit `1/4`-extractor for efficient `(n − 2)`-sources**
[PS10, Theorem 183.6]: for every polynomial-time `Ext` and every `n`, `Ext` is not a
`1/4`-extractor for the efficiently samplable `(n − 2)`-sources on `{0,1}^n`.

**Proof sketch** (the source's, made explicit; fix `n`).
1. `U_n` is the law of the uniform PPT that outputs its coins, and it is an `n`-source, hence an
   `(n − 2)`-source (`isSource_uniform`, `IsSource.mono`). If `Ext` is not `1/4`-close to `U_1` on
   it, `U_n` is the witness.
2. Otherwise `q = Pr[Ext(U_n) = 1] ≥ 1/4`, so `S = {x : Ext(x) = 1}` has `|S| ≥ 2^{n−2}`.
3. The sampler `X` with `11n` coins tries up to 10 `n`-bit blocks for `Ext(x) = 1`, else outputs
   the 11th block. At this fixed `n`, ten applications of the polynomial-time conditional
   combinator construct the sampler with constant coin polynomial `11n` and empty advice.
   The canonical block equivalence identifies its coins with eleven independent uniform blocks.
4. Its law is the mixture `(1 − q)^{10} U_n + (1 − (1 − q)^{10}) flat(S)` (rejection sampling).
   Both components are `(n − 2)`-sources, and min-entropy is preserved by mixtures (each point has
   probability at most `2^{−(n−2)}`).
5. `Pr[Ext(X) = 1] = 1 − (1 − q)^{11} ≥ 1 − (3/4)^{11} > 3/4`, so the statistical distance from
   `U_1` exceeds `1/4` (`abs_probTrue_sub_le_statDist`). `X` is the witness. -/
theorem not_isExtractor_effSources (Ext : List Bool → List Bool) (hExt : PolyTimeComputable Ext)
    (n : ℕ) :
    ¬ IsExtractor (effSources (fun n => (n : ℝ) - 2) n) (1 / 4) (extBit Ext n) := by
  intro h
  have hq := uniform_acceptance_lower Ext n h
  simp only [extBit_zero] at hq
  have hsource := rejection_mem_effSources hExt n hq
  have hclose := (isExtractor_iff.1 h) _ hsource
  have hb := (abs_probTrue_sub_le_statDist
    ((Rejection.law (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) 10).map
      (extBit Ext n))
    (FinDist.uniform (Fin 1 → Bool)) (fun x => x 0)).trans
      (epsClose_iff_statDist_le.1 hclose)
  rw [Rejection.probTrue_map, uniform_one_probTrue] at hb
  simp only [extBit_zero] at hb
  rw [Rejection.law_probTrue] at hb
  have hq1 := Rejection.probTrue_le_one (FinDist.uniform (Fin n → Bool))
    (fun a => (Ext (List.ofFn a)).headD false)
  have hpow :
      (1 - (FinDist.uniform (Fin n → Bool)).probTrue
        (fun a => (Ext (List.ofFn a)).headD false)) ^ 11 ≤ (3 / 4 : ℝ) ^ 11 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 11
  have hnum : (3 / 4 : ℝ) ^ 11 < 1 / 4 := by norm_num
  have hu := (abs_le.1 hb).2
  norm_num only [Nat.reduceAdd] at hu
  linarith

end TCSlib.Cryptography.Randomness

## ===== TCSlib/Cryptography/Randomness/Extraction/Rejection.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Samples
import TCSlib.InformationTheory.Entropy

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite rejection sampling

The first accepted point among `t` independent trials is returned; a final independent point
is returned when all trials fail. The resulting law and its acceptance probability are computed
from the published finite-distribution readers.

## Main definitions

* `Rejection.select`: the first accepted point among the first `t` entries, otherwise entry `t`.
* `Rejection.law`: the recursive distribution of this rejection sampler.

## Main results

* `Rejection.select_uniform_law`: the recursive law is the law of the finite tuple selector.
* `Rejection.law_eq_mixture`: the law is a mixture of uniform and the accepted flat law.
* `Rejection.law_probTrue`: its acceptance probability is `1-(1-q)^(t+1)`.
* `Rejection.law_isSource`: the source bound is preserved by this mixture.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.2, Theorem 183.6.
-/

namespace TCSlib.Cryptography.Randomness.Rejection

open TCSlib.InformationTheory Finset

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Pushing the uniform distribution through a bijection preserves uniformity:
`map e U_α = U_β`. -/
theorem map_uniform_equiv [DecidableEq β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (FinDist.uniform α).map e = FinDist.uniform β := by
  classical
  apply FinDist.ext
  intro b
  rw [FinDist.map_apply]
  have hf : (univ : Finset α).filter (fun a => e a = b) = {e.symm b} := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply b).symm)
    · rintro rfl
      exact e.apply_symm_apply b
  rw [hf, sum_singleton, FinDist.uniform_apply, FinDist.uniform_apply,
    Fintype.card_congr e]

/-- Summing a function over a pushforward is summing its composite over the original law:
`∑ b, map f p b · g b = ∑ a, p a · g (f a)`. The proof exchanges the two finite sums and
uses the unique image `f a` of each input. -/
theorem sum_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (∑ b, (p.map f) b * g b) = ∑ a, p a * g (f a) := by
  classical
  simp only [FinDist.map_apply, sum_mul, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_eq_single (f a)]
  · simp
  · intro b _ hba
    simp only [if_neg (Ne.symm hba), zero_mul]
  · intro h
    exact False.elim (h (mem_univ _))

/-- Expectation under a pushforward composes the test:
`E_{map f p}[g] = E_p[g ∘ f]`. -/
theorem expect_map [DecidableEq β] (p : FinDist α) (f : α → β) (g : β → ℝ) :
    (p.map f).expect g = p.expect (fun a => g (f a)) := by
  rw [FinDist.expect_eq, FinDist.expect_eq]
  exact sum_map p f g

/-- Acceptance under a pushforward composes the Boolean test:
`Pr_{map f p}[D] = Pr_p[D ∘ f]`. -/
theorem probTrue_map [DecidableEq β] (p : FinDist α) (f : α → β) (D : β → Bool) :
    (p.map f).probTrue D = p.probTrue (fun a => D (f a)) := by
  rw [FinDist.probTrue_eq_expect, expect_map, FinDist.probTrue_eq_expect]

/-- A Boolean acceptance probability is nonnegative: `0 ≤ Pr_p[D]`. -/
theorem probTrue_nonneg (p : FinDist α) (D : α → Bool) : 0 ≤ p.probTrue D := by
  rw [FinDist.probTrue_eq]
  exact sum_nonneg fun a _ => p.nonneg a

/-- A Boolean acceptance probability is at most one: `Pr_p[D] ≤ 1`. -/
theorem probTrue_le_one (p : FinDist α) (D : α → Bool) : p.probTrue D ≤ 1 := by
  rw [FinDist.probTrue_eq, ← p.sum_prob]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a _ _ => p.nonneg a)

/-- A pushforward's mass at `b` is the expectation of its preimage indicator:
`map f p b = E_p[1_{f(a)=b}]`. -/
theorem map_apply_expect [DecidableEq β] (p : FinDist α) (f : α → β) (b : β) :
    (p.map f) b = p.expect (fun a => if f a = b then 1 else 0) := by
  classical
  rw [FinDist.map_apply, FinDist.expect_eq, sum_filter]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp

/-- Successive pushforwards compose: `map g (map f p) = map (g ∘ f) p`. -/
theorem map_map [DecidableEq β] [DecidableEq γ] (p : FinDist α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (fun a => g (f a)) := by
  classical
  apply FinDist.ext
  intro c
  rw [map_apply_expect, expect_map, map_apply_expect]

/-- Mapping only the second coordinate of an independent pair can be done before or after
pairing: `map g (p × map f q) = map (fun (x,y) => g (x,f y)) (p × q)`. -/
theorem map_prod_snd [DecidableEq β] [DecidableEq γ] {δ : Type*} [Fintype δ]
    [DecidableEq δ] (p : FinDist α) (q : FinDist β) (f : β → γ) (g : α × γ → δ) :
    (p.prod (q.map f)).map g = (p.prod q).map (fun z => g (z.1, f z.2)) := by
  classical
  apply FinDist.ext
  intro d
  rw [map_apply_expect, map_apply_expect, FinDist.expect_prod, FinDist.expect_prod]
  congr 1
  funext a
  exact expect_map q f (fun c => if g (a, c) = d then 1 else 0)

/-- The product of two uniform laws is the uniform law on pairs: `U_α × U_β = U_(α×β)`. -/
theorem uniform_prod [Nonempty α] [Nonempty β] :
    (FinDist.uniform α).prod (FinDist.uniform β) = FinDist.uniform (α × β) := by
  apply FinDist.ext
  intro z
  rw [FinDist.prod_apply, FinDist.uniform_apply, FinDist.uniform_apply,
    FinDist.uniform_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

/-- A nonempty tuple is equivalent to its first entry and its tail:
`(Fin (t+1+1) → α) ≃ α × (Fin (t+1) → α)`. -/
def tupleEquiv (t : ℕ) : (Fin (t + 1 + 1) → α) ≃ α × (Fin (t + 1) → α) where
  toFun x := (x 0, fun i => x i.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv z := by
    apply Prod.ext
    · simp
    · funext i
      simp

/-- The tuple equivalence reads the first entry and the tail:
`tupleEquiv t x = (x 0, fun i => x i.succ)`. -/
theorem tupleEquiv_apply (t : ℕ) (x : Fin (t + 1 + 1) → α) :
    tupleEquiv t x = (x 0, fun i => x i.succ) := rfl

/-- The inverse tuple equivalence prepends its first coordinate:
`(tupleEquiv t).symm (a,x) = Fin.cons a x`. -/
theorem tupleEquiv_symm_apply (t : ℕ) (z : α × (Fin (t + 1) → α)) :
    (tupleEquiv t).symm z = Fin.cons z.1 z.2 := rfl

/-- The first entry of the inverse tuple equivalence is the pair's first coordinate:
`(tupleEquiv t).symm z 0 = z.1`. -/
theorem tupleEquiv_symm_zero (t : ℕ) (z : α × (Fin (t + 1) → α)) :
    (tupleEquiv t).symm z 0 = z.1 := by
  rw [tupleEquiv_symm_apply]
  simp

/-- Each successor entry of the inverse tuple equivalence is the corresponding tail entry:
`(tupleEquiv t).symm z i.succ = z.2 i`. -/
theorem tupleEquiv_symm_succ (t : ℕ) (z : α × (Fin (t + 1) → α)) (i : Fin (t + 1)) :
    (tupleEquiv t).symm z i.succ = z.2 i := by
  rw [tupleEquiv_symm_apply]
  simp

/-- Select the first accepted entry among `t` trials; if all fail, return the final entry:
`select D 0 x = x 0` and `select D (t+1) x = if D (x 0) then x 0 else select D t (x ∘ succ)`.
There are `t+1` entries in total, so the fallback is always present. -/
def select (D : α → Bool) : (t : ℕ) → (Fin (t + 1) → α) → α
  | 0, x => x 0
  | t + 1, x => if D (x 0) then x 0 else select D t (fun i => x i.succ)

/-- With no rejection trials, the selector returns its sole entry: `select D 0 x = x 0`. -/
theorem select_zero (D : α → Bool) (x : Fin 1 → α) : select D 0 x = x 0 := rfl

/-- With one more rejection trial, accept the first entry if its test succeeds, otherwise
select from the tail: `select D (t+1) x = if D (x 0) then x 0 else select D t (x ∘ succ)`. -/
theorem select_succ (D : α → Bool) (t : ℕ) (x : Fin (t + 1 + 1) → α) :
    select D (t + 1) x = if D (x 0) then x 0 else select D t (fun i => x i.succ) := rfl

/-- The law of rejection sampling with `t` trials and an independent uniform fallback:
`law D 0 = U_α` and `law D (t+1) = map (fun (x,y) => if D x then x else y) (U_α × law D t)`.
At each trial, a fresh uniform point is accepted if its test succeeds. -/
noncomputable def law [DecidableEq α] [Nonempty α] (D : α → Bool) : ℕ → FinDist α
  | 0 => FinDist.uniform α
  | t + 1 => ((FinDist.uniform α).prod (law D t)).map
      (fun z => if D z.1 then z.1 else z.2)

/-- With zero trials, the rejection law is uniform: `law D 0 = U_α`. -/
theorem law_zero [DecidableEq α] [Nonempty α] (D : α → Bool) :
    law D 0 = FinDist.uniform α := rfl

/-- One more trial draws a fresh uniform point independently of the remaining sampler:
`law D (t+1) = map (fun (x,y) => if D x then x else y) (U_α × law D t)`. -/
theorem law_succ [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    law D (t + 1) = ((FinDist.uniform α).prod (law D t)).map
      (fun z => if D z.1 then z.1 else z.2) := rfl

/-- Selecting from `t+1` independent uniform entries has the recursive rejection law:
`map (select D t) U_(α^(t+1)) = law D t`.

**Proof sketch.** Split a tuple into its first entry and its tail. Uniformity is preserved by
this bijection, and uniformity on pairs is the product of the two uniform laws. The induction
hypothesis identifies the selected tail with the remaining rejection sampler. -/
theorem select_uniform_law [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    (FinDist.uniform (Fin (t + 1) → α)).map (select D t) = law D t := by
  classical
  induction t with
  | zero =>
    rw [law_zero]
    let e : (Fin 1 → α) ≃ α :=
      { toFun := fun x => x 0
        invFun := fun a _ => a
        left_inv := by
          intro x
          funext i
          have hi : i = 0 := Subsingleton.elim _ _
          rw [hi]
        right_inv := fun _ => rfl }
    exact map_uniform_equiv e
  | succ t ih =>
    rw [law_succ, ← ih]
    have hu : FinDist.uniform (Fin (t + 1 + 1) → α) =
        (FinDist.uniform (α × (Fin (t + 1) → α))).map (tupleEquiv t).symm :=
      (map_uniform_equiv (tupleEquiv (α := α) t).symm).symm
    rw [hu, map_map, ← uniform_prod, map_prod_snd]
    congr 1

/-- Independent branching returns the first point on acceptance and the second on rejection:
`map (fun (x,y) => if D x then x else y) (p × q) a = 1_{D(a)} p(a) + (1-Pr_p[D]) q(a)`.

**Proof sketch.** Expand the map and product readers. For a fixed first point, the inner sum
is either its whole mass or the mass of the second point at `a`. Split the outer sum into
accepted and rejected first points. -/
theorem branch_apply [DecidableEq α] (p q : FinDist α) (D : α → Bool) (a : α) :
    ((p.prod q).map (fun z => if D z.1 then z.1 else z.2)) a =
      (if D a then p a else 0) + (1 - p.probTrue D) * q a := by
  classical
  rw [FinDist.map_apply, sum_filter, Fintype.sum_prod_type]
  simp only [FinDist.prod_apply]
  have inner (x : α) :
      (∑ y, if (if D x then x else y) = a then p x * q y else 0) =
        if D x then (if x = a then p x else 0) else p x * q a := by
    cases hd : D x
    · simp [hd]
    · by_cases hxa : x = a
      · simp [hd, hxa, ← mul_sum, q.sum_prob]
      · simp [hd, hxa]
  simp_rw [inner]
  have split (x : α) :
      (if D x then (if x = a then p x else 0) else p x * q a) =
        (if x = a then (if D a then p a else 0) else 0) +
          (if !D x then p x * q a else 0) := by
    by_cases hxa : x = a
    · subst x
      cases D a <;> simp
    · cases hd : D x <;> simp [hd, hxa]
  simp_rw [split]
  rw [sum_add_distrib]
  have hn : (∑ x, if !D x then p x * q a else 0) =
      (1 - p.probTrue D) * q a := by
    rw [← FinDist.probTrue_not, FinDist.probTrue_eq, sum_mul, sum_filter]
  rw [hn]
  simp

/-- One rejection trial satisfies the point recurrence
`law D (t+1) a = 1_{D(a)} / |α| + (1-q) law D t a`, where `q = Pr_{U_α}[D]`. -/
theorem law_succ_apply [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) (a : α) :
    law D (t + 1) a =
      (if D a then (Fintype.card α : ℝ)⁻¹ else 0) +
        (1 - (FinDist.uniform α).probTrue D) * law D t a := by
  rw [law_succ, branch_apply, FinDist.uniform_apply]

/-- The acceptance probabilities obey
`Pr_{law D (t+1)}[D] = q + (1-q) Pr_{law D t}[D]`. -/
theorem law_succ_probTrue [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    (law D (t + 1)).probTrue D =
      (FinDist.uniform α).probTrue D +
        (1 - (FinDist.uniform α).probTrue D) * (law D t).probTrue D := by
  classical
  rw [FinDist.probTrue_eq]
  simp_rw [law_succ_apply]
  rw [sum_add_distrib, ← mul_sum]
  have hi : (∑ a ∈ (univ : Finset α).filter (fun a => D a = true),
      if D a then (Fintype.card α : ℝ)⁻¹ else 0) = (FinDist.uniform α).probTrue D := by
    rw [FinDist.probTrue_eq]
    apply sum_congr rfl
    intro a ha
    simp [(mem_filter.1 ha).2, FinDist.uniform_apply]
  rw [hi, ← FinDist.probTrue_eq (law D t) D]

/-- The rejection sampler accepts with probability `1-(1-q)^(t+1)`, including the independent
fallback's chance to accept. This formula also holds for `q=0` and `q=1`.

**Proof sketch.** The zero-trial law has acceptance `q`. Each additional trial fails with
probability `1-q`, multiplying the probability that the remaining sampler fails by that factor. -/
theorem law_probTrue [DecidableEq α] [Nonempty α] (D : α → Bool) (t : ℕ) :
    (law D t).probTrue D = 1 - (1 - (FinDist.uniform α).probTrue D) ^ (t + 1) := by
  induction t with
  | zero => rw [law_zero]; ring
  | succ t ih => rw [law_succ_probTrue, ih, pow_succ]; ring

/-- For positive uniform acceptance `q = Pr_{U_α}[D] > 0`, the rejection law's point mass is
`law D t a = (1-q)^t / |α| + 1_{D(a)} (1-(1-q)^t) / (|α| q)`.

**Proof sketch.** Induct on the trial count using the point recurrence. On accepted points the
geometric sum contributes `(1-(1-q)^t)/q`; on rejected points only the fallback contributes. -/
theorem law_apply [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (a : α) :
    law D t a =
      (1 - (FinDist.uniform α).probTrue D) ^ t * (Fintype.card α : ℝ)⁻¹ +
        (if D a then
          (1 - (1 - (FinDist.uniform α).probTrue D) ^ t) *
            (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D else 0) := by
  have hq0 : (FinDist.uniform α).probTrue D ≠ 0 := ne_of_gt hq
  induction t with
  | zero => rw [law_zero, FinDist.uniform_apply]; simp
  | succ t ih =>
    rw [law_succ_apply, ih, pow_succ]
    cases D a <;> simp
    · ring
    · field_simp [hq0]
      <;> ring

/-- Uniform acceptance is the cardinality of the accepted set divided by the whole cardinality:
`Pr_{U_α}[D] = |{a : D a}| / |α|`. -/
theorem uniform_probTrue [Nonempty α] (D : α → Bool) :
    (FinDist.uniform α).probTrue D =
      (((univ : Finset α).filter (fun a => D a = true)).card : ℝ) *
        (Fintype.card α : ℝ)⁻¹ := by
  classical
  rw [FinDist.probTrue_eq]
  simp only [FinDist.uniform_apply, sum_const, nsmul_eq_mul]

/-- Positive uniform acceptance implies that the accepted set is nonempty:
`0 < Pr_{U_α}[D] → {a : D a}.Nonempty`. -/
theorem accepted_nonempty [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) :
    ((univ : Finset α).filter (fun a => D a = true)).Nonempty := by
  classical
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.1 h
  have hz : (FinDist.uniform α).probTrue D = 0 := by
    rw [FinDist.probTrue_eq, he, sum_empty]
  linarith

/-- The flat law on the accepted set has point mass `1/(|α| q)` at accepted points and zero
elsewhere, where `q=Pr_{U_α}[D]`. -/
theorem accepted_flat_apply [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hs : ((univ : Finset α).filter (fun a => D a = true)).Nonempty) (a : α) :
    FinDist.flat ((univ : Finset α).filter (fun a => D a = true)) hs a =
      if D a then (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D else 0 := by
  classical
  rw [FinDist.flat_apply]
  have hm : a ∈ (univ : Finset α).filter (fun a => D a = true) ↔ D a = true := by simp
  simp only [hm]
  by_cases hd : D a = true
  · rw [if_pos hd, if_pos hd, uniform_probTrue]
    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hs0 : ((((univ : Finset α).filter (fun a => D a = true)).card : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 hs.card_pos.ne'
    field_simp [hc, hs0]
  · rw [if_neg hd, if_neg hd]

/-- The rejection law is the pointwise mixture
`(1-q)^t U_α + (1-(1-q)^t) flat({a : D a})` for `q>0`. -/
theorem law_apply_flat [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (a : α) :
    law D t a =
      (1 - (FinDist.uniform α).probTrue D) ^ t * (FinDist.uniform α) a +
        (1 - (1 - (FinDist.uniform α).probTrue D) ^ t) *
          FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
            (accepted_nonempty D hq) a := by
  rw [law_apply D hq, FinDist.uniform_apply, accepted_flat_apply]
  cases D a <;> simp <;> ring

/-- A mixture of `p` and `q` with weight `w∈[0,1]` gives mass
`w p(a) + (1-w) q(a)` to each point. -/
noncomputable def mixture (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) : FinDist α where
  prob a := w * p a + (1 - w) * q a
  nonneg a := add_nonneg (mul_nonneg hw0 (p.nonneg a))
    (mul_nonneg (sub_nonneg.2 hw1) (q.nonneg a))
  sum_prob := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, p.sum_prob, q.sum_prob]
    ring

/-- The point probability of the mixture is its defining convex combination:
`mixture w p q a = w p(a) + (1-w) q(a)`. -/
theorem mixture_apply (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) (a : α) :
    mixture w hw0 hw1 p q a = w * p a + (1 - w) * q a := rfl

/-- Mixtures of two `k`-sources are `k`-sources:
`IsSource k p → IsSource k q → IsSource k (mixture w p q)`. Their point probabilities share
the same upper bound `2^(-k)`, which is preserved by a convex combination. -/
theorem mixture_isSource (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (p q : FinDist α) (k : ℝ) (hp : FinDist.IsSource k p) (hq : FinDist.IsSource k q) :
    FinDist.IsSource k (mixture w hw0 hw1 p q) := by
  have hp' := (FinDist.hasMinEntropy_iff p k).1
    (FinDist.isSource_iff_hasMinEntropy.1 hp)
  have hq' := (FinDist.hasMinEntropy_iff q k).1
    (FinDist.isSource_iff_hasMinEntropy.1 hq)
  apply FinDist.isSource_iff_hasMinEntropy.2
  apply (FinDist.hasMinEntropy_iff _ _).2
  intro a
  rw [mixture_apply]
  calc w * p a + (1 - w) * q a
      ≤ w * (2 : ℝ) ^ (-k) + (1 - w) * (2 : ℝ) ^ (-k) :=
        add_le_add (mul_le_mul_of_nonneg_left (hp' a) hw0)
          (mul_le_mul_of_nonneg_left (hq' a) (sub_nonneg.2 hw1))
    _ = (2 : ℝ) ^ (-k) := by ring

/-- The probability `(1-q)^t` that all rejection trials fail is nonnegative:
`0 ≤ (1-Pr_{U_α}[D])^t`. -/
theorem failure_pow_nonneg [Nonempty α] (D : α → Bool) (t : ℕ) :
    0 ≤ (1 - (FinDist.uniform α).probTrue D) ^ t :=
  pow_nonneg (sub_nonneg.2 (probTrue_le_one _ _)) _

/-- The probability `(1-q)^t` that all rejection trials fail is at most one:
`(1-Pr_{U_α}[D])^t ≤ 1`. -/
theorem failure_pow_le_one [Nonempty α] (D : α → Bool) (t : ℕ) :
    (1 - (FinDist.uniform α).probTrue D) ^ t ≤ 1 := by
  have hb0 : 0 ≤ 1 - (FinDist.uniform α).probTrue D :=
    sub_nonneg.2 (probTrue_le_one _ _)
  have hb1 : 1 - (FinDist.uniform α).probTrue D ≤ 1 := by
    linarith [probTrue_nonneg (FinDist.uniform α) D]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ]
    calc (1 - (FinDist.uniform α).probTrue D) ^ t *
        (1 - (FinDist.uniform α).probTrue D) ≤ 1 * 1 := mul_le_mul ih hb1 hb0 zero_le_one
      _ = 1 := one_mul _

/-- The rejection law is exactly the convex mixture
`law D t = mixture ((1-q)^t) U_α flat({a : D a})` for `q = Pr_{U_α}[D] > 0`, that is,
`(1-q)^t U_α + (1-(1-q)^t) flat({a : D a})`. -/
theorem law_eq_mixture [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) :
    law D t = mixture ((1 - (FinDist.uniform α).probTrue D) ^ t)
      (failure_pow_nonneg D t) (failure_pow_le_one D t) (FinDist.uniform α)
      (FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
        (accepted_nonempty D hq)) := by
  apply FinDist.ext
  intro a
  rw [mixture_apply]
  exact law_apply_flat D hq t a

/-- If `1/(|α|q) ≤ 2^(-k)`, the flat law on the accepted set is a `k`-source. -/
theorem accepted_flat_isSource [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hs : ((univ : Finset α).filter (fun a => D a = true)).Nonempty) (k : ℝ)
    (hbound : (Fintype.card α : ℝ)⁻¹ / (FinDist.uniform α).probTrue D ≤ (2 : ℝ) ^ (-k)) :
    FinDist.IsSource k (FinDist.flat ((univ : Finset α).filter (fun a => D a = true)) hs) := by
  apply FinDist.isSource_iff_hasMinEntropy.2
  apply (FinDist.hasMinEntropy_iff _ _).2
  intro a
  rw [accepted_flat_apply]
  split_ifs
  · exact hbound
  · positivity

/-- The rejection law is a `k`-source whenever its uniform and accepted-flat components are
`k`-sources: `IsSource k U_α → IsSource k flat({a : D a}) → IsSource k (law D t)`.
This follows from its exact mixture identity and convexity of the point bound. -/
theorem law_isSource [DecidableEq α] [Nonempty α] (D : α → Bool)
    (hq : 0 < (FinDist.uniform α).probTrue D) (t : ℕ) (k : ℝ)
    (hU : FinDist.IsSource k (FinDist.uniform α))
    (hflat : FinDist.IsSource k
      (FinDist.flat ((univ : Finset α).filter (fun a => D a = true))
        (accepted_nonempty D hq))) :
    FinDist.IsSource k (law D t) := by
  rw [law_eq_mixture D hq t]
  exact mixture_isSource _ _ _ _ _ _ hU hflat

end TCSlib.Cryptography.Randomness.Rejection

## ===== TCSlib/Cryptography/Randomness/Extraction/Sampler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Complexity.ClassP.BinaryArith.Basic
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
import TCSlib.Cryptography.Randomness.Extraction.Rejection

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A bounded rejection sampler on consecutive coin blocks

The sampler used in [PS10, Theorem 183.6] reads a fixed number of blocks and returns the
first whose extractor output starts with `true`, using the last block as a fallback.
The security parameter at which the counterexample is needed is fixed before the sampler
is chosen, so fixed block widths and a constant coin polynomial suffice. The resulting
machine has no advice and is therefore uniform.

## Main definitions

* `RejectionSampler.chooseWord`: bounded first-success selection from a bit tape.
* `RejectionSampler.machine`: the uniform PPT implementing the selection.
* `RejectionSampler.coinEquiv`: its coins as a tape of exactly `(t + 1) * n` bits.

## Main results

* `RejectionSampler.chooseWord_poly`: fixed-width bounded selection is polynomial-time.
* `RejectionSampler.chooseWord_blocks`: its typed interpretation is `Rejection.select`.
* `RejectionSampler.machine_runAt_coinEquiv`: the machine implements that tape selection.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §8.3.2, Theorem 183.6.
-/

namespace TCSlib.Cryptography.Randomness.RejectionSampler

open Complexity Turing

/-- Trying `t` blocks of width `n` and falling back to block `t` means returning the first
block whose extractor output starts with `true`, or the final block if every test fails:
`chooseWord Ext n 0 r = r.take n`, and `chooseWord Ext n (t+1) r = r.take n` if
`(Ext (r.take n)).headD false`, otherwise
`chooseWord Ext n (t+1) r = chooseWord Ext n t (r.drop n)`.
[PS10, Theorem 183.6]. Short input tapes are truncated by `List.take`. -/
def chooseWord (Ext : List Bool → List Bool) (n : ℕ) : ℕ → List Bool → List Bool
  | 0, r => r.take n
  | t + 1, r =>
      if (Ext (r.take n)).headD false then r.take n else chooseWord Ext n t (r.drop n)

/-- With no trials, `chooseWord` returns the first `n` bits: `chooseWord Ext n 0 r = r.take n`.
-/
theorem chooseWord_zero (Ext : List Bool → List Bool) (n : ℕ) (r : List Bool) :
    chooseWord Ext n 0 r = r.take n := rfl

/-- One additional trial tests the first block, returning it on acceptance and otherwise
running the remaining trials on the tape with that block dropped:
`chooseWord Ext n (t+1) r = if (Ext (r.take n)).headD false then r.take n else
chooseWord Ext n t (r.drop n)`. -/
theorem chooseWord_succ (Ext : List Bool → List Bool) (n t : ℕ) (r : List Bool) :
    chooseWord Ext n (t + 1) r =
      if (Ext (r.take n)).headD false then r.take n else chooseWord Ext n t (r.drop n) := rfl

/-- Taking any fixed number `n` of input bits is polynomial-time computable:
`PolyTimeComputable (fun r : List Bool => r.take n)`.

**Proof sketch.** Pair a constant unary word of length `n` with the input and apply the
published length-gated prefix machine. -/
theorem take_poly (n : ℕ) : PolyTimeComputable (fun r : List Bool => r.take n) := by
  have henc : PolyTimeComputable fun r => pairEncode (List.replicate n true) r :=
    (polyTimeComputable_const (List.replicate n true)).pairEncode polyTimeComputable_id
  have h := polyTimeComputable_takePrefixByLength.comp henc
  convert h using 1
  funext r
  change r.take n = PrefixByLength.take (pairEncode (List.replicate n true) r)
  rw [PrefixByLength.take_def, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- If `Ext` is polynomial-time, the fixed-width sampler with any fixed number of trials is
polynomial-time: `PolyTimeComputable Ext → PolyTimeComputable (chooseWord Ext n t)`.
[PS10, Theorem 183.6, the efficiency claim].

**Proof sketch.** Induct on the fixed number of trials. The head-bit test composes the
extractor with a fixed prefix, and the conditional combinator joins that prefix with the
inductively constructed sampler on the fixed-width suffix. -/
theorem chooseWord_poly {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : PolyTimeComputable (chooseWord Ext n t) := by
  induction t with
  | zero =>
    convert take_poly n using 1
  | succ t ih =>
    have htest : PolyTimeComputable fun r => [(Ext (r.take n)).headD false] :=
      polyTimeComputable_headD.comp (hExt.comp (take_poly n))
    have h := polyTimeComputable_ite htest (take_poly n)
      (ih.comp (BinArith.polyTimeComputable_drop n))
    convert h using 1

/-- On a concatenated tuple of `n`-bit blocks, string selection encodes typed selection:
`chooseWord Ext n t (flatten (ofFn (ofFn ∘ x))) = ofFn (select D t x)`, where
`D a = (Ext (ofFn a)).headD false`.

**Proof sketch.** At each successor trial, `take n` reads the first encoded block and
`drop n` leaves the concatenation of the remaining blocks. Both selectors therefore make
the same branch choice; induction identifies the remaining trials. -/
theorem chooseWord_flatten (Ext : List Bool → List Bool) (n t : ℕ)
    (x : Fin (t + 1) → Fin n → Bool) :
    chooseWord Ext n t (List.ofFn fun i => List.ofFn (x i)).flatten =
      List.ofFn
        (Rejection.select (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t x) := by
  induction t with
  | zero =>
    rw [Rejection.select_zero, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil, chooseWord_zero]
    exact List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
  | succ t ih =>
    have hflat : (List.ofFn fun i : Fin (t + 1 + 1) => List.ofFn (x i)).flatten =
        List.ofFn (x 0) ++ (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten := by
      rw [List.ofFn_succ, List.flatten_cons]
    have ht : (List.ofFn (x 0) ++
        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten).take n =
        List.ofFn (x 0) := List.take_left' List.length_ofFn
    have hd : (List.ofFn (x 0) ++
        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten).drop n =
        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten :=
      List.drop_left' List.length_ofFn
    rw [hflat, chooseWord_succ, ht, hd, Rejection.select_succ]
    split_ifs
    · rfl
    · exact ih (fun i => x i.succ)

/-- On `(t + 1) * n` uniform coin bits, `chooseWord` encodes typed first-success selection
from the canonical `(t + 1)` blocks. This includes `n = 0`. -/
theorem chooseWord_blocks (Ext : List Bool → List Bool) (n t : ℕ)
    (r : Fin ((t + 1) * n) → Bool) :
    chooseWord Ext n t (List.ofFn r) =
      List.ofFn (Rejection.select (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t
        (FunFamily.blocks (t + 1) n r)) := by
  have h := FunFamily.ofFn_blocks_symm (t + 1) n (FunFamily.blocks (t + 1) n r)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  exact chooseWord_flatten Ext n t _

/-- The bounded rejection machine on `(t + 1) * n` coins has empty advice and runs
`chooseWord Ext n t` on its coin tape: `(machine hExt n t).runAtL m y r = chooseWord Ext n t r`
and `(machine hExt n t).coins = .const ((t + 1) * n)`. [PS10, Theorem 183.6]. -/
noncomputable def machine {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : NUPPT :=
  NUPPT.ofPolyTimeUniform ((chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD)
    (.const ((t + 1) * n))

/-- The rejection machine packages the polynomial-time coin function with constant coin
polynomial `(t + 1) * n` and empty advice:
`machine hExt n t = NUPPT.ofPolyTimeUniform f (.const ((t + 1) * n))`, where `f` is
`(chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD`. -/
theorem machine_eq {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext) (n t : ℕ) :
    machine hExt n t =
      NUPPT.ofPolyTimeUniform ((chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD)
        (.const ((t + 1) * n)) := rfl

/-- The bounded rejection machine is uniform: it has empty advice at every parameter,
`(machine hExt n t).Uniform`, i.e. `∀ m, (machine hExt n t).advice m = []`. -/
theorem machine_uniform {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : (machine hExt n t).Uniform := by
  rw [machine_eq]
  exact NUPPT.ofPolyTimeUniform_uniform _ _

/-- The rejection machine's coin polynomial is the constant `(t + 1) * n`:
`(machine hExt n t).coins = .const ((t + 1) * n)`. -/
theorem machine_coins {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : (machine hExt n t).coins = .const ((t + 1) * n) := by
  rw [machine_eq, NUPPT.coins_ofPolyTimeUniform]

/-- On an untyped coin tape `r`, at every activation parameter and argument, the rejection
machine returns `chooseWord Ext n t r`: `(machine hExt n t).runAtL m y r = chooseWord Ext n t r`.
-/
theorem machine_runAtL {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (y r : List Bool) :
    (machine hExt n t).runAtL m y r = chooseWord Ext n t r := by
  rw [machine_eq, NUPPT.runAtL_ofPolyTimeUniform]
  change chooseWord Ext n t (pairSndD (pairEncode (pairEncode (NUPPT.advInput m y) []) r)) = _
  rw [pairSndD_pairEncode]

/-- On typed coins, the rejection machine runs `chooseWord` on the coin string:
`(machine hExt n t).runAt m y r = chooseWord Ext n t (List.ofFn r)`. -/
theorem machine_runAt {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (y : List Bool) (r : (machine hExt n t).Coins m) :
    (machine hExt n t).runAt m y r = chooseWord Ext n t (List.ofFn r) := by
  rw [NUPPT.runAt_eq, machine_runAtL]

/-- At every activation parameter, the rejection machine uses exactly `(t + 1) * n` bits:
`(machine hExt n t).coinLen m = (t + 1) * n`. -/
theorem machine_coinLen {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) : (machine hExt n t).coinLen m = (t + 1) * n := by
  rw [NUPPT.coinLen_eq, machine_coins, PolyExpr.eval_const]

/-- The rejection machine's coins are canonically the bit tape of length `(t + 1) * n`,
independently of its activation parameter:
`(machine hExt n t).Coins m ≃ (Fin ((t + 1) * n) → Bool)`. -/
noncomputable def coinEquiv {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) : (machine hExt n t).Coins m ≃ (Fin ((t + 1) * n) → Bool) :=
  Equiv.arrowCongr (finCongr (machine_coinLen hExt n t m)) (Equiv.refl Bool)

/-- The canonical rejection-coin equivalence is the arrow equivalence induced by the
published equality `coinLen m = (t + 1) * n`. -/
theorem coinEquiv_eq {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) : coinEquiv hExt n t m =
      Equiv.arrowCongr (finCongr (machine_coinLen hExt n t m)) (Equiv.refl Bool) := rfl

/-- The canonical rejection-coin equivalence preserves the encoded coin string:
`List.ofFn (coinEquiv hExt n t m r) = List.ofFn r`. -/
theorem coinEquiv_ofFn {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (r : (machine hExt n t).Coins m) :
    List.ofFn (coinEquiv hExt n t m r) = List.ofFn r :=
  (List.ofFn_congr (machine_coinLen hExt n t m) r).symm

/-- The inverse canonical rejection-coin equivalence preserves the encoded coin string:
`List.ofFn ((coinEquiv hExt n t m).symm r) = List.ofFn r`. -/
theorem coinEquiv_symm_ofFn {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (r : Fin ((t + 1) * n) → Bool) :
    List.ofFn ((coinEquiv hExt n t m).symm r) = List.ofFn r := by
  rw [← coinEquiv_ofFn hExt n t m, Equiv.apply_symm_apply]

/-- Running the rejection machine on a tape transported through `coinEquiv` is precisely
`chooseWord Ext n t` on that tape:
`(machine hExt n t).runAt m y ((coinEquiv hExt n t m).symm r) = chooseWord Ext n t (List.ofFn r)`.
-/
theorem machine_runAt_coinEquiv {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (y : List Bool) (r : Fin ((t + 1) * n) → Bool) :
    (machine hExt n t).runAt m y ((coinEquiv hExt n t m).symm r) =
      chooseWord Ext n t (List.ofFn r) := by
  rw [machine_runAt, coinEquiv_symm_ofFn]

end TCSlib.Cryptography.Randomness.RejectionSampler

## ===== TCSlib/Cryptography/Randomness.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.Extraction
import TCSlib.Cryptography.Randomness.Extraction.Rejection
import TCSlib.Cryptography.Randomness.Extraction.Sampler
import TCSlib.Cryptography.Randomness.Learning
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Randomness.Derandomization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomness, learning and derandomization

The definitions, constructions and theorem statements of [PS10, Chapter 8].
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Extraction` — no efficient one-bit extractor for the stated efficient-source class.
* `Learning` — PRFs give a hard-to-predict concept class.
* `BPPBridge` — the public bridge from BPP computations to distinguishers.
* `Derandomization` — PRGs give the BPP deterministic-time inclusion.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
