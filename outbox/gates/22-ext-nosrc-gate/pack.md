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
