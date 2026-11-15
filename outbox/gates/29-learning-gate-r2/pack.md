# Gate 29 · PRF concepts are not efficiently predictable (`learning`, Theorem 179.1(b))

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #313](https://github.com/Shilun-Allan-Li/tcslib/pull/313) at
  `8befc58966fd39f974a54250849736df194584b9` (branch `land/pass-shelat-learning`, tree
  `5ad10b2805cd43d65c290e31b4140ca233ef1b9a`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `4561c3407f9f015da55255a6a4cbcfc5840fd1f3` (the merge base).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. Between the issue base and the PR base, the
    only merged PR that changes non-record files is #307 (dl-crh, merge `25fe1c05`). None of its 9 modules is in the
    unit's closure (review evidence `order/pr307-modules.txt`, `order/unit-closure.txt`).
  - From the PR base to the records tip `f52a24be7442013d00bef3608ce5336429dd4719` there are 22 commits. Their only
    non-record paths are #311's `SecureComputation.lean` and `SecureComputation/SpecialEncryptionMulti.lean`, #312's
    `Complexity/Randomized.lean` and `Complexity/Randomized/SeedMajority.lean`, and `machine-library-design.md`.
    Re-checked for this pack from git objects: no path is shared with the PR; none of those modules is in the import
    closure, at the head, of a changed module (138 files); the only tip module downstream of both a delta module
    and a PR module is root `TCSlib`. `git merge-tree --write-tree` of the tip with the head gives tree
    `0d41a4a2fd1a2c6fa9aceeb42878b3075a9c51ed` with no conflict.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...8befc589`, which equals
    `4561c340..8befc589` byte for byte.
- **Commits:** 5.
  - The Claude worker's 3 commits (job `learning`), applied with `git am` with the delivered committer data (every
    worker hash reproduces) and rebased onto `4561c340` without conflict, author kept:
    `876145de248c691b5724a2d594ad3ab6b2744a17` (checkpoint 1: the distinguisher and the real game),
    `331c15f4d66e99537c59403b6bc77eb952a52e47` (checkpoint 2: the random function) and
    `b4caa53bb4a8f51e30789f282080ed0eb8d2827a` (Theorem 179.1(b) proved). At `b4caa53b` the 5 files are
    byte-identical to the worker's `src/` (worker head `f30d80f02aa3a79c8dd1bb6c674e1ba071b0f568`).
  - Landing edit **LE-doc** `7f5bdd510c15357ca8e4bc28ca74ec6bcdf211c1`: 17 formula docstrings; docstrings only.
  - Landing edit **LE-reuse** `8befc58966fd39f974a54250849736df194584b9` (the head): two proofs in `Random.lean`
    re-pointed to published lemmas, one import added, two docstrings extended; proof only.
- **Scope:** a **proof audit**. The job proves the admitted `Randomness.predictAdv_prfConcept_negligible` [PS10, §8.1,
  Theorem 179.1(b)]: if `F` is a PRF, every non-uniform PPT learner `A` with `m(n)` uniform labelled examples
  predicts the concept `prfConcept F n k` at a fresh uniform point with negligible advantage over `½`. Its statement
  passed the prong D statement phase (ruling D-5: the learning game is the PAC layer of `TCSlib/LearningTheory`) and
  Gate 06, and is frozen. Part (c), `not_weakLearnsUnder_prfConcept`, is proved from (b) at the base and is unchanged.
- **Brief:** `fills/learning/issued-r1/brief.md` on the records branch (SHA-256 `6f6c2648…`; exchange pack `2b9270ad`):
  three checkpoints following the docstring sketch (distinguisher and real game; random function; bound), the owned
  file plus the helper directory `Randomness/Learning/` only, `Games/Efficiency.lean` and every other file frozen,
  the binding duplication rule with an `## Overlap and reuse` section, Rule 10 with the projection-coercion ruling and
  seals with `PolyExpr.eval` both excluded and sealed, the G26-N1 error count, and the evidence-completeness rule.

## What changed

All paths are under `TCSlib/Cryptography/Randomness/`; `L/` is `Learning/`. The PR touches 5 Lean files: 1 modified
and 4 new (859 insertions, 13 deletions). Line counts are base → worker head `b4caa53b` → LE-doc `7f5bdd51` → PR head.

| File | Status | Lines |
|---|---|---:|
| `Learning.lean` | owned, modified | 149 → 220 → 220 → 220 |
| `L/Sample.lean` | helper, new | 259 → 275 → 275 |
| `L/Distinguisher.lean` | helper, new | 136 → 137 → 137 |
| `L/Law.lean` | helper, new | 173 → 174 → 174 |
| `L/Random.lean` | helper, new | 203 → 203 → 189 |

The facade `Randomness.lean` already imports `Learning`, which imports the four helpers; after #305 no facade edit is
needed, and none was made.

The proof follows [PS10, Theorem 179.1] and the frozen sketch (REPORT § 1, review § Content; the target's step list
was rewritten to describe the delivered proof):
1. **The distinguisher and the real game** (`Sample`, `Distinguisher`, `Law`): `LearnPRF.exists_learnDist` builds a
   next-query machine `B` whose coins are, by a bijection, `m(n) + 1` points and `A`'s coins. Its query tree with
   budget `m(n) + 1` evaluates to `decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, where `S` is the sample of
   the first `m(n)` points labelled by `firstBit ∘ g`. `B` is the public query chain `MultiMsg.exists_queryChain_nuppt`
   with the zero message vector, applied to the machine that computes the learner's input and the last label from the
   encoded tuple, runs `A` and compares. `exists_learnDist_acceptProb` gives, for every keyed family `G`,
   `acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n)+1))) = gameProb (m n) G (learnerFn A n (m n))`; the
   prediction game is the same uniform probability (`predictSuccess_eq_uprob`, through `iid_uniform`,
   `Rejection.uniform_prod`, `Rejection.uniform_probTrue`). In the owned file `learnerFn = learnerOf` and
   `firstBit ∘ F n k = prfConcept F n k`, through the owned readers.
2. **The random function** (`Random`, `abs_gameProb_random_sub_half_le`): for `n ≥ 1`,
   `|gameProb m (fun R => R) ℓ − ½| ≤ m/2^n`. For a fresh point `x`, flipping the first bit of `R x` (`flipAt`) is
   an involution that keeps the examples' labels and negates `x`'s, so the conditional success is exactly `½`
   (`uprob_flip_half`); otherwise it lies in `[0, 1]`. The coupling bound against the constant `½` and the union
   bound with `Pr[s_j = x] = 2^{-n}` (`uprob_eq_point`) give `m/2^n`.
3. **The bound** (owned file): for `n ≥ 1`,
   `predictAdv ≤ |acceptProb (F n) D − acceptProb R D| + |acceptProb R D − ½| ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n`.
   This is negligible by `PRF.negligible_prfAdv` at budget `m + 1`, `EnsembleLemmas.negligible_polyExpr_mul` with
   `negligible_two_pow_neg`, and `Negligible.add`; `Negligible.mono` from `n = 1` makes `n = 0` a finite exception.

The edge cases are `n = 0` (steps 1 and 3 hold at every `n`; step 2 needs `n ≥ 1`), `m(n) = 0` (no examples, the
union bound is `0`), a fresh point equal to an example (no case split in step 1; the bad event of step 2), a learner
output other than `[true]` (`decide (… = [true])` throughout), and the query chain's timeout (exactly `m(n) + 1`
queries within the budget, so it is not reached).

**Statements:** decls2 from the issue base to the head gives 47 ADDED, 0 CHANGED, 0 REMOVED (review
`statements/decls2.tsv`, `head-le/decls2-vs-base.tsv`; LE-reuse `statements/decls2-vs-7f5bdd51.tsv`, empty). All 9
pre-existing declaration headers of `Learning.lean` are byte-identical, the target's and part (c)'s included. Only the
target's body and sketch changed, plus four imports, the module title, the Main-results line of part (b) and a new
`## Contents`. Re-checked for this pack from git objects with `maintainer/tools/decls2.py`'s parser: 47 ADDED and 9
unchanged against both the issue base and the PR base; 0 rows and 56 unchanged for `7f5bdd51..8befc589`.

## Rulings and records in force

1. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This
   is `FinDist`'s `⟨FinDist.prob⟩` (`FinDist.instCoeFunForallReal`). The coe-variant seals are canonical; the strict
   variant is still run and its differences attributed. **For this unit the seals agree in every row** (all five files
   pass A and B, strict and coe, at the head; the owned file also at the base; `logs/seal-table.txt`). The one
   strict-harness difference is in the controls: see the dispositions.
2. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal A, which exempts it, is canonical; seal B is run
   and reported because the brief asks for both.
3. **The facade-completeness lint fix, #305 (Seyoon's ruling of 2026-11-14 to fix the bug by a PR on our branch).**
   The baseline at the issue base is **92 FAIL / 101 WARN** (the brief; #309 resolved one WARN of the 92/102 of
   #305's record). The records tip `4561c340`, the worker head `b4caa53b` and LE-doc `7f5bdd51` all give 92 / 101 with
   identical non-INFO line sets; LE-reuse (head) gives 92 / 101 with identical FAIL and WARN lines, the full diff being
   `Random.lean`'s INFO line (203 → 189 lines). Under the pre-#305 lint the four helpers would add 4 "facade does not
   import child module" FAILs (`lint/lint-old-diff.txt`), the class #305 fixed. No FAIL or WARN is new.
4. **LE-doc (the maintainer's landing edit): docstrings only.** 17 formulas for the new public declarations that the
   review's docaudit flagged NO-FORMULA (14 in `Sample`, 1 each in `Distinguisher`, `Law`, `Random`). With all doc
   comments blanked, the four files are byte-identical to the worker head (`landing/le-doc-doconly.txt` in
   `review-evidence.zip`; re-checked for this pack from git objects: `b4caa53b..7f5bdd51`, 4 files, 0 failing).
   Docaudit after: 47 OK; the one NO-FORMULA row is the frozen target's base prose. Sketches: every theorem with 15 or
   more proof lines has a `**Proof sketch.**` (4 theorems, `statements/sketchaudit-le.tsv`).
5. **LE-reuse (the maintainer's landing edit): proof only, done before the gate.** The review found two undisclosed
   restatements of public lemmas (findings 1 and 2). The brief makes undisclosed duplication a freeze violation, and
   the majors that held Gates 23 and 24 were of exactly this class (G23-01, a private copy of
   `length_le_length_encodeLog`; G24-01, `inputWord_take` re-proving `take_ofFn_castLE`, fixed by a maintainer
   LE-reuse on #307). So the maintainer re-pointed both before opening the PR rather than leave a known major for the
   gate (decision log 2026-11-15, "G24-01 precedent"). `Random.lean` only (`reuse-evidence.zip`:
   `0001-LE-reuse.patch`, `checks/le-reuse.diff`):
   - `LearnPRF.uprob_eq_point` is now proved from the public `OneWay.uprob_eq_one_div_card`
     (`OneWayFunctions/Basic.lean:144`, already in `Random`'s closure), reversing the equation and reading
     `|{0,1}^n| = 2^n`. Its docstring gains one `**Proof sketch.**` paragraph, a pure insertion.
   - In `abs_gameProb_random_sub_half_le`, the local `hpt`, `hcard` and the averaging proof of `hdev` (25 lines) are
     replaced by the public coupling bound `MultiMsg.abs_uexp_sub_le_uprob` (`FromPRF/HybridLemmas.lean:61`) with
     `a = p`, `b = fun _ => ½`, `E = bad`, plus `OneWay.uexp_const`. The three hypotheses are the old case split's
     branches. The sketch's "Averaging," gains a parenthesis naming the lemma, a pure insertion. The rest of the
     proof is unchanged.
   - One import, `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas`. It was not in `Random`'s closure;
     it adds exactly that one module to the closures of `Random`, `Randomness.Learning` and `Randomness`, and none to
     root `TCSlib`. Its own closure (30 modules) is inside `Random`'s old closure and contains none of the 5 unit
     modules, so there is no cycle (`checks/imports.txt`). `HybridLemmas` defines nothing, so no seal request set
     changes.
   - Checks: decls2 against `7f5bdd51` empty; `touched` 2 CHANGED (the two theorems' bodies and docstrings), 59
     UNCHANGED; 63 header comparisons, 0 different (`statements/header-bytes-vs-7f5bdd51.txt`); both theorems'
     keyword-to-`:=` headers identical (`statements/docstring-header.txt`). The 66-module build is rc 0 with 0 errors
     and 0 sorry; every module has the same source and object SHA-256 as the review's `7f5bdd51` records except
     `Random` (`build/summary.txt`). Seals A and B, strict and coe, pass for `Random` with the review's request sets
     (`rule10/seal-rows-vs-review.txt`: 0 rows gone, new or changed); controls ALL_OK in both harnesses; axioms
     standard; lint unchanged.
   - **The promotion request for `uprob_eq_point` is withdrawn** (it is a reversed instance of a public lemma).
6. **DL-45 (duplication ledger, open).** Items 1 and 2 (`uprob_eq_point`, the inline coupling bound) are paid by
   LE-reuse. The rest is deferred to the cleanup (Seyoon's 2026-11-14 deferral of cleanup): the private `length_blk`
   re-proves `MultiMsg.length_histBlock` for the **disclosed** private copy `blk` of `histBlock` (no reader for
   `histBlock` exists; the worker's reader request stands); `flip0`/`flip0_flip0` duplicate `flipBit`/
   `flipBit_flipBit` (`BooleanAnalysis`) and `flipAt` (`DeterministicCC`), both outside the cryptography closure;
   `foldr_pairEncode_nil`'s left side is `Strategy.encodeMsgs`; and the short-name reuses `relabel`/`relabel_eq` (the
   DL-36 family, `Games.EffFill.relabel`) and `flipAt`.
7. **The disclosed route deviation: `MultiMsg.exists_queryChain_nuppt` is reused, not T1/T4.** The brief's step 1
   names T1 (non-adaptive queries) and T4. The worker instead calls the public `MultiMsg.exists_queryChain_nuppt` of
   the §3.9 reduction (`FromPRF/ReductionMachine.lean:461`), already a non-adaptive next-query machine with points
   from its coins and a final verdict of an arbitrary machine on the encoded tuple, at `ℓ₁ = ℓ₂ = n`; and it bridges
   probabilities in the `uprob` layer instead of the suggested `ProbComp`/`trialDist` bridge. No statement changes.
   It is called, not copied (review finding 8; `logs/duplication-grep.txt`). **Not a finding** by itself. What you
   can raise: a reason the reused chain does not give a legitimate PPT distinguisher with the budget used.
8. **The landing edits are the maintainer's** (the ext-nosrc, cca2-ett, dl-crh, hash-sign and lamport precedents):
   LE-doc docstrings only, LE-reuse proof only (with one acyclic import and two docstring insertions). Both were
   re-checked for this pack from git objects (rulings 4 and 5).

## What is frozen

- **The target's statement** (quoted in the brief), the 8 other pre-existing declarations of `Learning.lean` (part (c)
  and its proof included), the statement prose and the global simp attributes.
- **Every file outside** `Randomness/Learning.lean` and `Randomness/Learning/`. That includes the PAC layer
  (`LearningTheory/PAC/*`), `Games/Efficiency.lean`, `FromPRF/ReductionMachine.lean` and `FromPRF/HybridLemmas.lean`.
  The last two are owned by the running `prf-long` job (final delivered 2026-11-15, under review), whose binding
  frozen-statement rule keeps every existing header byte-identical; this unit uses `exists_queryChain_nuppt`,
  `histBlockLen`, `eval_histBlockLen`, `flatMap_range_blocks` and `abs_uexp_sub_le_uprob` from them.
- **The landing edits:** LE-doc docstrings only; LE-reuse two proofs, one import line and two docstring insertions.

## Questions for the audit

**1. Correctness against [PS10, Theorem 179.1(b)]**
- Does the proof establish the frozen statement for every PRF `F`, learner `A` and polynomial `m`, including `n = 0`,
  `m(n) = 0`, a fresh point equal to an example, and learner outputs other than `[true]`?
- Is `B` a legitimate distinguisher for `PRF.negligible_prfAdv`: a NUPPT next-query machine with budget `m + 1`, coins
  split correctly between the `m(n) + 1` points and `A`'s coins, and no timeout reached?
- Is `exists_learnDist_acceptProb` right: is the oracle game with `f_k` exactly the prediction game
  `predictSuccess (prfConcept F n) (m n) (learnerOf A n (m n))`, with the fresh point allowed to equal an example?
- Is the random-function bound `|gameProb − ½| ≤ m/2^n` right: is `flipAt` an involution that fixes the examples'
  labels and negates the fresh point's, and is the bad event exactly "the fresh point is an example"?
- Does the final calc with the negligible closure give `Negligible`, with `n = 0` handled by the eventual bound?
- **Part (c).** Is `not_weakLearnsUnder_prfConcept` now sorry-free with the standard axioms only
  (`landing/axioms-head.txt`; census in `review-evidence.zip`: `logs/census-summary.txt`,
  `logs/census-base-vs-head.txt`)?
- Does the rewritten target sketch describe the delivered proof?

**2. Frozen-statement integrity**
- Are the target's header and the other 8 pre-existing declarations byte-identical (`statements/head-le/header-bytes.txt`,
  `statements/head-le/decls2-vs-base.tsv` in `review-evidence.zip`; `statements/header-bytes-vs-7f5bdd51.txt` in
  `reuse-evidence.zip`), and are only the target's body and sketch, the imports, the title, the part (b) Main-results
  line and `## Contents` changed?

**3. LE-doc (ruling 4)**
- Does each of the 17 new formulas state what its declaration proves or defines, with arguments in the Lean order
  (`landing/le-doc.diff` and `statements/docaudit-le.tsv` in `review-evidence.zip`)? A formula that misstates its
  declaration is a minor. Is LE-doc docstrings only?

**4. LE-reuse (ruling 5)**
- Is it proof only (plus the import line and the two docstring insertions)? Are the two re-derivations correct
  instances of `OneWay.uprob_eq_one_div_card` and `MultiMsg.abs_uexp_sub_le_uprob`?
- Is the new import acyclic and justified, and is carrying the four untouched files' seals forward from `7f5bdd51`
  sound (their sources are unchanged; `HybridLemmas` adds no definition to any closure)?
- Do the re-run seals and controls for `Random.lean` bite (`rule10/` in `reuse-evidence.zip`)?

**5. Duplication**
- Does any new declaration duplicate a public TCSlib or Mathlib lemma, or copy a private one, beyond the worker's
  `## Overlap and reuse` table and DL-45 (ruling 6)? In particular, does any other part of a proof re-prove a public
  lemma inline, as `hpt`/`hdev` did before LE-reuse?
- Are the worker's disclosed overlaps (`learnerFn` vs the owned `learnerOf`, `firstBit` vs `prfConcept`, `sampleOf` vs
  `MultiMsg.blockMapFun`, `blk` vs `histBlock`, `tupleWord` vs `preFun_encodeHist`, `iid_uniform`,
  `predictSuccess_eq_uprob`, `snocEquiv`) accurate, and are its "why not reused" reasons valid?

**6. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 5 files
  over the full closure, at the base and the head, in both variants (`logs/seal-table.txt`, `seals*/`,
  `base-seals*/`)? Do the coe controls (16 probes, 46 sealed negatives, ALL_OK; `logs/ctlcheck.log`) show that the
  seals bite? Explicit-unfold scan at `7f5bdd51`: 242 items, 0 foreign (`logs/scan2-head.log`).
- Is the strict-harness attribution of the two failing reader positives right (dispositions)?
- Does any proof read a foreign definition (the owned `prfConcept`, `encodeSample`, `learnerOf`; `PAC.label`;
  `MultiMsg.histBlock`, `blockMapFun`; `FinDist` internals) other than through a published reader?

## Known dispositions (not findings)

- **The strict-harness artifact on the FinDist reader controls** (review finding 7). In the strict control harness
  (`controls-strict/`, 16 probes, 54 sealed negatives; `logs/ctlcheck-strict.log`), every sealed negative fails
  exactly once, `ctlCoe` included, and every unsealed probe passes; but the reader positives `ctlUniformReader` and
  `ctlCoeReader` also fail, in all 8 sealed probes. With the `CoeFun` instance sealed, the control's own statement
  elaborates to `CoeFun.coe p a` instead of `p.prob a`, so a reader stated in the `.prob` form no longer matches
  (`seal-runs/mods/LnProbe_KS_ControlS_*.log`, "Type mismatch"). The canonical coe controls are ALL_OK, and the
  seals themselves agree in both variants (ruling 1). LE-reuse's controls drop the `FinDist` rows for this reason
  and are ALL_OK in both harnesses. The worker's own probe (`worker/evidence/logs/coe-probe.log`) reports that the
  strict seal cannot make a projection coercion fail; the review's strict `ctlCoe` negative does fail. The two
  controls are built differently; the canonical variant is coe either way. What you can raise: a reason the strict
  difference hides a real Rule-10 read.
- **Strict and coe seals agree** for this unit, at the base and the head (ruling 1); the worker's
  `seals-compare.log` reports the same.
- **The worker's promotion requests** (`iid_uniform` → `InformationTheory/Samples.lean`, `predictSuccess_eq_uprob` →
  `PAC/Prediction.lean`, `foldr_pairEncode_nil` → `PolyTimePairing.lean`) and **reader requests** (`MultiMsg.histBlock`,
  `MultiMsg.blockMapFun`) are recorded for the deferred cleanup; the `uprob_eq_point` promotion request is withdrawn
  (ruling 5).
- **The helper imports.** The brief names `Games/Efficiency`, `Games/Hopping`, `OracleFromPRF` and
  `Asymptotic/SamplingFinDist` as importable. The delivery imports `FromPRF/ReductionMachine` and
  `GGM/Reduction` (`Sample`), `Extraction/Rejection` and `LearningTheory.PAC` (`Law`), and after LE-reuse
  `FromPRF/HybridLemmas` (`Random`). None is downstream of a unit module, so there is no cycle (review
  `order/closure-*.txt`; LE-reuse `checks/imports.txt`). What you can raise: a cycle, or an import that changes what
  a frozen file's importers see.
- **The interaction with #314** (Gate 30, the `prfAdv_eq_expect` promotion). `Pseudorandom/Functions/Defs.lean`,
  which #314 changes, is in this unit's closure (through `HybridLemmas` and the PRF layer); #314's new import adds
  `Games.Probability`, `Games.Advantage` and `Games.Bridges.Experiments` to it. `git merge-tree --write-tree 8befc589
  5757bc06` gives tree `647c2e96fbb887ce32cd094d08536f7d1a57a8e8` with no conflict. The combined tree has not been
  built; whichever PR merges second is rebuilt on the merged tip.
- **No whole-tree check at the final head.** The review's whole-tree check (1245 modules plus PFR, RESULT OK;
  `landing/tree-check-7f5bdd51.txt`) is at LE-doc `7f5bdd51`. LE-reuse rebuilt the review's 66-module set at
  `8befc589` (`landing/root-checks.jsonl`), and `landing/build-summary.txt` shows that every module but `Random` has the
  same source and object hashes as the review's records; so the `7f5bdd51` tree check carries over except `Random`,
  which is rebuilt rc 0.
- **No explicit-unfold scan at the final head.** The review's scan is at `7f5bdd51`. LE-reuse's new proof text names
  only theorems (`OneWay.uprob_eq_one_div_card`, `Fintype.card_fun`, `Fintype.card_bool`, `Fintype.card_fin`,
  `Nat.cast_pow`, `Nat.cast_two`, `eq_comm`, `MultiMsg.abs_uexp_sub_le_uprob`, `uprob_nonneg`, `uprob_le_one`,
  `uprob_flip_half`, `OneWay.uexp_const`), and its seals pass.
- **#307 was built as base delta** in the review; none of its modules is in the unit's closure.
- **The worker's manifests list paths with a leading `./`** (review finding 9); the review's checker strips it, and
  both manifests verify (153/153, 142/142).

## Also check

**Axioms**
- At the head, `predictAdv_prfConcept_negligible`, `not_weakLearnsUnder_prfConcept`, `LearnPRF.uprob_eq_point` and
  `LearnPRF.abs_gameProb_random_sub_half_le` each print `[propext, Classical.choice, Quot.sound]`
  (`landing/axioms-head.txt`). At the base the target and part (c) also had `sorryAx`.
- Census at `7f5bdd51` (`review-evidence.zip`: `logs/census-summary.txt`, `logs/census-base-vs-head.txt`): 71 stored
  constants in the 5 files (12 internal or auxiliary, 7 private), axiom union `{propext, Classical.choice,
  Quot.sound}`, no `sorryAx`; base 11 → head 71, 60 added, none removed, type-changed, attribute-changed or moved; the
  only axiom changes are the target and part (c). LE-reuse changes two proofs and adds no constant.
- Nothing new is `@[simp]`, an instance or an abbreviation.

**Admissions:** 20 → 19 in the issued modules; only `predictAdv_prfConcept_negligible` is removed
(`logs/sorry-census.txt`).

**Sizes and widths:** every file is at most 275 lines and every line at most 100 characters (`source-head.json`).

**Build:** at `8befc589`, the 66 modules of the review's head set (the 51 base-delta modules of #303 and #306–#309 and
their downstream, the 5 unit modules, `Randomness`, root `TCSlib` and `audits/pass-shelat/Checks`) have rc 0, 0 errors
in both diagnostic forms and 0 sorry (`landing/root-checks.jsonl`, whose last line is the runner's `done` record;
each changed file's `source_sha256` matches `source-head.json`). The olean tree was restored to the base snapshot
afterwards (`restore/tree-check-post.txt` in `reuse-evidence.zip`).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS. It was written before LE-reuse
  and says "LE-reuse is in progress"; LE-reuse's record is `fills/learning/final-r1/landing-reuse/` (the review record
  is not edited).
- **`verification.zip`** (31 entries): every file the review and the LE-reuse record cite, as byte-identical originals.
  Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/learning/final-r1/`, SHA-256 `88ab5b78…`) and `review-evidence-SHA256SUMS`, its
    manifest. The ZIP has 489 entries, all files: under `learning-r1/`, exactly the 488 manifest paths plus that
    folder's `SHA256SUMS`, which is byte-identical to the manifest; all 488 hashes verify. It covers integrity, the
    landing and LE-doc, the build and the whole-tree check with the restore, decls2, header bytes, `touched`, the
    docstring and sketch audits, the census and axioms, the strict and coe seals at the base and the head, the
    paired controls in both harnesses, the scan, the old and new lint, sizes and the duplication grep;
  - `reuse-evidence.zip` (`fills/learning/final-r1/landing-reuse/learning-r1-reuse-evidence.zip`, SHA-256
    `5df65c56…`) and `reuse-evidence-SHA256SUMS`: 281 entries, 32 directory entries and 249 files, exactly the 248
    manifest paths plus `SHA256SUMS` (byte-identical to the manifest); and `landing-reuse/PROVENANCE.txt`, which
    equals the ZIP's `PROVENANCE.txt`. It covers LE-reuse's patch, the imports, statements, the 66-module build, axioms,
    seals and controls for `Random.lean`, lint and the restore;
  - `landing/`: the review's extracts `PROVENANCE.txt` and `duplication-grep.txt` (byte copies of ZIP entries);
  - `records/`: the issue package `fills/learning/issued-r1/`, the duplication ledger, the decision log, the #305
    record `maintainer/lint-facade-fix-2026-11-14/` (README and patch) and the issued prf-long brief, at records
    `f52a24be7442013d00bef3608ce5336429dd4719`;
  - `worker/`: byte copies from exchange `365d6639c0a3fbd2550e6ce792c2aee9b927010a` (`inbox/fills/learning/`):
    `patches/COMMITS.tsv` and `evidence/` files `seals/seals-compare.log`, `logs/coe-probe.log`, `probes/CoeProbe.lean`,
    `logs/final-searches.log`, `logs/final-census-vs-base.diff`, `logs/final-lint-vs-base.diff`, `logs/final-axioms.log`.
- **The worker's own evidence:** on the exchange at `365d6639c0a3fbd2550e6ce792c2aee9b927010a`, under
  `inbox/fills/learning/`. Its top `SHA256SUMS` lists 153 files and `evidence/SHA256SUMS` 142, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries.
  - `root-checks.jsonl` (= `reuse-evidence.zip`: `build/results.jsonl`): the 66 modules at `8befc589`, rc 0.
  - `build-summary.txt` (= `build/summary.txt`): the counts and the hash comparison with the review's records.
  - `axioms-head.txt` (= `axioms/AxiomsHead.log`): the four axiom prints at the head.
  - `tree-check-7f5bdd51.txt` (= `review-evidence.zip`: `learning-r1/tree/tree-check-head.txt`): the whole-tree
    check at LE-doc.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `365d6639`.
- **`pr-description.md`:** the PR #313 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (5 paths, 859 insertions, 13 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 5 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 138 files.
- **Evidence note.** `logs/duplication-grep.txt` (and its `landing/` copy) shows `grep: --include=*.lean: No such file
  or directory` once per search: the option was passed after the path, so each search covered every file under
  `TCSlib/`, not only `.lean` files. The matches shown are still the Lean declarations; the search was wider, not
  narrower.

## Findings delivery

Return `gate29-learning-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-45, or necessary evidence that
  cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
