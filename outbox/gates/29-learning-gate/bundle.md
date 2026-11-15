## ===== briefs/pass-shelat-ch5-8/gates/29-learning/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/review.md =====

# learning · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** LE-doc is done. The landing edit **LE-reuse** is in progress: it re-proves two
undisclosed restatements (findings 1 and 2) from the published lemmas, by a proof-only change.

## Delivery and landing branch

**Delivery**
- **Source.** Claude worker. Exchange final `365d6639c0a3fbd2550e6ce792c2aee9b927010a`; checkpoints `8318ce34` and `6ebe473c`.
  The issue base is `107f1e8c`.
- **Target.** `Randomness.predictAdv_prfConcept_negligible`, [PS10, Theorem 179.1(b)].
- **Side effect.** Part (c), `not_weakLearnsUnder_prfConcept`, used the standard axioms plus `sorryAx` and now uses the
  standard axioms only. The census confirms it.

**Landing branch** `land/pass-shelat-learning`
- **Base.** Rebased onto records tip `4561c340`, which includes #303 and #306–#309. The rebase had no conflict.
- **Worker commits** (3, author Claude): `876145de`, `331c15f4`, `b4caa53b`.
- **LE-doc** `7f5bdd510c15357ca8e4bc28ca74ec6bcdf211c1` (tree `240da503`). It adds 17 docstring-only formulas. The code is
  identical when the doc comments are blanked.
- **Files.** The owned file `Randomness/Learning.lean`, plus four new helpers, `Learning/{Sample,Distinguisher,Law,Random}.lean`.

**Evidence.** `review-evidence.zip`, SHA-256 `88ab5b78391d33d67990e49e69db5c0360951f5c3e1d60c4ce259667573cc14d`.
- It holds 489 entries: the 488 manifest paths plus `SHA256SUMS`.
- The manifest is in `evidence-SHA256SUMS`.

## Checks

**Integrity.**
- The manifests verify 153/153 and 142/142 after normalizing the `./` prefix.
- `git am` with the `COMMITS.tsv` committer data reproduces every hash.
- The issue package verifies 7/7, and its sources 246/246.

**Build.** 66 modules give rc 0 and 0 errors, counting both diagnostic forms:
- the 51 base-delta modules;
- the unit's 5 modules;
- their downstream, through root `TCSlib` and `audits/pass-shelat/Checks`.

None of #307's modules is in the unit's closure. The whole-tree check covers 1245 modules plus PFR, and passes.

**Statements.**
- decls2 gives 47 ADDED, 0 CHANGED and 0 REMOVED.
- All 9 pre-existing headers are byte-identical.

**Axioms.** All 71 stored constants use only the standard axioms. There is no `@[simp]`, no instance and no abbreviation.

**Rule 10.**
- Seals A and B pass in both variants, at the head and at the base.
- The coe controls are ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions.
- In the strict variant, two reader positives fail. This is a harness artifact of sealing the coercion, which is
  notation by ruling. Every strict negative fails exactly once.

**Admissions.** They go from 20 to 19.

**Lint.** 92/101 at the tip and at the head. Every line is at most 100 characters, and every file is at most 275 lines.

**Content.** The proof follows the book:
- the real game is the distinguisher with `f_k`;
- with a random function, the game is within `m(n)/2^n` of ½, by a bit-flip involution and a union bound;
- negligibility then follows from the PRF advantage.

The edge cases are handled: `n = 0`, `m = 0`, a fresh point equal to an example, and an output other than `[true]`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | **Undisclosed.** `LearnPRF.uprob_eq_point` is the public `OneWay.uprob_eq_one_div_card`, reversed, with `|X| = 2^n`. The worker also asked to promote it. | **LE-reuse**, proof only. The promotion request is withdrawn. Ledger DL-45. |
| 2 | minor | **Undisclosed inline re-proof.** `hpt`/`hdev` in `abs_gameProb_random_sub_half_le` re-prove `MultiMsg.abs_uexp_sub_le_uprob` (`FromPRF/HybridLemmas`). | **LE-reuse**, proof only, if the import is acyclic and the change modest. Otherwise ledger it. DL-45. |
| 3 | minor | The private `length_blk` re-proves `MultiMsg.length_histBlock`, for the disclosed private copy `blk` of `histBlock`. | Ledger DL-45, with the worker's reader request for `histBlock`. |
| 4 | info | `flip0`/`flip0_flip0` duplicate `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); both of those are outside the crypto closure. There is also a short-name reuse of `flipAt`. | Ledger DL-45. |
| 5 | info | The left side of `foldr_pairEncode_nil` is `Strategy.encodeMsgs`. `relabel`/`relabel_eq` share their short names with `Games.EffFill.relabel` (DL-36 family). | Ledger DL-45. |
| 6 | minor | 17 docstrings had no formula. | **Fixed** by LE-doc. |
| 7 | info | Strict-variant positive controls are a coercion-seal artifact. | Recorded. |
| 8 | info | Disclosed route deviation: `MultiMsg.exists_queryChain_nuppt` is reused, as a call. | None. |
| 9 | info | The manifest paths carry a `./` prefix. | None. |

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/worker-report.md =====

# Fill learning — final

**Unit** `learning` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/learning` (local), head
`f30d80f02` · **Lean** 4.25.0, Mathlib at the base's manifest.

## 0. Status

| Target | Status |
|---|---|
| `Randomness.predictAdv_prfConcept_negligible` (PS10 Thm 179.1 (b)) | **proved**; statement unchanged; axioms `[propext, Classical.choice, Quot.sound]` |
| `Randomness.not_weakLearnsUnder_prfConcept` (part (c), unchanged) | its axioms are now standard: `[propext, Classical.choice, Quot.sound]` |

Commits (the series in `patches/`, with `patches/COMMITS.tsv`):
1. `c323e6041` checkpoint 1 — the distinguisher and the real game (exchange `8318ce34f`);
2. `d80d3e5e3` checkpoint 2 — the random function (exchange `6ebe473c0`);
3. `f30d80f02` Theorem 179.1 (b) proved.

The final sweep of the supplied order with the four helpers inserted before the owned module has
0 errors, and the sorry census is `base-sorries.txt` minus `predictAdv_prfConcept_negligible`
(§6).

## 1. The proof

Fix `hF : PRF F`, a learner machine `A` and a polynomial `m`. Write `X = {0,1}^n`.

1. **The distinguisher and the real game** (`Learning/Sample.lean`, `Learning/Distinguisher.lean`,
   `Learning/Law.lean`). `LearnPRF.exists_learnDist`: a next-query machine `B` whose coins are, by
   a bijection, `m(n) + 1` points `ρ` and `A`'s coins `c`, and whose query tree with budget
   `m(n) + 1` against any oracle `g` evaluates to
   `decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, with `S` the nested labelled examples
   `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩`, `j < m(n)`. `B` is the public non-adaptive query chain
   `MultiMsg.exists_queryChain_nuppt` (zero message vector) of the machine that computes the
   learner's input and the last label from the encoded tuple (`learnIn`, `lastLabel`: block map of
   `relabel` over the first `m(n)` blocks, polynomial-time), runs `A` on it
   (`NUPPT.exists_compParam`) and compares (`NUPPT.exists_seq` with the uniform machine of
   `verdictFun`). Then `exists_learnDist_acceptProb`: for every keyed family `G : K → X → X`,
   `acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n)+1))) = gameProb (m n) G (learnerFn A n (m n))`,
   the uniform probability over `((k, (s, r)), x)` that the learner, on `s` labelled by
   `firstBit ∘ G k`, predicts `firstBit (G k x)` (coins relabelled by the bijection and
   `snocEquiv`). The prediction game is the same uniform probability (`predictSuccess_eq_uprob`:
   its law is the uniform law on the product, `iid_uniform`, `Rejection.uniform_prod`,
   `Rejection.uniform_probTrue`). In the owned file `learnerFn = learnerOf` (`learnerOf_eq`,
   `encodeSample_eq`) and `firstBit ∘ F n k = prfConcept F n k` (`prfConcept_eq`), so
   `predictSuccess (prfConcept F n) (m n) (learnerOf A n (m n)) = acceptProb (F n) D`.
2. **The random function** (`Learning/Random.lean`, `abs_gameProb_random_sub_half_le`): for
   `n ≥ 1`, `|gameProb m (fun R => R) ℓ − ½| ≤ m/2^n` for every learner `ℓ`. With `R` averaged first:
   at a fresh point `x ∉ s`, `flipAt hn x` (flip the first bit of `R x`) is an involution that keeps
   the examples' labels and negates `x`'s, so it exchanges winning and losing functions and the
   probability is exactly `½` (`uprob_flip_half`); otherwise it lies in `[0, 1]`. Hence
   `|gameProb − ½| ≤ Pr[∃ j, s_j = x] ≤ m · 2^{-n}` (`uprob_exists_le`, `uprob_eq_point`).
   With `randomFunction_apply`, this bounds `|acceptProb (randomFunction X X) D − ½|`.
3. **The bound** (owned file): for `n ≥ 1`,
   `predictAdv = |acceptProb (F n) D − ½| ≤ |acceptProb (F n) D − acceptProb R D| + |acceptProb R D − ½|
   ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n` (`prfAdv_def`, `distAdv_def`, `abs_sub_le`). The sum is
   negligible: `PRF.negligible_prfAdv hF B (m + 1)`, and `m(n)/2^n = m(n) · (½)^n`
   (`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`), `Negligible.add`; the
   eventual bound (`Negligible.mono` from `n = 1`) handles `n = 0`.

**Route deviation (no statement changed).** The brief's step 1 names T1 (non-adaptive queries)
and T4. The proof uses instead the public `MultiMsg.exists_queryChain_nuppt` of the §3.9 reduction
(`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:461`), which already is a non-adaptive
next-query machine with points from its coins and a final verdict of an arbitrary machine on the
encoded tuple (`toOracleAdversary` at `ℓ₁ = ℓ₂ = n`): no handler or bridge proof was needed. The
probability bridge is the uniform-probability (`uprob`) layer: `acceptProb` is a `uprob`
(`acceptProb_def`), and the prediction game's `FinDist` law is the uniform law on the product; the
`ProbComp`/`trialDist`-as-oracle-run bridge suggested by the brief is not needed.

**Edge cases.** `n = 0`: steps 1 and 3 hold at every `n` (the single point, `firstBit` is
`false`); step 2 needs `n ≥ 1` and the final eventual bound starts at `n = 1`. `m(n) = 0`: no
examples (`Fin 0`), the encoded tuple is the last block alone, the union bound is `0`. A fresh
point equal to an example: no case split in step 1; it is the bad event of step 2. `A` printing
anything other than `[true]`: the prediction is `decide (… = [true])` throughout. The codecs'
timeout outputs: the query chain makes exactly `m(n) + 1` queries within the budget `m(n) + 1`,
and `B`'s verdict is the equation of `exists_queryChain_nuppt` for every oracle; no timeout is
reached. The coins: `B`'s coins are, by the bijection, `m(n) + 1` `n`-bit points (`(m(n)+1)·n` bits,
blocks of `FunFamily.blocks`) and `A`'s coins (the composed machine has `A.coins + 0`, relabelled by
`finCongr`).

## 2. Changed and new files

| File | Lines | Role |
|---|---|---|
| `TCSlib/Cryptography/Randomness/Learning.lean` (owned) | 220 | the proof of part (b) |
| `TCSlib/Cryptography/Randomness/Learning/Sample.lean` | 259 | the learner's input and the last label from the encoded tuple |
| `TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean` | 136 | the distinguisher |
| `TCSlib/Cryptography/Randomness/Learning/Law.lean` | 173 | the game probability, both games |
| `TCSlib/Cryptography/Randomness/Learning/Random.lean` | 203 | the random-function bound |

Every line ≤ 100 characters, every file ≤ 1000 lines (`logs/final-width.log`). Import graph:
Sample ← Distinguisher ← Law ← Random; Sample imports `FromPRF/ReductionMachine` and
`GGM/Reduction`; Law imports `Randomness/Extraction/Rejection` and `LearningTheory.PAC`. The owned
file imports the four helpers (the facade). No helper imports the owned file; none of the imported
modules is downstream of the owned file (all precede it in `order.txt`, and the sweep checks the
order with the helpers inserted).

**Owned-file edits.** Title (dropped "(statement phase)"); `## Main results` (part (b) proved); a
new `## Contents` (the helpers); four imports; the target's docstring sketch rewritten to the
delivered proof (three steps, the deviation from T1); the target's body. The statement, every other
declaration (including part (c) and its proof), the statement prose and the simp attributes are
unchanged.

## 3. New declarations

All in namespace `TCSlib.Cryptography.Randomness.LearnPRF`; each public one has a docstring with
its formula, and each proof of 15 lines or more a `**Proof sketch.**`.
- Sample: `foldr_pairEncode_nil`, `firstBit` (`firstBit_eq`), `tupleWord` (`tupleWord_eq`),
  `relabel` (`relabel_eq`, `polyTimeComputable_relabel`), `sampleLen` (`sampleLen_eval`),
  `sampleOf` (`sampleOf_eq`), `lastPair` (`lastPair_eq`, `polyTimeComputable_lastPair`), `learnIn`
  (`learnIn_eq`, `polyTimeComputable_learnIn`), `lastLabel` (`lastLabel_eq`,
  `polyTimeComputable_lastLabel`), `learnIn_tupleWord`, `lastLabel_tupleWord`; private `blk`,
  `length_blk`, `relabel_blk`, `tupleWord_split`.
- Distinguisher: `verdictFun` (`verdictFun_eq`, `polyTimeComputable_verdictFun`),
  `exists_learnDist`; private `zero_add_fun`.
- Law: `iid_uniform`, `predictSuccess_eq_uprob`, `gameProb` (`gameProb_eq`), `learnerFn`
  (`learnerFn_eq`), `snocEquiv` (`snocEquiv_apply`), `exists_learnDist_acceptProb`.
- Random: `flip0` (`flip0_eq`, `flip0_flip0`), `firstBit_of_pos`, `firstBit_flip0`, `flipAt`
  (`flipAt_eq`, `flipAt_involutive`), `uprob_flip_half`, `uprob_eq_point`,
  `abs_gameProb_random_sub_half_le`.
- Owned file: none (the proof of the target).

No `@[simp]`; no new `abbrev`. Every new public `def` has an `_eq`/`_eval`/`_apply` reader (lint
check 8: no WARN for the new files).

## 4. Overlap and reuse

| New declaration | Nearest relative (`path:line`) | Relation | Why not reused |
|---|---|---|---|
| `learnerFn` | owned `learnerOf` (`Randomness/Learning.lean:96`) | restates it, with `encodeSample` unfolded through `encodeSample_eq` | helpers cannot import the owned file (it imports them), and the owned definitions are foreign to the helpers (Rule 10); the proof identifies them by `learnerOf_eq`, `encodeSample_eq` |
| `firstBit` | owned `prfConcept` (`Randomness/Learning.lean:77`) | its body (`(List.ofFn y).headD false`) as a function of the output | as above; identified by `prfConcept_eq` |
| `foldr_pairEncode_nil` | `MultiMsg.encodeHist_eq_flatMap` (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:60`) | the same fact (nested pairs ending in `[]` are a concatenation), for a fold of words instead of `encodeHist` | different fold; stated generally |
| `sampleOf` | `MultiMsg.blockMapFun` (`ReductionMachine.lean:229`) | the same block map, for `relabel` | `blockMapFun` has no published reader (lint check 8 lists it), so Rule 10 forbids unfolding it; `sampleOf` is the function of the public `Complexity.polyTimeComputable_blockMap` |
| `blk` (private) | `MultiMsg.histBlock` (`ReductionMachine.lean:50`) | the same block `⟨⟨x, y⟩, []⟩` | `histBlock` has no reader (lint check 8) |
| `sampleLen` | `MultiMsg.histBlockLen` (`ReductionMachine.lean:68`) | `m · histBlockLen` | reuses `histBlockLen` and `eval_histBlockLen` |
| `tupleWord`, `learnIn_tupleWord` | `MultiMsg.preFun_encodeHist` (`ReductionMachine.lean:433`) | the same encoded tuple shape `⟨⟨ρ_j, y_j⟩, []⟩` (with the zero mask) | different processing (relabelling, not masking) |
| `exists_learnDist` | `MultiMsg.exists_queryChain_nuppt` (`ReductionMachine.lean:461`) | a specialization (zero messages, the learner's verdict machine) | reused, not copied |
| `iid_uniform` | none found (`iid` occurs only in the PAC layer); cf. `Rejection.uniform_prod` (`Randomness/Extraction/Rejection.lean:134`) | the `m`-fold analogue of `uniform_prod` | no `iid` version exists; promotion request |
| `predictSuccess_eq_uprob` | `PAC.predictSuccess_eq_one_sub_expectedErr` (`LearningTheory/PAC/Prediction.lean`) | another reading of `predictSuccess` | the uniform-probability form is what `acceptProb` gives; promotion request (PAC layer) |
| `snocEquiv` | Mathlib `Fin.snocEquiv`; `Rejection.tupleEquiv` (`Rejection.lean:144`) | tuple splitting | the triple `(k, (s, r)), x` regrouping is specific; built from `Fin.snoc`/`Fin.init` |
| `uprob_eq_point` | `Rejection.uniform_probTrue` (`Rejection.lean:343`) | the uniform point mass, here in `uprob` form | stated directly from `uprob_eq_card_filter` |
| `uprob_flip_half`, `flipAt`, `flip0` | PRFGame collision bound `abs_expect_fImpl_sub_le` (`OracleFromPRF/Collision.lean:375`); GGM's lazy sampling | a different argument (a bit-flip involution at one fresh point, no lazy sampling) | not applicable |
| `abs_gameProb_random_sub_half_le` | `acceptProb_random_eq_lazy` (`Pseudorandom/Functions/Asymptotic/Defs.lean:128`) | random-function acceptance | the bound is direct in `uprob`; no lazy run needed |
| `zero_add_fun` (private) | Mathlib `Bool` xor lemmas | `(fun _ => false) + y = y` for the `Pi` `+` of `Bool` | one-line local fact |
| `verdictFun` | `MultiMsg.postFun` (`ReductionMachine.lean:296`) | another post-processor of a query chain | different verdict |

Nearest relatives named by the brief: ext-nosrc's sampler law (`Randomness/Extraction/Sampler.lean`:
a block law of an extractor, not reused), the GGM reduction (`GGM/Reduction.lean`: reused
`pairEncode_append_right`), the T1 reductions of hash-sign and Lamport (not used: the query chain
replaces T1), the PRFGame collision bound (above).

**Searches** (`logs/final-searches.log`): ripgrep over `TCSlib/` and Mathlib for the statement
shapes and key names of each new declaration (`foldr pairEncode`, `iid`, `uniform_prod`,
`blockMap`, `queryChain`, `snoc`, `update` with `uprob`, `headD` of `ofFn`, `label_apply`, …).

## 5. Scope requests, promotion and reader requests

**Scope requests:** none (no frozen file was edited; the route needed none).

**Promotion requests** (generic facts placed in the helpers):
- `iid_uniform` → `InformationTheory/Samples.lean` (beside `iid`).
- `predictSuccess_eq_uprob` → `LearningTheory/PAC/Prediction.lean`.
- `foldr_pairEncode_nil` → `Complexity/ClassNP/PolyTimePairing.lean` (beside `pairEncode`).
- `uprob_eq_point` → `Foundations/Probability.lean`.

**Reader requests** (missing readers met; worked around without a scope request):
`MultiMsg.histBlock`, `MultiMsg.blockMapFun` (`FromPRF/ReductionMachine.lean`) have no `_eq`
readers (lint check 8 WARN at the base); readers would let `blk` and `sampleOf` be dropped.

## 6. Checks (final)

All Lean runs one process at a time, one module per `scripts/lean_check_tree.sh` call (via
`tools/check.sh`, with start/end time, elapsed time and max RSS); the post-sweep runs are driven by
`tools/final_pipeline.sh` (step log `logs/final-pipeline.log`). No host restart during the runs.

- **Recheck and sweep** (`logs/final-sweep.log`, 01:22–01:45 UTC): the 250 modules of
  `logs/order-with-helpers.txt` (`order.txt` with the four helpers inserted before the owned
  module), each checked from scratch, in order: **250/250 status 0, no `error:`/`error(…)` line**;
  the five files of this fill emit no warning.
- **Sorry census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 19 declarations in
  9 modules; the diff against `base-sorries.txt` is exactly the line
  `TCSlib/Cryptography/Randomness/Learning: 1: predictAdv_prfConcept_negligible` and the total
  (20 → 19).
- **Axioms** (`logs/final-axioms.log`, `probes/AxiomsFinal.lean`): `predictAdv_prfConcept_negligible`
  and `not_weakLearnsUnder_prfConcept` depend on `[propext, Classical.choice, Quot.sound]`; the
  71 stored constants of the five files (auxiliary constants included) use exactly
  `{Classical.choice, Quot.sound, propext}`; no `sorryAx`.
- **Whole-file seals** (`seals/`; `tools/seal_gen.py`, `seal_run.py`, `seal_all.sh`). Each file is
  copied to a new module that makes every TCSlib definition of its full import closure
  irreducible and removes it from instance unfolding, abbreviations excluded; it must elaborate.
  Variants: **A** (`PolyExpr.eval` excluded as notation) and **B** (sealed), each **strict**
  (projection coercions sealed) and **coe** (projection coercions treated as notation: the one
  in the closure is `FinDist.instCoeFunForallReal`, `⟨FinDist.prob⟩`). The runner counts both
  diagnostic forms (`^\S+\.lean:\d+:\d+: error[:(]`) and keeps every raw log (`*.out`).
  - final (`final-{A,B}-{strict,coe}.jsonl`): **all five files elaborate in all four variants:
    0 errors, 0 failing declarations** (about 1,130–1,300 definitions sealed per file);
  - base (`base-{A,B}-{strict,coe}.jsonl`; the owned file is the only changed file that exists at
    the base, checked from `base/LearningBase.lean`, whose sha256 equals `SOURCE-SHA256SUMS`):
    0 errors in all four variants;
  - `seals/seals-compare.log`: no new failing declaration in any variant; strict and coe agree in
    both A and B (no difference to attribute). Why they agree: coercions are expanded at
    elaboration (`p b` is `p.prob b`), and even an explicit `CoeFun.coe inst p b` reduces under the
    strict seal, since Lean reduces a projection of an instance although the instance is
    irreducible (`probes/CoeProbe.lean`, `logs/coe-probe.log`: status `irreducible`, and the
    `isDefEq` trace unfolding `instCoeFunForallReal.1`).
  During development (not delivered) the first coe-A seal run failed once, in
  `exists_learnDist_acceptProb` (`simp only [label_apply]` made no progress on the labelled
  sample and the goal closed only by unfolding `PAC.label`); the proof now rewrites with the
  function form of `label_apply` (`hlab`).
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-*.jsonl`):
  - `CtlUnfold` (`LearnPRF.firstBit y = … := rfl`): unsealed status 0; **1 error in each of the
    four sealed variants** (`ctl_unfold_firstBit`);
  - `CtlEval` (`(PolyExpr.const 1).eval 5 = 1 := rfl`): unsealed 0; A-strict 0, A-coe 0;
    **B-strict 1 error, B-coe 1 error** (`ctl_unfold_eval`);
  - `CtlReader` (the same facts through `firstBit_eq`, `PolyExpr.eval_const`, and `p b = p.prob b`):
    0 everywhere;
  - `CtlCoe` (an explicit application of the coercion instance by `rfl`): 0 everywhere. It was
    meant as the negative control of the strict variant and is kept as a documented probe: no
    control can make the strict variant fail on a projection coercion (see above).
  Each sealed negative fails exactly once, and the positive passes.
- **Explicit-unfold scan** (`scan/`; `tools/rwids.py`, `rwids_run.sh`, `cmp_scans.py`): every
  identifier of a `rw`/`simp`/`unfold`/… list is resolved in the file's namespaces and `open`s
  (scan modules in `scan/sources/`). Final: 179 rows: 149 theorems, 2 definitions of the scanned
  file itself (`prfConcept` in `prfConcept_decidable`, base code; `sampleLen` in `sampleLen_eval`),
  28 unresolved (local hypotheses and private declarations of the scanned file: `blk`,
  `zero_add_fun`), and **0 definitions of another TCSlib file** (`scan/scan-compare.log`); base:
  6 rows, 0 foreign.
- **Lint** (`logs/base-lint.log`, `logs/final-lint.log`, `logs/final-lint-vs-base.diff`):
  `campaign_style_lint.py TCSlib/Cryptography --check8b` gives 92 FAIL / 101 WARN at the base and at
  the final, and **the FAIL and WARN line sets are identical** (the diff is empty); no line for the
  new files.
- **Width and size** (`logs/final-width.log`): every line ≤ 100 characters, every file ≤ 1000 lines.
- **Patch reproduction** (`logs/final-repro.log`): in a scratch clone at the base, `git am` of each
  patch with the committer name, email and date of `patches/COMMITS.tsv` reproduces every commit
  hash (the author data are in the patches).

## 7. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

`evidence/SHA256SUMS` lists exactly the files under `evidence/`; the top-level `SHA256SUMS` lists
every delivered file under `inbox/fills/learning/` except itself (both checked by
`tools/manifest.sh` before the push: paths equal, hashes verified).
- `logs/`: environment and bootstrap (`preflight.log`, `source-sha256.log`, `order.txt`,
  `mathlib-roots.txt`, `cache-store.log`, `cache-get.log`, `packages-check.log`, `cache-probe.log`,
  `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`, `base-lint.log`);
  checkpoints (`checkpoint{1,2}-{checks,axioms,lint,width,repro}.log`); final
  (`order-with-helpers.txt`, `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`,
  `final-axioms.log`, `final-lint.log`, `final-lint-vs-base.diff`, `final-width.log`,
  `final-searches.log`, `final-pipeline.log`, `controls-plain.log`, `coe-probe.log`,
  `scan-final.ids.log`, `scan-final.raw.log`, `scan-base.ids.log`, `scan-base.raw.log`,
  `final-repro.log`).
- `seals/`: `{final,base,controls}-{A,B}-{strict,coe}.jsonl` and `.out` (raw output),
  `seals-compare.log`, `sources/<tag>/` (every sealed copy that was checked).
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `sources/{final,base}/`.
- `controls/`: `CtlUnfold.lean`, `CtlEval.lean`, `CtlCoe.lean`, `CtlReader.lean`.
- `base/`: `LearningBase.lean` (the owned file at the base).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`, `AxiomsCP2.lean`, `AxiomsFinal.lean`,
  `CoeProbe.lean`.
- `tools/`: every script used (`check.sh`, `dev.sh`, `mk.py`, `sweep_chunk.sh`, `census.py`,
  `cmpcensus.sh`, `pkgcheck.py`, `seal_gen.py`, `seal_run.py`, `seal_all.sh`, `rwids.py`,
  `rwids_run.sh`, `cmp_scans.py`, `width_check.py`, `final_pipeline.sh`, `payload.sh`,
  `repro_check.sh`, `manifest.sh`, `finalize.sh`).

`patches/`: `git format-patch 107f1e8c..f30d80f02` (3 patches) and `COMMITS.tsv`; `src/`: the five
changed and new files at `f30d80f02`.

## 8. From the checkpoints

### 8.1 Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom
  is `MemAvailable` = 16489095168 B = 15.36 GiB; the clone's filesystem (ext4, `/dev/vda`) has
  18171547648 B = 16.92 GiB free (floor 12 GiB): `PREFLIGHT PASS`. Before the preflight the disk had
  9.87 GiB free (below the floor); with the user's approval in the session, the two git worktrees
  of this host's finished, delivered fills (`/workspace/dlc`, `/workspace/ett`) were removed
  (`git worktree remove`; their branches are kept). No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/learn` of the local repository, branch `fill/learning` at
  the issue base. Its source files match `SOURCE-SHA256SUMS` (246 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) already held 2402 archives, left by
  this host's earlier fills. The narrowed `lake exe cache get` for the 82 roots
  (`mathlib-roots.txt`, the same list as the pack's `roots.txt`) cloned the packages of the
  manifest, printed "No files to download" and "Decompressing 2125 file(s)", and exited 0
  (`cache-get.log`). No zero-size olean. The probe importing `Mathlib.Algebra.BigOperators.Field`
  elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`): the 246 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`, with start/end time and max RSS), in order: 246/246 status 0,
  no error. No host restart. Sorry census = `base-sorries.txt` (20 declarations in 10 modules;
  `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`: identical).

### 8.2 Step 1 (checkpoint 1)

New helper modules (namespace `TCSlib.Cryptography.Randomness.LearnPRF`):

| File | Lines | Role |
|---|---|---|
| `Randomness/Learning/Sample.lean` | 259 | the learner's input and the last label, as polynomial-time functions of the encoded tuple |
| `Randomness/Learning/Distinguisher.lean` | 136 | the distinguisher `exists_learnDist` |
| `Randomness/Learning/Law.lean` | 173 | the game probability; prediction game and acceptance probability |

The owned file imports the three modules (and nothing else changes in it at this checkpoint).

- **The distinguisher** (`exists_learnDist`): for a learner machine `A` and a polynomial `m`, a
  next-query machine `B` whose coins at `n` are, by a bijection `φ`, `m(n) + 1` points `ρ` and
  `A`'s coins `c`, and whose tree with budget `m(n) + 1` against any oracle `g` evaluates to
  `decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, with `S` the nested labelled examples
  `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points. It is the public query chain
  `MultiMsg.exists_queryChain_nuppt` (non-adaptive queries at points from the coins, here with the
  zero message vector) of the machine `C` that runs `A` on `learnIn m` (`NUPPT.exists_compParam`)
  and compares with `lastLabel m` (`NUPPT.exists_seq` with the uniform machine of `verdictFun`).
  So no T1/T2/T4 run is needed: the query chain already gives a next-query machine
  (`toOracleAdversary`) at `ℓ₁ = ℓ₂ = n`.
- **The learner's input** (`learnIn_tupleWord`, `lastLabel_tupleWord`): the encoded tuple is the
  concatenation of `m(n) + 1` blocks of `6n + 6` bits; a fold of pairs ending in `[]` is a
  concatenation (`foldr_pairEncode_nil`), so the labelled sample is the block map of `relabel` over
  the first `m(n)` blocks (`MultiMsg.flatMap_range_blocks`), polynomial-time by
  `Complexity.polyTimeComputable_blockMap`, `polyTimeComputable_pairTakePoly`/`DropPoly`.
- **The law** (`exists_learnDist_acceptProb`, `predictSuccess_eq_uprob`): for every keyed family
  `G : K → {0,1}^n → {0,1}^n`, `acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n)+1)))` is
  `gameProb (m n) G (learnerFn A n (m n))`, the uniform probability over `((k, (s, r)), x)` of
  `learnerFn … (label (firstBit ∘ G k) s) r x == firstBit (G k x)`; the coins are relabelled by
  `φ` and `snocEquiv` (examples, then the fresh point). The prediction game is the same uniform
  probability: its law is a product of uniform laws (`iid_uniform`, `Rejection.uniform_prod`,
  `Rejection.uniform_probTrue`). The final step identifies `learnerFn` with the owned `learnerOf`
  (`learnerOf_eq`, `encodeSample_eq`) and `firstBit ∘ F n k` with `prfConcept F n k`
  (`prfConcept_eq`), giving `predictSuccess (prfConcept F n) m (learnerOf A n m) = acceptProb (F n) D`.

**Edge cases of step 1.** `n = 0`: all statements hold (one point, `firstBit` is `false`).
`m(n) = 0`: the sample is empty (`List.ofFn` over `Fin 0`), the tuple is the single last block.
A fresh point equal to an example: no case distinction, the uniform probabilities range over all
tuples. `A` printing anything other than `[true]`: `learnerFn` is `decide (… = [true])`, as
`learnerOf`. The coins: `B`'s coins are, by `φ`, the `(m(n) + 1)` points (`(m(n)+1)·n` bits, in
`n`-bit blocks) and `A`'s coins (`C`'s coins are `A.coins + 0`, relabelled by `finCongr`).

### 8.3 Step 2 (checkpoint 2)

New helper `Randomness/Learning/Random.lean` (203 lines), imported by the owned file:
`abs_gameProb_random_sub_half_le`: for `n ≥ 1`, every learner `ℓ` and `m` examples,
`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`, the game with a uniform random function
`R : {0,1}^n → {0,1}^n` in place of the keyed family (with step 1, `acceptProb (randomFunction …) D`
is this game, `randomFunction_apply`).

- Put `R` last and average over it first (`uprob_comp_equiv`, `uprob_prod`). For fixed examples
  `s`, coins `r` and fresh point `x`:
  - if `x` is none of the examples, `flipAt hn x R = update R x (flip0 (R x))` (flip the first bit
    of `R x`) is an involution of the functions (`flipAt_involutive`) that keeps the labels of the
    examples (`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`); it maps the
    winning functions onto the losing ones, so the probability is exactly `½` (`uprob_flip_half`,
    `uprob_comp_equiv`, `uprob_not`);
  - otherwise the probability is in `[0, 1]`.
- So `|gameProb − ½| ≤ Pr[∃ j, s_j = x]` (the average of `|p − ½| ≤ [x ∈ s]`), and the union bound
  (`uprob_exists_le`) with `Pr[s_j = x] = 2^{-n}` (`uprob_prod`, `uprob_eq_point`) gives `m / 2^n`.
- `n ≥ 1` is needed for the first bit; at `n = 0` the final step uses an eventual bound.

New declarations: `flip0` (`flip0_eq`, `flip0_flip0`), `firstBit_of_pos`, `firstBit_flip0`,
`flipAt` (`flipAt_eq`, `flipAt_involutive`), `uprob_flip_half`, `uprob_eq_point`,
`abs_gameProb_random_sub_half_le`.

Overlap (step 2): the flip argument has no TCSlib relative (searched `update`/`involutive`/`flip`
with `uprob` in `TCSlib/Cryptography`); `uprob_eq_point` (`Pr[x = y] = 1/2^n`) is the uniform
point mass, which `Rejection.uniform_probTrue` would give through `FinDist`; the `uprob` form is
stated directly from `uprob_eq_card_filter`. The PRFGame collision bound
(`OracleFromPRF/Collision.lean:375`, `abs_expect_fImpl_sub_le`) bounds the repetition of a nonce
in the CPA game (lazy sampling, `q²/2ⁿ`); here the bad event is one fixed point among `m` samples,
bounded directly.

Evidence added: `logs/checkpoint2-checks.log` (status 0; the one `sorry` warning is the target),
`checkpoint2-axioms.log` (`propext`, `Classical.choice`, `Quot.sound`), `checkpoint2-lint.log`
(92 FAIL / 101 WARN, the base's line sets), `checkpoint2-width.log`, `checkpoint2-repro.log`
(both hashes reproduced), `probes/AxiomsCP2.lean`.


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

## ===== briefs/pass-shelat-ch5-8/fills/learning/issued-r1/brief.md =====

# Claude fill · no efficient learner predicts the PRF concept class (`predictAdv_prfConcept_negligible`, Theorem 179.1 (b))

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `learning`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `predictAdv_prfConcept_negligible` of [PS10, §8.1, Theorem 179.1] in
`TCSlib/Cryptography/Randomness/Learning.lean`. The statement passed the prong D statement phase (ruling D-5: the learning game is the PAC layer of `TCSlib/LearningTheory`) and Gate 06,
and is frozen. Its docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated. The PRF, machine and probability interfaces exist, and the PAC game reads through published lemmas. The main work is the law bridge between the oracle run and `trialDist`. No dependency on an admitted target: `bpp_subset_dtime_subexp` is in the closure only through the `Randomness` facade.

**Estimated size:** 1,200–2,500 lines in 3–6 helper modules.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/learning` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/learning/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/learning/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill learning: checkpoint N` and `fill learning: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `derand`, `seq-zk`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Target (frozen; quoted from the issue base)

```lean
theorem predictAdv_prfConcept_negligible (hF : PRF F) (A : NUPPT) (m : PolyExpr) :
    Negligible fun n => predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Randomness`. The section variable is `F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)` (explicit). The
theorem takes `hF : PRF F`, a machine `A : NUPPT` and a polynomial `m : PolyExpr`.

**The game** (`TCSlib/LearningTheory/PAC/Prediction.lean`): `predictAdv C m L = |predictSuccess C m L − ½|`
(`predictAdv_eq`). `predictSuccess` (`predictSuccess_eq`, `trialDist_eq`) is the probability, over a uniform key, `m`
independent uniform examples, uniform coins and a fresh uniform point `x`, that the hypothesis agrees with `C_k(x)`.
The examples are labelled by `label` (`label_apply`). The fresh point may coincide with an example.

**The owned definitions:** `prfConcept F n k x` is the first bit of `F n k x`, `false` at `n = 0`
(`prfConcept_eq`); `encodeSample_eq`; `learnerOf A n m S r x` is `[A(1^n, ⟨S, x⟩; r) = [true]]` (`learnerOf_eq`).

**Dependencies.** The proof needs neither `prfMAC_secure` (the MAC modules are not in this closure) nor any
other admitted target. Part (c), `not_weakLearnsUnder_prfConcept`, in the same file is proved from this target
and is unchanged; its axioms become standard with yours.

## Published interfaces

| Interface | Provider |
|---|---|
| `prfConcept_eq`, `encodeSample_eq`, `learnerOf_eq`, `prfConcept_decidable` (the evaluator pattern) | owned file |
| `trialDist_eq`, `predictSuccess_eq`, `predictAdv_eq`, `label_apply`, `predictSuccess_coin` | `LearningTheory/PAC/Prediction.lean`, `PAC/Defs.lean` |
| `FinDist` laws (`uniform`, `prod`, `iid`, `probTrue`) and their readers; `uprob_comp_eq_probTrue_map` | `InformationTheory/FinDist.lean`, `Asymptotic/SamplingFinDist.lean` |
| `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`, `prfAdv_def`, `oracleDist_apply`, `acceptProb_random_eq_lazy`, `lazyDist_apply` | `Pseudorandom/Functions/Asymptotic/Defs.lean`, `…/Defs.lean`, `…/OracleAdversary.lean`, `…/LazySampling.lean` |
| T1 `exists_handlerMachine` (non-adaptive queries) and the `PolyHandler` readers; T2; T4 `exists_toOracleAdversary_of_bitCodec` | `Games/Efficiency.lean` |
| `prob_mem_le`, `expect_sample_mem_le` | `Games/Hopping.lean` |
| `NUPPT.exists_comp`, `ofPolyTimeUniform` and the run/coin readers; `coinBlock`, `FunFamily.blocks`, `ofFn_blocks` | `Complexity/Randomized/Closure.lean`, `Asymptotic/Adversary.lean`, `Foundations/BitLists.lean` |
| `Negligible.add`, `mono`, `mul_pow` (the polynomial factor `m(n)`), `negligible_two_pow_neg` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the distinguisher and the real game (sketch step 1).** Build `D`: its coins are `A`'s coins and `m(n) + 1` blocks of `n` bits (`coinBlock`). It queries its oracle at the `m(n) + 1` points (T1, non-adaptive), labels the first `m(n)` with the first bits of the answers, runs `A` on `⟨encodeSample S, x_last⟩`, and outputs whether `A`'s prediction equals the first bit of the last answer. Make it an oracle adversary with T4 at `ℓ₁ = ℓ₂ = var`. Prove that with the oracle `f_k` its acceptance probability is `predictSuccess (prfConcept F n) (m n) (learnerOf A n (m n))`: the oracle run with uniform coins has the law `trialDist × uniform`, through `uprob_comp_eq_probTrue_map` and the `FinDist` product and `iid` readers. Send this checkpoint.
2. **Checkpoint 2 · the random function (sketch step 2).** With a uniform random function, the acceptance probability is within `m(n)/2^n` of `½` for `n ≥ 1`: unless the last point was sampled (probability at most `m(n)/2^n`), its label is the first bit of a fresh uniform value, independent of the sample. Send this checkpoint.
3. **Final · the bound (sketch step 3).** `predictAdv ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n` for `n ≥ 1`. It is negligible by `PRF.negligible_prfAdv`, `Negligible.mul_pow` and `Negligible.add`. Handle `n = 0` by `Negligible.mono` (eventual bounds).

Check the edge cases: `n = 0` (one point, `prfConcept` constant `false`); `m(n) = 0` (no examples); a fresh point equal to an example; `A` printing anything other than `[true]`; the codecs' timeout outputs; the coin split between `A.Coins n` and the `(m(n) + 1) · n` sample bits.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Randomness/Learning.lean` (149 lines at the issue base):
  - replace the target's proof body and edit its sketch to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Randomness/Learning/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `Games/Efficiency`, `Games/Hopping`, `Encryption/PrivateKey/OracleFromPRF` (and its helpers) and `Asymptotic/SamplingFinDist`. None is downstream of the owned file, so there is no cycle (checked at the issue base); the order includes their upstream closure.
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines. Do not add to it.
  - **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
    import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff
    and the reason, and go ahead only on his approval. Record the request and his answer verbatim under
    `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. The Codex fills obtained their facade
    imports, and dl-crh its two `DiscreteLog` readers, this way. Seyoon prefers a route with no frozen-file edit
    where one exists.
  - A lemma that belongs in an existing file goes in your helper module, with a promotion request.
- **Parallel fills.** The seven fills `prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot` and
  `sc-compose` are issued from the same base. Edit only your owned file and helper directory.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:** ext-nosrc's sampler law (`Randomness/Extraction/Sampler.lean`), the GGM reduction (`Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean`), the T1 reductions of hash-sign and Lamport (`Signatures/HashAndSign/*`, `Signatures/Lamport/*`) and the PRFGame collision bound (`OracleFromPRF/Collision.lean`).
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file. The owned file's definitions
    are foreign to your helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (246 modules) and the narrow `roots.txt` (82), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (20 declarations in 10 modules). The only change
    must be the removal of `predictAdv_prfConcept_negligible`.
- **Axioms.**
  - Print the axioms of `predictAdv_prfConcept_negligible`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files, and of `not_weakLearnsUnder_prfConcept`.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (after #305).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base and the status of each target;
  - the changed files and the sketch edits;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

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
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `PRF.prfAdv_eq_expect` (to be published); the list readers above; `GGMRed.tblEnc` | Open | F-01 by the promotion PR; F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse where the import is acyclic); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |

## ===== briefs/pass-shelat-ch5-8/gates/29-learning/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Randomness/Learning.lean b/TCSlib/Cryptography/Randomness/Learning.lean
index 82ab19b87..ddb1a07aa 100644
--- a/TCSlib/Cryptography/Randomness/Learning.lean
+++ b/TCSlib/Cryptography/Randomness/Learning.lean
@@ -6,13 +6,17 @@ import TCSlib.LearningTheory.PAC
 import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
+import TCSlib.Cryptography.Randomness.Learning.Sample
+import TCSlib.Cryptography.Randomness.Learning.Distinguisher
+import TCSlib.Cryptography.Randomness.Learning.Law
+import TCSlib.Cryptography.Randomness.Learning.Random
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Pseudorandom functions make an unlearnable concept class (statement phase)
+# Pseudorandom functions make an unlearnable concept class
 
 [PS10, §8.1, Theorem 179.1]: if pseudorandom functions exist, there is a p.p.t.-decidable
 concept class that no non-uniform p.p.t. learner can learn: given polynomially many labelled uniform
@@ -36,14 +40,26 @@ notions are those of the information-theoretic layer `TCSlib.LearningTheory.PAC`
 
 * `Randomness.prfConcept_decidable` (Thm 179.1, part (a), proved): membership is
   polynomial-time decidable given the key.
-* `Randomness.predictAdv_prfConcept_negligible` (Thm 179.1, part (b), stated; a `sorry` under the
-  source's sketch): every efficient learner's prediction advantage is negligible.
+* `Randomness.predictAdv_prfConcept_negligible` (Thm 179.1, part (b), proved): every efficient
+  learner's prediction advantage is negligible.
 * `Randomness.not_weakLearnsUnder_prfConcept` (Thm 179.1, part (c), proved from (b) and the PAC
   layer's bridge): no efficient learner weakly PAC-learns the class under the uniform distribution
   with a constant edge `γ` at fixed failure probability `δ < γ`. Amplifying a KV94-style
   weak learner changes the learner and its resources; that amplification and its resource
   bridge are additional results, not a construction already supplied by part (c).
 
+## Contents
+
+This file states the class, the learner and Theorem 179.1, and assembles the proof of part (b)
+from the helper modules under `Learning/` (namespace `Randomness.LearnPRF`):
+- `Sample`: the learner's input and the last label as polynomial-time functions of the encoded
+  tuple of query points and answers (`learnIn`, `lastLabel`);
+- `Distinguisher`: the PRF distinguisher built from a learner (`exists_learnDist`);
+- `Law`: the prediction game and the distinguisher's acceptance probability as one uniform
+  probability (`predictSuccess_eq_uprob`, `gameProb`, `exists_learnDist_acceptProb`);
+- `Random`: with a uniform random function the prediction is within `m/2^n` of `½`
+  (`abs_gameProb_random_sub_half_le`).
+
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
@@ -103,18 +119,73 @@ a PRF, then for every non-uniform PPT learner `A` and polynomial number `m` of e
 prediction advantage `|Pr[A predicts C_k(x)] − ½|` at uniform `k`, uniform examples and a fresh
 uniform `x` is negligible.
 
-**Proof sketch** (the source's, made explicit).
-1. The distinguisher `D` against the PRF draws `m(n) + 1` uniform points, queries its oracle at
-   them, labels the first `m(n)` with the answers' first bits, runs `A` on the labelled sample and
-   the last point, and outputs whether `A`'s prediction equals the last answer's first bit. With
-   `f_k` this is the prediction game. `D` is a machine by T1 (non-adaptive queries).
-2. With a random function, the last point's label is a uniform bit independent of the sample,
-   unless the last point was sampled, with probability at most `m(n)/2^n`. So `D` accepts with
-   probability at most `½ + m(n)/2^n`, and at least `½ − m(n)/2^n`.
-3. Hence the advantage is at most the PRF advantage plus `m(n)/2^n`: negligible. -/
+**Proof sketch** (the source's, made explicit; the delivered proof).
+1. **The distinguisher and the real game.** The next-query machine `D` of
+   `LearnPRF.exists_learnDist_acceptProb` takes `m(n) + 1` uniform points from its coins, queries
+   its oracle at them (the non-adaptive query chain `MultiMsg.exists_queryChain_nuppt`), labels
+   the first `m(n)` with the answers' first bits, runs `A` (with its own coins) on the labelled
+   sample and the last point, and accepts when `A`'s prediction equals the last answer's first
+   bit. Against any keyed family its acceptance probability is a uniform probability over the
+   key, the examples, the coins and the fresh point (`LearnPRF.gameProb`); with `f_k` this is
+   the prediction game (`LearnPRF.predictSuccess_eq_uprob`), so
+   `predictSuccess = acceptProb (F n) D`. The fresh point may equal an example, in both.
+2. **The random function.** With a uniform random function `R`, for `n ≥ 1`: when the last point
+   is none of the examples, flipping the first bit of `R` there exchanges winning and losing
+   functions, so `D` wins with probability exactly `½`; the last point is an example with
+   probability at most `m(n)/2^n` (union bound). So `|acceptProb R D − ½| ≤ m(n)/2^n`
+   (`LearnPRF.abs_gameProb_random_sub_half_le`).
+3. **The bound.** For `n ≥ 1`, `predictAdv ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n`, which is
+   negligible by `PRF.negligible_prfAdv` (budget `m + 1`), `EnsembleLemmas.negligible_polyExpr_mul`
+   with `negligible_two_pow_neg`, and `Negligible.add`; the eventual bound gives negligibility
+   (`Negligible.mono` from `n = 1`, so `n = 0` needs no case). -/
 theorem predictAdv_prfConcept_negligible (hF : PRF F) (A : NUPPT) (m : PolyExpr) :
     Negligible fun n => predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) := by
-  sorry
+  obtain ⟨B, hB⟩ := LearnPRF.exists_learnDist_acceptProb A m
+  -- The owned learner and concept are the helpers' `learnerFn` and `firstBit`.
+  have hL : ∀ n, learnerOf A n (m.eval n) = LearnPRF.learnerFn A n (m.eval n) := fun n => by
+    funext S r x
+    rw [learnerOf_eq, LearnPRF.learnerFn_eq, encodeSample_eq]
+  have hC : ∀ n (k : Fin n → Bool), prfConcept F n k = fun x => LearnPRF.firstBit (F n k x) :=
+    fun n k => funext fun x => by rw [prfConcept_eq, LearnPRF.firstBit_eq]
+  -- Step 1: the prediction game is the distinguisher's game with `f_k`.
+  have hreal : ∀ n, predictSuccess (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) =
+      acceptProb (F n) (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) := by
+    intro n
+    rw [hB, LearnPRF.predictSuccess_eq_uprob, LearnPRF.gameProb_eq, hL]
+    simp only [hC]
+  -- Step 2: with a random function the acceptance probability is within `m(n)/2^n` of `½`.
+  have hrand : ∀ n, 0 < n →
+      |acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
+          (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) - 1 / 2| ≤
+        (m.eval n : ℝ) / 2 ^ n := by
+    intro n hn
+    rw [hB]
+    have h := LearnPRF.abs_gameProb_random_sub_half_le hn (m.eval n)
+      (LearnPRF.learnerFn A n (m.eval n))
+    rwa [show (fun R : (Fin n → Bool) → (Fin n → Bool) => R) =
+      randomFunction (Fin n → Bool) (Fin n → Bool) from
+        funext fun R => (randomFunction_apply _ _ R).symm] at h
+  -- Step 3: the bound, negligible by PRF security and `m(n)/2^n → 0`.
+  have hQ : ∀ n, (PolyExpr.add m (.const 1)).eval n = m.eval n + 1 := fun n => by
+    rw [PolyExpr.eval_add, PolyExpr.eval_const]
+  have hprf := hF.negligible_prfAdv B (.add m (.const 1))
+  simp only [hQ] at hprf
+  have hpow : Negligible fun n => (m.eval n : ℝ) / 2 ^ n := by
+    refine (EnsembleLemmas.negligible_polyExpr_mul m negligible_two_pow_neg).mono
+      ⟨0, fun n _ => le_of_eq ?_⟩
+    rw [inv_pow, div_eq_mul_inv]
+  refine (hprf.add hpow).mono ⟨1, fun n hn => ?_⟩
+  have h₁ := hrand n (by omega)
+  have h₂ := prfAdv_nonneg (F n) (B.toOracleAdversary n n n (m.eval n + 1))
+  have h₃ : (0 : ℝ) ≤ (m.eval n : ℝ) / 2 ^ n := by positivity
+  rw [predictAdv_eq, hreal, abs_abs, abs_of_nonneg (add_nonneg h₂ h₃), prfAdv_def, distAdv_def]
+  calc _ ≤ |acceptProb (F n) (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) -
+          acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
+            (oracleDist (B.toOracleAdversary n n n (m.eval n + 1)))| +
+        |acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
+            (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) - 1 / 2| :=
+        abs_sub_le _ _ _
+    _ ≤ _ := by linarith
 
 /-- **Theorem 179.1 (c): no efficient weak PAC learner** under the uniform distribution: for edges
 `δ < γ ≤ ½`, every efficient learner fails to `(γ, δ)`-weakly learn the class from some
diff --git a/TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean b/TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean
new file mode 100644
index 000000000..5d114cc57
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean
@@ -0,0 +1,137 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Randomness.Learning.Sample
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The PRF distinguisher built from a learner
+
+Step 1 of [PS10, Theorem 179.1, proof]: from a learner machine `A` and a polynomial number `m` of
+examples, a next-query machine `B` that queries its oracle `g` at `m(n) + 1` points `ρ` drawn from
+its coins, labels the first `m(n)` by the first bits of the answers, runs `A` (with its own coins)
+on the labelled sample and the last point, and accepts when `A`'s prediction (its output being
+`[true]`) equals the first bit of the last answer (`exists_learnDist`).
+
+`B` is the query chain of `MultiMsg.exists_queryChain_nuppt` (non-adaptive queries at points
+from the coins, the zero message vector) applied to the machine `C` that, on the encoded tuple,
+runs `A` on `learnIn m` (`NUPPT.exists_compParam`) and then compares with `lastLabel m`
+(`NUPPT.exists_seq` with the uniform machine of `verdictFun`).
+
+## Main definitions
+
+* `LearnPRF.verdictFun`: the comparison of the prediction with the last label.
+
+## Main results
+
+* `LearnPRF.polyTimeComputable_verdictFun`.
+* `LearnPRF.exists_learnDist`: the distinguisher and its verdict against every oracle.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §8.1, Theorem 179.1 (book p. 179).
+-/
+
+namespace TCSlib.Cryptography.Randomness.LearnPRF
+
+open Complexity Turing TCSlib.Cryptography
+
+/-- **The verdict** on the raw layout whose argument is `⟨w, a⟩` (the encoded tuple `w` and the
+learner's output `a`) at parameter `u = 1^n`: `[decide (a = [true]) == lastLabel m ⟨u, w⟩]`. -/
+def verdictFun (m : PolyExpr) (z : List Bool) : List Bool :=
+  [decide (pairSndD (NUPPT.inArg z) = [true]) ==
+    lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))]
+
+/-- `verdictFun m z = [decide (pairSndD (inArg z) = [true]) ==
+lastLabel m ⟨inParam z, pairFstD (inArg z)⟩]`. -/
+theorem verdictFun_eq (m : PolyExpr) (z : List Bool) :
+    verdictFun m z =
+      [decide (pairSndD (NUPPT.inArg z) = [true]) ==
+        lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))] := rfl
+
+/-- The verdict is polynomial-time: an equality test (`polyTimeComputable_pairEq`) selecting the
+last label or its negation (`polyTimeComputable_ite`, `polyTimeComputable_not`,
+`polyTimeComputable_lastLabel`): `PolyTimeComputable (verdictFun m)`, for
+`verdictFun m : List Bool → List Bool`. -/
+theorem polyTimeComputable_verdictFun (m : PolyExpr) : PolyTimeComputable (verdictFun m) := by
+  have hArg := NUPPT.polyTimeComputable_inArg
+  have hEq : PolyTimeComputable fun z => [decide (pairSndD (NUPPT.inArg z) = [true])] :=
+    (polyTimeComputable_pairEq.comp ((polyTimeComputable_pairSndD.comp hArg).pairEncode
+      (polyTimeComputable_const [true]))).congr fun z => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  have hL : PolyTimeComputable fun z =>
+      [lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))] :=
+    (polyTimeComputable_lastLabel m).comp
+      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_pairFstD.comp hArg))
+  refine (polyTimeComputable_ite hEq hL (polyTimeComputable_not hL)).congr fun z => ?_
+  rw [verdictFun_eq]
+  cases decide (pairSndD (NUPPT.inArg z) = [true]) <;>
+    cases lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z))) <;> rfl
+
+/-- The zero message vector leaves the answers unchanged: `(fun _ => false) + y = y`. -/
+private theorem zero_add_fun {n : ℕ} (y : Fin n → Bool) : (fun _ => false) + y = y := by
+  funext i
+  rw [Pi.add_apply]
+  cases y i <;> rfl
+
+/-- **The distinguisher of [PS10, Theorem 179.1, proof]:** for a learner machine `A` and a
+polynomial `m`, there is a next-query machine `B` whose coins at `n` are, up to a bijection `φ`,
+the `m(n) + 1` query points `ρ` and `A`'s coins `c`, and whose query tree with budget `m(n) + 1`,
+evaluated against any oracle `g`, is
+`decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, where `S` is the nested labelled
+examples `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points.
+
+**Proof sketch.** `A₁ := exists_compParam A` with `pre = learnIn m` and `post = pairSndD` runs `A`
+on the learner's input; `C := exists_seq A₁ V` with the uniform machine `V` of `verdictFun m`
+compares its output with the last label; `B := MultiMsg.exists_queryChain_nuppt C m 0`. Against
+`g` the tree of `B` gives `C`'s verdict on the encoded tuple `tupleWord ρ g` (`zero_add_fun`); the
+runs of `C`, `A₁` and `V` unfold by their equations (`NUPPT.runAtL_ofPolyTimeUniform`, the layout
+readers), the learner's input and the last label are `learnIn_tupleWord` and
+`lastLabel_tupleWord`, and `decide ([b] = [true]) = b`. The coins of `C` are those of `A`
+(`A.coins + 0`), relabelled by `finCongr` (`ofFn_arrowCongr_finCongr`). -/
+theorem exists_learnDist (A : NUPPT) (m : PolyExpr) :
+    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (m.eval n + 1) → Fin n → Bool) × A.Coins n ≃ B.Coins n,
+      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (m.eval n + 1) → Fin n → Bool)
+        (c : A.Coins n),
+        (B.toOracleAdversary n n n (m.eval n + 1) (φ (ρ, c))).eval g =
+          (decide (A.runAt n (pairEncode ((List.ofFn fun j : Fin (m.eval n) =>
+              pairEncode (List.ofFn (ρ j.castSucc)) [firstBit (g (ρ j.castSucc))]).foldr
+                pairEncode []) (List.ofFn (ρ (Fin.last _)))) c = [true]) ==
+            firstBit (g (ρ (Fin.last _)))) := by
+  obtain ⟨A₁, hA₁c, -, -, hA₁⟩ :=
+    NUPPT.exists_compParam A (polyTimeComputable_learnIn m) polyTimeComputable_pairSndD
+  obtain ⟨C, hCc, -, hC⟩ :=
+    A₁.exists_seq (NUPPT.ofPolyTimeUniform (polyTimeComputable_verdictFun m) (.const 0))
+  obtain ⟨B, hB⟩ := MultiMsg.exists_queryChain_nuppt C m (fun _ _ _ => false)
+  refine ⟨B, fun n => ?_⟩
+  obtain ⟨φ₀, hφ₀⟩ := hB n
+  have hlen : A.coinLen n = C.coinLen n := by
+    simp only [NUPPT.coinLen_eq, hCc, hA₁c, NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_add,
+      PolyExpr.eval_const, Nat.add_zero]
+  have hlen₁ : A₁.coinLen n = A.coinLen n := by simp only [NUPPT.coinLen_eq, hA₁c]
+  let ψ : A.Coins n ≃ C.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
+  refine ⟨((Equiv.refl _).prodCongr ψ).trans φ₀, fun g ρ c => ?_⟩
+  have hw : (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (ρ j))
+      (List.ofFn ((fun _ _ _ => false : ∀ n, Fin (m.eval n + 1) → Fin n → Bool) n j +
+        g (ρ j)))) []).flatten = tupleWord ρ g := by
+    rw [tupleWord_eq]
+    refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
+    rw [zero_add_fun]
+  have hc : (List.ofFn c).length ≤ A₁.coinLen n := by rw [List.length_ofFn, hlen₁]
+  rw [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, hφ₀, hw,
+    NUPPT.runAt_eq, ofFn_arrowCongr_finCongr, hC, List.take_of_length_le hc,
+    NUPPT.runAtL_ofPolyTimeUniform, hA₁, pairSndD_pairEncode, verdictFun_eq, NUPPT.inArg_eq,
+    NUPPT.inParam_eq]
+  simp only [NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+  rw [learnIn_tupleWord, lastLabel_tupleWord, ← NUPPT.runAt_eq]
+  cases decide (A.runAt n (pairEncode ((List.ofFn fun j : Fin (m.eval n) =>
+      pairEncode (List.ofFn (ρ j.castSucc)) [firstBit (g (ρ j.castSucc))]).foldr pairEncode [])
+      (List.ofFn (ρ (Fin.last _)))) c = [true]) <;>
+    cases firstBit (g (ρ (Fin.last _))) <;> rfl
+
+end TCSlib.Cryptography.Randomness.LearnPRF
diff --git a/TCSlib/Cryptography/Randomness/Learning/Law.lean b/TCSlib/Cryptography/Randomness/Learning/Law.lean
new file mode 100644
index 000000000..1b106aaf5
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Learning/Law.lean
@@ -0,0 +1,174 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Randomness.Learning.Distinguisher
+import TCSlib.Cryptography.Randomness.Extraction.Rejection
+import TCSlib.LearningTheory.PAC
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The prediction game as the distinguisher's acceptance probability
+
+Step 1 of [PS10, Theorem 179.1, proof], the law: both the prediction game of the PAC layer and
+the acceptance probability of the distinguisher of `exists_learnDist` against a keyed family are
+uniform probabilities of one event over the keys, `m` examples, the learner's coins and a fresh
+point (`gameProb`).
+
+* **The prediction game** (`predictSuccess_eq_uprob`): its law is a product of uniform laws, the
+  uniform law on the product (`iid_uniform`, `Rejection.uniform_prod`), so its success
+  probability is the uniform probability of the event (`Rejection.uniform_probTrue`).
+* **The distinguisher** (`exists_learnDist_acceptProb`): its coins are, through the bijection of
+  `exists_learnDist`, the `m(n) + 1` points and the learner's coins; the points are the examples
+  followed by the fresh point (`Fin.snoc`, `snocEquiv`), so for every family `G`,
+  `acceptProb G (oracleDist B) = gameProb m G (learnerFn A n m)`.
+
+## Main definitions
+
+* `LearnPRF.gameProb`: the game probability with a family `G` and a learner `ℓ`.
+* `LearnPRF.learnerFn`: the learner of a machine, as a function (the learner of the learning
+  game, restated here since helper modules do not import the owned file).
+* `LearnPRF.snocEquiv`: examples and a fresh point as one tuple.
+
+## Main results
+
+* `LearnPRF.iid_uniform`: independent uniform samples are a uniform tuple.
+* `LearnPRF.predictSuccess_eq_uprob`: the prediction game as a uniform probability.
+* `LearnPRF.exists_learnDist_acceptProb`: the distinguisher's acceptance probability is the game
+  probability of the machine's learner.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §8.1, Theorem 179.1 (book p. 179).
+-/
+
+namespace TCSlib.Cryptography.Randomness.LearnPRF
+
+open Complexity Turing TCSlib.Cryptography TCSlib.InformationTheory TCSlib.LearningTheory.PAC
+  Finset
+
+/-! ### Uniform laws -/
+
+/-- **Independent uniform samples are a uniform tuple:** `(U_X)^m = U_{X^m}`.
+
+**Proof sketch.** Both give every tuple `|X|^{-m}` (`FinDist.iid_apply`, `FinDist.uniform_apply`,
+`Fintype.card_fun`, `Finset.prod_const`). -/
+theorem iid_uniform {X : Type*} [Fintype X] [Nonempty X] (m : ℕ) :
+    (FinDist.uniform X).iid m = FinDist.uniform (Fin m → X) := by
+  classical
+  apply FinDist.ext
+  intro s
+  rw [FinDist.iid_apply]
+  simp only [FinDist.uniform_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
+    Fintype.card_fun, Nat.cast_pow, inv_pow]
+
+/-- **The prediction game as a uniform probability:** `predictSuccess C m L` is the uniform
+probability over `((i, (s, r)), x)` of `L (label (C i) s) r x == C i x`.
+
+**Proof sketch.** The law of the game is `(U_I × (U_X^m × U_ρ)) × U_X`, the uniform law on the
+product (`iid_uniform`, `Rejection.uniform_prod`); acceptance under a uniform law counts the
+accepted points (`Rejection.uniform_probTrue`, `uprob_eq_card_filter`). -/
+theorem predictSuccess_eq_uprob {X I ρ : Type*} [Fintype X] [Nonempty X] [Fintype I] [Nonempty I]
+    [Fintype ρ] [Nonempty ρ] (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
+    predictSuccess C m L =
+      uprob fun w : (I × ((Fin m → X) × ρ)) × X =>
+        (L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2) = true := by
+  classical
+  rw [predictSuccess_eq, trialDist_eq, iid_uniform, Rejection.uniform_prod,
+    Rejection.uniform_prod, Rejection.uniform_prod, Rejection.uniform_probTrue,
+    uprob_eq_card_filter, div_eq_mul_inv]
+
+/-! ### The game probability -/
+
+section Game
+
+variable {n : ℕ}
+
+/-- **The game probability** with a family `G : K → {0,1}^n → {0,1}^n` and a learner `ℓ`: the
+uniform probability over `((k, (s, r)), x)` that `ℓ`, on the examples `s` labelled by the first
+bits of `G k` and the coins `r`, predicts at `x` the first bit of `G k x`. -/
+noncomputable def gameProb {K ρ : Type*} [Fintype K] [Fintype ρ] (m : ℕ)
+    (G : K → (Fin n → Bool) → (Fin n → Bool))
+    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) : ℝ :=
+  uprob fun w : (K × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) =>
+    (ℓ (label (fun x => firstBit (G w.1.1 x)) w.1.2.1) w.1.2.2 w.2 == firstBit (G w.1.1 w.2)) =
+      true
+
+/-- `gameProb m G ℓ = uprob (fun ((k, (s, r)), x) =>
+(ℓ (label (firstBit ∘ G k) s) r x == firstBit (G k x)) = true)`. -/
+theorem gameProb_eq {K ρ : Type*} [Fintype K] [Fintype ρ] (m : ℕ)
+    (G : K → (Fin n → Bool) → (Fin n → Bool))
+    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
+    gameProb m G ℓ =
+      uprob fun w : (K × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) =>
+        (ℓ (label (fun x => firstBit (G w.1.1 x)) w.1.2.1) w.1.2.2 w.2 ==
+          firstBit (G w.1.1 w.2)) = true := rfl
+
+/-- **The learner of a machine** `A` at parameter `n` with `m` examples, as a function: on the
+labelled sample `S`, the coins `r` and the point `x`, whether `A(1^n, ⟨S', ⟦x⟧⟩; r) = [true]`,
+where `S'` is the nested pairs of the examples `⟨⟦x_j⟧, [b_j]⟩`. -/
+def learnerFn (A : NUPPT) (n m : ℕ) :
+    (Fin m → (Fin n → Bool) × Bool) → A.Coins n → (Fin n → Bool) → Bool :=
+  fun S r x => decide (A.runAt n (pairEncode ((List.ofFn fun j =>
+    pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []) (List.ofFn x)) r = [true])
+
+/-- `learnerFn A n m S r x =
+decide (A.runAt n ⟨(ofFn j ↦ ⟨⟦(S j).1⟧, [(S j).2]⟩).foldr pairEncode [], ⟦x⟧⟩ r = [true])`. -/
+theorem learnerFn_eq (A : NUPPT) (n m : ℕ) (S : Fin m → (Fin n → Bool) × Bool) (r : A.Coins n)
+    (x : Fin n → Bool) :
+    learnerFn A n m S r x = decide (A.runAt n (pairEncode ((List.ofFn fun j =>
+      pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []) (List.ofFn x)) r = [true]) :=
+  rfl
+
+/-- **Examples and a fresh point as one tuple:** `((k, (s, r)), x) ↦ (k, (snoc s x, r))`, an
+equivalence `(K × ((Fin m → X) × ρ)) × X ≃ K × ((Fin (m + 1) → X) × ρ)`. -/
+def snocEquiv (K X ρ : Type*) (m : ℕ) :
+    (K × ((Fin m → X) × ρ)) × X ≃ K × ((Fin (m + 1) → X) × ρ) where
+  toFun w := (w.1.1, (Fin.snoc w.1.2.1 w.2, w.1.2.2))
+  invFun z := ((z.1, (Fin.init z.2.1, z.2.2)), z.2.1 (Fin.last m))
+  left_inv w := by
+    obtain ⟨⟨k, s, r⟩, x⟩ := w
+    simp only [Fin.init_snoc, Fin.snoc_last]
+  right_inv z := by
+    obtain ⟨k, t, r⟩ := z
+    simp only [Fin.snoc_init_self]
+
+/-- `snocEquiv K X ρ m ((k, (s, r)), x) = (k, (Fin.snoc s x, r))`. -/
+theorem snocEquiv_apply (K X ρ : Type*) (m : ℕ) (w : (K × ((Fin m → X) × ρ)) × X) :
+    snocEquiv K X ρ m w = (w.1.1, (Fin.snoc w.1.2.1 w.2, w.1.2.2)) := rfl
+
+/-- **The distinguisher's acceptance probability is the game probability** [PS10, Theorem 179.1,
+proof, step 1]: for a learner machine `A` and a polynomial `m` there is a next-query machine `B`
+such that for every `n` and every family `G : K → {0,1}^n → {0,1}^n` (uniform keys),
+`acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n) + 1)))` is
+`gameProb (m n) G (learnerFn A n (m n))`.
+
+**Proof sketch.** `B` is `exists_learnDist A m`. Relabel the seeds `(k, c)` of the acceptance
+probability by `((k, (s, r)), x) ↦ (k, φ (snoc s x, r))` (`uprob_comp_equiv`, `snocEquiv`,
+`Equiv.prodCongr`); the verdict of `B` at `φ (snoc s x, r)` against `G k` is the learner's
+prediction on the examples `s` labelled by `firstBit ∘ G k` compared with `firstBit (G k x)`
+(`exists_learnDist`, `Fin.snoc_castSucc`, `Fin.snoc_last`, `label_apply`). -/
+theorem exists_learnDist_acceptProb (A : NUPPT) (m : PolyExpr) :
+    ∃ B : NUPPT, ∀ (n : ℕ) {K : Type*} [Fintype K] (G : K → (Fin n → Bool) → (Fin n → Bool)),
+      acceptProb G (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) =
+        gameProb (m.eval n) G (learnerFn A n (m.eval n)) := by
+  obtain ⟨B, hB⟩ := exists_learnDist A m
+  refine ⟨B, fun n K _ G => ?_⟩
+  obtain ⟨φ, hφ⟩ := hB n
+  rw [acceptProb_def, gameProb_eq, ← uprob_comp_equiv ((snocEquiv K (Fin n → Bool) (A.Coins n)
+    (m.eval n)).trans ((Equiv.refl K).prodCongr φ))]
+  congr 1
+  funext w
+  have hlab : ∀ (c : (Fin n → Bool) → Bool) (s : Fin (m.eval n) → Fin n → Bool),
+      label c s = fun j => (s j, c (s j)) := fun c s => funext (label_apply c s)
+  rw [Equiv.trans_apply, snocEquiv_apply, Equiv.prodCongr_apply, Prod.map_apply,
+    Equiv.refl_apply, oracleDist_apply, hφ, learnerFn_eq, Fin.snoc_last, hlab]
+  simp only [Fin.snoc_castSucc]
+
+end Game
+
+end TCSlib.Cryptography.Randomness.LearnPRF
diff --git a/TCSlib/Cryptography/Randomness/Learning/Random.lean b/TCSlib/Cryptography/Randomness/Learning/Random.lean
new file mode 100644
index 000000000..c2e90978d
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Learning/Random.lean
@@ -0,0 +1,189 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Randomness.Learning.Law
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# With a random function, no learner predicts better than `½ ± m/2^n`
+
+Step 2 of [PS10, Theorem 179.1, proof]: in the game with a uniform random function
+`R : {0,1}^n → {0,1}^n` in place of the keyed family, every learner `ℓ` predicts the first bit of
+`R x` with probability within `m/2^n` of `½`, for `n ≥ 1` (`abs_gameProb_random_sub_half_le`).
+
+**Proof.** Fix the examples `s`, the coins `r` and the fresh point `x`. If `x` is none of the
+examples, flipping the first bit of `R x` (`flipAt`, an involution of the random functions) keeps
+the labelled examples and negates the label of `x`, so it exchanges the winning and the losing
+functions: the probability over `R` is exactly `½` (`uprob_flip_half`). Otherwise the probability
+is between `0` and `1`. So the game probability is within `Pr[x ∈ s]` of `½`, and
+`Pr[x ∈ s] ≤ Σ_j Pr[x = s_j] = m · 2^{-n}` (`uprob_exists_le`, `uprob_eq_point`).
+
+## Main definitions
+
+* `LearnPRF.flip0`, `LearnPRF.flipAt`: flipping the first bit of a string, and of a function's
+  value at a point.
+
+## Main results
+
+* `LearnPRF.firstBit_flip0`, `LearnPRF.flipAt_involutive`.
+* `LearnPRF.uprob_flip_half`: at a fresh point, the prediction wins with probability `½`.
+* `LearnPRF.uprob_eq_point`: a uniform point hits a given point with probability `2^{-n}`.
+* `LearnPRF.abs_gameProb_random_sub_half_le`: the bound `|gameProb − ½| ≤ m/2^n`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §8.1, Theorem 179.1 (book p. 179).
+-/
+
+namespace TCSlib.Cryptography.Randomness.LearnPRF
+
+open Complexity TCSlib.Cryptography TCSlib.LearningTheory.PAC Finset
+
+section Random
+
+variable {n : ℕ} (hn : 0 < n)
+
+/-- **Flipping the first bit** of an `n`-bit string (`n ≥ 1`):
+`flip0 hn y = update y 0 (!y 0)`. -/
+def flip0 (y : Fin n → Bool) : Fin n → Bool := Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)
+
+/-- `flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩)`. -/
+theorem flip0_eq (y : Fin n → Bool) : flip0 hn y = Function.update y ⟨0, hn⟩ (!y ⟨0, hn⟩) := rfl
+
+/-- Flipping twice is the identity: `flip0 hn (flip0 hn y) = y`. -/
+theorem flip0_flip0 (y : Fin n → Bool) : flip0 hn (flip0 hn y) = y := by
+  rw [flip0_eq, flip0_eq, Function.update_self, Function.update_idem, Bool.not_not,
+    Function.update_eq_self]
+
+/-- The first bit of an `n`-bit string with `n ≥ 1` is its bit `0`:
+`firstBit y = y ⟨0, hn⟩`. -/
+theorem firstBit_of_pos (y : Fin n → Bool) : firstBit y = y ⟨0, hn⟩ := by
+  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
+  rw [firstBit_eq, List.ofFn_succ, List.headD_cons]
+  rfl
+
+/-- Flipping the first bit negates it: `firstBit (flip0 hn y) = !firstBit y`. -/
+theorem firstBit_flip0 (y : Fin n → Bool) : firstBit (flip0 hn y) = !firstBit y := by
+  rw [firstBit_of_pos hn, firstBit_of_pos hn, flip0_eq, Function.update_self]
+
+/-- **Flipping the first bit of a function's value at `x`:**
+`flipAt hn x R = update R x (flip0 hn (R x))`. -/
+def flipAt (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
+    (Fin n → Bool) → (Fin n → Bool) :=
+  Function.update R x (flip0 hn (R x))
+
+/-- `flipAt hn x R = Function.update R x (flip0 hn (R x))`. -/
+theorem flipAt_eq (x : Fin n → Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
+    flipAt hn x R = Function.update R x (flip0 hn (R x)) := rfl
+
+/-- `flipAt hn x` is an involution: `flipAt hn x (flipAt hn x R) = R`. -/
+theorem flipAt_involutive (x : Fin n → Bool) : Function.Involutive (flipAt hn x) := by
+  intro R
+  rw [flipAt_eq, flipAt_eq, Function.update_self, flip0_flip0, Function.update_idem,
+    Function.update_eq_self]
+
+include hn in
+/-- **At a fresh point the prediction wins with probability `½`:** if `x` is none of the
+examples `s`, then for every learner `ℓ` and coins `r`, the uniform probability over `R` that
+`ℓ (label (firstBit ∘ R) s) r x == firstBit (R x)` is `½`.
+
+**Proof sketch.** `flipAt hn x` is a bijection of the functions (`flipAt_involutive`), so it
+preserves the probability (`uprob_comp_equiv`). It keeps the labels of the examples
+(`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`), so it maps the event to
+its complement; hence `p = 1 − p` (`uprob_not`). -/
+theorem uprob_flip_half {m : ℕ} {ρ : Type*}
+    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) (s : Fin m → Fin n → Bool)
+    (r : ρ) (x : Fin n → Bool) (hx : ∀ j, s j ≠ x) :
+    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
+      (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true) = 1 / 2 := by
+  set σ := Function.Involutive.toPerm (flipAt hn x) (flipAt_involutive hn x) with hσ
+  have h1 := uprob_comp_equiv σ (fun R =>
+    (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true)
+  have h2 : (fun R : (Fin n → Bool) → (Fin n → Bool) =>
+      (ℓ (label (fun z => firstBit (σ R z)) s) r x ==
+        firstBit (σ R x)) = true) =
+      fun R => ¬ (ℓ (label (fun z => firstBit (R z)) s) r x == firstBit (R x)) = true := by
+    funext R
+    have hl : label (fun z => firstBit (σ R z)) s =
+        label (fun z => firstBit (R z)) s := by
+      funext j
+      rw [label_apply, label_apply, hσ, Function.Involutive.coe_toPerm, flipAt_eq,
+        Function.update_of_ne (hx j)]
+    rw [hl, hσ, Function.Involutive.coe_toPerm, flipAt_eq, Function.update_self, firstBit_flip0]
+    cases ℓ (label (fun z => firstBit (R z)) s) r x <;> cases firstBit (R x) <;> decide
+  rw [h2, uprob_not] at h1
+  linarith
+
+/-- **A uniform point hits a given point with probability `2^{-n}`:**
+`uprob (fun x : {0,1}^n => y = x) = 1 / 2^n`.
+
+**Proof sketch.** This is `OneWay.uprob_eq_one_div_card` with the equation reversed and
+`|{0,1}^n| = 2^n`. -/
+theorem uprob_eq_point (y : Fin n → Bool) :
+    uprob (fun x : Fin n → Bool => y = x) = 1 / 2 ^ n := by
+  rw [show (fun x : Fin n → Bool => y = x) = (fun x => x = y) from
+      funext fun _ => propext eq_comm, OneWay.uprob_eq_one_div_card, Fintype.card_fun,
+    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_two]
+
+include hn in
+/-- **With a random function the prediction is within `m/2^n` of `½`** [PS10, Theorem 179.1,
+proof, step 2]: for `n ≥ 1`, every learner `ℓ` and `m` examples,
+`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`.
+
+**Proof sketch.** Put the function last (`uprob_comp_equiv`) and average over it first
+(`uprob_prod`): for fixed `((s, r), x)` the probability `p` is `½` when `x` is fresh
+(`uprob_flip_half`) and in `[0, 1]` otherwise, so `|p − ½| ≤ [x ∈ s]`. Averaging (the
+coupling bound `MultiMsg.abs_uexp_sub_le_uprob` against the constant `½`),
+`|gameProb − ½| ≤ Pr[∃ j, s_j = x]`, which the union bound (`uprob_exists_le`) bounds by
+`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`). -/
+theorem abs_gameProb_random_sub_half_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (m : ℕ)
+    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
+    |gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ - 1 / 2| ≤ m / 2 ^ n := by
+  classical
+  -- the random function last
+  let e : (((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) × ((Fin n → Bool) → (Fin n → Bool)) ≃
+      (((Fin n → Bool) → (Fin n → Bool)) × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) :=
+    { toFun := fun w => ((w.2, w.1.1), w.1.2)
+      invFun := fun w => ((w.1.2, w.2), w.1.1)
+      left_inv := fun _ => rfl
+      right_inv := fun _ => rfl }
+  set p : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → ℝ := fun t =>
+    uprob (fun R : (Fin n → Bool) → (Fin n → Bool) =>
+      (ℓ (label (fun z => firstBit (R z)) t.1.1) t.1.2 t.2 == firstBit (R t.2)) = true) with hp
+  have hgame : gameProb m (fun R : (Fin n → Bool) → (Fin n → Bool) => R) ℓ = uexp p := by
+    rw [gameProb_eq, ← uprob_comp_equiv e, uprob_prod]
+    rfl
+  -- the bad event: the fresh point is an example
+  set bad : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) → Prop :=
+    fun t => ∃ j ∈ (Finset.univ : Finset (Fin m)), t.1.1 j = t.2 with hbad
+  -- the coupling bound against the constant `½`: off the bad event, `p = ½`
+  have hdev : |uexp p - 1 / 2| ≤ uprob bad := by
+    have h := MultiMsg.abs_uexp_sub_le_uprob p (fun _ => 1 / 2) bad
+      (fun _ => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun _ => ⟨by norm_num, by norm_num⟩)
+      (fun t hb => uprob_flip_half hn ℓ t.1.1 t.1.2 t.2 fun j hj => hb ⟨j, Finset.mem_univ j, hj⟩)
+    rwa [OneWay.uexp_const] at h
+  -- the union bound
+  have hj : ∀ j : Fin m, uprob (fun t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool) =>
+      t.1.1 j = t.2) = 1 / 2 ^ n := by
+    intro j
+    rw [uprob_prod]
+    simp only [uprob_eq_point, uexp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
+    have : (0 : ℝ) < Fintype.card ((Fin m → Fin n → Bool) × ρ) := by
+      exact_mod_cast Fintype.card_pos
+    field_simp
+  have hunion := uprob_exists_le (Finset.univ : Finset (Fin m))
+    (fun j (t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) => t.1.1 j = t.2)
+  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
+  rw [hgame]
+  refine hdev.trans (hunion.trans (le_of_eq ?_))
+  ring
+
+end Random
+
+end TCSlib.Cryptography.Randomness.LearnPRF
diff --git a/TCSlib/Cryptography/Randomness/Learning/Sample.lean b/TCSlib/Cryptography/Randomness/Learning/Sample.lean
new file mode 100644
index 000000000..0cb257b08
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Learning/Sample.lean
@@ -0,0 +1,275 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
+import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The learner's input, computed from the distinguisher's encoded tuple
+
+The distinguisher of [PS10, Theorem 179.1, proof] queries its oracle at `m(n) + 1` points
+`ρ_0, …, ρ_m` and receives the encoded tuple of the pairs `(ρ_j, g(ρ_j))`: the concatenation
+`tupleWord ρ g` of the blocks `⟨⟨ρ_j, g(ρ_j)⟩, []⟩`, each of `6n + 6` bits (the query chain of
+`MultiMsg.exists_queryChain_nuppt`). It runs the learner on the labelled sample of the first
+`m(n)` points, labelled by the first bits of the answers, and the last point, and compares the
+prediction with the first bit of the last answer.
+
+This file computes, by polynomial-time string functions of `⟨1^n, tupleWord ρ g⟩`:
+- `learnIn m`: the learner's input `⟨S, ρ_m⟩`, where `S` is the nested pairs of the labelled
+  examples `⟨ρ_j, [g(ρ_j)₁]⟩` (the sample encoding of the learning game);
+- `lastLabel m`: the first bit of the last answer.
+
+The labelled sample is a fold of pairs, which is a flat concatenation (`foldr_pairEncode_nil`),
+so it is a block map of the first `m(n)` blocks of the tuple (`MultiMsg.flatMap_range_blocks`).
+
+## Main definitions
+
+* `LearnPRF.firstBit`, `LearnPRF.tupleWord`, `LearnPRF.relabel`, `LearnPRF.sampleLen`,
+  `LearnPRF.learnIn`, `LearnPRF.lastLabel`.
+
+## Main results
+
+* `LearnPRF.foldr_pairEncode_nil`: a fold of pairs ending in `[]` is a concatenation.
+* `LearnPRF.polyTimeComputable_learnIn`, `LearnPRF.polyTimeComputable_lastLabel`.
+* `LearnPRF.learnIn_tupleWord`, `LearnPRF.lastLabel_tupleWord`: their values on an encoded tuple.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §8.1, Theorem 179.1 (book p. 179).
+-/
+
+namespace TCSlib.Cryptography.Randomness.LearnPRF
+
+open Complexity Turing TCSlib.Cryptography
+
+/-! ### Folds of pairs -/
+
+/-- **A fold of pairs ending in `[]` is a concatenation:**
+`L.foldr pairEncode [] = L.flatMap (fun a => pairEncode a [])`.
+
+**Proof sketch.** Induction on `L`; `pairEncode a w = pairEncode a [] ++ w`
+(`GGMRed.pairEncode_append_right`). -/
+theorem foldr_pairEncode_nil (L : List (List Bool)) :
+    L.foldr pairEncode [] = L.flatMap fun a => pairEncode a [] := by
+  induction L with
+  | nil => rfl
+  | cons a L ih =>
+    rw [List.foldr_cons, ih, List.flatMap_cons, ← GGMRed.pairEncode_append_right,
+      List.nil_append]
+
+/-! ### Words -/
+
+/-- The first bit of an `n`-bit string, `false` for `n = 0`: `firstBit y = ⟦y⟧.headD false`. -/
+def firstBit {n : ℕ} (y : Fin n → Bool) : Bool := (List.ofFn y).headD false
+
+/-- `firstBit y = (List.ofFn y).headD false`. -/
+theorem firstBit_eq {n : ℕ} (y : Fin n → Bool) : firstBit y = (List.ofFn y).headD false := rfl
+
+/-- **The encoded tuple** of the pairs `(ρ_j, g(ρ_j))`: the concatenation of the blocks
+`⟨⟨ρ_j, g(ρ_j)⟩, []⟩` (as in `MultiMsg.exists_queryChain_nuppt`):
+`tupleWord ρ g = (List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦g (ρ j)⟧⟩, []⟩).flatten`. -/
+def tupleWord {n k : ℕ} (ρ : Fin k → Fin n → Bool) (g : (Fin n → Bool) → (Fin n → Bool)) :
+    List Bool :=
+  (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (g (ρ j)))) []).flatten
+
+/-- `tupleWord ρ g = (List.ofFn fun j => ⟨⟨⟦ρ j⟧, ⟦g (ρ j)⟧⟩, []⟩).flatten`. -/
+theorem tupleWord_eq {n k : ℕ} (ρ : Fin k → Fin n → Bool) (g : (Fin n → Bool) → (Fin n → Bool)) :
+    tupleWord ρ g = (List.ofFn fun j =>
+      pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (g (ρ j)))) []).flatten :=
+  rfl
+
+/-- The block of a pair `(x, y)`: `⟨⟨⟦x⟧, ⟦y⟧⟩, []⟩`. -/
+private def blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
+  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []
+
+/-- A block has `6n + 6 = histBlockLen(n)` bits. -/
+private theorem length_blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
+    (blk p).length = MultiMsg.histBlockLen.eval n := by
+  rw [blk, length_pairEncode, length_pairEncode, List.length_ofFn, List.length_ofFn,
+    List.length_nil, MultiMsg.eval_histBlockLen]
+  omega
+
+/-- **Relabelling a block:** `⟨⟨x, y⟩, []⟩ ↦ ⟨⟨x, [y.headD false]⟩, []⟩`, the encoded labelled
+example of the pair:
+`relabel w = ⟨⟨pairFstD (pairFstD w), [(pairSndD (pairFstD w)).headD false]⟩, []⟩`. -/
+def relabel (w : List Bool) : List Bool :=
+  pairEncode (pairEncode (pairFstD (pairFstD w)) [(pairSndD (pairFstD w)).headD false]) []
+
+/-- `relabel w = ⟨⟨pairFstD (pairFstD w), [(pairSndD (pairFstD w)).headD false]⟩, []⟩`. -/
+theorem relabel_eq (w : List Bool) :
+    relabel w =
+      pairEncode (pairEncode (pairFstD (pairFstD w)) [(pairSndD (pairFstD w)).headD false]) [] :=
+  rfl
+
+/-- Relabelling is polynomial-time: `PolyTimeComputable relabel`, for
+`relabel : List Bool → List Bool`. -/
+theorem polyTimeComputable_relabel : PolyTimeComputable relabel := by
+  have hF := polyTimeComputable_pairFstD
+  have hD := polyTimeComputable_pairSndD
+  exact (((hF.comp hF).pairEncode (polyTimeComputable_headD.comp (hD.comp hF))).pairEncode
+    (polyTimeComputable_const [])).congr fun w => rfl
+
+/-- The relabelled block of `(x, y)` is `⟨⟨⟦x⟧, [firstBit y]⟩, []⟩`. -/
+private theorem relabel_blk {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
+    relabel (blk p) = pairEncode (pairEncode (List.ofFn p.1) [firstBit p.2]) [] := by
+  rw [relabel_eq, blk, pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, firstBit_eq]
+
+/-! ### The learner's input and the last label -/
+
+/-- The length `m(n) · (6n + 6)` of the first `m(n)` blocks:
+`sampleLen m = m · histBlockLen` as a `PolyExpr`. -/
+def sampleLen (m : PolyExpr) : PolyExpr := .mul m MultiMsg.histBlockLen
+
+/-- `(sampleLen m).eval n = m(n) · (6n + 6)`. -/
+theorem sampleLen_eval (m : PolyExpr) (n : ℕ) : (sampleLen m).eval n = m.eval n * (6 * n + 6) := by
+  rw [sampleLen, PolyExpr.eval_mul, MultiMsg.eval_histBlockLen]
+
+/-- The relabelled first `m(|u|)` blocks of `s`, on `⟨u, s⟩`: the block map of `relabel` over
+`s.take (sampleLen m (|u|))` (the function of `Complexity.polyTimeComputable_blockMap`):
+`sampleOf m ⟨u, s⟩ = (range (|s'| / b)).flatMap fun i => relabel ((s'.drop (i * b)).take b)`,
+with `s' = s.take ((sampleLen m).eval |u|)` and `b = histBlockLen.eval |u|`. -/
+def sampleOf (m : PolyExpr) (z : List Bool) : List Bool :=
+  (List.range (((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).length /
+      MultiMsg.histBlockLen.eval (pairFstD z).length)).flatMap fun i =>
+    relabel ((((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).drop
+      (i * MultiMsg.histBlockLen.eval (pairFstD z).length)).take
+        (MultiMsg.histBlockLen.eval (pairFstD z).length))
+
+/-- `sampleOf m z` is the block map of `relabel` over the first `sampleLen m` bits:
+`sampleOf m ⟨u, s⟩ = (range (|s'| / b)).flatMap fun i => relabel ((s'.drop (i * b)).take b)`,
+with `s' = s.take ((sampleLen m).eval |u|)` and `b = histBlockLen.eval |u|`. -/
+theorem sampleOf_eq (m : PolyExpr) (z : List Bool) :
+    sampleOf m z =
+      (List.range (((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).length /
+          MultiMsg.histBlockLen.eval (pairFstD z).length)).flatMap fun i =>
+        relabel ((((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)).drop
+          (i * MultiMsg.histBlockLen.eval (pairFstD z).length)).take
+            (MultiMsg.histBlockLen.eval (pairFstD z).length)) := rfl
+
+/-- The last block's pair `⟨x, y⟩` on `⟨u, s⟩`:
+`lastPair m ⟨u, s⟩ = pairFstD (s.drop ((sampleLen m).eval |u|))`. -/
+def lastPair (m : PolyExpr) (z : List Bool) : List Bool :=
+  pairFstD ((pairSndD z).drop ((sampleLen m).eval (pairFstD z).length))
+
+/-- `lastPair m z = pairFstD ((pairSndD z).drop ((sampleLen m).eval |pairFstD z|))`. -/
+theorem lastPair_eq (m : PolyExpr) (z : List Bool) :
+    lastPair m z = pairFstD ((pairSndD z).drop ((sampleLen m).eval (pairFstD z).length)) := rfl
+
+/-- **The learner's input** on `⟨1^n, s⟩`: `⟨sampleOf m z, x⟩`, the relabelled first `m(n)`
+blocks and the point `x` of the last block: `learnIn m z = ⟨sampleOf m z, pairFstD (lastPair m z)⟩`.
+-/
+def learnIn (m : PolyExpr) (z : List Bool) : List Bool :=
+  pairEncode (sampleOf m z) (pairFstD (lastPair m z))
+
+/-- `learnIn m z = ⟨sampleOf m z, pairFstD (lastPair m z)⟩`. -/
+theorem learnIn_eq (m : PolyExpr) (z : List Bool) :
+    learnIn m z = pairEncode (sampleOf m z) (pairFstD (lastPair m z)) := rfl
+
+/-- **The last label** on `⟨1^n, s⟩`: the first bit of the answer of the last block,
+`lastLabel m z = (pairSndD (lastPair m z)).headD false`. -/
+def lastLabel (m : PolyExpr) (z : List Bool) : Bool := (pairSndD (lastPair m z)).headD false
+
+/-- `lastLabel m z = (pairSndD (lastPair m z)).headD false`. -/
+theorem lastLabel_eq (m : PolyExpr) (z : List Bool) :
+    lastLabel m z = (pairSndD (lastPair m z)).headD false := rfl
+
+/-- The last block's pair is polynomial-time (`polyTimeComputable_pairDropPoly`):
+`PolyTimeComputable (lastPair m)`, for `lastPair m : List Bool → List Bool`. -/
+theorem polyTimeComputable_lastPair (m : PolyExpr) : PolyTimeComputable (lastPair m) :=
+  (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairDropPoly (sampleLen m))).congr
+    fun _ => rfl
+
+/-- The learner's input is polynomial-time: the block map of `relabel`
+(`Complexity.polyTimeComputable_blockMap`) after the head cut
+(`polyTimeComputable_pairTakePoly`), paired with the last point: `PolyTimeComputable (learnIn m)`,
+for `learnIn m : List Bool → List Bool`. -/
+theorem polyTimeComputable_learnIn (m : PolyExpr) : PolyTimeComputable (learnIn m) := by
+  have hcut : PolyTimeComputable fun z => pairEncode (pairFstD z)
+      ((pairSndD z).take ((sampleLen m).eval (pairFstD z).length)) :=
+    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairTakePoly (sampleLen m))
+  have hS : PolyTimeComputable (sampleOf m) :=
+    ((polyTimeComputable_blockMap MultiMsg.histBlockLen polyTimeComputable_relabel).comp
+      hcut).congr fun z => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, sampleOf_eq]
+  exact (hS.pairEncode (polyTimeComputable_pairFstD.comp (polyTimeComputable_lastPair m))).congr
+    fun _ => rfl
+
+/-- The last label, as a one-bit output, is polynomial-time:
+`PolyTimeComputable fun z => [lastLabel m z]`, for `z ↦ [lastLabel m z] : List Bool → List Bool`. -/
+theorem polyTimeComputable_lastLabel (m : PolyExpr) :
+    PolyTimeComputable fun z => [lastLabel m z] :=
+  (polyTimeComputable_headD.comp (polyTimeComputable_pairSndD.comp
+    (polyTimeComputable_lastPair m))).congr fun _ => rfl
+
+/-! ### Values on an encoded tuple -/
+
+section Values
+
+variable {n : ℕ} (m : PolyExpr) (ρ : Fin (m.eval n + 1) → Fin n → Bool)
+  (g : (Fin n → Bool) → (Fin n → Bool))
+
+/-- The encoded tuple is the first `m(n)` blocks followed by the last block, and the first part
+has `sampleLen m` bits. -/
+private theorem tupleWord_split :
+    tupleWord ρ g =
+      (List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten ++
+        blk (ρ (Fin.last _), g (ρ (Fin.last _))) ∧
+    ((List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten).length =
+      (sampleLen m).eval n := by
+  refine ⟨?_, ?_⟩
+  · rw [tupleWord_eq, List.ofFn_succ', List.concat_eq_append, List.flatten_append,
+      List.flatten_singleton]
+    rfl
+  · rw [MultiMsg.length_flatten_of_length (MultiMsg.histBlockLen.eval n) _ (fun x hx => by
+        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
+        exact length_blk _), List.length_ofFn, sampleLen_eval, MultiMsg.eval_histBlockLen]
+
+/-- **The learner's input on an encoded tuple:** on `⟨1^n, tupleWord ρ g⟩`, `learnIn m` is the
+pair of the nested labelled examples `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points and
+the last point `⟦ρ_m⟧`:
+`learnIn m ⟨1^n, tupleWord ρ g⟩ =
+⟨(ofFn j ↦ ⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩).foldr pairEncode [], ⟦ρ_m⟧⟩` (`j < m(n)`).
+
+**Proof sketch.** Split the tuple into its first `m(n)` blocks and the last
+(`tupleWord_split`); the head cut keeps the first part and the tail cut the last block
+(`List.take_left'`, `List.drop_left'`). The block map over the first part relabels each block
+(`MultiMsg.flatMap_range_blocks`, `MultiMsg.flatMap_ofFn`, `relabel_blk`), and the fold of the
+examples is the same concatenation (`foldr_pairEncode_nil`). -/
+theorem learnIn_tupleWord :
+    learnIn m (pairEncode (List.replicate n true) (tupleWord ρ g)) =
+      pairEncode ((List.ofFn fun j : Fin (m.eval n) => pairEncode (List.ofFn (ρ j.castSucc))
+          [firstBit (g (ρ j.castSucc))]).foldr pairEncode [])
+        (List.ofFn (ρ (Fin.last _))) := by
+  obtain ⟨hsplit, hlen⟩ := tupleWord_split m ρ g
+  have hb : 0 < MultiMsg.histBlockLen.eval n := by rw [MultiMsg.eval_histBlockLen]; omega
+  have hblocks : ∀ x ∈ List.ofFn (fun j : Fin (m.eval n) => (ρ j.castSucc, g (ρ j.castSucc))),
+      (blk x).length = MultiMsg.histBlockLen.eval n := fun x _ => length_blk x
+  have hflat : (List.ofFn fun j : Fin (m.eval n) => blk (ρ j.castSucc, g (ρ j.castSucc))).flatten =
+      (List.ofFn fun j : Fin (m.eval n) => (ρ j.castSucc, g (ρ j.castSucc))).flatMap blk :=
+    (MultiMsg.flatMap_ofFn _ blk).symm
+  rw [learnIn_eq, sampleOf_eq, lastPair_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    List.length_replicate, hsplit, List.take_left' hlen, List.drop_left' hlen, blk,
+    pairFstD_pairEncode, pairFstD_pairEncode, hflat,
+    MultiMsg.flatMap_range_blocks blk relabel hb _ hblocks, foldr_pairEncode_nil,
+    MultiMsg.flatMap_ofFn, MultiMsg.flatMap_ofFn]
+  congr 2
+  exact congrArg List.ofFn (funext fun j => relabel_blk _)
+
+/-- **The last label on an encoded tuple:** on `⟨1^n, tupleWord ρ g⟩`, `lastLabel m` is the first
+bit of the last answer: `lastLabel m ⟨1^n, tupleWord ρ g⟩ = firstBit (g ρ_m)`. -/
+theorem lastLabel_tupleWord :
+    lastLabel m (pairEncode (List.replicate n true) (tupleWord ρ g)) =
+      firstBit (g (ρ (Fin.last _))) := by
+  obtain ⟨hsplit, hlen⟩ := tupleWord_split m ρ g
+  rw [lastLabel_eq, lastPair_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
+    hsplit, List.drop_left' hlen, blk, pairFstD_pairEncode, pairSndD_pairEncode, firstBit_eq]
+
+end Values
+
+end TCSlib.Cryptography.Randomness.LearnPRF

## ===== TCSlib/Cryptography/Randomness/Learning.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Randomness.Learning.Sample
import TCSlib.Cryptography.Randomness.Learning.Distinguisher
import TCSlib.Cryptography.Randomness.Learning.Law
import TCSlib.Cryptography.Randomness.Learning.Random

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom functions make an unlearnable concept class

[PS10, §8.1, Theorem 179.1]: if pseudorandom functions exist, there is a p.p.t.-decidable
concept class that no non-uniform p.p.t. learner can learn: given polynomially many labelled uniform
examples, it predicts the label of a fresh uniform point with probability at most `½` plus a
negligible amount.

**The class.** For a PRF family `{f_k}`, `C_k = {x : f_k(x)₁ = 1}`, the first output bit
(`prfConcept`).

**The learner.** An efficient learner is a machine `A` run at parameter `n` on
`⟨labelled sample, x⟩`. Its hypothesis on `x` is whether it outputs `[true]` (`learnerOf`). The
examples are given non-adaptively, as in the source's question. The prediction game and the PAC
notions are those of the information-theoretic layer `TCSlib.LearningTheory.PAC` (S3d layer 1,
[Shilun-Allan-Li/tcslib#194]), at the uniform distribution on `{0,1}^n` and uniform keys.

## Main definitions

* `Randomness.prfConcept`, `Randomness.encodeSample`, `Randomness.learnerOf`.

## Main results

* `Randomness.prfConcept_decidable` (Thm 179.1, part (a), proved): membership is
  polynomial-time decidable given the key.
* `Randomness.predictAdv_prfConcept_negligible` (Thm 179.1, part (b), proved): every efficient
  learner's prediction advantage is negligible.
* `Randomness.not_weakLearnsUnder_prfConcept` (Thm 179.1, part (c), proved from (b) and the PAC
  layer's bridge): no efficient learner weakly PAC-learns the class under the uniform distribution
  with a constant edge `γ` at fixed failure probability `δ < γ`. Amplifying a KV94-style
  weak learner changes the learner and its resources; that amplification and its resource
  bridge are additional results, not a construction already supplied by part (c).

## Contents

This file states the class, the learner and Theorem 179.1, and assembles the proof of part (b)
from the helper modules under `Learning/` (namespace `Randomness.LearnPRF`):
- `Sample`: the learner's input and the last label as polynomial-time functions of the encoded
  tuple of query points and answers (`learnIn`, `lastLabel`);
- `Distinguisher`: the PRF distinguisher built from a learner (`exists_learnDist`);
- `Law`: the prediction game and the distinguisher's acceptance probability as one uniform
  probability (`predictSuccess_eq_uprob`, `gameProb`, `exists_learnDist_acceptProb`);
- `Random`: with a uniform random function the prediction is within `m/2^n` of `½`
  (`abs_gameProb_random_sub_half_le`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity Turing TCSlib.Cryptography TCSlib.LearningTheory.PAC TCSlib.InformationTheory

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))

/-- **The concept class of Theorem 179.1** at parameter `n`: `C_k(x) = f_k(x)₁`, the first output
bit (`false` at `n = 0`). -/
def prfConcept (n : ℕ) (k x : Fin n → Bool) : Bool := (List.ofFn (F n k x)).headD false

/-- The concept value is the first output bit of `F n k x`, with default `false` for an
empty output: `prfConcept F n k x = (List.ofFn (F n k x)).headD false`. -/
theorem prfConcept_eq (n : ℕ) (k x : Fin n → Bool) :
    prfConcept F n k x = (List.ofFn (F n k x)).headD false := rfl

/-- The encoding of a labelled sample for a learner machine: the nested pairs of `⟨x_j, [b_j]⟩`. -/
def encodeSample {n m : ℕ} (S : Fin m → (Fin n → Bool) × Bool) : List Bool :=
  (List.ofFn fun j => pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []

/-- A labelled sample is encoded by folding its list of pairs `⟨x_j, [b_j]⟩` from the right,
with empty terminal word. -/
theorem encodeSample_eq {n m : ℕ} (S : Fin m → (Fin n → Bool) × Bool) :
    encodeSample S =
      (List.ofFn fun j => pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode [] := rfl

/-- **The learner of a machine** `A` at parameter `n` with `m` examples: on the labelled sample `S`
and coins `r`, the hypothesis `x ↦ [A(1^n, ⟨S, x⟩; r) = [true]]`. -/
def learnerOf (A : NUPPT) (n m : ℕ) :
    (Fin m → (Fin n → Bool) × Bool) → A.Coins n → (Fin n → Bool) → Bool :=
  fun S r x => decide (A.runAt n (pairEncode (encodeSample S) (List.ofFn x)) r = [true])

/-- The learner's prediction on `S`, coins `r` and input `x` is the decision whether the
machine run on `⟨encodeSample S, List.ofFn x⟩` outputs `[true]`. -/
theorem learnerOf_eq (A : NUPPT) (n m : ℕ) (S : Fin m → (Fin n → Bool) × Bool)
    (r : A.Coins n) (x : Fin n → Bool) :
    learnerOf A n m S r x =
      decide (A.runAt n (pairEncode (encodeSample S) (List.ofFn x)) r = [true]) := rfl

/-- **Theorem 179.1 (a): the class is p.p.t.-decidable** given the key: the first bit of the PRF's
evaluator decides membership. -/
theorem prfConcept_decidable (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n (k x : Fin n → Bool), f (pairEncode (List.ofFn k) (List.ofFn x)) = [prfConcept F n k x] :=
  ⟨fun z => [(E z).headD false], polyTimeComputable_headD.comp hE, fun n k x => by
    simp only [prfConcept, hFE]⟩

/-- **Theorem 179.1 (b): no efficient learner predicts the class** [PS10, Theorem 179.1]: if `F` is
a PRF, then for every non-uniform PPT learner `A` and polynomial number `m` of examples, the
prediction advantage `|Pr[A predicts C_k(x)] − ½|` at uniform `k`, uniform examples and a fresh
uniform `x` is negligible.

**Proof sketch** (the source's, made explicit; the delivered proof).
1. **The distinguisher and the real game.** The next-query machine `D` of
   `LearnPRF.exists_learnDist_acceptProb` takes `m(n) + 1` uniform points from its coins, queries
   its oracle at them (the non-adaptive query chain `MultiMsg.exists_queryChain_nuppt`), labels
   the first `m(n)` with the answers' first bits, runs `A` (with its own coins) on the labelled
   sample and the last point, and accepts when `A`'s prediction equals the last answer's first
   bit. Against any keyed family its acceptance probability is a uniform probability over the
   key, the examples, the coins and the fresh point (`LearnPRF.gameProb`); with `f_k` this is
   the prediction game (`LearnPRF.predictSuccess_eq_uprob`), so
   `predictSuccess = acceptProb (F n) D`. The fresh point may equal an example, in both.
2. **The random function.** With a uniform random function `R`, for `n ≥ 1`: when the last point
   is none of the examples, flipping the first bit of `R` there exchanges winning and losing
   functions, so `D` wins with probability exactly `½`; the last point is an example with
   probability at most `m(n)/2^n` (union bound). So `|acceptProb R D − ½| ≤ m(n)/2^n`
   (`LearnPRF.abs_gameProb_random_sub_half_le`).
3. **The bound.** For `n ≥ 1`, `predictAdv ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n`, which is
   negligible by `PRF.negligible_prfAdv` (budget `m + 1`), `EnsembleLemmas.negligible_polyExpr_mul`
   with `negligible_two_pow_neg`, and `Negligible.add`; the eventual bound gives negligibility
   (`Negligible.mono` from `n = 1`, so `n = 0` needs no case). -/
theorem predictAdv_prfConcept_negligible (hF : PRF F) (A : NUPPT) (m : PolyExpr) :
    Negligible fun n => predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) := by
  obtain ⟨B, hB⟩ := LearnPRF.exists_learnDist_acceptProb A m
  -- The owned learner and concept are the helpers' `learnerFn` and `firstBit`.
  have hL : ∀ n, learnerOf A n (m.eval n) = LearnPRF.learnerFn A n (m.eval n) := fun n => by
    funext S r x
    rw [learnerOf_eq, LearnPRF.learnerFn_eq, encodeSample_eq]
  have hC : ∀ n (k : Fin n → Bool), prfConcept F n k = fun x => LearnPRF.firstBit (F n k x) :=
    fun n k => funext fun x => by rw [prfConcept_eq, LearnPRF.firstBit_eq]
  -- Step 1: the prediction game is the distinguisher's game with `f_k`.
  have hreal : ∀ n, predictSuccess (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) =
      acceptProb (F n) (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) := by
    intro n
    rw [hB, LearnPRF.predictSuccess_eq_uprob, LearnPRF.gameProb_eq, hL]
    simp only [hC]
  -- Step 2: with a random function the acceptance probability is within `m(n)/2^n` of `½`.
  have hrand : ∀ n, 0 < n →
      |acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
          (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) - 1 / 2| ≤
        (m.eval n : ℝ) / 2 ^ n := by
    intro n hn
    rw [hB]
    have h := LearnPRF.abs_gameProb_random_sub_half_le hn (m.eval n)
      (LearnPRF.learnerFn A n (m.eval n))
    rwa [show (fun R : (Fin n → Bool) → (Fin n → Bool) => R) =
      randomFunction (Fin n → Bool) (Fin n → Bool) from
        funext fun R => (randomFunction_apply _ _ R).symm] at h
  -- Step 3: the bound, negligible by PRF security and `m(n)/2^n → 0`.
  have hQ : ∀ n, (PolyExpr.add m (.const 1)).eval n = m.eval n + 1 := fun n => by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  have hprf := hF.negligible_prfAdv B (.add m (.const 1))
  simp only [hQ] at hprf
  have hpow : Negligible fun n => (m.eval n : ℝ) / 2 ^ n := by
    refine (EnsembleLemmas.negligible_polyExpr_mul m negligible_two_pow_neg).mono
      ⟨0, fun n _ => le_of_eq ?_⟩
    rw [inv_pow, div_eq_mul_inv]
  refine (hprf.add hpow).mono ⟨1, fun n hn => ?_⟩
  have h₁ := hrand n (by omega)
  have h₂ := prfAdv_nonneg (F n) (B.toOracleAdversary n n n (m.eval n + 1))
  have h₃ : (0 : ℝ) ≤ (m.eval n : ℝ) / 2 ^ n := by positivity
  rw [predictAdv_eq, hreal, abs_abs, abs_of_nonneg (add_nonneg h₂ h₃), prfAdv_def, distAdv_def]
  calc _ ≤ |acceptProb (F n) (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) -
          acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
            (oracleDist (B.toOracleAdversary n n n (m.eval n + 1)))| +
        |acceptProb (randomFunction (Fin n → Bool) (Fin n → Bool))
            (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) - 1 / 2| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- **Theorem 179.1 (c): no efficient weak PAC learner** under the uniform distribution: for edges
`δ < γ ≤ ½`, every efficient learner fails to `(γ, δ)`-weakly learn the class from some
parameter on. Proved from part (b) and the PAC layer's `not_weakLearnsUnder_of_predictAdv_le`.

**Proof sketch.** Part (b) eventually bounds the prediction advantage by `1/n`. Since
`γ - δ > 0`, choose a second cutoff beyond which `1/n ≤ (γ - δ)/2`. Above both cutoffs,
the advantage is strictly smaller than the edge required for weak learning, so the PAC
prediction-to-learning bound rules out a weak learner. -/
theorem not_weakLearnsUnder_prfConcept (hF : PRF F) (A : NUPPT) (m : PolyExpr) {γ δ : ℝ}
    (hδγ : δ < γ) (hγ : γ ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ¬ WeakLearnsUnder (FinDist.uniform (Fin n → Bool)) (prfConcept F n)
      (m.eval n) (learnerOf A n (m.eval n)) γ δ := by
  have hneg := predictAdv_prfConcept_negligible F hF A m
  rw [negligible_iff] at hneg
  obtain ⟨n₁, hn₁⟩ := hneg 1
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (2 / (γ - δ))
  refine ⟨max n₁ (n₂ + 1), fun n hn => ?_⟩
  have h1 := hn₁ n (le_trans (le_max_left _ _) hn)
  have hpos : (0 : ℝ) < γ - δ := by linarith
  have hn' : (n₂ : ℝ) + 1 ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg n₂ : (0 : ℝ) ≤ n₂)]
  have hsmall : 1 / (n : ℝ) ^ 1 ≤ (γ - δ) / 2 := by
    rw [pow_one, div_le_div_iff₀ hnpos (by norm_num)]
    have : 2 / (γ - δ) < n := by linarith
    rw [div_lt_iff₀ hpos] at this
    linarith
  have hadv : predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) ≤ (γ - δ) / 2 :=
    le_trans (le_abs_self _) (le_trans h1.le hsmall)
  exact not_weakLearnsUnder_of_predictAdv_le hadv (by linarith) hγ

end TCSlib.Cryptography.Randomness

## ===== TCSlib/Cryptography/Randomness/Learning/Sample.lean =====

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

## ===== TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.Learning.Sample

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PRF distinguisher built from a learner

Step 1 of [PS10, Theorem 179.1, proof]: from a learner machine `A` and a polynomial number `m` of
examples, a next-query machine `B` that queries its oracle `g` at `m(n) + 1` points `ρ` drawn from
its coins, labels the first `m(n)` by the first bits of the answers, runs `A` (with its own coins)
on the labelled sample and the last point, and accepts when `A`'s prediction (its output being
`[true]`) equals the first bit of the last answer (`exists_learnDist`).

`B` is the query chain of `MultiMsg.exists_queryChain_nuppt` (non-adaptive queries at points
from the coins, the zero message vector) applied to the machine `C` that, on the encoded tuple,
runs `A` on `learnIn m` (`NUPPT.exists_compParam`) and then compares with `lastLabel m`
(`NUPPT.exists_seq` with the uniform machine of `verdictFun`).

## Main definitions

* `LearnPRF.verdictFun`: the comparison of the prediction with the last label.

## Main results

* `LearnPRF.polyTimeComputable_verdictFun`.
* `LearnPRF.exists_learnDist`: the distinguisher and its verdict against every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity Turing TCSlib.Cryptography

/-- **The verdict** on the raw layout whose argument is `⟨w, a⟩` (the encoded tuple `w` and the
learner's output `a`) at parameter `u = 1^n`: `[decide (a = [true]) == lastLabel m ⟨u, w⟩]`. -/
def verdictFun (m : PolyExpr) (z : List Bool) : List Bool :=
  [decide (pairSndD (NUPPT.inArg z) = [true]) ==
    lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))]

/-- `verdictFun m z = [decide (pairSndD (inArg z) = [true]) ==
lastLabel m ⟨inParam z, pairFstD (inArg z)⟩]`. -/
theorem verdictFun_eq (m : PolyExpr) (z : List Bool) :
    verdictFun m z =
      [decide (pairSndD (NUPPT.inArg z) = [true]) ==
        lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))] := rfl

/-- The verdict is polynomial-time: an equality test (`polyTimeComputable_pairEq`) selecting the
last label or its negation (`polyTimeComputable_ite`, `polyTimeComputable_not`,
`polyTimeComputable_lastLabel`): `PolyTimeComputable (verdictFun m)`, for
`verdictFun m : List Bool → List Bool`. -/
theorem polyTimeComputable_verdictFun (m : PolyExpr) : PolyTimeComputable (verdictFun m) := by
  have hArg := NUPPT.polyTimeComputable_inArg
  have hEq : PolyTimeComputable fun z => [decide (pairSndD (NUPPT.inArg z) = [true])] :=
    (polyTimeComputable_pairEq.comp ((polyTimeComputable_pairSndD.comp hArg).pairEncode
      (polyTimeComputable_const [true]))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hL : PolyTimeComputable fun z =>
      [lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))] :=
    (polyTimeComputable_lastLabel m).comp
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_pairFstD.comp hArg))
  refine (polyTimeComputable_ite hEq hL (polyTimeComputable_not hL)).congr fun z => ?_
  rw [verdictFun_eq]
  cases decide (pairSndD (NUPPT.inArg z) = [true]) <;>
    cases lastLabel m (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z))) <;> rfl

/-- The zero message vector leaves the answers unchanged: `(fun _ => false) + y = y`. -/
private theorem zero_add_fun {n : ℕ} (y : Fin n → Bool) : (fun _ => false) + y = y := by
  funext i
  rw [Pi.add_apply]
  cases y i <;> rfl

/-- **The distinguisher of [PS10, Theorem 179.1, proof]:** for a learner machine `A` and a
polynomial `m`, there is a next-query machine `B` whose coins at `n` are, up to a bijection `φ`,
the `m(n) + 1` query points `ρ` and `A`'s coins `c`, and whose query tree with budget `m(n) + 1`,
evaluated against any oracle `g`, is
`decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, where `S` is the nested labelled
examples `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points.

**Proof sketch.** `A₁ := exists_compParam A` with `pre = learnIn m` and `post = pairSndD` runs `A`
on the learner's input; `C := exists_seq A₁ V` with the uniform machine `V` of `verdictFun m`
compares its output with the last label; `B := MultiMsg.exists_queryChain_nuppt C m 0`. Against
`g` the tree of `B` gives `C`'s verdict on the encoded tuple `tupleWord ρ g` (`zero_add_fun`); the
runs of `C`, `A₁` and `V` unfold by their equations (`NUPPT.runAtL_ofPolyTimeUniform`, the layout
readers), the learner's input and the last label are `learnIn_tupleWord` and
`lastLabel_tupleWord`, and `decide ([b] = [true]) = b`. The coins of `C` are those of `A`
(`A.coins + 0`), relabelled by `finCongr` (`ofFn_arrowCongr_finCongr`). -/
theorem exists_learnDist (A : NUPPT) (m : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (m.eval n + 1) → Fin n → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (m.eval n + 1) → Fin n → Bool)
        (c : A.Coins n),
        (B.toOracleAdversary n n n (m.eval n + 1) (φ (ρ, c))).eval g =
          (decide (A.runAt n (pairEncode ((List.ofFn fun j : Fin (m.eval n) =>
              pairEncode (List.ofFn (ρ j.castSucc)) [firstBit (g (ρ j.castSucc))]).foldr
                pairEncode []) (List.ofFn (ρ (Fin.last _)))) c = [true]) ==
            firstBit (g (ρ (Fin.last _)))) := by
  obtain ⟨A₁, hA₁c, -, -, hA₁⟩ :=
    NUPPT.exists_compParam A (polyTimeComputable_learnIn m) polyTimeComputable_pairSndD
  obtain ⟨C, hCc, -, hC⟩ :=
    A₁.exists_seq (NUPPT.ofPolyTimeUniform (polyTimeComputable_verdictFun m) (.const 0))
  obtain ⟨B, hB⟩ := MultiMsg.exists_queryChain_nuppt C m (fun _ _ _ => false)
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hB n
  have hlen : A.coinLen n = C.coinLen n := by
    simp only [NUPPT.coinLen_eq, hCc, hA₁c, NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_add,
      PolyExpr.eval_const, Nat.add_zero]
  have hlen₁ : A₁.coinLen n = A.coinLen n := by simp only [NUPPT.coinLen_eq, hA₁c]
  let ψ : A.Coins n ≃ C.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  refine ⟨((Equiv.refl _).prodCongr ψ).trans φ₀, fun g ρ c => ?_⟩
  have hw : (List.ofFn fun j => pairEncode (pairEncode (List.ofFn (ρ j))
      (List.ofFn ((fun _ _ _ => false : ∀ n, Fin (m.eval n + 1) → Fin n → Bool) n j +
        g (ρ j)))) []).flatten = tupleWord ρ g := by
    rw [tupleWord_eq]
    refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
    rw [zero_add_fun]
  have hc : (List.ofFn c).length ≤ A₁.coinLen n := by rw [List.length_ofFn, hlen₁]
  rw [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, hφ₀, hw,
    NUPPT.runAt_eq, ofFn_arrowCongr_finCongr, hC, List.take_of_length_le hc,
    NUPPT.runAtL_ofPolyTimeUniform, hA₁, pairSndD_pairEncode, verdictFun_eq, NUPPT.inArg_eq,
    NUPPT.inParam_eq]
  simp only [NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [learnIn_tupleWord, lastLabel_tupleWord, ← NUPPT.runAt_eq]
  cases decide (A.runAt n (pairEncode ((List.ofFn fun j : Fin (m.eval n) =>
      pairEncode (List.ofFn (ρ j.castSucc)) [firstBit (g (ρ j.castSucc))]).foldr pairEncode [])
      (List.ofFn (ρ (Fin.last _)))) c = [true]) <;>
    cases firstBit (g (ρ (Fin.last _))) <;> rfl

end TCSlib.Cryptography.Randomness.LearnPRF

## ===== TCSlib/Cryptography/Randomness/Learning/Law.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.Learning.Distinguisher
import TCSlib.Cryptography.Randomness.Extraction.Rejection
import TCSlib.LearningTheory.PAC

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The prediction game as the distinguisher's acceptance probability

Step 1 of [PS10, Theorem 179.1, proof], the law: both the prediction game of the PAC layer and
the acceptance probability of the distinguisher of `exists_learnDist` against a keyed family are
uniform probabilities of one event over the keys, `m` examples, the learner's coins and a fresh
point (`gameProb`).

* **The prediction game** (`predictSuccess_eq_uprob`): its law is a product of uniform laws, the
  uniform law on the product (`iid_uniform`, `Rejection.uniform_prod`), so its success
  probability is the uniform probability of the event (`Rejection.uniform_probTrue`).
* **The distinguisher** (`exists_learnDist_acceptProb`): its coins are, through the bijection of
  `exists_learnDist`, the `m(n) + 1` points and the learner's coins; the points are the examples
  followed by the fresh point (`Fin.snoc`, `snocEquiv`), so for every family `G`,
  `acceptProb G (oracleDist B) = gameProb m G (learnerFn A n m)`.

## Main definitions

* `LearnPRF.gameProb`: the game probability with a family `G` and a learner `ℓ`.
* `LearnPRF.learnerFn`: the learner of a machine, as a function (the learner of the learning
  game, restated here since helper modules do not import the owned file).
* `LearnPRF.snocEquiv`: examples and a fresh point as one tuple.

## Main results

* `LearnPRF.iid_uniform`: independent uniform samples are a uniform tuple.
* `LearnPRF.predictSuccess_eq_uprob`: the prediction game as a uniform probability.
* `LearnPRF.exists_learnDist_acceptProb`: the distinguisher's acceptance probability is the game
  probability of the machine's learner.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness.LearnPRF

open Complexity Turing TCSlib.Cryptography TCSlib.InformationTheory TCSlib.LearningTheory.PAC
  Finset

/-! ### Uniform laws -/

/-- **Independent uniform samples are a uniform tuple:** `(U_X)^m = U_{X^m}`.

**Proof sketch.** Both give every tuple `|X|^{-m}` (`FinDist.iid_apply`, `FinDist.uniform_apply`,
`Fintype.card_fun`, `Finset.prod_const`). -/
theorem iid_uniform {X : Type*} [Fintype X] [Nonempty X] (m : ℕ) :
    (FinDist.uniform X).iid m = FinDist.uniform (Fin m → X) := by
  classical
  apply FinDist.ext
  intro s
  rw [FinDist.iid_apply]
  simp only [FinDist.uniform_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_pow, inv_pow]

/-- **The prediction game as a uniform probability:** `predictSuccess C m L` is the uniform
probability over `((i, (s, r)), x)` of `L (label (C i) s) r x == C i x`.

**Proof sketch.** The law of the game is `(U_I × (U_X^m × U_ρ)) × U_X`, the uniform law on the
product (`iid_uniform`, `Rejection.uniform_prod`); acceptance under a uniform law counts the
accepted points (`Rejection.uniform_probTrue`, `uprob_eq_card_filter`). -/
theorem predictSuccess_eq_uprob {X I ρ : Type*} [Fintype X] [Nonempty X] [Fintype I] [Nonempty I]
    [Fintype ρ] [Nonempty ρ] (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L =
      uprob fun w : (I × ((Fin m → X) × ρ)) × X =>
        (L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2) = true := by
  classical
  rw [predictSuccess_eq, trialDist_eq, iid_uniform, Rejection.uniform_prod,
    Rejection.uniform_prod, Rejection.uniform_prod, Rejection.uniform_probTrue,
    uprob_eq_card_filter, div_eq_mul_inv]

/-! ### The game probability -/

section Game

variable {n : ℕ}

/-- **The game probability** with a family `G : K → {0,1}^n → {0,1}^n` and a learner `ℓ`: the
uniform probability over `((k, (s, r)), x)` that `ℓ`, on the examples `s` labelled by the first
bits of `G k` and the coins `r`, predicts at `x` the first bit of `G k x`. -/
noncomputable def gameProb {K ρ : Type*} [Fintype K] [Fintype ρ] (m : ℕ)
    (G : K → (Fin n → Bool) → (Fin n → Bool))
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) : ℝ :=
  uprob fun w : (K × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) =>
    (ℓ (label (fun x => firstBit (G w.1.1 x)) w.1.2.1) w.1.2.2 w.2 == firstBit (G w.1.1 w.2)) =
      true

/-- `gameProb m G ℓ = uprob (fun ((k, (s, r)), x) =>
(ℓ (label (firstBit ∘ G k) s) r x == firstBit (G k x)) = true)`. -/
theorem gameProb_eq {K ρ : Type*} [Fintype K] [Fintype ρ] (m : ℕ)
    (G : K → (Fin n → Bool) → (Fin n → Bool))
    (ℓ : (Fin m → (Fin n → Bool) × Bool) → ρ → (Fin n → Bool) → Bool) :
    gameProb m G ℓ =
      uprob fun w : (K × ((Fin m → Fin n → Bool) × ρ)) × (Fin n → Bool) =>
        (ℓ (label (fun x => firstBit (G w.1.1 x)) w.1.2.1) w.1.2.2 w.2 ==
          firstBit (G w.1.1 w.2)) = true := rfl

/-- **The learner of a machine** `A` at parameter `n` with `m` examples, as a function: on the
labelled sample `S`, the coins `r` and the point `x`, whether `A(1^n, ⟨S', ⟦x⟧⟩; r) = [true]`,
where `S'` is the nested pairs of the examples `⟨⟦x_j⟧, [b_j]⟩`. -/
def learnerFn (A : NUPPT) (n m : ℕ) :
    (Fin m → (Fin n → Bool) × Bool) → A.Coins n → (Fin n → Bool) → Bool :=
  fun S r x => decide (A.runAt n (pairEncode ((List.ofFn fun j =>
    pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []) (List.ofFn x)) r = [true])

/-- `learnerFn A n m S r x =
decide (A.runAt n ⟨(ofFn j ↦ ⟨⟦(S j).1⟧, [(S j).2]⟩).foldr pairEncode [], ⟦x⟧⟩ r = [true])`. -/
theorem learnerFn_eq (A : NUPPT) (n m : ℕ) (S : Fin m → (Fin n → Bool) × Bool) (r : A.Coins n)
    (x : Fin n → Bool) :
    learnerFn A n m S r x = decide (A.runAt n (pairEncode ((List.ofFn fun j =>
      pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []) (List.ofFn x)) r = [true]) :=
  rfl

/-- **Examples and a fresh point as one tuple:** `((k, (s, r)), x) ↦ (k, (snoc s x, r))`, an
equivalence `(K × ((Fin m → X) × ρ)) × X ≃ K × ((Fin (m + 1) → X) × ρ)`. -/
def snocEquiv (K X ρ : Type*) (m : ℕ) :
    (K × ((Fin m → X) × ρ)) × X ≃ K × ((Fin (m + 1) → X) × ρ) where
  toFun w := (w.1.1, (Fin.snoc w.1.2.1 w.2, w.1.2.2))
  invFun z := ((z.1, (Fin.init z.2.1, z.2.2)), z.2.1 (Fin.last m))
  left_inv w := by
    obtain ⟨⟨k, s, r⟩, x⟩ := w
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv z := by
    obtain ⟨k, t, r⟩ := z
    simp only [Fin.snoc_init_self]

/-- `snocEquiv K X ρ m ((k, (s, r)), x) = (k, (Fin.snoc s x, r))`. -/
theorem snocEquiv_apply (K X ρ : Type*) (m : ℕ) (w : (K × ((Fin m → X) × ρ)) × X) :
    snocEquiv K X ρ m w = (w.1.1, (Fin.snoc w.1.2.1 w.2, w.1.2.2)) := rfl

/-- **The distinguisher's acceptance probability is the game probability** [PS10, Theorem 179.1,
proof, step 1]: for a learner machine `A` and a polynomial `m` there is a next-query machine `B`
such that for every `n` and every family `G : K → {0,1}^n → {0,1}^n` (uniform keys),
`acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n) + 1)))` is
`gameProb (m n) G (learnerFn A n (m n))`.

**Proof sketch.** `B` is `exists_learnDist A m`. Relabel the seeds `(k, c)` of the acceptance
probability by `((k, (s, r)), x) ↦ (k, φ (snoc s x, r))` (`uprob_comp_equiv`, `snocEquiv`,
`Equiv.prodCongr`); the verdict of `B` at `φ (snoc s x, r)` against `G k` is the learner's
prediction on the examples `s` labelled by `firstBit ∘ G k` compared with `firstBit (G k x)`
(`exists_learnDist`, `Fin.snoc_castSucc`, `Fin.snoc_last`, `label_apply`). -/
theorem exists_learnDist_acceptProb (A : NUPPT) (m : PolyExpr) :
    ∃ B : NUPPT, ∀ (n : ℕ) {K : Type*} [Fintype K] (G : K → (Fin n → Bool) → (Fin n → Bool)),
      acceptProb G (oracleDist (B.toOracleAdversary n n n (m.eval n + 1))) =
        gameProb (m.eval n) G (learnerFn A n (m.eval n)) := by
  obtain ⟨B, hB⟩ := exists_learnDist A m
  refine ⟨B, fun n K _ G => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  rw [acceptProb_def, gameProb_eq, ← uprob_comp_equiv ((snocEquiv K (Fin n → Bool) (A.Coins n)
    (m.eval n)).trans ((Equiv.refl K).prodCongr φ))]
  congr 1
  funext w
  have hlab : ∀ (c : (Fin n → Bool) → Bool) (s : Fin (m.eval n) → Fin n → Bool),
      label c s = fun j => (s j, c (s j)) := fun c s => funext (label_apply c s)
  rw [Equiv.trans_apply, snocEquiv_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_apply, oracleDist_apply, hφ, learnerFn_eq, Fin.snoc_last, hlab]
  simp only [Fin.snoc_castSucc]

end Game

end TCSlib.Cryptography.Randomness.LearnPRF

## ===== TCSlib/Cryptography/Randomness/Learning/Random.lean =====

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
`Σ_j Pr[s_j = x] = m · 2^{-n}` (`uprob_prod`, `uprob_eq_point`). -/
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
    simp only [uprob_eq_point, uexp_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card ((Fin m → Fin n → Bool) × ρ) := by
      exact_mod_cast Fintype.card_pos
    field_simp
  have hunion := uprob_exists_le (Finset.univ : Finset (Fin m))
    (fun j (t : ((Fin m → Fin n → Bool) × ρ) × (Fin n → Bool)) => t.1.1 j = t.2)
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
  rw [hgame]
  refine hdev.trans (hunion.trans (le_of_eq ?_))
  ring

end Random

end TCSlib.Cryptography.Randomness.LearnPRF

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability and coin relabelling for PRF encryption

## Main definitions

The lemmas use the existing uniform expectations and finite oracle adversaries.

## Main results

* `MultiMsg.abs_uexp_sub_le_uprob` bounds the difference of two expectations by the
  probability of the event on which the functions can disagree.
* `MultiMsg.card_filter_lt_pairs` counts the pairs of distinct query indices in increasing order.
* `MultiMsg.negligible_choose_div_two_pow` proves negligibility of the collision term.
* `MultiMsg.prfAdv_congr_equiv` transports the PRF advantage along a bijection of coins
  when the two adversaries agree on every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Probability: coupling, pair counting, the collision term -/

/-- The absolute value of an average is at most the average of the absolute values. -/
theorem abs_uexp_le_uexp_abs {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    |uexp f| ≤ uexp fun ω => |f ω| := by
  rw [uexp_def, uexp_def]
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- **The coupling bound**: two `[0,1]`-valued functions on a finite sample space that agree
outside the event `E` have averages at most `Pr[E]` apart (the "two experiments that agree
on an event `E` have advantage `≤ Pr[¬E]`" step of [PS10, Theorem 99.2, proof, `H²` vs `H³`]).

**Proof sketch.** `|E a − E b| = |E (a − b)| ≤ E |a − b|` (`abs_uexp_le_uexp_abs`), and
pointwise `|a − b| ≤ [E]` since the difference vanishes off `E` and is at most `1` on it. -/
theorem abs_uexp_sub_le_uprob {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E] (ha : ∀ ω, 0 ≤ a ω ∧ a ω ≤ 1) (hb : ∀ ω, 0 ≤ b ω ∧ b ω ≤ 1)
    (heq : ∀ ω, ¬ E ω → a ω = b ω) :
    |uexp a - uexp b| ≤ uprob E := by
  rw [← HardcoreBit.uexp_sub, uprob_eq_uexp]
  refine (abs_uexp_le_uexp_abs _).trans (HardcoreBit.uexp_mono fun ω => ?_)
  by_cases hE : E ω
  · rw [if_pos hE]
    obtain ⟨h1, h2⟩ := ha ω
    obtain ⟨h3, h4⟩ := hb ω
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · rw [if_neg hE, heq ω hE, sub_self, abs_zero]

/-- **Counting the pairs `i < j`**: there are `C(k, 2)` pairs `(i, j)` with `i < j` in
`Fin k × Fin k` (the `C(q(n)+1, 2)` of the birthday bound of [PS10, Theorem 99.2]).

**Proof sketch.** The pairs `i < j` and their swaps partition the off-diagonal of
`Fin k × Fin k`, which has `k² − k` elements (`Finset.offDiag_card`); the swap is injective,
so `2 · #{i < j} = k(k − 1)` and `Nat.choose_two_right` finishes. -/
theorem card_filter_lt_pairs (k : ℕ) :
    ((univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2).card = k.choose 2 := by
  set S := (univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2 with hS
  have hunion : S ∪ S.image Prod.swap = (univ : Finset (Fin k)).offDiag := by
    ext ⟨i, j⟩
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_offDiag, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨a, b, hab, rfl, rfl⟩)
      · exact ne_of_lt h
      · exact ne_of_gt hab
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, i, h, rfl, rfl⟩
  have hdisj : Disjoint S (S.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hij hji
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hji
    obtain ⟨a, b, hab, rfl, rfl⟩ := hji
    exact absurd hij (not_lt.2 hab.le)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Prod.swap_injective,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  omega

/-- Two independent uniform elements of a nonempty finite type coincide with probability
`1 / |α|` (Fubini and `OneWay.uprob_eq_one_div_card`). -/
theorem uprob_eq_pair {α : Type*} [Fintype α] [Nonempty α] :
    uprob (fun z : α × α => z.1 = z.2) = 1 / Fintype.card α := by
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : α => a = b) = 1 / Fintype.card α := by
    intro a
    rw [← OneWay.uprob_eq_one_div_card a]
    exact uprob_congr fun b => eq_comm
  simp_rw [h]
  exact HardcoreBit.uexp_const _

/-- **The collision term is negligible**: `n ↦ C(q(n)+1, 2) / 2^n` is negligible for every
syntactic polynomial `q` ([PS10, Theorem 99.2, proof: the collision probability is
negligible]).

**Proof sketch.** `C(k, 2) ≤ k²` (`Nat.choose_le_pow`) and `q(n) + 1 ≤ (C+1)(n+1)^c ≤
(C+1) 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), so the term is at most a constant times
`n^{2c} · 2^{−n}`, negligible by `negligible_two_pow_neg`, `Negligible.mul_pow` and
`Negligible.const_mul`; conclude with `Negligible.mono`. -/
theorem negligible_choose_div_two_pow (q : PolyExpr) :
    Negligible fun n => (Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n := by
  obtain ⟨C, c, hC⟩ := q.eval_le
  have hν : Negligible fun n =>
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow (2 * c)).const_mul _
  refine hν.mono ⟨1, fun n hn => ?_⟩
  have hnat : Nat.choose (q.eval n + 1) 2 ≤ ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by
    have h1 : q.eval n + 1 ≤ (C + 1) * (n + 1) ^ c := by
      have := hC n
      have hp : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos n)
      nlinarith
    have h2 : (n + 1) ^ c ≤ (2 * n) ^ c := Nat.pow_le_pow_left (by omega) c
    calc Nat.choose (q.eval n + 1) 2 ≤ (q.eval n + 1) ^ 2 := Nat.choose_le_pow _ _
      _ ≤ ((C + 1) * (2 * n) ^ c) ^ 2 :=
          Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left _ h2)) 2
      _ = ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by ring
  have hR : (Nat.choose (q.eval n + 1) 2 : ℝ) ≤
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) := by
    exact_mod_cast hnat
  have hinv : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow]
  calc (Nat.choose (q.eval n + 1) 2 : ℝ) * (2 : ℝ)⁻¹ ^ n
      ≤ ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hR hinv
    _ = _ := by ring

/-! ### Oracle adversaries: coin relabelling -/

/-- Relabelling the coins of an oracle adversary by a bijection preserves its acceptance
probability against every oracle sampler, provided the two trees agree on every oracle. -/
theorem acceptProb_oracleDist_congr_equiv {σ : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype σ] [Fintype ρ]
    [Fintype ρ'] (X : σ → I → O) (A : OracleAdversary ρ I O) (A' : OracleAdversary ρ' I O)
    (φ : ρ' ≃ ρ) (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    acceptProb X (oracleDist A) = acceptProb X (oracleDist A') := by
  simp only [acceptProb_def, oracleDist_apply]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr φ)]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, h]

/-- **Coin relabelling preserves the PRF advantage**: oracle adversaries whose trees agree on
every oracle after a bijective relabelling of the coins have the same `prfAdv`. -/
theorem prfAdv_congr_equiv {K : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype ρ] [Fintype ρ'] (F : K → I → O) (A : OracleAdversary ρ I O)
    (A' : OracleAdversary ρ' I O) (φ : ρ' ≃ ρ)
    (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    prfAdv F A = prfAdv F A' := by
  have hF := acceptProb_oracleDist_congr_equiv F A A' φ h
  have hR := acceptProb_oracleDist_congr_equiv (id : (I → O) → I → O) A A' φ h
  simp only [acceptProb_def, oracleDist_apply, id_eq] at hF hR
  rw [prfAdv_eq, prfAdv_eq, hF, hR]

end TCSlib.Cryptography.MultiMsg

## ===== TCSlib/LearningTheory/PAC/Prediction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The prediction game, and its bridge to PAC learning

[PS10, §8.1] (Def 179.a of the inventory) asks whether a learner, given labelled examples of a
random concept `C_i`, can predict the label of a fresh point. Under the uniform distribution
(the reading under which the source's Theorem 179.1 works) the game is:
`i ← I`, `m` examples `s ← X^m`, coins `r ← ρ`, a fresh point `x ← X`, all uniform and
independent; the learner wins when `L(s labelled by C_i, r)(x) = C_i(x)`.

**The bridge.** The fresh point is independent of the sample, so for fixed `(i, s, r)` the
probability of a correct prediction is `1 − err_U(h, C_i)` for the hypothesis `h = L(s, r)`.
So the prediction success is `1 − E_{i,s,r}[err_U(L(s, r), C_i)]`
(`predictSuccess_eq_one_sub_expectedErr`), with no collision issue between the fresh point and
the sample. A learner that PAC-learns under the uniform distribution with accuracy `ε ≥ 0` and
confidence `δ` has expected error at most `ε + δ`: split the expectation over the accuracy event,
where the error is at most `ε`, and its complement, of probability at most `δ`, where the error is
at most `1`. Hence its prediction success is at least `1 − ε − δ`, and a learner whose prediction
advantage is at most `γ` does not satisfy `WeakLearnsUnder` under the uniform distribution at an
edge `γ'` and confidence `δ` with `γ + δ < γ' ≤ ½` (`not_weakLearnsUnder_of_predictAdv_le`).

**Use in layer 2.** Layer 2 applies this to each efficient learner, turning [PS10, Thm 179.1]
into a statement at a confidence `δ` below the gap `γ' − γ`. A weak learner of
[KV94, §4.1, p. 74] need only succeed with probability `1/q(n, size(c))`, that is, at the
confidence `δ = 1 − 1/q(n, size(c))`. Starting only from that guarantee, the required small `δ`
is obtained by amplification ([KV94, §4.2, pp. 76–77]), unless the learner is already certified
at it; amplification gives a different learner, and layer 2 must account for that learner's
sample count, running time and edge before applying the bridge.
Information-theoretically the class is learnable; the hardness is computational.

**Source notes.** [PS10] leaves the sample distribution and "a new sample" implicit; uniform
and independent is the reading (design note S3d). "Better than `½ + ε`" is the advantage
`|Pr[correct] − ½|`.

## Main definitions

* `PAC.trialDist X I ρ m`: the joint law of the concept index, the examples and the coins.
* `PAC.predictSuccess C m L`, `PAC.predictAdv C m L`: the success probability of the prediction
  game, and its advantage over `½`.
* `PAC.expectedErr C m L`: the expected uniform error of the learner's hypothesis.

## Main results

* `PAC.predictSuccess_eq_one_sub_expectedErr`: **the bridge**, success `= 1 − E[err]`.
* `PAC.expectedErr_le_of_pacLearnsUnder`, `PAC.one_sub_sub_le_predictSuccess`: PAC learning
  under the uniform distribution with accuracy `ε ≥ 0` gives expected error at most `ε + δ` and
  success at least `1 − ε − δ`.
* `PAC.sub_le_predictAdv_of_weakLearnsUnder`, `PAC.not_weakLearnsUnder_of_predictAdv_le`: the
  weak-learning condition at edge `γ' ≤ ½` and confidence `δ` gives advantage at least `γ' − δ`;
  so advantage at most `γ` rules it out when `γ + δ < γ' ≤ ½`.
* `PAC.predictSuccess_coin`: the learner that outputs its coin succeeds with probability exactly
  `½` (non-vacuity).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1 (book p. 179).
* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994, §1.2, §4.1 (p. 74) and §4.2 (pp. 76–77).
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, ch. 3.
-/

namespace TCSlib.LearningTheory.PAC

open TCSlib.InformationTheory Finset

variable {X I ρ : Type*} [Fintype X] [Nonempty X] [Fintype I] [Nonempty I] [Fintype ρ]
  [Nonempty ρ]

/-! ### The game -/

variable (X I ρ) in
/-- The joint law of a trial of the prediction game: a uniform concept index, `m` uniform
independent examples and uniform coins. -/
noncomputable def trialDist (m : ℕ) : FinDist (I × ((Fin m → X) × ρ)) :=
  (FinDist.uniform I).prod (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ))

/-- The trial law is the product of the uniform index, the `m` uniform examples and the uniform
coins. -/
theorem trialDist_eq (m : ℕ) :
    trialDist X I ρ m =
      (FinDist.uniform I).prod (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ)) := rfl

/-- **The prediction game** [PS10, §8.1]: the probability that the learner `L`, given `m`
uniform examples labelled by a uniform concept `C_i` and uniform coins, predicts the label of a
fresh uniform point. [PS10] leaves the sample law and "a new sample" implicit. Here both are
uniform and independent, so the fresh point may coincide with an example. -/
noncomputable def predictSuccess (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
    fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2

/-- The success probability is the probability, over a trial `(i, (s, r)) ← trialDist` and an
independent uniform point `x`, of the event `L(s labelled by C_i, r)(x) = C_i(x)`. -/
theorem predictSuccess_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L = ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
      (fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2) := rfl

/-- The **prediction advantage** `|Pr[correct] − ½|` [PS10, §8.1, proof of Thm 179.1]: "better
than `½ + ε`", read two-sidedly. An upper bound on it bounds the one-sided success. -/
noncomputable def predictAdv (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  |predictSuccess C m L - 1 / 2|

/-- The prediction advantage is `|predictSuccess − ½|`. -/
theorem predictAdv_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictAdv C m L = |predictSuccess C m L - 1 / 2| := rfl

/-- The **expected error** `E_{i,s,r}[err_U(L(s labelled by C_i, r), C_i)]` of the learner's
hypothesis under the uniform distribution. -/
noncomputable def expectedErr (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  (trialDist X I ρ m).expect
    fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)

/-- The expected error is the expectation, over a trial `(i, (s, r)) ← trialDist`, of the
uniform error `err_U(L(s labelled by C_i, r), C_i)`. -/
theorem expectedErr_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    expectedErr C m L = (trialDist X I ρ m).expect
      (fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)) := rfl

/-! ### The bridge -/

/-- **The bridge: prediction success is one minus the expected error.**

**Proof sketch.** Split the fresh point off the trial (`expect_prod`). For a fixed trial with
hypothesis `h`, the correct-prediction indicator is one minus the disagreement indicator, so its
expectation over the uniform fresh point is `1 − err_U(h, C_i)` (`expect_one_sub`); then take the
expectation over the trial. -/
theorem predictSuccess_eq_one_sub_expectedErr (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L = 1 - expectedErr C m L := by
  rw [predictSuccess_eq, FinDist.probTrue_eq_expect, FinDist.expect_prod, expectedErr_eq,
    ← FinDist.expect_one_sub]
  congr 1
  funext t
  dsimp only
  rw [err_eq, FinDist.probTrue_eq_expect, ← FinDist.expect_one_sub]
  congr 1
  funext x
  cases L (label (C t.1) t.2.1) t.2.2 x <;> cases C t.1 x <;> simp

/-- **PAC learning under the uniform distribution bounds the expected error** by `ε + δ`
(for `ε ≥ 0`).

**Proof sketch.** For each concept `C_i`, the error is at most `1`, and at most `ε` except with
probability at most `δ` (the hypothesis `PACLearnsUnder`), so its expectation over the examples
and coins is at most `ε + δ` (`expect_le_add_of_le_one`, `probTrue_not`); average over `i`. -/
theorem expectedErr_le_of_pacLearnsUnder {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {ε δ : ℝ}
    (h : PACLearnsUnder (FinDist.uniform X) C m L ε δ) (hε : 0 ≤ ε) :
    expectedErr C m L ≤ ε + δ := by
  rw [expectedErr_eq, trialDist_eq, FinDist.expect_prod]
  calc _ ≤ (FinDist.uniform I).expect (fun _ => ε + δ) := FinDist.expect_le_expect _ fun i => ?_
    _ = ε + δ := FinDist.expect_const _ _
  dsimp only
  have h1 := FinDist.expect_le_add_of_le_one (((FinDist.uniform X).iid m).prod
    (FinDist.uniform ρ)) (f := fun b => err (FinDist.uniform X) (L (label (C i) b.1) b.2) (C i))
    (fun b => err_le_one _ _ _) hε
  have h2 := (pacLearnsUnder_iff (FinDist.uniform X) C m L ε δ).mp h i
  rw [accuracyProb_eq] at h2
  have h3 := FinDist.probTrue_not (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ))
    (fun b => decide (err (FinDist.uniform X) (L (label (C i) b.1) b.2) (C i) ≤ ε))
  dsimp only at h1 h2 h3
  linarith

/-- **PAC learning under the uniform distribution gives prediction success at least
`1 − ε − δ`** (for `ε ≥ 0`): the bridge and `expectedErr_le_of_pacLearnsUnder`. -/
theorem one_sub_sub_le_predictSuccess {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {ε δ : ℝ}
    (h : PACLearnsUnder (FinDist.uniform X) C m L ε δ) (hε : 0 ≤ ε) :
    1 - ε - δ ≤ predictSuccess C m L := by
  rw [predictSuccess_eq_one_sub_expectedErr]
  linarith [expectedErr_le_of_pacLearnsUnder h hε]

/-- **Weak learning under the uniform distribution gives prediction advantage at least
`γ − δ`** (for `γ ≤ ½`): success is at least `1 − (½ − γ) − δ = ½ + γ − δ`. -/
theorem sub_le_predictAdv_of_weakLearnsUnder {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {γ δ : ℝ}
    (h : WeakLearnsUnder (FinDist.uniform X) C m L γ δ) (hγ : γ ≤ 1 / 2) :
    γ - δ ≤ predictAdv C m L := by
  have hs := one_sub_sub_le_predictSuccess ((weakLearnsUnder_iff _ _ _ _ _ _).1 h)
    (by linarith)
  rw [predictAdv_eq]
  exact le_trans (by linarith) (le_abs_self _)

/-- **Small prediction advantage rules out the weak-learning condition below the gap**: if the
learner's prediction advantage is at most `γ`, it does not satisfy `WeakLearnsUnder` under the
uniform distribution at any edge `γ' ≤ ½` and confidence `δ` with `γ + δ < γ'`. The confidence
must be below the gap: at a constant confidence such as `δ = ½`, a learner with zero prediction
advantage can satisfy `WeakLearnsUnder`.

A weak learner of [KV94, §4.1, p. 74] need only succeed with probability `1/q(n, size(c))`, that
is, at the confidence `δ = 1 − 1/q(n, size(c))`, which in general is not below the gap. Starting
only from that guarantee, the small `δ` this lemma needs is obtained by confidence amplification
([KV94, §4.2, pp. 76–77]), unless the learner is already certified at it; amplification gives a
different learner, with its own sample count, running time and edge. It is the certified edge
`γ'`, sample count `m` and prediction advantage `γ` of the learner actually used that enter
here. -/
theorem not_weakLearnsUnder_of_predictAdv_le {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {γ γ' δ : ℝ} (hadv : predictAdv C m L ≤ γ)
    (hlt : γ + δ < γ') (hγ' : γ' ≤ 1 / 2) :
    ¬ WeakLearnsUnder (FinDist.uniform X) C m L γ' δ := fun h => by
  have := sub_le_predictAdv_of_weakLearnsUnder h hγ'
  linarith

/-! ### Non-vacuity -/

omit [Nonempty X] [Fintype I] [Nonempty I] in
/-- Against any target, the two constant hypotheses have errors summing to one, so a fair coin
between them has expected error `½`. -/
theorem expect_err_coin (D : FinDist X) (c : X → Bool) :
    (FinDist.uniform Bool).expect (fun r => err D (fun _ => r) c) = 1 / 2 := by
  have hnot : err D (fun _ => true) c = 1 - err D (fun _ => false) c := by
    simpa using err_not D (fun _ => false) c
  rw [FinDist.expect_eq, Fintype.sum_bool]
  simp only [FinDist.uniform_apply, Fintype.card_bool]
  rw [hnot]
  push_cast
  ring

/-- **The coin-flipping learner predicts with probability exactly `½`** (non-vacuity of the
game): the learner that ignores its examples and outputs its coin.

**Proof sketch.** By the bridge, the success is one minus the expected error; for every concept
and every sample, the error averaged over the coin is `½` (`expect_err_coin`). -/
theorem predictSuccess_coin (C : I → X → Bool) (m : ℕ) :
    predictSuccess C m (fun (_ : Fin m → X × Bool) (r : Bool) (_ : X) => r) = 1 / 2 := by
  rw [predictSuccess_eq_one_sub_expectedErr, expectedErr_eq, trialDist_eq, FinDist.expect_prod]
  dsimp only
  have hin : ∀ i, (((FinDist.uniform X).iid m).prod (FinDist.uniform Bool)).expect
      (fun b => err (FinDist.uniform X) (fun _ => b.2) (C i)) = 1 / 2 := by
    intro i
    rw [FinDist.expect_prod]
    dsimp only
    simp only [expect_err_coin]
    exact FinDist.expect_const _ _
  simp only [hin, FinDist.expect_const]
  norm_num

end TCSlib.LearningTheory.PAC
