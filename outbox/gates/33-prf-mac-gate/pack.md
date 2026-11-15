# Gate 33 · The PRF MAC is secure (`prf-mac`, Theorem 135.4)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #317](https://github.com/Shilun-Allan-Li/tcslib/pull/317) at
  `590d1a56a350d9e8e75ee33d31e0501182169f67` (branch `land/pass-shelat-prf-mac`, tree
  `af0609aebea492170df6d2f254ce0e7885a598d1`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `e99987221593020b9f7dbb87fe577bd6aac5ecbb` (the merge base; the records tip when the PR was opened).
  - The fill was issued on `107f1e8c218733eac12d6b9bee6fece441271317`. Between the issue base and the PR base four
    PRs merged with Lean changes: #307 (dl-crh), #311 (B1 statement), #312 (derand host) and **#314** (the
    `prfAdv_eq_expect` promotion). Re-checked for this pack from git objects: of their 15 Lean files only #314's
    `Pseudorandom/Functions/Defs.lean` is in the unit's closure at the head (172 modules); it reaches every unit module
    through the PRF layer, and its new `Games.Bridges.Experiments` import adds exactly that module to `Handler`'s
    closure (143 → 144) and nothing to the other five. The LE-reuse build (below) ran on the #314 merge, so it covers
    #314; its two rebases are recorded with `git range-diff` all `=`.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...590d1a56`, which equals `e9998722..590d1a56`
    byte for byte (6 paths, 1289 insertions, 19 deletions).
  - **Open PRs.** `git merge-tree --write-tree` of the head with #313 (`94b31964`), #315 (`fbd37f44`) and #316
    (`c18afbe6`) is clean in each case (`pack-checks/mergetrees.txt`). The unit is downstream of #315's
    `Pseudorandom/Functions/Asymptotic/Defs` and of #316's `Foundations/BitLists`. **Pending merge condition** (not an
    audit item): whichever of #317 and #315 (and of #317 and #316) merges second needs an integration rebuild on the
    merged tip; the maintainer runs that build (question 7).
- **Commits:** 6, all authored and committed by Claude and SSH-signed (`pack-checks/rebase.txt`).
  - The Claude worker's 4 commits (job `prf-mac`), applied with `git am` with the delivered committer data (the
    four worker hashes `9ca4e778`, `93d26bcb`, `5612cab6`, `f176a42c` reproduce only with the environment's signing on;
    review F-05), then rebased three times without conflict, author kept: `34d8e869d95039f814f6ce1f422a5b099996965f`
    (checkpoint 1: the distinguisher), `162edeaa3f23040e94353445e0fbfc55eac469db` (checkpoint 2: forging against a
    random function), `7413caf3c65e9daad07e511e65993ab9ca2997ad` (the bound and Theorem 135.4) and
    `404da63de0429501dd8929cd840f7e2637d5acf2` (a Rule-10 repair). At `404da63d` the 6 files are byte-identical to the
    worker's `src/` (exchange `51ae2c12`; `pack-checks/rebase.txt`).
  - Landing edit **LE-doc** `997dd8caeb8e9dfdde28da4b85f70467fed9c998` (the review's `bd45faec`, rebased; unit diff
    empty): two formula docstrings; docstrings only.
  - Landing edit **LE-reuse** `590d1a56a350d9e8e75ee33d31e0501182169f67` (the head): review finding F-01; proof only.
- **Scope:** a **proof audit**. The job proves the admitted `Authentication.prfMAC_secure` [PS10, Theorem 135.4]: if
  `F` is a PRF with a polynomial-time evaluator `E`, the PRF MAC of Protocol 134.3 (`Gen` samples the key,
  `Tag_k(m) = f_k(m)`, `Ver_k(m, σ)` accepts iff `f_k(m) = σ`) is secure. Its statement (in framework form after the
  F-1 restatement, moved to `Authentication/MAC/FromPRF.lean` by #278) is frozen and quoted in the brief.
- **Brief:** `fills/prf-mac/issued-r1/brief.md` on the records branch (SHA-256 `40f2552d…`; exchange pack `2b9270ad`):
  three checkpoints (the distinguisher; the random function; the bound), the owned file plus the helper directory
  `Authentication/MAC/FromPRF/` only, every other file frozen (`Games/Efficiency.lean` at 982 lines), the binding
  duplication rule with an `## Overlap and reuse` section, Rule 10 with the projection-coercion ruling and seals with
  `PolyExpr.eval` both excluded and sealed, the formula-docstring and sketch rules, the G26-N1 error count, and the
  evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/Authentication/MAC/`; `F/` is `FromPRF/`. The PR touches 6 Lean files: 1 modified
and 5 new (1289 insertions, 19 deletions). Line counts are base → worker head `404da63d` → LE-doc `997dd8ca` → PR head.

| File | Status | Lines |
|---|---|---:|
| `FromPRF.lean` | owned, modified | 147 → 222 → 222 → 222 |
| `F/Handler.lean` | helper, new | 444 → 446 → 446 |
| `F/Reduction.lean` | helper, new | 325 → 326 → 326 |
| `F/Random.lean` | helper, new | 155 → 155 → 155 |
| `F/Game.lean` | helper, new | 99 → 99 → 99 |
| `F/Bound.lean` | helper, new | 183 → 183 → 169 |

The owned file imports the five helpers, so after #305 no facade edit is needed, and none was made.

The proof follows [PS10, Theorem 135.4] and the frozen sketch (REPORT § *The proof*, review § Content; the target's
step list was rewritten to describe the delivered proof):
1. **The scheme, read through its readers** (owned file): `Gen` returns its coins, the key, read at `n` bits through
   `NUPPT.coinsEquivPoly`; `Tag` returns `E ⟨k, m⟩ = f_k(m)` whatever its empty coins; `Ver` accepts iff `f_k(m) = σ`.
2. **The distinguisher** (`Handler`, `Reduction`; checkpoint 1): `D` = T4 ∘ T2(`macHandler q ℓ t`) ∘ companion(`A`)
   with budget `macBudget q = q·1 + 1`. The handler stores each queried message as a block `1 ‖ m`, forwards each
   query, and finalizes with one query at the output message `m*` and the bit `[answer = σ*] ∧ [m* not stored]`.
   `exists_macReduction`: for every `n` and `f`, `𝔼_c[D^f(c) = 1] = 𝔼_r Pr[FnForge f | simulate (fnImpl f).withLog
   (A.toComp … r) ((), [])]`, following `PRFGame.exists_prfReduction` (coin bijections, simulation, composition,
   abstraction along runs of at most `q(n)` queries, the log-length bound, `decide_fnForge`).
3. **With `f_k`** (`Game`): `accept_forgeGame_eq`, `Pr[forgeGame] = 𝔼_rg 𝔼_r Pr[FnForge (g rg) | …]` for a MAC whose
   tag is a deterministic keyed function.
4. **With a random function** (`Random`; checkpoint 2): `expect_fnForge_random_le`, `≤ 2^{-b}` for every forger
   computation with no query bound, by lazy sampling with the table override `ETTGame.ovr`.
5. **The bound** (`Bound`): `exists_forgeGame_le`, `Pr[forge] ≤ prfAdv (F n) (D.toOracleAdversary n n n (q·1 + 1)) +
   2⁻ⁿ` at every `n`; after LE-reuse the PRF advantage is read through the published
   `TCSlib.Cryptography.prfAdv_eq_expect` (#314). The owned file instantiates it, and `ε n := prfAdv … + 2⁻ⁿ` is
   negligible by `PRF.negligible_prfAdv` at budget `macBudget q`, `Negligible.add` and `negligible_two_pow_neg`.

The edge cases are `n = 0` (empty messages and tags, the empty message stored as the block `[1]`; `2⁻⁰ = 1` covers an
unqueried forger, which wins with probability 1), budget `0` (the state stays `macState []`; the final query is the
`+ 1`), repeated queries (stored twice), a forger whose output message was queried (it fails both tests), malformed
and timeout outputs (the same output vector in the reduction and the game, `forgerCodec_timeout`), and the tag
machine's empty coins (`expect_const`).

**Statements:** decls2 from the issue base to the head gives **38 ADDED, 0 CHANGED, 0 REMOVED** (review
`statements/decls2.tsv`; LE-reuse `statements/decls2-vs-997dd8ca.tsv`, empty). All 8 pre-existing declarations of the
owned file have byte-identical headers, the target's included (review `statements/header-bytes.txt`, 9 rows; LE-reuse
`statements/header-bytes-vs-997dd8ca.txt`, 61 rows, 0 different). The LE-reuse frozen check (`frozencheck.py`)
compares all 59 declarations of the 6 files, headers, statement prose and every definition body, against LE-doc: 0
differences, and each of its three one-character controls reports exactly one. Re-checked for this pack from git
objects with `maintainer/tools/decls2.py`'s parser: 38 ADDED and 8 unchanged against both the issue base and the PR
base; 0 rows and 46 unchanged for `997dd8ca..590d1a56` and for `404da63d..997dd8ca`; the owned file's blob is the same
at the issue base and the PR base, and its 8 base headers are identical at the head, in order, with only the target's
docstring changed (`pack-checks/headers.txt`).

## Rulings and records in force

1. **F-01 (Seyoon, 2026-11-15): promote it now.** The review's one major: the local `hadv` in
   `Bound.exists_forgeGame_le` re-proved the public `ETTGame.prfAdv_eq_expect` line for line. The ruling: promote the
   identity to the PRF layer first (#314, Gate 30 CLEAR, merged at `59c2c1fb`; `gates/30-prfadv-promote/
   resolutions-r1.md`), then re-point `hadv` by a proof-only landing edit. That is **LE-reuse**.
2. **DL-44 (duplication ledger, open).** F-01 is paid by #314 and LE-reuse. **F-02** (`decide_fnForge`'s `hw`/`htake`/
   `hdrop` restate list readings of `splitBits`: `take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`,
   `FromDiscreteLog.ofFn_splitBits_fst/_snd`) and **F-03** (`PRFMAC.blocks`/`macState`/`hits_nil_iff`, an undisclosed
   nearest relative of `GGMRed.tblEnc`/`lookup`, a different encoding) are **ruled errata with ledger debt** (review;
   DL-44), deferred to the cleanup. The private `prfAdv_prfReduction` (`OracleFromPRF.lean`, DL-40) also stays.
   **Not a finding:** any item DL-44 lists. (DL-44's "existing copy" cell still reads `PRF.prfAdv_eq_expect (to be
   published)`; the published name is `TCSlib.Cryptography.prfAdv_eq_expect`.)
3. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This is
   `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical; the strict variant is run and its differences
   attributed. **For this unit strict and coe agree in every row** (review `logs/seal-table.txt`: head A 6/6, B 6/6,
   base 1/1 in each variant).
4. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal **A**, which exempts it, is **canonical**; seal B
   is run and reported because the brief asks for both.
5. **The facade-completeness lint fix, #305 (Seyoon's ruling of 2026-11-14).** The baseline is **92 FAIL / 101 WARN**.
   The records tip and the review head give 92 / 101 with identical line sets (review `lint/linediff.txt`, empty);
   LE-reuse gives 92 / 101, the only differing line being `Bound.lean`'s INFO line (183 → 169;
   `lint/linediff-parent-vs-edit.txt`), and no FAIL/WARN difference from the review
   (`linediff-review-bd45faec-vs-edit.txt`, empty).
6. **LE-doc (the maintainer's landing edit): docstrings only.** The two public declarations the review's docaudit
   flagged NO-FORMULA now state their formulas: `PRFMAC.macHandler`'s `simps` fields and the instance
   `Decidable (FnForge f w log)`. Re-checked for this pack from git objects: `404da63d..997dd8ca` touches `Handler` and
   `Reduction` only, and both are identical with doc comments deleted (`pack-checks/lecheck.txt`). Docaudit after:
   39 OK; the one NO-FORMULA row is the frozen target's base prose (F-06).
7. **LE-reuse (the maintainer's landing edit): proof only** (`fills/prf-mac/final-r1/landing-reuse/`, filed with this
   pack; `prf-mac-reuse-evidence.zip`, SHA-256 `203f1b03…`). In `exists_forgeGame_le` the 15-line `hadv` and
   `rw [hreal, hadv]` become `rw [hreal, TCSlib.Cryptography.prfAdv_eq_expect (F n) (D.toOracleAdversary n n n _)]`
   (`K = I = O = {0,1}^n`, `ρ = D.Coins n`, the `_` the budget `(macBudget q).eval n`); step 3 of the docstring sketch
   gains "; this is the published `TCSlib.Cryptography.prfAdv_eq_expect`", a pure insertion. +3/−17, one file, no
   import (`Pseudorandom.Functions.Defs` is already in `Bound`'s closure). Checks: decls2 against `997dd8ca` empty;
   `touched` 1 CHANGED (`exists_forgeGame_le`, proof and sketch), 58 UNCHANGED; header bytes 61/61; frozen check 0
   differences; the 136-module build rc 0; seals A and B, strict and coe, pass for `Bound` with the review's request
   sets (`rule10/seal-rows-vs-review.txt`: 0 rows gone, new or changed); `Bound`'s elaborated terms reference 31
   names instead of 39, the 8 gone being exactly those of the removed re-proof (`term-readers-vs-review.txt`); paired
   controls ALL_OK in both harnesses (4 probes, 25 sealed negatives each); axioms standard; census 97/97 unchanged;
   lint unchanged. Re-checked for this pack: `997dd8ca..590d1a56` touches `Bound.lean` only, in 2 hunks, with its 3
   headers identical, only `exists_forgeGame_le`'s docstring changed and the imports identical
   (`pack-checks/lecheck.txt`).
8. **The landing edits are the maintainer's** (the ext-nosrc, cca2-ett, dl-crh, hash-sign, lamport and learning
   precedents).

## What is frozen

- **The target's statement** (quoted in the brief), the 7 other pre-existing declarations of `FromPRF.lean`
  (`prfTagFun`, `prfVerFun`, their readers and polynomial-time lemmas, `prfMAC` with its `correct` proof and its
  `simps` fields), the statement prose and the global simp attributes.
- **Every file outside** `Authentication/MAC/FromPRF.lean` and `Authentication/MAC/FromPRF/`, in particular
  `Authentication/MAC/Defs.lean` (the game), `Games/Efficiency.lean`, `Games/Forwarding.lean`, the PRF layer and the
  `OracleFromPRF*` and `EncryptThenTag*` files the unit imports.
- **The landing edits:** LE-doc two docstrings; LE-reuse one proof and one docstring insertion.

## Questions for the audit

**1. Correctness against [PS10, Theorem 135.4]**
- Does the proof establish the frozen statement for every PRF `F` with evaluator `E`, every forger `A` and budget `q`,
  with `Pr[forge] ≤ prfAdv(F_n, D^{q·1+1}) + 2⁻ⁿ` at **every** `n`, including `n = 0`, budget `0`, repeated queries, a
  queried output message, malformed and timeout outputs, the empty tag coins and the `+ 1` final query?
- Is `D` a legitimate distinguisher for `PRF.negligible_prfAdv`: a NUPPT next-query machine (T2 for `macHandler`, the
  input-free companion, T4) with budget `macBudget q = q·1 + 1`, whose evaluation against any `f` is the forgery
  experiment with tagging oracle `f` (`exists_macReduction`)? Is the freshness test (`[m* not stored]`, read through
  `NMSim.chunkMap`) exactly `forgeGame`'s?
- Is `accept_forgeGame_eq` right for a deterministic tag with empty coins, and is the owned file's key bijection
  (`NUPPT.coinsEquivPoly`, `finCongr (PolyExpr.eval_var n)`) the one `forgeGame` samples?
- Is the random-function bound `≤ 2^{-b}` right with no query bound (`expect_fnForge_random_le`, lazy sampling by
  table override): a fresh message is no key at the end, so its value is uniform; a queried message is no forgery?
- Does `exists_forgeGame_le` move the widths (`eval_toOracleAdversary_width₂`, two independent widths
  `msgLen(n) = tagLen(n) = n`) and the function space (private `padFunEquiv`) correctly, and does the final step give
  `MAC.Secure` with `ε` negligible?
- Does the rewritten target sketch describe the delivered proof?

**2. Frozen-statement integrity**
- Are the target's header and the other 7 pre-existing declarations byte-identical (review
  `statements/header-bytes.txt`; LE-reuse `statements/header-bytes-vs-997dd8ca.txt` and `statements/frozen/`), with
  only the target's body and sketch, the imports, the title, the Main-results line and `## Contents` changed in the
  owned file? Is decls2 38 ADDED / 0 CHANGED / 0 REMOVED, and is every one of the 38 new declarations in the permitted
  helper directory or the owned file?

**3. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's `## Overlap and reuse` table and **DL-44** (ruling 2)? F-01 is fixed by LE-reuse (re-pointed onto
  the merged `prfAdv_eq_expect`); F-02 and F-03 are ruled errata with ledger debt. **Any further undisclosed duplicate
  of a public lemma is a major.** The recent majors of this class: G23-01, G24-01 (`inputWord_take` re-proving
  `take_ofFn_castLE`), prf-mac F-01 itself, learning (`uprob_eq_point`, an inline coupling bound), G29-01
  (`hj` = `OneWay.uexp_const`) and G29-02 (`firstBit_of_pos` re-proving `LamportFill.headD_drop_ofFn`). Search in
  particular probability and expectation identities (`expect_*`, `uprob_*`, `prob_*`, `acceptProb_*`,
  `prfAdv_*`), simulation and log lemmas (`simulate_*`, `allOutputs_*`, `withLog`), codec and list readings
  (`List.ofFn`/`take`/`drop`/`headD`/`getD`, `splitBits`, `padFin`, `blocks`), and the lazy-sampling chain
  (`ETTGame.ovr*`, `expect_sample_*`).
- Are the disclosed relations accurate and their "why not reused" reasons valid, in particular the disclosed
  re-derivations of private material (`expect_forge_pure_le` vs the private `ETTGame.expect_hitW_le`; the owned file's
  `key`/`hkey` vs the private `prfKeyEq`/`ofFn_prfKeyEq`), and the review's F-04 additions (`NUPPT.
  coinsEquiv_ofPolyTimeUniform(_ofFn)`, `ofFn_arrowCongr_finCongr`, Lamport's deterministic-signer lemmas)? The review's
  independent search is `landing/overlap-review.txt`; the worker's is `worker/evidence/overlap/dupsearch-base.log`.

**4. Rule 10**
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 6 files over
  the full closure, at the base and the head, in both variants (review `logs/seal-table.txt`, `seals*/`, `base-seals*/`;
  requests per file, strict A: owned 2258, `Bound` 2257, `Game` 2251, `Handler` 2023, `Random` 2238, `Reduction` 2227)?
  With **variant A canonical** (rulings 3 and 4), does every file pass, strict and coe?
- Do the paired controls bite (review: 16 probes and 68 sealed negatives on the coe records, rows `padFin`,
  `PolyExpr.eval` (B), `ProbComp.expect`, `InteractiveHandler.rAns`, `NMSim.chunkMap`, `ETTGame.ovr`,
  `MAC.forgerCodec`, `PRFMAC.fnImpl`, `FnForge`, `queried`, `macBudget`, `blocks`, `macHandler`, ALL_OK
  (`logs/ctlcheck.log`); LE-reuse on `Bound`: 25 sealed negatives per harness, ALL_OK strict and coe)? The worker's
  Rule-10 repair (`404da63d`: `ovr [] R` read through `ovr_nil`) is what made `Random` pass; is it a reader, not an
  unfolding?
- Explicit-unfold scan at the review head: 425 items, 319 theorems, 19 owned definitions (same-file only: the handler
  round functions, `blockLen`, `macStLen`, `macBudget`, the base `prfVerFun`), 87 local or unresolved, **0 foreign**
  (`logs/scan2-head.log`, `logs/scan-owned-and-local.txt`). Does any proof read a foreign definition (`MAC.forgeGame`,
  `tagImpl`, `forgerCodec`; `prfAdv`, `oracleDist`, `randomFunction`; `ETTGame.ovr`; `NMSim.chunkMap`; the owned
  file's definitions from a helper; `FinDist` internals) other than through a published reader?

**5. The landing edits**
- **LE-doc (ruling 6):** does each of the two new formulas state what its declaration defines, with arguments in the
  Lean order (review `landing/le-doc-check.txt`; the patch in `landing/`)? Is it docstrings only?
- **LE-reuse (ruling 7):** is it proof only (plus the one docstring insertion)? Is
  `TCSlib.Cryptography.prfAdv_eq_expect (F n) (D.toOracleAdversary n n n _)` a correct instance of the promoted
  lemma, with the budget unified by `rw`, and is the rest of the proof (the comment line and the final `linarith`)
  unchanged? Is the sketch's step 3, which still lists the rewrite chain before naming the published lemma, accurate
  (the G30-01 class)?
- Is carrying the five other files' seals and controls forward from the review sound? Their sources are unchanged
  and their oleans are byte-identical to the review build (`build/vs-prf-mac-r1.txt`); `Handler`'s closure gained
  `Games.Bridges.Experiments` through #314.

**6. The docstring and sketch rules**
- Does every new public declaration's docstring state its formula, with arguments in the Lean order and a `[PS10, …]`
  tag where it comes from the source (review `statements/docaudit.tsv`: 39 OK, 1 NO-FORMULA, the frozen target's base
  prose)? Does every proof of 15 lines or more carry a `**Proof sketch.**` (`statements/sketchaudit.tsv`: 11 theorems,
  0 without), and do the long proofs have step comments? A misstated formula or sketch is a minor.
- Does every new public `def` land with its readers (`_eq`, `_apply`, `_iff` or `simps` fields; lint check 8), and is
  nothing new `@[simp]` (census: no simp lemma, one instance, no abbreviation)?

**7. The merge interaction**
- `git merge-tree --write-tree 590d1a56 <x>` is clean for the tip (`af0609ae`, the head's own tree), #313 `94b31964`
  (`ca0b6432`), #315 `fbd37f44` (`9b02f3f8`) and #316 `c18afbe6` (`c99ebe8b`); no path is shared with any of them
  (`pack-checks/mergetrees.txt`).
- **Downstream** (`pack-checks/downstream.txt`): every unit module has #315's `Pseudorandom/Functions/Asymptotic/Defs`
  and #316's `Foundations/BitLists` in its closure (8 modules of each merged tree are downstream of both a #317 module
  and the other PR's module); no #313 module is in the unit's closure (only root `TCSlib` is downstream of both). Of
  the 136 built modules, 131 have #315's merged source, 135 #316's and 135 #313's (`pack-checks/srcequality.txt`).
- **Pending merge condition (not an audit item).** The combined trees are **not** built. Whichever of #317 and #315,
  and of #317 and #316, merges second needs an integration rebuild of the unit's downstream on the merged tip before
  it merges; the maintainer runs that build. Treat it as a condition on the merge, not as something for this audit to
  establish. What you can raise: a concrete reason a merged tree cannot build, or a name or instance interaction. The
  LE-reuse build already covers #314.

## Known dispositions (not findings)

- **F-04** (review, note): the relative lists of `key`/`hkey` and `accept_forgeGame_eq` were incomplete; erratum (the
  missing relatives are listed in question 3). **F-05** (note): `COMMITS.tsv` hashes reproduce only with the
  environment's deterministic SSH signing (`logs/git-am-integrity*.log`); future briefs record the signing.
  **F-06** (note): the target's frozen first docstring paragraph has no formula, and the base `prfMAC.correct` has no
  proof sketch; both pre-existing and disclosed.
- **The review predates LE-reuse** and says "the landing branch waits for that PR"; LE-reuse's record is
  `fills/prf-mac/final-r1/landing-reuse/` (the review record is not edited). The review's build (67 modules at
  `e211a57c`, Lean identical to `bd45faec`, on `e7fa2605`) and whole-tree check (1246 modules, RESULT OK;
  `landing/tree-check-bd45faec.txt`) are before #311, #312 and #314; the LE-reuse build (136 modules: the downstream of
  the 62 modules changed since `eff2dcd0`, including #314's two files and the 6 unit modules, through root `TCSlib` and
  both `audits/*/Checks`) is at `9a415163` on the #314 merge, and its rebase onto `e9998722` left the Lean, scripts and
  audits trees identical. There is no whole-tree check at the final head; every built module's `source_sha256` equals
  the blob at `590d1a56` (checked for this pack).
- **No explicit-unfold scan at the final head.** The review's scan is at `bd45faec`. LE-reuse's new proof text names
  only the theorem `TCSlib.Cryptography.prfAdv_eq_expect`, and `Bound`'s seals pass with its term readers a subset of
  the review's.
- **The worker's promotion requests** (`finish_of_query_padFin` → `Games/Forwarding.lean`, `forgerCodec_eq_bitCodec` →
  `MAC/Defs.lean`, `allOutputs_simulate_withLog_length` → `Games/Simulate.lean`) and the dedup candidate
  (`eval_toOracleAdversary_width₂`, `PRFGame.eval_toOracleAdversary_width`, `ETTGame.eval_toOracleAdversary_len`) are
  recorded for the deferred cleanup.
- **The two imports outside the supplied closure** (`NonMalleability/Simulation/Generic` by `Handler`, for
  `NMSim.chunkMap`; `EncryptThenTag/Tools` by `Random`, for `ETTGame.ovr`) are disclosed (REPORT § *Imports and
  order*); neither is downstream of a unit module.
- **Admissions:** the issued 20 in 10 modules become 18 at the review head; the two removed are `prfMAC_secure` and
  #307's `dlHash_crh` (base delta). The LE-reuse build's 11 sorry warnings are all in admitted base or base-delta
  modules (`build/summary.txt`).
- **`PROVENANCE.txt` of LE-reuse** notes that the records branch moved during its run through commits it did not make
  (`2d568af5`, `bea53eeb`): those were the first, unpushed Gate 32 staging, since replaced; they touched records only.

## Also check

**Axioms**
- At the head, `prfMAC_secure`, `PRFMAC.exists_forgeGame_le` and `TCSlib.Cryptography.prfAdv_eq_expect` each print
  `[propext, Classical.choice, Quot.sound]` (`landing/axioms-head.txt`). At the base the target also had `sorryAx`.
- Census: 97 stored constants in the 6 files, none outside the standard three, no `sorryAx`; at LE-reuse 97/97 common
  with the review head, 0 added, removed, type-, attribute- or axiom-changed (`axioms/census-*` in
  `reuse-evidence.zip`). Base: the 17 constants of the owned file identical except the target's axioms.

**Sizes and widths:** every file at most 446 lines and every line at most 100 characters (`source-head.json`; review
`logs/sizes-widths.txt`).

**Build:** at `9a415163` (Lean identical to `590d1a56`), the 136 modules have rc 0, 0 errors in both diagnostic forms
(`landing/root-checks.jsonl`, whose last line is the runner's `done` record; `landing/build-summary.txt`). 65 of
them, the five unchanged unit modules among them, have the same source and olean SHA-256 as the review's head build;
`Bound` (this edit) and #314's `EncryptThenTag/Reduction` differ; 69 have no record there
(`build/vs-prf-mac-r1.txt`). The olean tree was restored to the base snapshot afterwards (`tree/snapshot-post.txt` =
`snapshot-pre.txt`).

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS (F-01–F-06).
- **`verification.zip`** (114 entries): every file the review and the LE-reuse record cite, as byte-identical
  originals. Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/prf-mac/final-r1/`, SHA-256 `e8038014…`) and `review-evidence-SHA256SUMS`, its
    manifest: 373 entries, all files, under `prf-mac-r1/` exactly the 372 manifest paths plus that folder's
    `SHA256SUMS` (byte-identical to the manifest); every hash verifies. It covers integrity, the landing and LE-doc,
    the build and the whole-tree check with the restore, decls2, header bytes, `touched`, the docstring and sketch
    audits, the census and axioms, the strict and coe seals at the base and the head, the paired controls, the scan,
    the lint, sizes and the overlap review;
  - `reuse-evidence.zip` (`fills/prf-mac/final-r1/landing-reuse/prf-mac-reuse-evidence.zip`, SHA-256 `203f1b03…`) and
    `reuse-evidence-SHA256SUMS`: 331 entries, all files, exactly the 330 manifest paths plus `SHA256SUMS`
    (byte-identical to the manifest); and `landing-reuse/PROVENANCE.txt`, equal to the ZIP's. It covers LE-reuse's
    patch, the rebases, imports, statements and the frozen check, the 136-module build, axioms and the census, seals
    and controls for `Bound`, lint and the restore;
  - `landing/` (3): the review's extracts `PROVENANCE.txt` and `overlap-review.txt` (byte copies of ZIP entries) and
    the LE-doc patch (the ZIP's `landing/series/0005-…` with the subject `[PATCH]` for `[PATCH 5/5]`);
  - `records/` (14): the issue package `fills/prf-mac/issued-r1/`, the duplication ledger (DL-44), the decision log,
    the #305 record (README and patch) and Gate 30's resolutions, at records
    `be3d8bd262c9778d5de0a5f60cc3508f4823bd83`;
  - `evidence/review/` (29) and `evidence/reuse/` (36): byte copies of the ZIP entries this pack cites;
  - `worker/` (9): byte copies from exchange `51ae2c1215554ccda3dde19d8d72908ea74dd339` (`inbox/fills/prf-mac/`):
    `patches/COMMITS.tsv`, the `git am` check, the duplication search, the final axioms, the lint diff, the owned-file
    and decls2 checks, the sketch and width checks;
  - `pack-checks/` (16): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `51ae2c1215554ccda3dde19d8d72908ea74dd339`, under
  `inbox/fills/prf-mac/`. Its top `SHA256SUMS` lists 693 files and `evidence/SHA256SUMS` 680, all delivered.
- **`landing/`:** byte copies of evidence-ZIP entries.
  - `root-checks.jsonl` (= `reuse-evidence.zip`: `build/results.jsonl`): the 136 modules, rc 0.
  - `build-summary.txt` (= `build/summary.txt`).
  - `axioms-head.txt` (= `axioms/AxiomsHead.log`): the three axiom prints at the head.
  - `tree-check-bd45faec.txt` (= `review-evidence.zip`: `prf-mac-r1/tree/tree-check-head.txt`): the whole-tree check at
    the review head.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `51ae2c12`.
- **`pr-description.md`:** the PR #317 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (6 paths, 1289 insertions, 19 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 6 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 172 files.
- **The bundle** adds, as context at the head: `Authentication/MAC/Defs.lean` (the game and `MAC.Secure`) and
  `Pseudorandom/Functions/Defs.lean` (`prfAdv`, `prfAdv_eq_expect`).

## Findings delivery

Return `gate33-prf-mac-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside DL-44, or necessary evidence that
  cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
