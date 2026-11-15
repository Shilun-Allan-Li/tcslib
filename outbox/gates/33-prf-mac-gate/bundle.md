## ===== briefs/pass-shelat-ch5-8/gates/33-prf-mac/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/33-prf-mac/review.md =====

# prf-mac · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** One finding, F-01, is resolved by Seyoon's ruling: the duplicated lemma is
promoted first, in a separate PR, and prf-mac then re-points to it. The landing branch waits for that PR.

## Delivery and landing branch

**The delivery**
- **Worker and target.** A Claude worker proved `Authentication.prfMAC_secure`, [PS10, Theorem 135.4].
- **Exchange.** The final is at `51ae2c1215554ccda3dde19d8d72908ea74dd339`. Checkpoints were delivered at `f93d8a02` and `22b70519`.
- **Base.** The issue base is `107f1e8c`.

**The landing branch** `land/pass-shelat-prf-mac`
- **Head:** `bd45faecffa420497557dfeba9e2818d7d3cf4a3`, tree `25ad7a637d6c33353df4e463e02e2816e07d2aa2`.
- **Rebase:** it is rebased onto records tip `e7fa2605`. That tip includes #303 and #306–#309. The rebase had no conflict, and the Lean content is unchanged.
- **The worker's 4 commits:** `d8fb2380`, `99929a43`, `0872e5c1` and `fa72acc6` (Rule 10 repair).
- **LE-doc** `bd45faec`: two docstring-only formula fixes, one on `PRFMAC.macHandler`'s `simps` fields and one on the `FnForge` Decidable instance. The code is identical with doc comments blanked.

**Files**
- The owned file `MAC/FromPRF.lean` changes.
- Five helpers are new: `MAC/FromPRF/{Bound,Game,Handler,Random,Reduction}.lean`.
- No other file changes.

**Evidence:** `review-evidence.zip`, SHA-256 `e8038014cc178de78f93f194434f20795b396e1c918fa7d1140e5dd74e49cad5`.
- It has 373 entries, the manifest plus `SHA256SUMS`, and its manifest is `evidence-SHA256SUMS`.
- The overlap searches are in `landing/overlap-review.txt`.

## Checks
- **Integrity**
  - The manifests verify 693/693 and 680/680, with exact paths.
  - The issue package verifies 7/7, and its sources 208/208.
  - `git am` reproduces the 4 worker hashes. This works only with the environment's deterministic SSH commit signature (F-05).
- **Build**
  - 67 modules give rc 0 and 0 errors (both diagnostic forms). They are the 57 changed modules (51 base delta plus the unit's 6) and their downstream, through root `TCSlib` and `audits/pass-shelat/Checks`.
  - The whole-tree check at the head covers 1246 modules: OK.
  - There are no name clashes with #307, #308 or #309.
- **Statements:** decls2 gives 38 ADDED, 0 CHANGED, 0 REMOVED. All headers are byte-identical, the target's included.
- **Axioms:** the target uses only the standard three axioms. So do all 97 stored constants. There is no `@[simp]` and one instance.
- **Rule 10**
  - Seals A and B pass in both the strict and the coe variant: 6/6 at the head, 1/1 at the base.
  - Paired controls: 16 probes, 68 negatives, ALL_OK.
  - The explicit-unfold scan finds 0 foreign definitions.
- **Admissions:** 20 → 18. The two removed are `prfMAC_secure` and `dlHash_crh` (from #307).
- **Lint:** 92/101 at the tip and at the head, with identical lines. Widths are at most 100 characters.
- **Content**
  - The proof gives `Pr[forge] ≤ prfAdv(F_n, D^{q·1+1}) + 2⁻ⁿ` at every `n`.
  - It handles the edge cases: `n = 0`, budget 0, repeated queries, a queried output message, timeouts, and the `+1` final query.
- **Tooling:** the review runner was fixed to count both `error:` and `error(` (G26-N1).

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | major | **Undisclosed duplicate.** The local `hadv` in `Bound.exists_forgeGame_le` re-proves the public `ETTGame.prfAdv_eq_expect` (from #306) line for line. | **Ruling (Seyoon, 2026-11-15): promote it now.** A small PR promotes `prfAdv_eq_expect` to the PRF layer, beside `prfAdv`, and re-derives `ETTGame.prfAdv_eq_expect` from it with a proof-only change that keeps that API. prf-mac then re-points `hadv` to the promoted lemma with a proof-only landing edit. |
| F-02 | minor | **Undisclosed restatement.** `decide_fnForge`'s `hw`, `htake` and `hdrop` restate list readings of `splitBits`. The public relatives are `take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, and, since #307, `FromDiscreteLog.ofFn_splitBits_fst`/`_snd`. | Erratum; ledger DL-44. |
| F-03 | minor | **Undisclosed nearest relative.** The `blocks`/`macState` encoding and `hits_nil_iff` have an undisclosed nearest relative, `GGMRed.tblEnc`/`lookup` (reused by cca2-ett as `tblW`). This is a different encoding, not a restatement. | Erratum; ledger DL-44. |
| F-04 | note | **Incomplete relative lists.** The rows for `key`/`hkey` and for `accept_forgeGame_eq` are incomplete. The missing relatives are `NUPPT.coinsEquiv_ofPolyTimeUniform(_ofFn)`, `ofFn_arrowCongr_finCongr` and Lamport's deterministic-signer lemmas. | Erratum. |
| F-05 | note | `COMMITS.tsv` hashes reproduce only with the environment's deterministic SSH commit signing. | Future briefs must record the signing or require `commit.gpgsign=false`. |
| F-06 | note | Two pre-existing items, both disclosed: the target's frozen first docstring paragraph has no formula, and the base `prfMAC.correct` has no proof sketch. | None. |

## ===== briefs/pass-shelat-ch5-8/gates/33-prf-mac/worker-report.md =====

# Fill `prf-mac` · final · Theorem 135.4 proved

**Worker** Claude. **Unit** `prf-mac` (`Authentication.prfMAC_secure`, [PS10, Theorem 135.4]).
**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` (`cryptography/pass-shelat-ch2-4`), read from the
exchange at `2b9270ad095e993b020cb5e447d5a0043496802a` (inputs: 7/7 files and 208/208 source checksums OK,
`evidence/logs/inputs-check.log`). **Proof branch** `fill/prf-mac` (local), four commits over the base:

| Commit | Content |
|---|---|
| `9ca4e7788c723a435ff3f31c40a9058b2b5bb5cb` | checkpoint 1: the handler and the distinguisher (delivered in exchange `f93d8a02f`) |
| `93d26bcb57fed63152bf80684f1562d31fade057` | checkpoint 2: forging against a random function (delivered in exchange `22b70519b`) |
| `5612cab612125952212c6061ab678aedaff1750a` | final: the game with a deterministic tag, the bound, `prfMAC_secure` |
| `f176a42cda28046762db199a1b82cbf2661c3f5e` | final: a Rule-10 repair found by the seals (see *Rule 10*) |

## Status

| Target | Status |
|---|---|
| `prfMAC_secure` | **proved**; axioms `propext`, `Classical.choice`, `Quot.sound` (`evidence/axioms/axioms-final.log`) |

The statement is unchanged (checked byte for byte, `evidence/final/owned-file-bodies.txt`). The proof gives
the source's bound at **every** `n`, `n = 0` included: for every forger `A` and budget `q` there is a
next-query machine `D` with

`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D.toOracleAdversary n n n (q(n)·1 + 1)) + 2⁻ⁿ`

(`PRFMAC.exists_forgeGame_le`), and `ε n := prfAdv … + 2⁻ⁿ` is negligible by `PRF.negligible_prfAdv`,
`Negligible.add` and `negligible_two_pow_neg`. No statement was weakened and no escalation was needed: the
maintainer's sketch is sound as written.

## Changed and new files

| File | Lines | Change |
|---|---|---|
| `TCSlib/Cryptography/Authentication/MAC/FromPRF.lean` (owned) | 147 → 222 | proof of `prfMAC_secure`; title, `## Main results`, `## Contents`, imports of the five helpers; the sketch describes the delivered proof |
| `…/MAC/FromPRF/Handler.lean` (new) | 444 | the reduction's handler |
| `…/MAC/FromPRF/Reduction.lean` (new) | 325 | the distinguisher (checkpoint 1) |
| `…/MAC/FromPRF/Random.lean` (new) | 155 | the random function (checkpoint 2) |
| `…/MAC/FromPRF/Game.lean` (new) | 99 | the forgery game with a deterministic tag |
| `…/MAC/FromPRF/Bound.lean` (new) | 183 | the bound for a MAC whose tag is a keyed family |

No other file is edited (`Games/Efficiency.lean` untouched). All lines ≤ 100 characters and files ≤ 1000
lines (`evidence/checks/widths-final.txt`).

**Owned-file edits.** Title "The PRF MAC (statement phase)" → "The PRF MAC"; `## Main results` now says
"proved", with the bound; a `## Contents` list of the five helpers (the owned file imports each of them
directly, so the facade lint covers them); the theorem's `**Proof sketch**` is rewritten to the delivered
proof (steps 1–5, naming the lemmas used). The statement prose (first paragraph) and the closing paragraph of
the docstring, the statement, and every other declaration of the file (`prfTagFun`, `prfVerFun` and their
readers, `prfMAC` with its `simps` fields) are byte-identical to the base
(`evidence/final/owned-file-bodies.txt`; `decls2` of the owned file: empty, `evidence/final/decls2-owned.txt`).
The base proof `prfMAC.correct` (23 lines, no sketch, and its unused-simp-argument linter warning) is
untouched; it is the one `MISSING` line of `evidence/checks/sketches-final.txt`.

## The proof

1. **The scheme, read through its readers** (owned file). `Gen` returns its coins (`runAt_coinKey` after
   `prfMAC_gen`, through a `G = …` generalization so that the coin type is not rewritten); the key is the
   coin string read at `n` bits (`NUPPT.coinsEquivPoly`, `finCongr (PolyExpr.eval_var n)`). `Tag` returns
   `E ⟨k, m⟩` whatever its coins (`prfMAC_tag`, `NUPPT.runAt_eq`, `runAtL_ofPolyTimeUniform`,
   `prfTagFun_eq`, `NUPPT.inArg_eq`), which is `f_k(m)` by `hFE`; `Ver` accepts `(m, σ)` iff
   `f_k(m) = σ` (`MAC.accepts_iff`, `prfMAC_ver`, `prfVerFun_eq`, `atParam_eq`). Messages and tags have
   `msgLen(n) = tagLen(n) = n` bits (`prfMAC_msgLen`, `prfMAC_tagLen`, `PolyExpr.eval_var`).
2. **The distinguisher** (`Reduction.lean`, checkpoint 1). `D` = T4 ∘ T2(`macHandler q ℓ t`) ∘
   companion(`A`), budget `macBudget q = q·1 + 1`, and for every `n` and every `f`,
   `𝔼_c[D^f(c) = 1] = 𝔼_r Pr[FnForge f | simulate (fnImpl f).withLog (A.toComp … r) ((), [])]`
   (`exists_macReduction`). The handler stores the queried messages as blocks `1 ‖ m` (zeros after them),
   forwards each query (`macHandler_impl`), and finalizes with one query at the output message `m*` and the
   bit `[answer = σ*] ∧ [no stored block is 1 ‖ m*]` (`macHandler_finish`, freshness read with
   `NMSim.chunkMap`). The proof follows `PRFGame.exists_prfReduction`: coin bijections; evaluation is
   simulation with `fnImpl f` (`simulate_ofComp_pure`); composition (`simulate_comp`); abstraction of the
   composed state to the encoded queried messages along runs of at most `q(n)` queries
   (`simulate_eq_of_abs_bounded`); every final log has at most `q(n)` entries
   (`allOutputs_simulate_withLog_length`); the finalization's list test is `FnForge` (`decide_fnForge`).
3. **With `f_k`** (`Game.lean`). For a MAC whose tag returns `g rg m` whatever its coins and whose verifier
   accepts iff `g rg m = σ`, `Pr[forgeGame] = 𝔼_rg 𝔼_r Pr[FnForge (g rg) | … fnImpl (g rg) …]`
   (`accept_forgeGame_eq`: each tagging call has the law of `fnImpl`, `expect_simulate_congr`; the forger
   codec is the bit codec, `forgerCodec_eq_bitCodec`).
4. **With a random function** (`Random.lean`, checkpoint 2). `𝔼_R Pr[FnForge R | … fnImpl R …] ≤ 2^{-b}` for
   every forger computation, with no query bound (`expect_fnForge_random_le`): `R` is sampled lazily along the
   run with the table override `ETTGame.ovr` (`expect_sample_ovr` at a new query; a repeated query reads the
   table; every key is queried), so at the end a fresh message is no key and `R m` is uniform
   (`expect_sample_coord`, `expect_sample_mem_le`); a queried message is no forgery.
5. **The bound** (`Bound.lean`). `D`'s acceptance against `F_k` is the forgery probability (steps 2–3, the
   widths moved by `eval_toOracleAdversary_width₂`, the key by `expect_sample_equiv`); against a uniform `R`
   it is at most `2⁻ⁿ` (steps 2 and 4, the function space moved by a private `padFunEquiv`); the PRF
   advantage is the gap (`prfAdv_def`, `distAdv_def`, `Bridge.acceptProb_eq`, `Bridge.acceptGame_eq`,
   `oracleDist_apply`), so `Pr[forge] ≤ prfAdv + 2⁻ⁿ` (`exists_forgeGame_le`, generic in the MAC and the
   family; the owned file instantiates it).

**Edge cases.** `n = 0`: messages and tags are empty, the empty message is stored as the 1-bit block `[1]`,
and `2⁻⁰ = 1` covers an unqueried forger, which wins with probability 1. Budget `0`: the state stays
`macState []`; the final query is the `+ 1` of `q·1 + 1`. Repeated queries are stored twice (the freshness
test is unaffected). A forger whose output message was queried fails both `forgeGame`'s test and the
handler's. Malformed and timeout outputs: the reduction and the game read the same output vector (the
codec's `zeroBits` on a timeout, `forgerCodec_timeout`, through `forgerCodec_eq_bitCodec`). The tag
machine's empty coins: the tagging call is averaged over them and is constant (`expect_const`).

## New declarations (namespace `TCSlib.Cryptography.Authentication.PRFMAC`)

* *Handler.lean* — `finish_of_query_padFin`; `blockLen` (+`blockLen_eval`), `macStLen` (+`macStLen_eval`),
  `blocks` (+`blocks_eq`, `blocks_cons`, `length_blocks`); `macHandler` (simps fields `stateLen seedLen
  perCall init advIn outLen finCall`), `macState` (+`macState_eq`), `macHandler_stateLen_eval`,
  `macHandler_init_eq`, `ofFn_macState`, `macHandler_impl`, `macHandler_finish`; private `macRun`,
  `polyTimeComputable_macRun`, `msgOf`, `sigOf`, `hitEmit`, `hitsOf`, `macFin`,
  `polyTimeComputable_macFin`, `hits_nil_iff`.
* *Reduction.lean* — `fnImpl` (+`fnImpl_eq`, `fnImpl_apply`), `FnForge` (+`fnForge_iff`, a `Decidable`
  instance), `queried` (+`queried_eq`, `queried_nil`, `queried_append`, `length_queried`, `mem_queried`),
  `decide_fnForge`, `allOutputs_simulate_withLog_length`, `macBudget` (+`macBudget_eval`),
  `exists_macReduction`.
* *Random.lean* — `expect_fnForge_random_le`; private `expect_forge_pure_le`, `expect_forge_ovr_le`.
* *Game.lean* — `forgerCodec_eq_bitCodec`, `accept_forgeGame_eq`.
* *Bound.lean* — `eval_toOracleAdversary_width₂`, `exists_forgeGame_le`; private `padFunEquiv`.

97 stored constants in the six files (generated ones included). No `@[simp]`. Every public declaration's
docstring begins with its statement and gives its formula, with `[PS10, …]` where it comes from the source;
every proof of 15 lines or more has a `**Proof sketch.**` (`evidence/checks/sketches-final.txt`), and the long
proofs have step comments. Every new public `def` has `_eq`/`_apply`/`_iff` readers or `simps` fields (lint
check 8: no new WARN).

## Overlap and reuse

| New declaration | Nearest relative (path:line at the base) | Relation; why not reused |
|---|---|---|
| `finish_of_query_padFin` | `Games/Efficiency.lean:680` `InteractiveHandler.impl_of_query`; `Games/Forwarding.lean:79` `impl_of_query_padFin`; `Efficiency.lean:799` `finish_of_ret`, `Forwarding.lean:96` `finish_of_ret_padFin` | the finalization analogue of `impl_of_query_padFin` (one outer query, then a return); no finalization-with-query lemma exists. Proof re-follows `impl_of_query`'s published steps. **Promotion request** → `Games/Forwarding.lean`. |
| `macHandler`, its rounds | `Games/Forwarding.lean:130` `fwdHandler` | `fwdHandler` has an empty state; freshness needs the queried messages in the state. |
| `blocks`, `macState`, `hits_nil_iff` | `NonMalleability/Simulation/Generic.lean:78,138` `NMSim.chunkMap`, `chunkMap_flatten` | the chunk map is reused by import; the block encoding is new (the `blocks*` of `Asymptotic/*` and `Complexity/Randomized/RandomBits.lean:262` are `Fin`-vector reshapes, not list encodings). |
| `fnImpl` | `Signatures/Lamport/Planted.lean:256` `tableSigner`; `OracleFromPRF/Reduction.lean:55` `PRFGame.fOuter`; `EncryptThenTag/Reduction.lean:59` | same shape `QueryImpl.ofComp fun _ m => pure (f m)`; the relatives fix a table, or pad to a fixed spec. |
| `FnForge` | `MAC/Defs.lean:149` (`forgeGame`'s win test); `HashAndSign/FixedGame.lean:176` `Success`; `HashAndSign/ForwardGame.lean:252` `OriginalSuccess` | the MAC win test with `f m = σ` in place of `Accepts`; the relatives are for signature schemes. |
| `queried`, `mem_queried` | `HashAndSign/ForwardGame.lean:210` `forward_fresh`; `Lamport/Planted.lean:312` `fresh_firstLog_iff` | freshness readers for other logs; `queried` is the message list the state stores. |
| `decide_fnForge` | `HashAndSign/CodecReaders.lean:95,106` `splitBits_append`, `splitBits_pad_concat`; `Complexity/Randomized/Classes.lean:217` | the same `List.ofFn_fin_append`/`Fin.append_castAdd_natAdd` step, in the other direction (the list reading of a split vector). |
| `allOutputs_simulate_withLog_length` | `Games/Simulate.lean:241` `simulate_withLog`; `OracleFromPRF/Collision.lean:249` (a length bound for `lazyImpl`); `Games/Hopping.lean:179` `simulate_allOutputs_bad` | no published bound on a logged simulation's log; generic statement. Promotion candidate (`Games/Simulate.lean`). |
| `macBudget` | `OracleFromPRF/Reduction.lean:83` `PRFGame.qRed` | the same pattern with `finCall = 1`. |
| `exists_macReduction` | `OracleFromPRF/Reduction.lean:258` `PRFGame.exists_prfReduction` | the same template (companion, T2, T4, abstraction) for another handler and game; reuses `PRFGame.ofFn_evalFn_toCompOn` and `ChallengeSim.expect_sample_prod` by import. |
| `expect_forge_pure_le` (private) | `EncryptThenTag/Forgery.lean:294` `ETTGame.expect_hitW_le` (**private**) | re-derives, from the published `ovr` readers, `expect_sample_coord` and `expect_sample_mem_le`, the fresh-point case of that private lemma (a value of `R` off the table hits a fixed tag with probability `2^{-b}`), for this fill's `FnForge`. **Disclosed re-derivation of a private lemma.** |
| `expect_forge_ovr_le` (private), `expect_fnForge_random_le` | `EncryptThenTag/Forgery.lean:387` `ETTGame.expect_prob_bad_le`; `OracleFromPRF/Lazy.lean`, `EncryptThenTag/Lazy.lean`; `Pseudorandom/Functions/Asymptotic/Defs.lean` `acceptProb_random_eq_lazy` | the same lazy-sampling induction (`expect_sample_ovr` at a new query) for another game (one final guess, no budget). `acceptProb_random_eq_lazy` works on query trees, while T4 only identifies `D`'s evaluations, not its tree; so the table-override induction runs on the forger's computation. |
| `forgerCodec_eq_bitCodec` | `HashAndSign/CodecReaders.lean:72` `SignatureScheme.forgerCodec_eq_bitCodec` | the MAC analogue (same proof through `MachineCodec.ext_of_fields`, reused by import). **Promotion request** → `MAC/Defs.lean`. |
| `accept_forgeGame_eq` | `HashAndSign/ForwardGame.lean:303` `forgeGame_eq_fixed`; `OracleFromPRF.lean:246` `accept_prf_indGame` (private) | the MAC game with a deterministic tag; the relatives are the signature game with a fixed signer and the IND game of the §3.9 scheme. |
| `eval_toOracleAdversary_width₂` | `OracleFromPRF/Reduction.lean:228` `PRFGame.eval_toOracleAdversary_width`; `EncryptThenTag/Machines.lean:348` `ETTGame.eval_toOracleAdversary_len` | generalization to two independent widths `m₁ = n`, `m₂ = n` (the relatives move both widths to one value; here they are the distinct terms `msgLen(n)` and `tagLen(n)`). Dedup candidate: the three could be one lemma. |
| `padFunEquiv` (private) | `Complexity/Randomized/PPT.lean:266` `coinsEquivPoly` (`Equiv.arrowCongr (finCongr _)`) | an equivalence of function spaces read through `padFin`, so that the transported function is syntactically the one `eval_toOracleAdversary_width₂` produces. |
| owned-file `key`, `hkey`, `hgen` (local `let`/`have`s of the proof) | `Encryption/PrivateKey/OracleFromPRF.lean:131,138` `prfKeyEq`, `ofFn_prfKeyEq` (**private**), and its `gen.runAt` lemma above them | the same coin-to-key equivalence and readings for the PRF MAC, re-derived in a few lines from published readers (`NUPPT.coinsEquivPoly`, `coinsEquivPoly_ofFn`, `List.ofFn_congr`, `runAt_coinKey`); those are private to another scheme's file. **Disclosed re-derivation of a private definition and lemma.** |

Imported and reused: T2/T4/the companion, `impl_of_query_padFin`, `NMSim.chunkMap*`,
`Collection.ofFn_padFin_of_le`, `PRFGame.ofFn_evalFn_toCompOn`, `ChallengeSim.expect_sample_prod`,
`MachineCodec.ext_of_fields`, `ETTGame.ovr*`/`expect_sample_ovr`, `simulate_eq_of_abs_bounded`,
`expect_simulate_congr`, `expect_congr_of_allOutputs`, `expect_toCompOn_outLen`, `simulate_ofComp_pure`,
`expect_sample_coord`, `expect_sample_mem_le`, `Bridge.acceptProb_eq`/`acceptGame_eq`,
`PRF.negligible_prfAdv`. Searches: `evidence/overlap/dupsearch-base.log` (script `evidence/tools/dupsearch.sh`,
run on the issue base). Line references here supersede those of the checkpoint reports (two were off by a
few lines there).

## Scope requests

None. No frozen file was edited; the route needed no reader beside a foreign definition.

## Promotion and reader requests

* `PRFMAC.finish_of_query_padFin` → `Games/Forwarding.lean` (beside `finish_of_ret_padFin`).
* `PRFMAC.forgerCodec_eq_bitCodec` → `Authentication/MAC/Defs.lean` (beside the signature analogue's home).
* `PRFMAC.allOutputs_simulate_withLog_length` → `Games/Simulate.lean` (candidate).
* Dedup candidate: `PRFMAC.eval_toOracleAdversary_width₂`, `PRFGame.eval_toOracleAdversary_width`,
  `ETTGame.eval_toOracleAdversary_len`.

## Imports and order

* Two imported modules lie outside the supplied closure, each with its imports inside `order.txt`:
  `Encryption/PublicKey/NonMalleability/Simulation/Generic` (by `Handler`, for `NMSim.chunkMap`) and
  `Encryption/PrivateKey/EncryptThenTag/Tools` (by `Random`, for `ETTGame.ovr`). No new Mathlib import (the
  narrowed roots are unchanged).
* The final order (`evidence/final/order-final.txt`, 215 modules; `evidence/final/reorder.log`) is the
  supplied order with these two and the five helpers inserted before their consumers; this moves the owned
  file from position 139 to 214 (after the PRFGame modules it now imports) and the `Authentication` facade
  from 186 to 215. All other modules keep their relative order.

## Checks

* **Bootstrap** (base, `order.txt`, 208 modules): exit 0 for all, 0 error diagnostics
  (`evidence/logs/bootstrap.tsv`, raw logs `evidence/logs/bootstrap/`, `evidence/logs/bootstrap-errors.txt`).
  The background loop was lost to VM restarts twice and resumed chunk by chunk in the foreground
  (`evidence/logs/bootstrap-run.log`).
* **Owned module recheck, then the sweep** of the final order: 215/215 exit 0, **0 error diagnostics** counted
  with `^\S+\.lean:\d+:\d+: error[:(]` over every log (`evidence/final/sweep-errors.txt`, raw logs
  `evidence/final/sweep/`, `sweep.tsv`, `sweep-run.log`). After the Rule-10 repair commit `Random`,
  `Bound`, the owned file and the `Authentication` facade were checked again (pass 2); the pass-1 rows and
  logs are kept (`sweep-pass1.tsv`, `sweep-pass1-logs/`).
* **Sorry census**: base 20 declarations in 10 modules, equal to `base-sorries.txt`; final 19 in 9; the only
  change is the removal of `prfMAC_secure` (`evidence/final/sorry-census-{base,final,diff}.txt`).
* **Axioms**: `prfMAC_secure`: `[Classical.choice, Quot.sound, propext]`; all 97 stored constants of the six
  changed and new files: within these three (`evidence/axioms/axioms-final.log`; checkpoints:
  `axioms-cp1.log`, `axioms-cp2.log`).
* **Lint** `campaign_style_lint.py TCSlib/Cryptography --check8b`: base 92 FAIL / 101 WARN, final 92 / 101;
  line-set diff: **no new and no removed FAIL or WARN line** (`evidence/lint/lint-{base,final}.txt`,
  `lintdiff-final.txt`; checkpoints likewise).

### Rule 10

**Seals** (`evidence/tools/seals.py`; sources `evidence/scratch-src/seal/`, raw logs and
`results.jsonl` in `evidence/seals/{base,final}/`). For each file, a census module with exactly the file's
imports lists every constant of its TCSlib import closure; the requests are every closure definition that is
a matcher or not reducible (instances, private definitions and generated matchers included; reducible
abbreviations are notation). A: `PolyExpr.eval` exempt; B: sealed. Strict: projection coercions sealed;
coe (canonical): `FinDist.instCoeFunForallReal` exempt. The probe is the file verbatim, with `import Lean`
and a harness after its imports that makes every request `local irreducible` by its exact name, and an
end-of-file harness that verifies every request is still irreducible.

| File | requests (strict-A) | strict-A | strict-B | coe-A | coe-B | base (4 variants) |
|---|---|---|---|---|---|---|
| `MAC/FromPRF.lean` (owned) | 2258 | pass | pass | pass | pass | pass (1384 requests) |
| `MAC/FromPRF/Handler.lean` | 2023 | pass | pass | pass | pass | — (new) |
| `MAC/FromPRF/Reduction.lean` | 2227 | pass | pass | pass | pass | — |
| `MAC/FromPRF/Random.lean` | 2238 | pass | pass | pass | pass | — |
| `MAC/FromPRF/Game.lean` | 2251 | pass | pass | pass | pass | — |
| `MAC/FromPRF/Bound.lean` | 2257 | pass | pass | pass | pass | — |

All 24 final and 4 base probes: exit 0, 0 errors, every harness part installed and verified. **The strict and
coe variants agree everywhere**; their request sets differ by exactly the one coercion instance. **No
failing declaration** in any variant, so there is nothing to attribute between A and B either: no proof of
the fill reads `PolyExpr.eval` by unfolding (the widths are moved with `PolyExpr.eval_var/add/mul/const`).

**One finding, fixed.** The first final seal run (pass 1, `evidence/seals/final-pass1/`) failed in all four
variants in one declaration, `expect_fnForge_random_le`: `simp only [ovr_nil] at h` rewrote `ovr [] R` in the
bound but not in the `Decidable` instance argument of its `if`, and `exact h` then closed the goal by
unfolding `ETTGame.ovr`. Commit `f176a42c` rewrites the goal with `ovr_nil` instead (`rw` reaches the instance
argument); the pass-2 seals above pass.

**Paired controls** (`evidence/controls/`, source `evidence/scratch-src/controls/Controls.lean`, tool
`controls2.py`): unsealed, all examples close. Under each of the four variants (2260–2262 requests), the
sealed negatives `rfl`-reading `InteractiveHandler.rAns`, `PRFMAC.macBudget`, `PRFMAC.fnImpl`,
`MAC.forgerCodec` and `PRFMAC.macHandler`'s `perCall` **fail exactly once each**, and their published
readers close; the `PolyExpr.eval` negative closes under A and fails exactly once under B. A recorded
probe (C6) reads `FinDist`'s coercion through its instance by `rfl`: it closes under every variant, i.e.
sealing that instance does not block this reading in Lean 4.25, so the strict seal of the coercion has no
observable effect here (consistent with the variants agreeing).

**Explicit-unfold scan** (`evidence/final/rwids/rwids.tsv`, `scan-*.log`; tools `rwids.py`, `rwids_run.py`):
every identifier passed to `rw`/`simp`/`unfold`/… in the six files resolves to a theorem, a local
hypothesis, or a definition of the same file (`blockLen`, `macStLen`, `macBudget`, the private round
functions, and the base proof's `prfVerFun`): **no foreign TCSlib definition and no core or Mathlib
definition**.

## Patches and reproduction

`patches/0001…0004-*.patch` (`git format-patch` from the issue base) and `patches/COMMITS.tsv` (hash, author
name/email/date, committer name/email/date). **Checked before pushing:** a scratch clone at the issue base
applies the series with `git am`, the committer of each commit set from `COMMITS.tsv`, and reproduces all
four hashes and the final tree (`evidence/amcheck/amcheck-final.log`; checkpoints: `amcheck-cp1.log`,
`amcheck-cp2.log`).

## Notes

* **Environment.** 4 CPUs, ~15 GiB available memory. The initial free disk (9.7 GiB) was below the 12 GiB
  floor; I removed only my own finished scratch (earlier fills' worktrees and olean tree), leaving 12.9 GiB
  (`evidence/logs/preflight.log`). One Lean process at a time throughout; `python3 -I`; no `lake build`; the
  narrowed `lake exe cache get` only (`evidence/logs/cache-*.log`).
* **Exchange.** While delivering I saw the new `prf-long` brief on the exchange (issue base `7b307d62`, additive
  `ℓ`-generic PRF lemmas, no frozen statement change). This fill stays on its issue base and uses only
  `PRF.negligible_prfAdv`, whose statement that brief keeps.

## Evidence

`evidence/SHA256SUMS` lists every evidence file: the inputs, every raw log (bootstrap, checkpoint and
development compiles, the final sweep, censuses, axioms, seals, controls, scans, lint), the probe, seal,
census and control sources (`evidence/scratch-src/`), and the tools (`evidence/tools/`). The top-level
`SHA256SUMS` lists every delivered file except itself. Both manifests were checked to equal the delivered
paths exactly.

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

## ===== briefs/pass-shelat-ch5-8/fills/prf-mac/issued-r1/brief.md =====

# Claude fill · the PRF MAC is secure (`prfMAC_secure`, Theorem 135.4)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `prf-mac`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `prfMAC_secure` of [PS10, Theorem 135.4] in
`TCSlib/Cryptography/Authentication/MAC/FromPRF.lean`. The statement passed the prong A statement phase and Gate 06 (chapters 5–8 statements),
and is frozen. Its docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated. The machine and PRF interfaces it needs are published (T2, T3, T4, `PRF`, lazy sampling). It depends on no admitted target: the closure's admissions are the machine-library stubs and `dlHash_crh`, none of which is on the route.

**Estimated size:** 1,500–2,500 lines in 3–6 helper modules. For calibration, hash-sign landed 2,247 lines and cca2-ett 5,364.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/prf-mac` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/prf-mac/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/prf-mac/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill prf-mac: checkpoint N` and `fill prf-mac: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, but its closure contains `Candidates/DiscreteLog`, `Hashing/FromDiscreteLog` (through the `Authentication` facade), at their pre-#307 state, with `dlHash_crh` still admitted. If #307 merges during the fill, stay on the issue base; the maintainer rebases at landing.
- The other fills of this batch (`learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Target (frozen; quoted from the issue base)

```lean
theorem prfMAC_secure {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfMAC F E hE hFE).Secure := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. The theorem's arguments are `{F}` (a family `∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`),
`hF : PRF F`, the evaluator `E`, `hE : PolyTimeComputable E` and `hFE` (`E ⟨s, x⟩ = F n s x`).

**The scheme `prfMAC`** (Protocol 134.3, all in the owned file): `msgLen = tagLen = var`. `Gen`'s coins are the key
(`runAt_coinKey`); `Tag` has no coins (`.const 0`) and returns `E ⟨k, m⟩` (`prfTagFun_eq`); `Ver` returns
`[E ⟨k, m⟩ = σ]` (`prfVerFun_eq`). Read the scheme only through those lemmas and the `simps` fields of `prfMAC`
(`msgLen`, `tagLen`, `gen`, `tag`, `ver`).

**The security notion** (`Authentication/MAC/Defs.lean`): `MAC.Secure` (`secure_iff`) bounds `accept (forgeGame A
(q n) n)` by a negligible `ε n` for every forger `A` and budget `q`. `forgeGame_eq` samples the key and the forger's
coins, runs the forger against the logged tagging oracle (`tagImpl_eq`) through `forgerCodec` (`forgerCodec_*`),
and wins when `Accepts` (`accepts_iff`) holds and the output message was never queried.

## Published interfaces

| Interface | Provider |
|---|---|
| `prfTagFun_eq`, `prfVerFun_eq`, `polyTimeComputable_prfTagFun`, `polyTimeComputable_prfVerFun`, the `simps` fields of `prfMAC` | owned file |
| `MAC`, `accepts_iff`, `tagImpl_eq`, `forgerCodec_decodeMove`, `forgerCodec_encodeEntry`, `forgerCodec_timeout`, `forgeGame_eq`, `secure_iff` | `Authentication/MAC/Defs.lean` |
| `PRF` (`easy`, `pseudorandom`), `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`; `prfAdv_def`; `acceptProb_random_eq_lazy`; `lazyDist_apply`; `oracleDist_apply` | `Pseudorandom/Functions/Asymptotic/Defs.lean`, `Pseudorandom/Functions/Defs.lean`, `…/LazySampling.lean`, `…/OracleAdversary.lean` |
| T2 `exists_interactiveHandlerMachine` and the `InteractiveHandler` readers; the input-free companion `exists_toCompOn_of_toComp`; T4 `exists_toOracleAdversary_of_bitCodec` | `Games/Efficiency.lean` |
| `fwdHandler`, `fwdHandler_impl` | `Games/Forwarding.lean` |
| `prob_mem_le`, `prob_bad_le`, `expect_sample_mem_le`, `prob_eq_until_bad` | `Games/Hopping.lean` |
| PRFGame: `fImpl`, `lazyImpl`, `expect_lazyImpl`, `abs_expect_fImpl_sub_le` (import, do not copy) | `Encryption/PrivateKey/OracleFromPRF/*.lean` |
| `runAt_coinKey`, `NUPPT.runAt_eq`, `NUPPT.runAtL_ofPolyTimeUniform`, `NUPPT.inArg_eq`, `padFin_ofFn`, `atParam_eq` | `Encryption/PrivateKey/FromPRG.lean`, `Asymptotic/*`, `Games/BitCodec.lean` |
| `Negligible.add`, `mono`, `negligible_two_pow_neg` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the distinguisher (sketch steps 2, 3 and 6).** Apply `exists_toCompOn_of_toComp` to the forger. Build the forwarding reduction with T2: forward each tagging query `m` to the outer oracle, keep the queried messages in the state, and in the finalization make one query at the output message and return `[answer = σ ∧ m fresh]` (`finCall = 1`, `outLen = 1`, budget `q + 1`). Make it an oracle adversary at `ℓ₁ = ℓ₂ = var` with T4. Prove that against `f_k` its acceptance probability is the forgery probability: the tag oracle is deterministic (`.const 0` coins) and equals `f_k` through `hFE`, and the key is `Gen`'s coins (`runAt_coinKey`). Send this checkpoint.
2. **Checkpoint 2 · the random function (sketch step 4).** Against a uniform random function, the reduction accepts with probability at most `2^{-n}`: a fresh point's value is uniform and independent of the forger's view. Use lazy sampling (`acceptProb_random_eq_lazy`, `lazyDist_apply`) with `prob_mem_le`, or a direct count. Send this checkpoint.
3. **Final · the bound (sketch step 5).** `accept (forgeGame A (q n) n) ≤ prfAdv (F n) (D^{q n + 1}) + 2^{-n}`, negligible by `PRF.negligible_prfAdv`, `Negligible.add` and `negligible_two_pow_neg`. Take `ε` to be that bound, which holds at every `n`, `n = 0` included.

Check the edge cases: `n = 0` (the empty message: an unqueried forger wins with probability 1, and `2^{-0} = 1` covers it); budget 0; repeated queries; a forger whose output message was queried (not fresh); malformed outputs and the codecs' timeout outputs (`forgerCodec_timeout` is `zeroBits`); the tag machine's empty coins; the extra final query in the budget (`q + 1`).

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Authentication/MAC/FromPRF.lean` (147 lines at the issue base):
  - replace the target's proof body and edit its sketch to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Authentication/MAC/FromPRF/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `Encryption/PrivateKey/OracleFromPRF` and its helpers (the PRFGame API). They are not downstream of the owned file, so this creates no cycle (checked at the issue base); the order below includes their upstream closure.
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
  - **Nearest relatives here:** the random-function tag-forgery bound of cca2-ett (`Encryption/PrivateKey/EncryptThenTag/Forgery.lean`: `expect_prob_bad_le`, `abs_ettAcc_rej_sub_le`), the lazy random function of `OracleFromPRF/Collision.lean` and `EncryptThenTag/Lazy.lean`, hash-sign's forwarding game (`Signatures/HashAndSign/ForwardGame.lean`, `forward_fresh`) and Lamport's freshness readers (`Signatures/Lamport/Planted.lean`, `fresh_firstLog_iff`).
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
  - Bootstrap from `order.txt` (208 modules) and the narrow `roots.txt` (83), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (20 declarations in 10 modules). The only change
    must be the removal of `prfMAC_secure`.
- **Axioms.**
  - Print the axioms of `prfMAC_secure`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
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
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). |

## ===== briefs/pass-shelat-ch5-8/fills/prf-mac/final-r1/landing/overlap-review.txt =====

prf-mac review: independent overlap search at landing head bd45faecffa420497557dfeba9e2818d7d3cf4a3 (issue base 107f1e8c; worker searches: evidence/overlap/dupsearch-base.log, none for prfAdv/tblEnc/take_ofFn/ofFn_arrowCongr)

=== U1 (undisclosed): Bound.lean hadv (exists_forgeGame_le, lines 159-173) vs public ETTGame.prfAdv_eq_expect (EncryptThenTag/Reduction.lean:347, #306, present at the issue base 107f1e8c)
--- Bound.lean 159-173
  have hadv : prfAdv (F n) (D.toOracleAdversary n n n ((macBudget q).eval n)) =
      |(expect (sample (Fin n → Bool)) fun k => expect (sample (D.Coins n)) fun c =>
          if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval (F n k) = true
          then (1 : ℝ) else 0) -
        expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
          expect (sample (D.Coins n)) fun c =>
            if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
            then (1 : ℝ) else 0)| := by
    rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
      Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
    congr 2
    · refine congrArg _ (funext fun k => ?_)
      simp only [prob_bind, prob_pure, oracleDist_apply]
    · refine congrArg _ (funext fun R => ?_)
      simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]
--- EncryptThenTag/Reduction.lean 341-360
in general form from the published readers): for an oracle adversary `A'` on `m`-bit strings,
`prfAdv F A' = |𝔼_k 𝔼_c [A'(c)^{F k} = 1] − 𝔼_R 𝔼_c [A'(c)^R = 1]|`.

**Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
key (resp. the function table) and the coins (`Bridge.acceptProb_eq`, `accept_eq`,
`Bridge.acceptGame_eq`, `prob_bind`, `oracleDist_apply`, `randomFunction_apply`). -/
theorem prfAdv_eq_expect {m : ℕ} (Fm : (Fin m → Bool) → (Fin m → Bool) → (Fin m → Bool))
    {ρ : Type} [Fintype ρ] [Nonempty ρ] (A' : OracleAdversary ρ (Fin m → Bool) (Fin m → Bool)) :
    prfAdv Fm A' =
      |expect (sample (Fin m → Bool))
          (fun k => expect (sample ρ) fun c => if (A' c).eval (Fm k) = true then (1 : ℝ) else 0) -
        expect (sample ((Fin m → Bool) → (Fin m → Bool)))
          (fun R => expect (sample ρ) fun c => if (A' c).eval R = true then (1 : ℝ) else 0)| := by
  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
  congr 2
  · refine congrArg _ (funext fun k => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply]
  · refine congrArg _ (funext fun R => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]
--- importability: EncryptThenTag/Reduction closure at 107f1e8c has 164 modules, 0 under Authentication (no cycle); adding it to Bound's closure adds 4 modules: EncryptThenTag/{Games,Handler,Machines,Reduction}

=== U2 (undisclosed, landing-time + base): Reduction.lean decide_fnForge hw/htake/hdrop (lines 139-147)
      decide (FnForge f w log) := by
  have hw : List.ofFn w = List.ofFn (splitBits w).1 ++ List.ofFn (splitBits w).2 := by
    rw [← List.ofFn_fin_append,
      show (splitBits w).1 = fun i => w (Fin.castAdd b i) from funext (splitBits_fst w),
      show (splitBits w).2 = fun j => w (Fin.natAdd a j) from funext (splitBits_snd w),
      Fin.append_castAdd_natAdd]
  have htake : (List.ofFn w).take a = List.ofFn (splitBits w).1 := by
    rw [hw, List.take_left' List.length_ofFn]
  have hdrop : (List.ofFn w).drop a = List.ofFn (splitBits w).2 := by
--- merged #307 (after the issue base): Hashing/FromDiscreteLog/Encoding.lean:45,55
/-- The word of the first component of `splitBits w` is the first `a` bits of `w`:
`List.ofFn (splitBits w).1 = (List.ofFn w).take a`. -/
theorem ofFn_splitBits_fst {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).1 = (List.ofFn w).take a := by
  have hfst : (splitBits w).1 = fun j : Fin a => w (Fin.castAdd b j) :=
    funext fun j => splitBits_fst w j
  rw [hfst]
  have hwindow := ofFn_drop_take w 0 a (by omega)
  simpa only [List.drop_zero, Nat.zero_add] using hwindow.symm

/-- The word of the second component of `splitBits w` is the word of `w` after its first
`a` bits: `List.ofFn (splitBits w).2 = (List.ofFn w).drop a`. -/
theorem ofFn_splitBits_snd {a b : ℕ} (w : Fin (a + b) → Bool) :
    List.ofFn (splitBits w).2 = (List.ofFn w).drop a := by
--- at the issue base: Asymptotic/ReductionSupport.lean:288 take_ofFn_castLE (the G24-01 lemma), Asymptotic/CollectionsHelpers.lean:210 ofFn_drop_take
107f1e8c218733eac12d6b9bee6fece441271317:TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean:210:theorem ofFn_drop_take {L : ℕ} (b : Fin L → Bool) (a k : ℕ) (h : a + k ≤ L) :
107f1e8c218733eac12d6b9bee6fece441271317:TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean-211-    ((List.ofFn b).drop a).take k = List.ofFn fun i : Fin k => b ⟨a + i, by have := i.isLt; omega⟩ := by
--
107f1e8c218733eac12d6b9bee6fece441271317:TCSlib/Cryptography/Asymptotic/ReductionSupport.lean:288:theorem take_ofFn_castLE {ℓ m : ℕ} (h : m ≤ ℓ) (f : Fin ℓ → Bool) :
107f1e8c218733eac12d6b9bee6fece441271317:TCSlib/Cryptography/Asymptotic/ReductionSupport.lean-289-    (List.ofFn f).take m = List.ofFn fun i : Fin m => f (Fin.castLE h i) := by

=== U3 (undisclosed relative): blocks/macState/hitsOf/hits_nil_iff (Handler.lean) vs the published encoded table with poly-time lookup GGMRed.tblEnc / GGMRed.lookup / lookup_tblOf (Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean:180,349,472), reused by cca2-ett as tblW/lookup_tblW (EncryptThenTag/CPAHandler.lean:74,116) for a handler state of stored entries

=== U4 (undisclosed relatives of disclosed rows)
owned-file key/hkey: public NUPPT.coinsEquiv_ofPolyTimeUniform(_ofFn) (Complexity/Randomized/PPT.lean:417,422) and Asymptotic/Adversary.lean:232 ofFn_arrowCongr_finCongr (the disclosed relative was only the private prfKeyEq)
accept_forgeGame_eq: Lamport's deterministic-signer game lemmas lamport_signImpl_expect / lamport_loggedSignImpl_expect / lamport_forgeGame_accept_eq_honestProbability (Signatures/Lamport.lean:808,823,849; #309, at the issue base)
fnImpl: disclosed (tableSigner T = fnImpl-shape for Lamport)

=== Checked, disclosed or no overlap
finish_of_query_padFin: no finalization-with-query lemma elsewhere (all *_finish lemmas use finish_of_ret/buildComp_zero_of_ret; Decrypt.lean:218 simulate_decHandler_finish is decHandler-specific)
allOutputs_simulate_withLog_length: no withLog log-length lemma in TCSlib (Simulate.lean has only withLog_apply, simulate_withLog)
queried / FnForge: relatives in HashAndSign ForwardGame/CollisionHandler/FixedGame and Lamport Planted (disclosed rows)
eval_toOracleAdversary_width2, macBudget, forgerCodec_eq_bitCodec, expect_forge_*: disclosed
hash-sign CollisionHandler (one stored query, not a list) is not a restatement

=== Name clashes: statements/nameclash.txt (0 exact; one same short name under Authentication: SignatureScheme.forgerCodec_eq_bitCodec, different namespace)

## ===== briefs/pass-shelat-ch5-8/fills/prf-mac/final-r1/landing-reuse/PROVENANCE.txt =====

prf-mac landing edit LE-reuse (finding F-01, proof only), maintainer, 2026-11-15 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I throughout; Lean 4.25.0, PATH=$HOME/.elan/bin:$PATH; one Lean process at a time (ours), only
  scripts/lean_check_tree.sh (worktree copy byte-equal to /home/user/tcslib/scripts/) through tools-used/review/runner.py
  (the G26-N1-fixed runner, byte-equal in the prf-mac-r1 and prf-long-r1 zips) with TCSLIB_OLEANS=$SP/dl-oleans-2 (dl-oleans,
  in use by another review, not touched); no lake command; nothing pushed; /home/user/tcslib working tree not edited (its
  HEAD moved during the job by records commits not made here: e9998722 -> 2d568af5 -> bea53eeb).
Method and tools: the prf-mac review zip in records (briefs/pass-shelat-ch5-8/fills/prf-mac/final-r1/review-evidence.zip:
  PROVENANCE, tools/, order/), extracted to a fresh directory; frozencheck.py (+ frozencheck_lib.py) and buildsum.py from the
  prf-long review zip (fills/prf-long/final-r1/review-evidence.zip); runner.py there is byte-equal to prf-mac's. These are
  tools-used/review/ unmodified. Helpers from $SP/dl-review/learning-r1-reuse/tools-used/ unmodified: snap.py, impcheck.py,
  impdelta2.py, docheader.py, docdelta.py, sealrows.py, restoreplan.py, downstat.py. New here: lereuse_edit.py, refcmp.py.

landing: branch land/pass-shelat-prf-mac (local, no upstream), worktree $SP/wt-land-prf-mac (sparse, briefs/ excluded;
  .lake/packages -> /home/user/tcslib/.lake/packages). Start: head bd45faecffa420497557dfeba9e2818d7d3cf4a3 on e7fa2605.
  r1: rebased onto origin/cryptography/pass-shelat-ch2-4 59c2c1fbf8c1bb08f9d191012b7cdd7e15248531 (merge of #314)
    (landing/rebase.log, range-diff.txt: 5/5 identical; landing/rebase-summary.txt: the Lean delta e7fa2605..59c2c1fb is #311,
    #312, #314's 6 files; the unit diff old head vs rebased LE-doc is empty). LE-reuse committed as 9a415163 (tree ca9f169f);
    all builds and probes below ran at 9a415163.
  r2: origin moved during the job to e99987221593020b9f7dbb87fe577bd6aac5ecbb (records only: 39 paths under briefs/ and *.md,
    landing/origin-delta-r2-name-status.txt). Rebased (landing/rebase-r2.log): range-diff-r2.txt 6/6 identical; the Lean,
    scripts and audits diff 9a415163..head is empty and `git ls-tree -r` of TCSlib, TCSlib.lean, audits, scripts is identical
    (same hash) at 9a415163 and the head, so the build, probes and lint apply unchanged. Statement checks were rerun at r2.
  head   LE-reuse  590d1a56a350d9e8e75ee33d31e0501182169f67 (tree af0609aebea492170df6d2f254ce0e7885a598d1)
  parent LE-doc    997dd8caeb8e9dfdde28da4b85f70467fed9c998 (tree e5f7d88ea49a6a4dc98c05d35c2c9cd4e2674fed)
  author = committer = Claude <noreply@anthropic.com>; every one of the 6 commits SSH-signed by the environment default
  (commit.gpgsign=true, gpg.format ssh; not overridden): `git cat-file -p <c> | grep -c '^gpgsig'` = 1 each (checks/commit.txt).
  Message logs/commit-msg.txt, subject "prf-mac landing edit LE-reuse: hadv from the published prfAdv_eq_expect (F-01)", ending
  with the Co-Authored-By and Claude-Session lines. Patch 0001-LE-reuse.patch. Worktree clean at the head.

edit (tools-used/lereuse_edit.py, 2 exact replacements; checks/le-reuse.diff; checks/changed-paths.txt: one path,
  M TCSlib/Cryptography/Authentication/MAC/FromPRF/Bound.lean, +3/-17, 183 -> 169 lines, max width 99 at both revisions):
  (1) exists_forgeGame_le: the local `hadv` (prfAdv (F n) (D^{n,n,n}) = |E_k E_c [..F n k..] - E_R E_c [..R..]|, 15 lines,
      re-proved line for line as #314's proof) and `rw [hreal, hadv]` are replaced by
        rw [hreal, TCSlib.Cryptography.prfAdv_eq_expect (F n) (D.toOracleAdversary n n n _)]
      (K = I = O = {0,1}^n, ρ = D.Coins n; the `_` is the budget (macBudget q).eval n, unified by rw). The comment line
      "-- The PRF advantage is the gap." and the final linarith are unchanged. Compiled first time, 0 warnings.
  (2) docstring: step 3 of the sketch gains "; this is the published\n   `TCSlib.Cryptography.prfAdv_eq_expect`" before its
      final period (checks/docstring-delta.txt: pure insertion, 1612-character common prefix, 5-character suffix). Nothing
      else in any docstring changes; the module docstring is unchanged.
  imports (checks/imports.txt, impcheck.py): Pseudorandom.Functions.Defs is already in Bound's closure (170 project modules;
  chain through ...FromPRF.Random), no cycle. No import added.

statements (statements/; base = parent 997dd8ca, head 590d1a56; unit-paths.txt = the 6 unit files):
  decls2-vs-997dd8ca.tsv and .err: both empty.
  touched-997dd8ca-vs-head.tsv: 1 CHANGED (exists_forgeGame_le: proof and sketch), 58 UNCHANGED.
  header-bytes-vs-997dd8ca.txt (headerbytes.py; touched-before/after.json = eff2dcd0 vs parent/head; endpoints prfMAC_secure,
    exists_forgeGame_le): 61 compared, 0 different or missing.
  frozen/frozen-check-vs-997dd8ca.txt (frozencheck.py): 59 declarations in 6 files, header bytes, statement prose and every
    definition body identical, order preserved: 0 differences. frozen-check-vs-eff2dcd0.txt: the owned FromPRF.lean 8/8, the
    5 helpers new files: 0 differences. Controls (one character changed, each exactly 1 difference): control-header.txt
    (exists_forgeGame_le HEADER), control-prose.txt (its PROSE), control-body.txt (padFunEquiv BODY).
  checks/docstring-header.txt (docheader.py): keyword-to-`:=` header identical; docstring differs by the insertion only
    (its RESULT FAIL is the docstring comparison, by design).

build (build/; order/ by tools-used/review/downorder.py at 9a415163 vs eff2dcd0): changed.txt 62 modules (56 base delta since
  eff2dcd0: #303, #306-#309, #311, #312, #314 incl. Pseudorandom/Functions/Defs and EncryptThenTag/Reduction; 6 unit);
  down.txt their downstream closure through root TCSlib, audits/garg-ch1-3/Checks and audits/pass-shelat/Checks: 136 modules;
  build-queue.txt = order.txt (imports-first) restricted to down.txt. It contains the 6 unit modules, Authentication, the whole
  base delta, TCSlib and both audits Checks.
  build/summary.txt (buildsum.py): 136/136 rc 0, errors 0 (G26-N1 form), substring "error" 0 times, 815 s. Sorry warnings only
  in admitted base/base-delta modules (SeedMajority 2, SpecialEncryptionSecurity 3, SpecialEncryptionMulti 1, GarblingSecurity 1,
  Yao 3, Learning 1; as in prf-long-r1). Other warnings all inherited from unchanged sources: DDH 3, Lamport 7, Rejection 10,
  Extraction 2, SubHybrids 1, GGM 1, ReductionMachine 1, Encryption FromPRF 1, MAC/FromPRF 1 (base unused simp arg). Bound 0.
  build/vs-prf-mac-r1.txt (refcmp.py against the prf-mac review's 67-module head build): 65 identical source and olean SHA-256
  (incl. MAC/FromPRF, Authentication, TCSlib, audits/pass-shelat/Checks), 2 differ: EncryptThenTag/Reduction (#314) and Bound
  (this edit); 69 had no record there (downstream of #311/#312/#314 only).
  Before the build the 87 base oleans it overwrites were copied aside (tree/backed-up.txt with hashes) and the 49 new ones
  listed (tree/new-oleans.txt).

axioms (axioms/; rule10/probe-runs/, rc 0): AxiomsHead.log: prfMAC_secure, PRFMAC.exists_forgeGame_le and
  TCSlib.Cryptography.prfAdv_eq_expect each [propext, Classical.choice, Quot.sound]. Census (rule10/probe-sources/
  CensusHead.lean.txt = mkcensus_prfmac.py over the 6 unit modules, body identical to the review's): census-summary.txt 97 stored
  constants, none outside the standard three, no sorryAx; census-review-bd45faec-vs-head (censuscmp.py, review head census as
  base): 97/97 common, 0 removed, 0 added, 0 type-changed, 0 attr-changed, 0 axioms-changed.

Rule 10 (rule10/), Bound.lean at 9a415163 (= head sources):
  collector probe-sources/CollectHead.lean.txt (mkcollect.py, owners order/head-owners.txt = Bound) run as PmrProbe/CollectHead:
    CAT 3045, MODULE Bound stored 8 (review: 8).
  seals: mkseals_ab.py strict -> seals/{A,B} (B with SEAL_EVAL=1); mkseals_coe.py coe -> seals-coe/{A,B}; mkseals-*.log.
    Requests strict A 2257, B 2258, coe A 2256, coe B 2257 = the review's. seal-rows-vs-review.txt (sealrows.py vs prf-mac-r1
    seals): per variant 0 rows gone, 0 new, 0 changed. term-readers-vs-review.txt: Bound's elaborated terms reference 31 names
    instead of 39; gone are exactly those of the re-proof (Bridge.acceptGame, OracleComp.bind, ProbComp, ProbComp.prob,
    acceptProb, distAdv, oracleDist, randomFunction); none new; the readers of the remaining names unchanged.
  runs seal-runs/ (order/seal-control-queue.txt, NOSTOP=1, seal-runner.out); sealsum.py with statements/touched-after.json:
    seals-A.tsv, seals-B.tsv, seals-coe-A.tsv, seals-coe-B.tsv: strict A pass, strict B pass, coe A pass, coe B pass (rc 0,
    0 errors, install and EOF records present). As in the review (Bound passes A and B).
  paired controls (tools-used/review/mkctl_prfmac.py unmodified, on Bound's records only: seals-flat/ -> controls-strict/,
    PmrProbe/KS; seals-coe-flat/ -> controls-coe/, PmrProbe/K): 4 probes each (ControlS/ControlU x A/B), 25 sealed negatives
    each (A 12: padFin, expect, rAns, chunkMap, ovr, forgerCodec, fnImpl, FnForge, queried, macBudget, blocks, macHandler;
    B 13: those and PolyExpr.eval). ctlcheck-strict.log and ctlcheck-coe.log (ctlcheck2.py): each negative fails exactly once
    sealed, all readers and all unsealed probes pass, no stray error: ALL_OK True in both.
  probe-copies-check.txt: the 15 probe sources in the worktree were byte-equal to the copies here before PmrProbe/ was removed.

lint (lint/): python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b in the worktree at 9a415163
  (lint-edit-9a415163.txt) and in a git-archive export of the parent 6341afdf (lint-parent-6341afdf.txt; TCSlib, scripts,
  audits trees identical to 997dd8ca; export removed): both 92 FAIL, 101 WARN over 349 files. linediff-parent-vs-edit.txt: the
  only line that differs is Bound's INFO line (183 -> 169 lines). linediff-review-bd45faec-vs-edit.txt (FAIL/WARN lines,
  whitespace-normalised, vs the prf-mac review's lint-landing-head.txt, copied as lint-review-bd45faec-from-prf-mac-r1.txt): empty.

olean tree $SP/dl-oleans-2:
  pre: tree/snapshot-pre.txt (tools-used/review/snapshot.py): 1230 files, 0 empty dirs, SHA-256
    457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = the required base value.
  restore (restore/): the 87 backups copied back, each hash checked (restore-log.txt: 87 restored, 0 failed); restoreplan.py
    --delete against tree/snapshot-pre.txt: 60 extra files (= the 49 new oleans + the 11 PmrProbe/ probe oleans of
    probe-oleans.txt; the 4 sealed controls fail by design and leave none) deleted with 11 emptied directories
    (deleted-dirs.txt); 0 changed, 0 missing. Backups removed afterwards.
  post: tree/snapshot-post.txt: 1230 files, 0 empty dirs, SHA-256 457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f,
    byte-identical to tree/snapshot-pre.txt.
cleanup: the review-zip extracts ($SP/ex-pm-review, $SP/ex-pl-review, and $SP/ex-dlcrh-reuse, read only) removed; PmrProbe/ removed from the worktree, which is
  clean at 590d1a56.
SHA256SUMS: every file here except itself (paths without "./"); ../prf-mac-reuse-evidence.zip holds exactly these paths plus
  SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/30-prfadv-promote/resolutions-r1.md =====

# Gate 30 · resolutions, round 1 · CLOSED

Codex's verdict is **CLEAR**: 0 blockers, 0 majors, 1 minor, 0 notes.
- **Findings:** `findings/gate30-prfadv-promote-findings.md`.
- **Audited head:** `5757bc0604527602d790a1a57e9703374ce02c7b`.

Codex confirmed the following:
- the placement beside `prfAdv`;
- the import, which is acyclic and justified (closure 6 → 9 modules, 42 downstream modules gain it);
- the ETT API, which is unchanged;
- that no other unrecorded copy exists. The private `prfAdv_prfReduction` stays deferred.

| # | Severity | Disposition |
|---|---|---|
| G30-01 | minor | **Fixed by LE-gate30, docstring only** (`a24a6313e20a0c3120d457fa4fb0960c72c06312`, tree `6700d281`). The "re-derived here" claim is gone; the overlap note stays as provenance; the sketch now says the theorem is a direct specialization of `TCSlib.Cryptography.prfAdv_eq_expect`. Doc-only check OK, `decls2` empty, 14/14 headers identical, 129/129 rc 0, lint 92/101. Evidence `landing-r1/gate30-le-evidence.zip`, SHA-256 `944de88ab03ec983b82167d35e4fc1cd1aa2ee3db67beb795c235f4a4e194378`. |

**Follow-up from Codex.** DL-44 is not fully discharged until prf-mac re-points its `hadv`. The merged #313/#314 tree
needs an integration build before the second of the two merges.

**Closure (2026-11-15).** The minor was below the gate threshold, so no round 2. Seyoon merged [PR #314](https://github.com/Shilun-Allan-Li/tcslib/pull/314) with LE-gate30 as its head; the merge is `59c2c1fbf8c1bb08f9d191012b7cdd7e15248531`. **Gate 30 is CLOSED.**

Carried forward, outside this gate: prf-mac's local `hadv` re-point (DL-44 F-01, landing edit in progress); the integration rebuilds of #313 and #315 on the merged tip.

## ===== briefs/pass-shelat-ch5-8/gates/33-prf-mac/pr-description.md =====

Landing PR for the Pass–shelat `prf-mac` fill. It proves `Authentication.prfMAC_secure`, [PS10, Theorem 135.4]: the MAC built from a PRF is existentially unforgeable.

**Head:** `590d1a56a350d9e8e75ee33d31e0501182169f67`.
**Base:** `cryptography/pass-shelat-ch2-4` at `e99987221593020b9f7dbb87fe577bd6aac5ecbb`, which includes #314.

## What changes
6 Lean files, +1289 / −19:
- The owned file `Authentication/MAC/FromPRF.lean`: the target's proof, its sketch and the module docstring.
- Five new helpers in `Authentication/MAC/FromPRF/`: `Handler`, `Reduction`, `Game`, `Random` and `Bound`.

For every `n`, the proof gives `Pr[forge] ≤ prfAdv(F_n, D^{q·1+1}) + 2⁻ⁿ`. The edge cases are handled: `n = 0`, budget 0, repeated queries, a queried output message, timeouts, and the final `+1` query. Then negligibility finishes the theorem.

## Commits
- **Worker commits (4):** checkpoint 1, the distinguisher; checkpoint 2, forging against a random function; the final, the bound and Theorem 135.4; and the Rule-10 repair, which reads `ovr [] R` through `ovr_nil`.
- **LE-doc** `997dd8ca`: formula docstrings for `macHandler`'s `simps` fields and for the `FnForge` Decidable instance. It changes doc comments only.
- **LE-reuse** `590d1a56`, which closes review finding F-01, ledger DL-44. Under Seyoon's ruling, the delivery's local `hadv` in `Bound.exists_forgeGame_le` was promoted first, in #314. That PR published `TCSlib.Cryptography.prfAdv_eq_expect`. `hadv` is now replaced by that published lemma.
  - The change touches the proof only: +3 / −17.
  - The sketch now cites the lemma.
  - No import was added.

## Checks
These were run by the maintainer at the head. The evidence will be filed in the campaign records.
- **Statements:**
  - `decls2` gives 38 ADDED, 0 CHANGED and 0 REMOVED against the issue base.
  - Against LE-doc, `decls2` is empty.
  - Every header is byte-identical, the target's included.
- **Build:** 136 modules give rc 0 with 0 errors. The set is the downstream of every module changed since the base snapshot, including #314's two files. It covers `Authentication`, root `TCSlib`, and `audits/*/Checks`.
- **Axioms:** `prfMAC_secure` uses only `propext`, `Classical.choice` and `Quot.sound`.
- **Rule 10:**
  - Seals A and B pass in both the strict and the coe variant.
  - Paired controls are `ALL_OK`.
- **Lint:** 92 FAIL / 101 WARN, the same as the baseline.
- **Admissions:** the target is no longer admitted.

## Findings
These come from the delivery review, `fills/prf-mac/final-r1/review.md`.
- **F-01** (major): fixed by LE-reuse above.
- **F-02 and F-03** (minor): errata, recorded in ledger DL-44.
- **F-04 and F-05** (notes): errata.
- **F-06** (note): pre-existing and disclosed; no action.

A Codex gate will follow. Seyoon merges.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/33-prf-mac/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Authentication/MAC/FromPRF.lean b/TCSlib/Cryptography/Authentication/MAC/FromPRF.lean
index 842bf6c59..7aa48c8ef 100644
--- a/TCSlib/Cryptography/Authentication/MAC/FromPRF.lean
+++ b/TCSlib/Cryptography/Authentication/MAC/FromPRF.lean
@@ -3,6 +3,11 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Authentication.MAC.Defs
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Game
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Bound
 import TCSlib.Cryptography.Authentication.Encoding
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
 import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
@@ -14,7 +19,7 @@ set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# The PRF MAC (statement phase)
+# The PRF MAC
 
 [PS10, Protocol 134.3]: for a family `{f_s : {0,1}^n → {0,1}^n}`, `Gen(1^n)` samples a uniform
 `n`-bit key, `Tag_k(m) = f_k(m)`, and `Ver_k(m, σ)` accepts iff `f_k(m) = σ`. Theorem 135.4: when
@@ -32,8 +37,18 @@ the ch. 2–4 layer's `PRF`). `Gen` is the ch. 2–4 layer's coin-key machine (i
 
 ## Main results
 
-* `Authentication.prfMAC_secure` (Thm 135.4, stated; a `sorry` under its sketch): a PRF gives a
-  secure MAC.
+* `Authentication.prfMAC_secure` (Thm 135.4, proved): a PRF gives a secure MAC, with the forgery
+  probability at most `prfAdv(F_n, D) + 2^{-n}` at every `n` for a distinguisher `D`.
+
+## Contents
+
+* `MAC/FromPRF/Handler`: the reduction's handler (forwarded and stored queries, the final query).
+* `MAC/FromPRF/Reduction`: the distinguisher, accepting against `f` iff the forger forges against
+  the tagging oracle `f`.
+* `MAC/FromPRF/Random`: forging against a random function succeeds with probability `≤ 2^{-t}`.
+* `MAC/FromPRF/Game`: the forgery game of a MAC with a deterministic tag.
+* `MAC/FromPRF/Bound`: the bound `Pr[forge] ≤ prfAdv + 2^{-n}` for a MAC whose tag is a keyed
+  family.
 
 ## References
 
@@ -118,22 +133,25 @@ attribute [simps (config := { isSimp := false }) msgLen tagLen gen tag ver] prfM
 /-- **Theorem 135.4: a PRF gives a secure MAC** [PS10, Theorem 135.4]: if `F` is a pseudorandom
 function family, the PRF MAC is secure.
 
-**Proof sketch** (the source's, with its bound).
-1. Fix a forger `A` with budget `q`. Let `ε(n)` be its forgery probability against the PRF MAC.
-2. The distinguisher `D` runs `A` against its own oracle, answering each tagging query `m` with
-   the oracle's value. It then queries the oracle at `A`'s output message `m` and outputs `1`
-   iff the answer is `σ` and `m` was not queried before.
-3. With the oracle `f_k`, `D` outputs `1` exactly when `A` forges: probability `ε(n)`.
+**Proof sketch** (the source's, with its bound `ε(n) ≤ prfAdv(F_n, D) + 2^{-n}`).
+1. Fix a forger `A` with budget `q`; let `ε(n)` be its forgery probability. `Gen` returns its
+   coins, the key (`runAt_coinKey`, read at `n` bits by `NUPPT.coinsEquivPoly`); `Tag` returns
+   `E ⟨k, m⟩ = f_k(m)` whatever its (empty) coins (`prfTagFun_eq`, `hFE`); `Ver` accepts `(m, σ)`
+   iff `f_k(m) = σ` (`prfVerFun_eq`).
+2. The distinguisher `D` (`PRFMAC.exists_macReduction`) runs `A` against its own oracle, answering
+   each tagging query `m` with the oracle's value and storing `m` in its state. It then queries
+   the oracle at `A`'s output message `m` and outputs `1` iff the answer is `σ` and `m` was not
+   stored. It is T2 (`Games.exists_interactiveHandlerMachine`) for the handler
+   `PRFMAC.macHandler` (`finCall = 1`, `outLen = 1`, budget `q + 1`) on the input-free companion
+   of `A` (`Games.exists_toCompOn_of_toComp`), made an oracle adversary by T4
+   (`Games.exists_toOracleAdversary_of_bitCodec`).
+3. With the oracle `f_k`, `D` outputs `1` exactly when `A` forges (`PRFMAC.accept_forgeGame_eq`):
+   probability `ε(n)`.
 4. With a random function, a forgery is a guess of a fresh uniform value: probability at most
-   `2^{-n}` (the collision bound `prob_mem_le`, or a direct count).
-5. So `D`'s PRF advantage is at least `ε(n) − 2^{-n}`. Since `F` is a PRF it is negligible, so
-   `ε` is negligible.
-6. First use the input-free companion `Games.exists_toCompOn_of_toComp` for the forger.
-   The forwarding reduction is a machine by T2 (`Games.exists_interactiveHandlerMachine`):
-   its finalization makes one query at the output message, checks freshness from the state,
-   and returns one bit (`finCall = 1`, `outLen = 1`), with budget `q + 1`. T4
-   (`Games.exists_toOracleAdversary_of_bitCodec`) then supplies `OracleEnsemble.Indist`'s
-   oracle adversary.
+   `2^{-n}` (`PRFMAC.expect_fnForge_random_le`, sampling the function lazily by table override).
+5. So `ε(n) ≤ prfAdv(F_n, D) + 2^{-n}` at every `n`, `n = 0` included
+   (`PRFMAC.exists_forgeGame_le`), which is negligible (`PRF.negligible_prfAdv`, `Negligible.add`,
+   `negligible_two_pow_neg`).
 
 The PRF advantage is read through `OracleEnsemble.Indist`, in framework form after the F-1
 restatement. -/
@@ -142,6 +160,63 @@ theorem prfMAC_secure {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin
     (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
       List.ofFn (F n s x)) :
     (prfMAC F E hE hFE).Secure := by
-  sorry
+  -- `Gen` returns its coins, and `Tag` returns `E` of its argument.
+  have hgen : ∀ n (rg : (prfMAC F E hE hFE).gen.Coins n),
+      (prfMAC F E hE hFE).gen.runAt n [] rg = List.ofFn rg := by
+    intro n
+    have h : ∀ G : NUPPT, G = NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var →
+        ∀ rg : G.Coins n, G.runAt n [] rg = List.ofFn rg := by
+      rintro G rfl rg
+      exact runAt_coinKey .var n rg
+    exact h _ (prfMAC_gen F E hE hFE)
+  have htagE : ∀ n (w : List Bool) (rt : (prfMAC F E hE hFE).tag.Coins n),
+      (prfMAC F E hE hFE).tag.runAt n w rt = E w := by
+    intro n w
+    have h : ∀ T : NUPPT,
+        T = NUPPT.ofPolyTimeUniform (polyTimeComputable_prfTagFun hE) (.const 0) →
+        ∀ rt : T.Coins n, T.runAt n w rt = E w := by
+      rintro T rfl rt
+      rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, prfTagFun_eq, NUPPT.inArg_eq,
+        NUPPT.advInput_eq, pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode]
+    exact h _ (prfMAC_tag F E hE hFE)
+  -- The key is `Gen`'s coins, read at `n` bits.
+  have hcoins : (prfMAC F E hE hFE).gen.coins = .var := by
+    rw [prfMAC_gen, NUPPT.coins_ofPolyTimeUniform]
+  let key : ∀ n, (prfMAC F E hE hFE).gen.Coins n ≃ (Fin n → Bool) := fun n =>
+    (NUPPT.coinsEquivPoly hcoins n).trans
+      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))
+  have hkey : ∀ n rg, List.ofFn (key n rg) = List.ofFn rg := fun n rg => by
+    rw [← NUPPT.coinsEquivPoly_ofFn hcoins n rg]
+    exact (List.ofFn_congr (PolyExpr.eval_var n) _).symm
+  have hmsg : ∀ n, (prfMAC F E hE hFE).msgLen.eval n = n := fun n => by
+    rw [prfMAC_msgLen, PolyExpr.eval_var]
+  have htl : ∀ n, (prfMAC F E hE hFE).tagLen.eval n = n := fun n => by
+    rw [prfMAC_tagLen, PolyExpr.eval_var]
+  -- On the key of `rg`, `E` computes `F_{key rg}` (`hFE`).
+  have hEF : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool),
+      E (pairEncode ((prfMAC F E hE hFE).gen.runAt n [] rg) (List.ofFn m)) =
+        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) := by
+    intro n rg m
+    rw [hgen, ← hFE]
+    rw [hkey, ofFn_padFin_of_length (by rw [List.length_ofFn, hmsg])]
+  have htag : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool)
+      (rt : (prfMAC F E hE hFE).tag.Coins n),
+      (prfMAC F E hE hFE).tag.runAt n
+          (pairEncode ((prfMAC F E hE hFE).gen.runAt n [] rg) (List.ofFn m)) rt =
+        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) := fun n rg m rt => by
+    rw [htagE, hEF]
+  have hacc : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool)
+      (σ : Fin ((prfMAC F E hE hFE).tagLen.eval n) → Bool),
+      (prfMAC F E hE hFE).Accepts n ((prfMAC F E hE hFE).gen.runAt n [] rg) m σ ↔
+        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) = List.ofFn σ := by
+    intro n rg m σ
+    rw [MAC.accepts_iff, prfMAC_ver, prfVerFun_eq, atParam_eq]
+    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
+    rw [hEF, List.singleton_inj, decide_eq_true_iff]
+  -- The bound of the reduction, negligible.
+  rw [MAC.secure_iff]
+  intro A q
+  obtain ⟨D, hD⟩ := PRFMAC.exists_forgeGame_le (prfMAC F E hE hFE) F hmsg htl key htag hacc A q
+  exact ⟨_, (hF.negligible_prfAdv D (PRFMAC.macBudget q)).add negligible_two_pow_neg, hD⟩
 
 end TCSlib.Cryptography.Authentication
diff --git a/TCSlib/Cryptography/Authentication/MAC/FromPRF/Bound.lean b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Bound.lean
new file mode 100644
index 000000000..7e1c0a1b1
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Bound.lean
@@ -0,0 +1,169 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Game
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
+import TCSlib.Cryptography.Games.Bridges.Experiments
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The bound of the PRF-MAC reduction
+
+Step 5 of the proof of [PS10, Theorem 135.4], for any MAC whose tag is a keyed function family
+`F` (`n`-bit messages and tags, the key read off the generator's coins, a deterministic tag
+`F_k(m)` and verification `F_k(m) = σ`): for every forger `A` and budget `q` there is a
+distinguisher `D` with, at every `n`,
+`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D^{q(n) · 1 + 1}) + 2^{-n}` (`exists_forgeGame_le`).
+
+The forgery probability is the acceptance probability of `D` against `F_k` (`accept_forgeGame_eq`,
+`exists_macReduction`), and its acceptance probability against a uniform random function is at
+most `2^{-n}` (`exists_macReduction`, `expect_fnForge_random_le`). The functions of the scheme's
+widths are those of `n` bits read through `padFin` (`eval_toOracleAdversary_width₂`).
+
+## Main results
+
+* `PRFMAC.eval_toOracleAdversary_width₂`: an oracle adversary read at equal widths.
+* `PRFMAC.exists_forgeGame_le`: the bound.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 135.4 (book p. 135).
+-/
+
+namespace TCSlib.Cryptography.Authentication.PRFMAC
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-- **An oracle adversary read at equal widths:** for `m₁ = n` and `m₂ = n`, running
+`D.toOracleAdversary n n n q c` against `f` is running `D.toOracleAdversary n m₁ m₂ q c` against
+`f` with its inputs and outputs read at the widths `m₁`, `m₂`:
+`(D^{n,n} c).eval f = (D^{m₁,m₂} c).eval (fun x => padFin m₂ ⟦f (padFin n ⟦x⟧)⟧)`.
+
+**Proof sketch.** Substitute `m₁ = n` and `m₂ = n`; the readings are identities (`padFin_ofFn`). -/
+theorem eval_toOracleAdversary_width₂ (D : NUPPT) (n q : ℕ) (c : D.Coins n) {m₁ m₂ : ℕ}
+    (h₁ : m₁ = n) (h₂ : m₂ = n) (f : (Fin n → Bool) → (Fin n → Bool)) :
+    (D.toOracleAdversary n n n q c).eval f =
+      (D.toOracleAdversary n m₁ m₂ q c).eval
+        (fun x => padFin m₂ (List.ofFn (f (padFin n (List.ofFn x))))) := by
+  subst h₁ h₂
+  simp only [padFin_ofFn]
+
+/-- The functions `{0,1}^n → {0,1}^n` read at the widths `m₁ = n` and `m₂ = n`: `R` becomes
+`fun x => padFin m₂ ⟦R (padFin n ⟦x⟧)⟧`. -/
+private def padFunEquiv {n m₁ m₂ : ℕ} (h₁ : m₁ = n) (h₂ : m₂ = n) :
+    ((Fin n → Bool) → (Fin n → Bool)) ≃ ((Fin m₁ → Bool) → (Fin m₂ → Bool)) where
+  toFun R x := padFin m₂ (List.ofFn (R (padFin n (List.ofFn x))))
+  invFun R' y := padFin n (List.ofFn (R' (padFin m₁ (List.ofFn y))))
+  left_inv R := by
+    funext y
+    simp only
+    rw [ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn,
+      ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn]
+  right_inv R' := by
+    funext x
+    simp only
+    rw [ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn,
+      ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn]
+
+/-- **The bound of the PRF-MAC reduction** [PS10, Theorem 135.4, proof, step 5]: let `M` be a
+MAC with `n`-bit messages and tags (`hℓ`, `ht`) and `F` a keyed family, with a bijection `key n`
+from the generator's coins to `n`-bit keys, such that tagging `m` on the key of `rg` returns
+`F_{key rg}(m)` (`htag`) and verification accepts `(m, σ)` iff `F_{key rg}(m) = σ` (`hacc`), the
+messages read at `n` bits. Then for every forger `A` and budget `q` there is a next-query machine
+`D` with, at every `n`,
+`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D.toOracleAdversary n n n (q(n) · 1 + 1)) + 2⁻ⁿ`.
+
+**Proof sketch.** `D` is `exists_macReduction` at the widths `msgLen`, `tagLen`.
+1. *With `F_k`.* The tag is deterministic, so the forgery probability is the average over `rg`
+   of the forgery probability against `fnImpl (g rg)`, `g rg` being `F_{key rg}` read at the
+   scheme's widths (`accept_forgeGame_eq`); by `exists_macReduction` it is `D`'s acceptance
+   probability against `g rg`, which is `D`'s against `F_{key rg}` at `n` bits
+   (`eval_toOracleAdversary_width₂`); `key` relabels the coins (`expect_sample_equiv`).
+2. *With a random function.* `D`'s acceptance probability against a uniform `R` is, through the
+   widths (`padFunEquiv`, `expect_sample_equiv`) and `exists_macReduction`, the average over `A`'s
+   coins (`expect_sample_comm`) of the forgery probability against a random function, at most
+   `2^{-n}` (`expect_fnForge_random_le`).
+3. *The PRF advantage* is the absolute gap between the two (`prfAdv_def`, `distAdv_def`,
+   `Bridge.acceptProb_eq`, `Bridge.acceptGame_eq`, `oracleDist_apply`); this is the published
+   `TCSlib.Cryptography.prfAdv_eq_expect`. -/
+theorem exists_forgeGame_le (M : MAC) (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
+    (hℓ : ∀ n, M.msgLen.eval n = n) (ht : ∀ n, M.tagLen.eval n = n)
+    (key : ∀ n, M.gen.Coins n ≃ (Fin n → Bool))
+    (htag : ∀ n rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
+      M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m)) rt =
+        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))))
+    (hacc : ∀ n rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
+      M.Accepts n (M.gen.runAt n [] rg) m σ ↔
+        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) = List.ofFn σ)
+    (A : NUPPT) (q : PolyExpr) :
+    ∃ D : NUPPT, ∀ n, accept (M.forgeGame A (q.eval n) n) ≤
+      prfAdv (F n) (D.toOracleAdversary n n n ((macBudget q).eval n)) + (2 : ℝ)⁻¹ ^ n := by
+  obtain ⟨D, hD⟩ := exists_macReduction M.msgLen M.tagLen q A
+  refine ⟨D, fun n => ?_⟩
+  -- The tag function at the scheme's widths.
+  let g : M.gen.Coins n → (Fin (M.msgLen.eval n) → Bool) → (Fin (M.tagLen.eval n) → Bool) :=
+    fun rg m => padFin _ (List.ofFn (F n (key n rg) (padFin n (List.ofFn m))))
+  have hg_tag : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
+      padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m))
+        rt) = g rg m := fun rg m rt => by
+    rw [htag]
+  have hg_acc : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
+      M.Accepts n (M.gen.runAt n [] rg) m σ ↔ g rg m = σ := fun rg m σ => by
+    rw [hacc]
+    constructor
+    · intro h
+      show padFin _ (List.ofFn (F n (key n rg) (padFin n (List.ofFn m)))) = σ
+      rw [h, padFin_ofFn]
+    · intro h
+      rw [← h]
+      exact (ofFn_padFin_of_length (by rw [List.length_ofFn, ht])).symm
+  -- With `F_k`: the forgery probability.
+  have hreal : accept (M.forgeGame A (q.eval n) n) =
+      expect (sample (Fin n → Bool)) fun k => expect (sample (D.Coins n)) fun c =>
+        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval (F n k) = true
+        then (1 : ℝ) else 0 := by
+    rw [accept_forgeGame_eq M A (q.eval n) n g hg_tag hg_acc, ← expect_sample_equiv (key n)]
+    refine congrArg _ (funext fun rg => ?_)
+    rw [← hD n (g rg)]
+    refine congrArg _ (funext fun c => ?_)
+    rw [eval_toOracleAdversary_width₂ D n _ c (hℓ n) (ht n) (F n (key n rg))]
+  -- With a random function: at most `2⁻ⁿ`.
+  have hrand : expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
+      expect (sample (D.Coins n)) fun c =>
+        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
+        then (1 : ℝ) else 0) ≤ (2 : ℝ)⁻¹ ^ n := by
+    have he : ∀ R : (Fin n → Bool) → (Fin n → Bool),
+        (expect (sample (D.Coins n)) fun c =>
+          if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
+          then (1 : ℝ) else 0) =
+        expect (sample (D.Coins n)) fun c =>
+          if (D.toOracleAdversary n (M.msgLen.eval n) (M.tagLen.eval n) ((macBudget q).eval n)
+            c).eval (padFunEquiv (hℓ n) (ht n) R) = true then (1 : ℝ) else 0 := fun R => by
+      refine congrArg _ (funext fun c => ?_)
+      rw [eval_toOracleAdversary_width₂ D n _ c (hℓ n) (ht n) R]
+      rfl
+    simp only [he]
+    rw [expect_sample_equiv (padFunEquiv (hℓ n) (ht n)) (fun R' =>
+      expect (sample (D.Coins n)) fun c =>
+        if (D.toOracleAdversary n (M.msgLen.eval n) (M.tagLen.eval n) ((macBudget q).eval n)
+          c).eval R' = true then (1 : ℝ) else 0)]
+    simp only [hD n]
+    rw [expect_sample_comm]
+    refine (expect_mono _ fun r => expect_fnForge_random_le _).trans (le_of_eq ?_)
+    rw [expect_const, ht n, inv_pow]
+  -- The PRF advantage is the gap.
+  rw [hreal, TCSlib.Cryptography.prfAdv_eq_expect (F n) (D.toOracleAdversary n n n _)]
+  linarith [le_abs_self ((expect (sample (Fin n → Bool)) fun k => expect (sample (D.Coins n))
+    fun c => if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval (F n k) = true
+      then (1 : ℝ) else 0) -
+    expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
+      expect (sample (D.Coins n)) fun c =>
+        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
+        then (1 : ℝ) else 0))]
+
+end TCSlib.Cryptography.Authentication.PRFMAC
diff --git a/TCSlib/Cryptography/Authentication/MAC/FromPRF/Game.lean b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Game.lean
new file mode 100644
index 000000000..2281b4619
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Game.lean
@@ -0,0 +1,99 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
+import TCSlib.Cryptography.Authentication.MAC.Defs
+import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The forgery game of a MAC with a deterministic tag
+
+Step 3 of the proof of [PS10, Theorem 135.4], on the game side: when a MAC's tagging algorithm
+returns, on the key of the generator coins `rg`, a tag `g rg m` that does not depend on its own
+coins, and verification accepts `(m, σ)` exactly when `g rg m = σ`, the forgery probability is the
+average over the coins `rg` of the probability that the forger forges against the tagging oracle of
+the function `g rg` (`accept_forgeGame_eq`). The forger's codec is the bit codec
+(`forgerCodec_eq_bitCodec`).
+
+## Main results
+
+* `PRFMAC.forgerCodec_eq_bitCodec`: the forger codec of a MAC is the bit codec.
+* `PRFMAC.accept_forgeGame_eq`: the forgery game with a deterministic tag.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Definition 134.2 and Theorem 135.4 (book pp. 134–135).
+-/
+
+namespace TCSlib.Cryptography.Authentication.PRFMAC
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+
+/-- **The MAC forger codec is the bit codec** with message-length queries, tag-length answers and
+a message-plus-tag-length output: `M.forgerCodec n = bitCodec (fun _ => msgLen(n))
+(fun _ => tagLen(n)) (msgLen(n) + tagLen(n))`.
+
+**Proof sketch.** Codec extensionality (`MachineCodec.ext_of_fields`) on the published decoding,
+entry-encoding and timeout equations (`forgerCodec_decodeMove`, `forgerCodec_encodeEntry`,
+`forgerCodec_timeout`) and those of the bit codec. -/
+theorem forgerCodec_eq_bitCodec (M : MAC) (n : ℕ) :
+    M.forgerCodec n =
+      bitCodec (fun _ : Fin 1 => M.msgLen.eval n) (fun _ : Fin 1 => M.tagLen.eval n)
+        (M.msgLen.eval n + M.tagLen.eval n) := by
+  apply MachineCodec.ext_of_fields
+  · funext w
+    exact (M.forgerCodec_decodeMove n w).trans
+      (bitCodec_decodeMove (fun _ : Fin 1 => M.msgLen.eval n)
+        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) w).symm
+  · funext e
+    exact (M.forgerCodec_encodeEntry n e).trans
+      (bitCodec_encodeEntry (fun _ : Fin 1 => M.msgLen.eval n)
+        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) e).symm
+  · exact (M.forgerCodec_timeout n).trans
+      (bitCodec_timeout (fun _ : Fin 1 => M.msgLen.eval n)
+        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n)).symm
+
+/-- **The forgery game with a deterministic tag** [PS10, Definition 134.2]: if, on the key of the
+generator coins `rg`, tagging `m` returns `g rg m` whatever its coins, and verification accepts
+`(m, σ)` exactly when `g rg m = σ`, then
+`Pr[forgeGame A b n] = 𝔼_rg 𝔼_r Pr[FnForge (g rg) | simulate (fnImpl (g rg)).withLog (A.toComp … r)
+((), [])]`.
+
+**Proof sketch.** Unfold the game (`forgeGame_eq`, `prob_bind`) and the codec
+(`forgerCodec_eq_bitCodec`). Each call of the logged tagging oracle draws tag coins and returns
+`g rg m` (`tagImpl_eq`, `htag`), so it has the law of the logged `fnImpl (g rg)`
+(`expect_const`), and so do whole runs (`expect_simulate_congr`). The winning test is `FnForge` by
+`hacc`. -/
+theorem accept_forgeGame_eq (M : MAC) (A : NUPPT) (b n : ℕ)
+    (g : M.gen.Coins n → (Fin (M.msgLen.eval n) → Bool) → (Fin (M.tagLen.eval n) → Bool))
+    (htag : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
+      padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m))
+        rt) = g rg m)
+    (hacc : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
+      M.Accepts n (M.gen.runAt n [] rg) m σ ↔ g rg m = σ) :
+    accept (M.forgeGame A b n) =
+      expect (sample (M.gen.Coins n)) fun rg => expect (sample (A.Coins n)) fun r =>
+        expect (simulate (fnImpl (g rg)).withLog
+            (A.toComp (bitCodec (fun _ : Fin 1 => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
+              (M.msgLen.eval n + M.tagLen.eval n)) n b r) ((), []))
+          (fun res => if FnForge (g rg) res.1 res.2.2 then (1 : ℝ) else 0) := by
+  rw [accept_eq, MAC.forgeGame_eq, prob_bind]
+  refine congrArg _ (funext fun rg => ?_)
+  rw [prob_bind]
+  refine congrArg _ (funext fun r => ?_)
+  rw [prob_bind, forgerCodec_eq_bitCodec,
+    expect_simulate_congr (M.tagImpl n (M.gen.runAt n [] rg)).withLog (fnImpl (g rg)).withLog
+      (fun i x s G => ?_)]
+  · refine congrArg _ (funext fun res => ?_)
+    rw [prob_pure]
+    exact if_congr (by rw [decide_eq_true_iff, fnForge_iff, hacc]) rfl rfl
+  · simp only [QueryImpl.withLog_apply, MAC.tagImpl_eq, QueryImpl.ofComp_apply, fnImpl_apply,
+      expect_bind, expect_pure, OracleComp.pure_bind, htag, expect_const]
+
+end TCSlib.Cryptography.Authentication.PRFMAC
diff --git a/TCSlib/Cryptography/Authentication/MAC/FromPRF/Handler.lean b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Handler.lean
new file mode 100644
index 000000000..1ff897ea4
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Handler.lean
@@ -0,0 +1,446 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Forwarding
+import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
+import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The handler of the PRF-MAC reduction
+
+The distinguisher of [PS10, Theorem 135.4] runs a MAC forger against its own function oracle: it
+answers each tagging query `m` with the oracle's value at `m`, and at the end it asks the oracle at
+the forger's output message `m*` and accepts iff the answer is the output tag `σ*` and `m*` was
+never queried. This file builds it as a `Games.InteractiveHandler` (`macHandler q ℓ t`) with one
+inner and one outer oracle, both with `ℓ(n)`-bit queries and `t(n)`-bit answers.
+
+* **The state** keeps the queried messages, newest first, as blocks `1 ‖ m` of `ℓ(n) + 1` bits,
+  followed by zeros, in `q(n) · (ℓ(n) + 1)` bits (`macState`). A query shifts its block in and
+  drops the last `ℓ(n) + 1` bits, which are zeros while at most `q(n)` messages are stored.
+* **One call** forwards the query and stores it (`macHandler_impl`).
+* **The finalization** asks the outer oracle at the first `ℓ(n)` bits `m*` of the forger's output
+  and returns the bit `[y = σ*] ∧ [m* fresh]`, where `σ*` is the rest of the output and `y` the
+  answer; freshness is read from the state block by block with the chunk map `NMSim.chunkMap`
+  (`macHandler_finish`).
+
+## Main definitions
+
+* `PRFMAC.blockLen`, `PRFMAC.macStLen`: the block and state lengths.
+* `PRFMAC.blocks`, `PRFMAC.macState`: the encoded state of a list of queried messages.
+* `PRFMAC.macHandler q ℓ t`: the handler.
+
+## Main results
+
+* `PRFMAC.finish_of_query_padFin`: a finalization with one outer query (generic).
+* `PRFMAC.macHandler_impl`, `PRFMAC.macHandler_finish`: the handler's call and finalization on
+  encoded states; `PRFMAC.macHandler_init_eq`: the initial state.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 135.4 (book p. 135).
+-/
+
+namespace TCSlib.Cryptography.Authentication.PRFMAC
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
+open TCSlib.Cryptography.Games.InteractiveHandler (rU rS rI rX rL rAns finA)
+open TCSlib.Cryptography.Composability.NMSim (chunkMap chunkMap_flatten polyTimeComputable_chunkMap)
+
+/-! ### A finalization with one outer query -/
+
+section FinishQuery
+
+variable {k k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}
+
+/-- **A finalization with one outer query, on lists:** if the finalization's first round asks
+the outer query `x'` to oracle `j`, and its second round, with the answer `y` in the outer log,
+returns `⟨[true], b y⟩` with `|b y| = outLen(n)`, then (with `finCall(n) ≥ 1`)
+`H.finish n z ω s a = query j x' (fun y => pure (padFin _ (b y)))`.
+
+**Proof sketch.** As `InteractiveHandler.impl_of_query`: unfold the finalization (`finish_eq`) at
+the budget `finCall = p + 1`; the first round decodes to the query (`decodeBitMove_query`), which
+`buildComp_succ_of_query` asks; after the answer `y` the log encodes as in `hrun₁`
+(`bitCodec_encodeEntry`), and the second round decodes to the output `padFin _ (b y)`
+(`ofFn_padFin_of_length`, `decodeBitMove_ret`, `buildComp_of_ret`). -/
+theorem finish_of_query_padFin (H : InteractiveHandler k din dout k' din' dout') (n : ℕ)
+    (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool)
+    {d : ℕ} (a : Fin d → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
+    (b : (Fin ((dout' j).eval n) → Bool) → List Bool) (hb : ∀ y, (b y).length = H.outLen.eval n)
+    (hfc : 1 ≤ H.finCall.eval n)
+    (hrun₀ : H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
+      []) = pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
+    (hrun₁ : ∀ y, H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
+      (List.ofFn a) (pairEncode (pairEncode (List.replicate j true)
+        (pairEncode (List.ofFn x') (List.ofFn y))) [])) = pairEncode [true] (b y)) :
+    H.finish n z ω s a = .query j x' fun y => .pure (padFin _ (b y)) := by
+  obtain ⟨p, hp⟩ : ∃ p, H.finCall.eval n = p + 1 := ⟨H.finCall.eval n - 1, by omega⟩
+  rw [InteractiveHandler.finish_eq, hp,
+    buildComp_succ_of_query (i := j) (x := x') (by
+      rw [MachineCodec.encodeLog_nil, hrun₀]
+      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x')]
+  congr 1
+  funext y
+  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
+      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
+        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
+    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
+      bitCodec_encodeEntry]
+  refine buildComp_of_ret ?_
+  have h := decodeBitMove_ret (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
+    (H.outLen.eval n) (padFin _ (b y))
+  rwa [ofFn_padFin_of_length (hb y), ← hrun₁, ← hlog] at h
+
+end FinishQuery
+
+/-! ### Lengths and the encoded state -/
+
+/-- The length of a state block, a marker bit and a message: `blockLen ℓ = ℓ + 1`. -/
+def blockLen (ℓ : PolyExpr) : PolyExpr := .add ℓ (.const 1)
+
+/-- `(blockLen ℓ).eval n = ℓ(n) + 1`. -/
+theorem blockLen_eval (ℓ : PolyExpr) (n : ℕ) : (blockLen ℓ).eval n = ℓ.eval n + 1 := by
+  rw [blockLen, PolyExpr.eval_add, PolyExpr.eval_const]
+
+/-- The state length, `q` blocks: `macStLen q ℓ = q · (ℓ + 1)`. -/
+def macStLen (q ℓ : PolyExpr) : PolyExpr := .mul q (blockLen ℓ)
+
+/-- `(macStLen q ℓ).eval n = q(n) · (ℓ(n) + 1)`. -/
+theorem macStLen_eval (q ℓ : PolyExpr) (n : ℕ) :
+    (macStLen q ℓ).eval n = q.eval n * (ℓ.eval n + 1) := by
+  rw [macStLen, PolyExpr.eval_mul, blockLen_eval]
+
+/-- The blocks of a list of messages, each message `m` as `1 ‖ m`:
+`blocks L = (L.map fun m => true :: ⟦m⟧).flatten`. -/
+def blocks {a : ℕ} (L : List (Fin a → Bool)) : List Bool :=
+  (L.map fun m => true :: List.ofFn m).flatten
+
+/-- `blocks L = (L.map fun m => true :: ⟦m⟧).flatten`. -/
+theorem blocks_eq {a : ℕ} (L : List (Fin a → Bool)) :
+    blocks L = (L.map fun m => true :: List.ofFn m).flatten :=
+  rfl
+
+/-- `blocks (m :: L) = true :: ⟦m⟧ ++ blocks L`. -/
+theorem blocks_cons {a : ℕ} (m : Fin a → Bool) (L : List (Fin a → Bool)) :
+    blocks (m :: L) = true :: List.ofFn m ++ blocks L := by
+  rw [blocks_eq, blocks_eq, List.map_cons, List.flatten_cons]
+
+/-- Each block has `a + 1` bits: `|blocks L| = |L| · (a + 1)`. -/
+theorem length_blocks {a : ℕ} (L : List (Fin a → Bool)) :
+    (blocks L).length = L.length * (a + 1) := by
+  induction L with
+  | nil => rw [blocks_eq, List.map_nil, List.flatten_nil, List.length_nil, List.length_nil,
+      Nat.zero_mul]
+  | cons m L ih =>
+    rw [blocks_cons, List.length_append, List.length_cons, List.length_ofFn, ih,
+      List.length_cons]
+    ring
+
+/-! ### The round and the finalization -/
+
+/-- One round of a call: with an empty outer log, ask the outer oracle the query; with the answer
+`y` in the log, return `y` and the state with the block `1 ‖ x` shifted in and cut to `q(n)` blocks.
+-/
+private def macRun (q ℓ : PolyExpr) (w : List Bool) : List Bool :=
+  if decide (rL w = []) then pairEncode [false] (pairEncode (rI w) (rX w))
+  else pairEncode [true]
+    (rAns w ++ ([true] ++ rX w ++ rS w).take ((macStLen q ℓ).eval (rU w).length))
+
+/-- The round is polynomial-time. -/
+private theorem polyTimeComputable_macRun (q ℓ : PolyExpr) : PolyTimeComputable (macRun q ℓ) := by
+  have hcut : PolyTimeComputable fun w : List Bool =>
+      ([true] ++ rX w ++ rS w).take ((macStLen q ℓ).eval (rU w).length) :=
+    ((polyTimeComputable_pairTakePoly (macStLen q ℓ)).comp
+      (InteractiveHandler.polyTimeComputable_rU.pairEncode
+        (((polyTimeComputable_const [true]).append InteractiveHandler.polyTimeComputable_rX).append
+          InteractiveHandler.polyTimeComputable_rS))).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+  exact polyTimeComputable_ite
+    (polyTimeComputable_isNil.comp InteractiveHandler.polyTimeComputable_rL)
+    ((polyTimeComputable_const [false]).pairEncode
+      (InteractiveHandler.polyTimeComputable_rI.pairEncode
+        InteractiveHandler.polyTimeComputable_rX))
+    ((polyTimeComputable_const [true]).pairEncode
+      (InteractiveHandler.polyTimeComputable_rAns.append hcut))
+
+/-- The output message of a finalization input: the first `ℓ(n)` bits of the forger's output. -/
+private def msgOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
+  (finA w).take (ℓ.eval (rU w).length)
+
+/-- The output tag of a finalization input: the forger's output after its first `ℓ(n)` bits. -/
+private def sigOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
+  (finA w).drop (ℓ.eval (rU w).length)
+
+/-- The emission of the freshness test on a block: `[true]` iff the block is `1 ‖ m*`, where `m*`
+is the second component of the context. -/
+private def hitEmit (ctx ch : List Bool) : List Bool :=
+  if decide (ch = [true] ++ pairSndD ctx) then [true] else []
+
+/-- The blocks of the state equal to `1 ‖ m*`, one `true` each (a chunk map over the state). -/
+private def hitsOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
+  chunkMap (blockLen ℓ) hitEmit (pairEncode (pairEncode (rU w) (msgOf ℓ w)) (rS w))
+
+/-- One round of the finalization: with an empty outer log, ask the oracle at `m*`; with the
+answer `y` in the log, return the bit `[y = σ*] ∧ [no block is 1 ‖ m*]`. -/
+private def macFin (ℓ : PolyExpr) (w : List Bool) : List Bool :=
+  if decide (rL w = []) then pairEncode [false] (pairEncode [] (msgOf ℓ w))
+  else pairEncode [true]
+    (if decide (rAns w = sigOf ℓ w) then [decide (hitsOf ℓ w = [])] else [false])
+
+/-- The finalization round is polynomial-time.
+
+**Proof sketch.** Its pieces are built from the published readers (`rU`, `rL`, `rS`, `rAns`,
+`finA`) with the pair primitives: the message and tag by `polyTimeComputable_pairTakePoly` and
+`polyTimeComputable_pairDropPoly`, the block test by `polyTimeComputable_pairEq`, the freshness
+test by the chunk map (`NMSim.polyTimeComputable_chunkMap`) and `polyTimeComputable_isNil`, and
+the branches by `polyTimeComputable_ite`. -/
+private theorem polyTimeComputable_macFin (ℓ : PolyExpr) : PolyTimeComputable (macFin ℓ) := by
+  have hU := InteractiveHandler.polyTimeComputable_rU
+  have hA := InteractiveHandler.polyTimeComputable_finA
+  have hmsg : PolyTimeComputable (msgOf ℓ) :=
+    ((polyTimeComputable_pairTakePoly ℓ).comp (hU.pairEncode hA)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, msgOf]
+  have hsig : PolyTimeComputable (sigOf ℓ) :=
+    ((polyTimeComputable_pairDropPoly ℓ).comp (hU.pairEncode hA)).congr fun w => by
+      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, sigOf]
+  have hemit : PolyTimeComputable fun z => hitEmit (pairFstD z) (pairSndD z) := by
+    have hc : PolyTimeComputable fun z : List Bool =>
+        [decide (pairSndD z = [true] ++ pairSndD (pairFstD z))] :=
+      (polyTimeComputable_pairEq.comp (polyTimeComputable_pairSndD.pairEncode
+        ((polyTimeComputable_const [true]).append
+          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)))).congr fun z => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
+    exact (polyTimeComputable_ite hc (polyTimeComputable_const [true])
+      (polyTimeComputable_const [])).congr fun z => by simp only [hitEmit]
+  have hhits : PolyTimeComputable (hitsOf ℓ) :=
+    ((polyTimeComputable_chunkMap (blockLen ℓ) hemit).comp
+      ((hU.pairEncode hmsg).pairEncode InteractiveHandler.polyTimeComputable_rS)).congr fun w => by
+      simp only [Function.comp_apply, hitsOf]
+  have hbit : PolyTimeComputable fun w : List Bool =>
+      if decide (rAns w = sigOf ℓ w) then [decide (hitsOf ℓ w = [])] else [false] :=
+    polyTimeComputable_ite
+      ((polyTimeComputable_pairEq.comp
+        (InteractiveHandler.polyTimeComputable_rAns.pairEncode hsig)).congr fun w => by
+        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
+      (polyTimeComputable_isNil.comp hhits) (polyTimeComputable_const [false])
+  exact polyTimeComputable_ite
+    (polyTimeComputable_isNil.comp InteractiveHandler.polyTimeComputable_rL)
+    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hmsg))
+    ((polyTimeComputable_const [true]).pairEncode hbit)
+
+/-! ### The handler -/
+
+/-- **The handler of the PRF-MAC reduction** [PS10, Theorem 135.4, proof], for the query budget
+`q` and `ℓ(n)`-bit messages with `t(n)`-bit tags: one inner and one outer oracle, both with these
+lengths; the state keeps the queried messages in `q(n) · (ℓ(n) + 1)` bits; no seed; one outer
+query per call, which forwards the inner query; the adversary gets the empty input; the
+finalization makes one outer query and returns one bit:
+`(macHandler q ℓ t).stateLen = macStLen q ℓ`, `seedLen = .const 0`,
+`perCall = finCall = outLen = .const 1` and `advIn _ = []` (the `simps` fields). -/
+def macHandler (q ℓ t : PolyExpr) :
+    InteractiveHandler 1 (fun _ => ℓ) (fun _ => t) 1 (fun _ => ℓ) (fun _ => t) where
+  stateLen := macStLen q ℓ
+  seedLen := .const 0
+  perCall := .const 1
+  init _ := zeroBits _
+  run := macRun q ℓ
+  poly := polyTimeComputable_macRun q ℓ
+  advIn _ := []
+  advIn_poly := polyTimeComputable_const []
+  outLen := .const 1
+  finCall := .const 1
+  finRun := macFin ℓ
+  finRun_poly := polyTimeComputable_macFin ℓ
+
+attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall]
+  macHandler
+
+variable (q ℓ t : PolyExpr)
+
+/-- **The encoded state** of the queried messages `L` (newest first): their blocks `1 ‖ m`,
+followed by zeros, read at the state length: `macState q ℓ t n L = padFin _ (blocks L)`. -/
+def macState (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) :
+    Fin ((macHandler q ℓ t).stateLen.eval n) → Bool :=
+  padFin _ (blocks L)
+
+/-- `macState q ℓ t n L = padFin _ (blocks L)`. -/
+theorem macState_eq (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) :
+    macState q ℓ t n L = padFin _ (blocks L) :=
+  rfl
+
+/-- The state has `q(n) · (ℓ(n) + 1)` bits:
+`(macHandler q ℓ t).stateLen.eval n = q(n) · (ℓ(n) + 1)`. -/
+theorem macHandler_stateLen_eval (n : ℕ) :
+    (macHandler q ℓ t).stateLen.eval n = q.eval n * (ℓ.eval n + 1) := by
+  rw [macHandler_stateLen, macStLen_eval]
+
+/-- **The initial state stores no message:** `(macHandler q ℓ t).init n = macState q ℓ t n []`. -/
+theorem macHandler_init_eq (n : ℕ) : (macHandler q ℓ t).init n = macState q ℓ t n [] := by
+  funext j
+  rw [macHandler_init, macState_eq, zeroBits_apply, padFin_def, blocks_eq, List.map_nil,
+    List.flatten_nil]
+  rfl
+
+/-- The encoded state of at most `q(n)` messages is their blocks followed by zeros:
+`⟦macState q ℓ t n L⟧ = blocks L ++ 0^{q(n)(ℓ(n)+1) − |L|(ℓ(n)+1)}`. -/
+theorem ofFn_macState (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) (hL : L.length ≤ q.eval n) :
+    List.ofFn (macState q ℓ t n L) = blocks L ++
+      List.replicate (q.eval n * (ℓ.eval n + 1) - L.length * (ℓ.eval n + 1)) false := by
+  rw [macState_eq, Collection.ofFn_padFin_of_le, length_blocks, macHandler_stateLen_eval]
+  rw [macHandler_stateLen_eval, length_blocks]
+  exact Nat.mul_le_mul_right _ hL
+
+/-! ### The call -/
+
+/-- **One call forwards the query and stores it:** from the encoded state of `L` with
+`|L| < q(n)`, the inner query `x` is the outer query `x`, answered with the outer answer `y` and
+the state of `x :: L`: `(macHandler q ℓ t).impl n z ω i x (macState q ℓ t n L) =
+query i x (fun y => pure (y, macState q ℓ t n (x :: L)))`.
+
+**Proof sketch.** `InteractiveHandler.impl_of_query_padFin` with one outer query: the first round
+has an empty outer log (`rL_input`) and asks `⟨1^i, x⟩` (`rI_input`, `rX_input`); the second reads
+the answer (`rAns_input`) and returns it with `(1 ‖ x ‖ ⟦s⟧)` cut to `q(n)(ℓ(n) + 1)` bits. With
+`⟦s⟧ = blocks L ‖ 0…0` (`ofFn_macState`) the cut drops `ℓ(n) + 1` zeros (`List.take_append`,
+`List.take_replicate`) and leaves the encoded state of `x :: L`. -/
+theorem macHandler_impl (n : ℕ) (z : List Bool) (ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool)
+    (i : Fin 1) (x : Fin (ℓ.eval n) → Bool) (L : List (Fin (ℓ.eval n) → Bool))
+    (hL : L.length < q.eval n) :
+    (macHandler q ℓ t).impl n z ω i x (macState q ℓ t n L) =
+      .query i x fun y => .pure (y, macState q ℓ t n (x :: L)) := by
+  have hN := macHandler_stateLen_eval q ℓ t n
+  have hcut : ([true] ++ List.ofFn x ++ List.ofFn (macState q ℓ t n L)).take
+      ((macStLen q ℓ).eval (List.replicate n true).length) =
+      List.ofFn (macState q ℓ t n (x :: L)) := by
+    have hle : (L.length + 1) * (ℓ.eval n + 1) ≤ q.eval n * (ℓ.eval n + 1) :=
+      Nat.mul_le_mul_right _ hL
+    rw [List.length_replicate, macStLen_eval, ofFn_macState q ℓ t n L hL.le,
+      ofFn_macState q ℓ t n (x :: L) hL, blocks_cons, List.length_cons]
+    have hB : ([true] ++ List.ofFn x ++ blocks L).length = (L.length + 1) * (ℓ.eval n + 1) := by
+      rw [List.length_append, List.length_append, List.length_ofFn, length_blocks]
+      simp only [List.length_singleton]
+      ring
+    rw [← List.append_assoc, List.take_append, List.take_of_length_le (by rw [hB]; exact hle), hB,
+      List.take_replicate]
+    have hmin : min (q.eval n * (ℓ.eval n + 1) - (L.length + 1) * (ℓ.eval n + 1))
+        (q.eval n * (ℓ.eval n + 1) - L.length * (ℓ.eval n + 1)) =
+        q.eval n * (ℓ.eval n + 1) - (L.length + 1) * (ℓ.eval n + 1) :=
+      Nat.min_eq_left (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _)
+    rw [hmin]
+    simp only [List.cons_append, List.nil_append, List.append_assoc]
+  refine (InteractiveHandler.impl_of_query_padFin _ n z ω i x (macState q ℓ t n L) i x
+    (fun y => List.ofFn y) (fun _ => List.ofFn (macState q ℓ t n (x :: L)))
+    (fun y => List.length_ofFn) (fun _ => List.length_ofFn)
+    (by rw [macHandler_perCall, PolyExpr.eval_const]) ?_ fun y => ?_).trans ?_
+  · show macRun q ℓ _ = _
+    rw [macRun, InteractiveHandler.rL_input, InteractiveHandler.rI_input,
+      InteractiveHandler.rX_input, if_pos (decide_eq_true rfl)]
+  · show macRun q ℓ _ = _
+    rw [macRun, InteractiveHandler.rL_input, InteractiveHandler.rAns_input,
+      InteractiveHandler.rX_input, InteractiveHandler.rS_input, InteractiveHandler.rU_input,
+      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)), hcut]
+  · simp only [padFin_ofFn]
+
+/-! ### The finalization -/
+
+/-- The freshness test on the encoded state of at most `q(n)` messages: no block is `1 ‖ u` iff no
+stored message has the list `u`: `chunkMap … ⟨⟨1^n, u⟩, ⟦macState q ℓ t n L⟧⟩ = [] ↔
+∀ m ∈ L, ⟦m⟧ ≠ u`.
+
+**Proof sketch.** The state is the concatenation of the blocks `1 ‖ m` and of `q(n) − |L|` zero
+blocks, all of `ℓ(n) + 1 > 0` bits (`ofFn_macState`, `List.flatten_replicate_replicate`), so the
+chunk map emits `hitEmit` of each block (`NMSim.chunkMap_flatten`), and the result is empty iff
+every emission is (`List.flatten_eq_nil_iff`). A block `1 ‖ m` emits iff `⟦m⟧ = u`
+(`List.cons_injective`); a zero block starts with `0` and never emits. -/
+private theorem hits_nil_iff (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool))
+    (hL : L.length ≤ q.eval n) (u : List Bool) :
+    chunkMap (blockLen ℓ) hitEmit (pairEncode (pairEncode (List.replicate n true) u)
+        (List.ofFn (macState q ℓ t n L))) = [] ↔ ∀ m ∈ L, List.ofFn m ≠ u := by
+  have hflat : List.ofFn (macState q ℓ t n L) =
+      (L.map (fun m => true :: List.ofFn m) ++
+        List.replicate (q.eval n - L.length) (List.replicate (ℓ.eval n + 1) false)).flatten := by
+    rw [ofFn_macState q ℓ t n L hL, List.flatten_append, List.flatten_replicate_replicate,
+      blocks_eq, Nat.sub_mul]
+  have hlen : ∀ ch ∈ L.map (fun m => true :: List.ofFn m) ++
+      List.replicate (q.eval n - L.length) (List.replicate (ℓ.eval n + 1) false),
+      ch.length = (blockLen ℓ).eval n := by
+    intro ch hch
+    rw [blockLen_eval]
+    rcases List.mem_append.1 hch with h | h
+    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
+      rw [List.length_cons, List.length_ofFn]
+    · rw [List.eq_of_mem_replicate h, List.length_replicate]
+  rw [hflat, chunkMap_flatten (blockLen ℓ) hitEmit n u _ hlen
+    (by rw [blockLen_eval]; omega), List.flatten_eq_nil_iff]
+  constructor
+  · intro h m hm hmu
+    have := h _ (List.mem_map.2 ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩), rfl⟩)
+    rw [hitEmit, pairSndD_pairEncode, if_pos (decide_eq_true (by rw [hmu]; rfl))] at this
+    exact List.cons_ne_nil _ _ this
+  · intro h x hx
+    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hx
+    rcases List.mem_append.1 hch with hc | hc
+    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
+      rw [hitEmit, pairSndD_pairEncode, if_neg]
+      intro he
+      exact h m hm (List.cons_injective (of_decide_eq_true he))
+    · rw [List.eq_of_mem_replicate hc, hitEmit, pairSndD_pairEncode, if_neg]
+      intro he
+      have := of_decide_eq_true he
+      rw [List.replicate_succ] at this
+      exact Bool.false_ne_true (List.cons_eq_cons.1 this).1
+
+/-- **The finalization** from the encoded state of `L` with `|L| ≤ q(n)`, after the output `a`
+of at least `ℓ(n)` bits: ask the oracle at `m* = a[0, ℓ(n))` and output the bit
+`[⟦y⟧ = a[ℓ(n), …)] ∧ [∀ m ∈ L, ⟦m⟧ ≠ ⟦m*⟧]` for its answer `y`:
+`(macHandler q ℓ t).finish n z ω (macState q ℓ t n L) a = query 0 (padFin _ (⟦a⟧.take ℓ(n)))
+(fun y => pure (padFin _ [decide (⟦y⟧ = ⟦a⟧.drop ℓ(n)) && decide (∀ m ∈ L, ⟦m⟧ ≠ ⟦a⟧.take ℓ(n))]))`.
+
+**Proof sketch.** `finish_of_query_padFin`. The first round has an empty outer log
+(`rL_finInput`) and asks the first `ℓ(n)` bits of `a` (`finA_finInput`, `rU_finInput`). The second
+reads the answer `y` from the one-entry log (`rAns_eq`, `rL_finInput`) and compares it with the rest
+of `a`; the freshness test reads the state block by block (`NMSim.chunkMap_flatten` on the blocks
+and the zero blocks, `ofFn_macState`): a zero block never starts with the marker bit. -/
+theorem macHandler_finish (n : ℕ) (z : List Bool)
+    (ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool) (L : List (Fin (ℓ.eval n) → Bool))
+    (hL : L.length ≤ q.eval n) {d : ℕ} (a : Fin d → Bool) (hd : ℓ.eval n ≤ d) :
+    (macHandler q ℓ t).finish n z ω (macState q ℓ t n L) a =
+      .query 0 (padFin _ ((List.ofFn a).take (ℓ.eval n))) fun y =>
+        .pure (padFin _ [decide (List.ofFn y = (List.ofFn a).drop (ℓ.eval n)) &&
+          decide (∀ m ∈ L, List.ofFn m ≠ (List.ofFn a).take (ℓ.eval n))]) := by
+  have htake : ((List.ofFn a).take (ℓ.eval n)).length = ℓ.eval n := by
+    rw [List.length_take, List.length_ofFn, Nat.min_eq_left hd]
+  have hx : List.ofFn (padFin (ℓ.eval n) ((List.ofFn a).take (ℓ.eval n))) =
+      (List.ofFn a).take (ℓ.eval n) := ofFn_padFin_of_length htake
+  refine finish_of_query_padFin _ n z ω (macState q ℓ t n L) a 0
+    (padFin _ ((List.ofFn a).take (ℓ.eval n))) _ (fun y => by
+      rw [List.length_singleton, macHandler_outLen, PolyExpr.eval_const])
+    (by rw [macHandler_finCall, PolyExpr.eval_const]) ?_ fun y => ?_
+  · show macFin ℓ _ = _
+    rw [macFin, InteractiveHandler.rL_finInput, if_pos (decide_eq_true rfl), msgOf,
+      InteractiveHandler.finA_finInput, InteractiveHandler.rU_finInput, List.length_replicate, hx]
+    rfl
+  · show macFin ℓ _ = _
+    have hans : rAns (InteractiveHandler.finInput n z (List.ofFn ω)
+        (List.ofFn (macState q ℓ t n L)) (List.ofFn a)
+        (pairEncode (pairEncode (List.replicate ((0 : Fin 1) : ℕ) true)
+          (pairEncode (List.ofFn (padFin (ℓ.eval n) ((List.ofFn a).take (ℓ.eval n))))
+            (List.ofFn y))) [])) = List.ofFn y := by
+      rw [InteractiveHandler.rAns_eq, InteractiveHandler.rL_finInput, pairFstD_pairEncode,
+        pairSndD_pairEncode, pairSndD_pairEncode]
+    rw [macFin, InteractiveHandler.rL_finInput,
+      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)), hans, sigOf, hitsOf, msgOf,
+      InteractiveHandler.finA_finInput, InteractiveHandler.rU_finInput,
+      InteractiveHandler.rS_finInput, List.length_replicate]
+    congr 1
+    by_cases hy : List.ofFn y = (List.ofFn a).drop (ℓ.eval n)
+    · rw [if_pos (decide_eq_true hy), decide_eq_true hy, Bool.true_and]
+      congr 1
+      exact decide_eq_decide.2 (hits_nil_iff q ℓ t n L hL _)
+    · rw [if_neg (fun h => hy (of_decide_eq_true h)), decide_eq_false hy, Bool.false_and]
+
+end TCSlib.Cryptography.Authentication.PRFMAC
diff --git a/TCSlib/Cryptography/Authentication/MAC/FromPRF/Random.lean b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Random.lean
new file mode 100644
index 000000000..b524809cb
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Random.lean
@@ -0,0 +1,155 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
+import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Forging against a random function
+
+Step 4 of the proof of [PS10, Theorem 135.4]: against a uniform random function `R`, a forgery
+`(m, σ)` with `m` never queried is a guess of the value `R m`, which is uniform and independent of
+everything the forger saw, so every forger (whatever its number of queries) forges with probability
+at most `2^{-t}` for `t`-bit tags (`expect_fnForge_random_le`).
+
+The proof samples `R` lazily along the run, with the table override `ETTGame.ovr` of the
+encrypt-then-tag proof: a new query `x` reads `R x`, which `ETTGame.expect_sample_ovr` moves into
+the table; a repeated query reads the table. Every table key is a queried message, so at the end a
+fresh message is not a key, and its value is `R` there, uniform (`expect_sample_coord`,
+`expect_sample_mem_le`).
+
+## Main results
+
+* `PRFMAC.expect_fnForge_random_le`: the forgery probability against a random function is at most
+  `2^{-t}` (checkpoint 2).
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 135.4 (book p. 135).
+-/
+
+namespace TCSlib.Cryptography.Authentication.PRFMAC
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+open TCSlib.Cryptography.Composability.ETTGame (ovr ovr_nil ovr_of_mem ovr_of_not_mem
+  expect_sample_ovr)
+
+variable {a b : ℕ}
+
+/-- A fresh message's value under a random function is a guess: for an output `w` whose message is
+no key of the table `M` and was not queried, the forgery probability against `ovr M R`, averaged
+over a uniform `R`, is at most `2^{-b}`; a queried message is no forgery:
+`𝔼_R [FnForge (ovr M R) w log] ≤ 2^{-b}` when every key of `M` is queried.
+
+**Proof sketch.** If the message `m = (splitBits w).1` was queried, there is no forgery
+(`mem_queried`). Otherwise it is no key of `M`, so `ovr M R m = R m` (`ovr_of_not_mem`) and a
+forgery needs `R m = σ`; the coordinate `R m` of a uniform table is uniform
+(`expect_sample_coord`), and hits the one value `σ` with probability `1 / 2^b`
+(`expect_sample_mem_le`, `Fintype.card_fun`). This re-derives, from the published `ovr` readers,
+the fresh-point case of the private `ETTGame.expect_hitW_le` (disclosed). -/
+private theorem expect_forge_pure_le (w : Fin (a + b) → Bool)
+    (M : List ((Fin a → Bool) × (Fin b → Bool)))
+    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
+    (hM : ∀ p ∈ M.map Prod.fst, p ∈ queried log) :
+    expect (sample ((Fin a → Bool) → (Fin b → Bool)))
+        (fun R => if FnForge (ovr M R) w log then (1 : ℝ) else 0) ≤ ((2 : ℝ) ^ b)⁻¹ := by
+  have hδ : (0 : ℝ) ≤ ((2 : ℝ) ^ b)⁻¹ := by positivity
+  by_cases hq : (splitBits w).1 ∈ queried log
+  · have h0 : (fun R => if FnForge (ovr M R) w log then (1 : ℝ) else 0) = fun _ => 0 := by
+      funext R
+      refine if_neg fun h => ?_
+      obtain ⟨e, he, hem⟩ := (mem_queried log _).1 hq
+      exact ((fnForge_iff _ _ _).1 h).2 e he hem
+    rw [h0, expect_const]
+    exact hδ
+  · have hk : (splitBits w).1 ∉ M.map Prod.fst := fun h => hq (hM _ h)
+    have hle : ∀ R : (Fin a → Bool) → (Fin b → Bool),
+        (if FnForge (ovr M R) w log then (1 : ℝ) else 0) ≤
+          if R (splitBits w).1 ∈ [(splitBits w).2] then 1 else 0 := by
+      intro R
+      by_cases h : FnForge (ovr M R) w log
+      · rw [if_pos h, if_pos]
+        rw [List.mem_singleton, ← ovr_of_not_mem hk R]
+        exact ((fnForge_iff _ _ _).1 h).1
+      · rw [if_neg h]
+        split <;> norm_num
+    refine (expect_mono _ hle).trans ?_
+    rw [expect_sample_coord (splitBits w).1 (fun y (_ : (Fin a → Bool) → (Fin b → Bool)) =>
+      if y ∈ [(splitBits w).2] then (1 : ℝ) else 0) (fun _ _ _ => rfl)]
+    simp only [expect_const]
+    refine (expect_sample_mem_le _).trans (le_of_eq ?_)
+    rw [List.length_singleton, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
+    push_cast
+    rw [one_div]
+
+/-- **Lazy forging against a random function:** from a log `log` and a table `M` whose keys are
+all queried, the forgery probability against `ovr M R`, averaged over a uniform `R`, is at most
+`2^{-b}`:
+`𝔼_R Pr[FnForge (ovr M R) | simulate (fnImpl (ovr M R)).withLog c ((), log)] ≤ 2^{-b}`.
+
+**Proof sketch.** Induction on `c`. A return is `expect_forge_pure_le`. A query `x` that is a key
+reads the table (`ovr_of_mem`); the continuation starts from the longer log with the same table. A
+new query reads `R x` (`ovr_of_not_mem`), which `expect_sample_ovr` moves into the table as a
+uniform `y`; the new key `x` is queried, and the continuation's bound holds for every `y`. -/
+private theorem expect_forge_ovr_le
+    (c : OracleComp (bitSpec (fun _ : Fin 1 => a) (fun _ => b)) (Fin (a + b) → Bool))
+    (M : List ((Fin a → Bool) × (Fin b → Bool)))
+    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
+    (hM : ∀ p ∈ M.map Prod.fst, p ∈ queried log) :
+    expect (sample ((Fin a → Bool) → (Fin b → Bool))) (fun R =>
+      expect (simulate (fnImpl (ovr M R)).withLog c ((), log))
+        (fun res => if FnForge (ovr M R) res.1 res.2.2 then (1 : ℝ) else 0)) ≤
+      ((2 : ℝ) ^ b)⁻¹ := by
+  induction c generalizing M log with
+  | pure w =>
+    simp only [simulate_pure, expect_pure]
+    exact expect_forge_pure_le w M log hM
+  | query i x k ih =>
+    simp only [simulate_query, QueryImpl.withLog_apply, fnImpl_apply, OracleComp.pure_bind]
+    by_cases hx : x ∈ M.map Prod.fst
+    · have e : ∀ R : (Fin a → Bool) → (Fin b → Bool),
+          ovr M R x = ovr M (fun _ _ => false) x := fun R => ovr_of_mem hx R _
+      simp only [e]
+      refine ih _ M _ fun p hp => ?_
+      rw [queried_append]
+      exact List.mem_cons_of_mem _ (hM p hp)
+    · have e : ∀ R : (Fin a → Bool) → (Fin b → Bool), ovr M R x = R x :=
+        fun R => ovr_of_not_mem hx R
+      simp only [e]
+      have hF := expect_sample_ovr M hx
+        (fun (y : Fin b → Bool) (g : (Fin a → Bool) → (Fin b → Bool)) =>
+          expect (simulate (fnImpl g).withLog (k y) ((), log ++ [⟨i, x, y⟩]))
+            (fun res => if FnForge g res.1 res.2.2 then (1 : ℝ) else 0))
+      rw [hF]
+      refine (expect_mono _ fun y => ih y ((x, y) :: M) _ fun p hp => ?_).trans
+        (le_of_eq (expect_const _ _))
+      rw [queried_append]
+      rw [List.map_cons, List.mem_cons] at hp
+      rcases hp with rfl | hp
+      · exact List.mem_cons_self
+      · exact List.mem_cons_of_mem _ (hM p hp)
+
+/-- **Forging against a random function** [PS10, Theorem 135.4, proof, step 4]: every forger
+computation `c` with `a`-bit messages and `b`-bit tags, run against the tagging oracle of a uniform
+random function `R`, forges with probability at most `2^{-b}`:
+`𝔼_R Pr[FnForge R | simulate (fnImpl R).withLog c ((), [])] ≤ 2^{-b}`.
+
+**Proof sketch.** `expect_forge_ovr_le` from the empty table and the empty log (`ovr_nil`). -/
+theorem expect_fnForge_random_le
+    (c : OracleComp (bitSpec (fun _ : Fin 1 => a) (fun _ => b)) (Fin (a + b) → Bool)) :
+    expect (sample ((Fin a → Bool) → (Fin b → Bool))) (fun R =>
+      expect (simulate (fnImpl R).withLog c ((), []))
+        (fun res => if FnForge R res.1 res.2.2 then (1 : ℝ) else 0)) ≤ ((2 : ℝ) ^ b)⁻¹ := by
+  refine le_of_eq_of_le (congrArg _ (funext fun R => ?_))
+    (expect_forge_ovr_le c [] [] fun p hp => by
+      rw [List.map_nil] at hp
+      exact absurd hp List.not_mem_nil)
+  rw [ovr_nil]
+
+end TCSlib.Cryptography.Authentication.PRFMAC
diff --git a/TCSlib/Cryptography/Authentication/MAC/FromPRF/Reduction.lean b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Reduction.lean
new file mode 100644
index 000000000..fea7c8943
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/MAC/FromPRF/Reduction.lean
@@ -0,0 +1,326 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
+import TCSlib.Cryptography.Authentication.Encoding
+import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The distinguisher of the PRF-MAC reduction
+
+Steps 2, 3 and 6 of the proof of [PS10, Theorem 135.4], for a forger with `ℓ(n)`-bit messages and
+`t(n)`-bit tags: T2 (`Games.exists_interactiveHandlerMachine`) applied to the handler `macHandler`
+(through the input-free companion `Games.exists_toCompOn_of_toComp`), then T4
+(`Games.exists_toOracleAdversary_of_bitCodec`), give a next-query machine `D` whose acceptance
+probability against any function `f` is the probability that the forger forges against the
+tagging oracle `f`: its output `(m, σ)` has `f m = σ` and `m` was never queried
+(`exists_macReduction`).
+
+The proof answers the handler's outer queries by `f` (`fnImpl`, `simulate_ofComp_pure`) and composes
+the two implementations (`simulate_comp`). From the encoded state of the queried messages, newest
+first (`queried`), each composed call is the logged call of `fnImpl f` with the new state abstracted
+(`macHandler_impl`); the forger asks at most `q(n)` queries, so this holds along every run
+(`Games.simulate_eq_of_abs_bounded`), and the log of every run has at most `q(n)` entries
+(`allOutputs_simulate_withLog_length`). The finalization then tests exactly the forgery
+(`macHandler_finish`).
+
+## Main definitions
+
+* `PRFMAC.fnImpl f`: the tagging oracle of the function `f`.
+* `PRFMAC.FnForge f a log`: the output `a = (m, σ)` is a forgery against `f` given the log.
+* `PRFMAC.queried log`: the queried messages of a log, newest first.
+* `PRFMAC.macBudget q`: the distinguisher's query budget `q · 1 + 1`.
+
+## Main results
+
+* `PRFMAC.allOutputs_simulate_withLog_length`: the log of a run grows by at most its query count.
+* `PRFMAC.exists_macReduction`: the distinguisher (checkpoint 1).
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  Theorem 135.4 (book p. 135).
+-/
+
+namespace TCSlib.Cryptography.Authentication.PRFMAC
+
+open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
+open TCSlib.Cryptography.Composability.ChallengeSim (expect_sample_prod)
+
+/-! ### The tagging oracle of a function and forgeries against it -/
+
+section Fn
+
+variable {a b : ℕ}
+
+/-- **The tagging oracle of the function `f`**: each query `m` is answered `f m`, the state kept:
+`fnImpl f = QueryImpl.ofComp fun _ m => pure (f m)`. -/
+def fnImpl (f : (Fin a → Bool) → (Fin b → Bool)) :
+    QueryImpl (bitSpec (fun _ : Fin 1 => a) (fun _ => b)) Unit unifSpec :=
+  QueryImpl.ofComp fun _ m => .pure (f m)
+
+/-- `fnImpl f = QueryImpl.ofComp fun _ m => pure (f m)`. -/
+theorem fnImpl_eq (f : (Fin a → Bool) → (Fin b → Bool)) :
+    fnImpl f = QueryImpl.ofComp fun _ m => .pure (f m) :=
+  rfl
+
+/-- The tagging oracle of `f` answers `f x`: `fnImpl f i x s = pure (f x, s)`. -/
+theorem fnImpl_apply (f : (Fin a → Bool) → (Fin b → Bool)) (i : Fin 1) (x : Fin a → Bool)
+    (s : Unit) : fnImpl f i x s = .pure (f x, s) := by
+  rw [fnImpl_eq, QueryImpl.ofComp_apply, OracleComp.pure_bind]
+
+/-- **A forgery against `f`** [PS10, Definition 134.2]: the output `w = (m, σ)` (`splitBits`) has
+`f m = σ` and `m` is the message of no entry of the log:
+`FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1`. -/
+def FnForge (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
+    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : Prop :=
+  f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1
+
+/-- `FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1`.
+-/
+theorem fnForge_iff (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
+    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
+    FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1 :=
+  Iff.rfl
+
+/-- Forgeries are decidable, as the conjunction they unfold to (`fnForge_iff`):
+`Decidable (FnForge f w log)` from `f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, …`. -/
+instance (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
+    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : Decidable (FnForge f w log) :=
+  inferInstanceAs (Decidable (_ ∧ _))
+
+/-- **The queried messages of a log**, newest first: `queried log = (log.map (·.2.1)).reverse`. -/
+def queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : List (Fin a → Bool) :=
+  (log.map fun e => e.2.1).reverse
+
+/-- `queried log = (log.map (·.2.1)).reverse`. -/
+theorem queried_eq (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
+    queried log = (log.map fun e => e.2.1).reverse :=
+  rfl
+
+/-- `queried [] = []`. -/
+theorem queried_nil : queried ([] : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) = [] :=
+  rfl
+
+/-- A new entry is the newest message: `queried (log ++ [e]) = e.2.1 :: queried log`. -/
+theorem queried_append (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
+    (e : Σ i, (bitSpec (fun _ : Fin 1 => a) (fun _ => b)).dom i ×
+      (bitSpec (fun _ : Fin 1 => a) (fun _ => b)).rng i) :
+    queried (log ++ [e]) = e.2.1 :: queried log := by
+  rw [queried_eq, queried_eq, List.map_append, List.reverse_append, List.map_singleton,
+    List.reverse_singleton, List.singleton_append]
+
+/-- `|queried log| = |log|`. -/
+theorem length_queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
+    (queried log).length = log.length := by
+  rw [queried_eq, List.length_reverse, List.length_map]
+
+/-- `m ∈ queried log ↔ ∃ e ∈ log, e.2.1 = m`. -/
+theorem mem_queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
+    (m : Fin a → Bool) : m ∈ queried log ↔ ∃ e ∈ log, e.2.1 = m := by
+  rw [queried_eq, List.mem_reverse, List.mem_map]
+
+/-- **A forgery read on lists:** for an output `w` of `a + b` bits, the list test of the
+finalization is the forgery: `(decide (⟦f (padFin a (⟦w⟧.take a))⟧ = ⟦w⟧.drop a) &&
+decide (∀ m ∈ queried log, ⟦m⟧ ≠ ⟦w⟧.take a)) = decide (FnForge f w log)`.
+
+**Proof sketch.** `⟦w⟧ = ⟦m⟧ ++ ⟦σ⟧` for `(m, σ) = splitBits w` (`Fin.append_castAdd_natAdd`,
+`List.ofFn_fin_append`), so the first `a` bits are `⟦m⟧` and the rest `⟦σ⟧`; `List.ofFn` is
+injective, and `queried` lists the logged messages (`mem_queried`). -/
+theorem decide_fnForge (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
+    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
+    (decide (List.ofFn (f (padFin a ((List.ofFn w).take a))) = (List.ofFn w).drop a) &&
+      decide (∀ m ∈ queried log, List.ofFn m ≠ (List.ofFn w).take a)) =
+      decide (FnForge f w log) := by
+  have hw : List.ofFn w = List.ofFn (splitBits w).1 ++ List.ofFn (splitBits w).2 := by
+    rw [← List.ofFn_fin_append,
+      show (splitBits w).1 = fun i => w (Fin.castAdd b i) from funext (splitBits_fst w),
+      show (splitBits w).2 = fun j => w (Fin.natAdd a j) from funext (splitBits_snd w),
+      Fin.append_castAdd_natAdd]
+  have htake : (List.ofFn w).take a = List.ofFn (splitBits w).1 := by
+    rw [hw, List.take_left' List.length_ofFn]
+  have hdrop : (List.ofFn w).drop a = List.ofFn (splitBits w).2 := by
+    rw [hw, List.drop_left' List.length_ofFn]
+  rw [htake, hdrop, padFin_ofFn, ← Bool.decide_and]
+  refine decide_eq_decide.2 ?_
+  rw [fnForge_iff]
+  refine and_congr List.ofFn_inj ⟨fun h e he hm => h e.2.1 ((mem_queried log _).2 ⟨e, he, rfl⟩)
+    (by rw [hm]), fun h m hm hl => ?_⟩
+  obtain ⟨e, he, rfl⟩ := (mem_queried log m).1 hm
+  exact h e he (List.ofFn_inj.1 hl)
+
+end Fn
+
+/-- **The log of a run grows by at most its query count:** for a computation making at most `m`
+queries, every output of the logged simulation from `(s, log)` has a log of at most `|log| + m`
+entries: `(simulate impl.withLog c (s, log)).AllOutputs fun p => |p.2.2| ≤ |log| + m`.
+
+**Proof sketch.** Induction on `c`: a return keeps the log; a query appends one entry
+(`QueryImpl.withLog_apply`) and leaves at most `m - 1` queries (`OracleComp.costBoundedBy_query`).
+-/
+theorem allOutputs_simulate_withLog_length {ι ι' : Type} {spec : OracleSpec ι}
+    {spec' : OracleSpec ι'} {σ α : Type} (impl : QueryImpl spec σ spec') (c : OracleComp spec α)
+    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ) (log : QueryLog spec) :
+    (simulate impl.withLog c (s, log)).AllOutputs fun p => p.2.2.length ≤ log.length + m := by
+  induction c generalizing m s log with
+  | pure a =>
+    rw [simulate_pure, OracleComp.allOutputs_pure]
+    exact Nat.le_add_right _ _
+  | query i x k ih =>
+    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
+    have hm1 : 1 ≤ m := hm
+    rw [simulate_query, QueryImpl.withLog_apply, OracleComp.bind_assoc]
+    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun ys _ => ?_
+    rw [OracleComp.pure_bind]
+    refine OracleComp.AllOutputs.mono (fun p hp => ?_) (ih ys.1 (m - 1) (hk ys.1) ys.2 _)
+    dsimp only at hp
+    rw [List.length_append, List.length_singleton] at hp
+    omega
+
+/-- The distinguisher's query budget, `q` forwarded queries and one final query:
+`macBudget q = q · 1 + 1`. -/
+def macBudget (q : PolyExpr) : PolyExpr := .add (.mul q (.const 1)) (.const 1)
+
+/-- `(macBudget q).eval n = q(n) · 1 + 1`, with the constants read by `PolyExpr.eval`. -/
+theorem macBudget_eval (q : PolyExpr) (n : ℕ) :
+    (macBudget q).eval n = q.eval n * (PolyExpr.const 1).eval n + (PolyExpr.const 1).eval n := by
+  rw [macBudget, PolyExpr.eval_add, PolyExpr.eval_mul]
+
+/-! ### The reduction -/
+
+/-- **The PRF-MAC distinguisher** [PS10, Theorem 135.4, proof, steps 2–3]: for a forger `A` with
+budget `q`, `ℓ(n)`-bit messages and `t(n)`-bit tags, there is a next-query machine `D` such that
+at every `n` and for every function `f : {0,1}^ℓ(n) → {0,1}^t(n)`, `D` with budget `q · 1 + 1`
+accepts against `f` with the probability that `A` forges against the tagging oracle `f`:
+`𝔼_c [D^f(c) = 1] = 𝔼_r Pr[FnForge f | simulate (fnImpl f).withLog (A.toComp … r) ((), [])]`.
+
+**Proof sketch.** `D` is T4 applied to T2's machine `B` for `macHandler q ℓ t` and the input-free
+companion `A'` of `A`. Its coins are, through the bijections of T4, T2 and the companion, an empty
+seed `ω` and `A`'s coins `r` (`expect_sample_equiv`, `ChallengeSim.expect_sample_prod`,
+`expect_sample_comm`); the run does not read `ω` (`expect_const`). For fixed `ω` and `r`, T4 and
+T2 turn `D`'s run against `f` into the evaluation of the reduction with `f`
+(`PRFGame.ofFn_evalFn_toCompOn`), which is its simulation with `fnImpl f`
+(`simulate_ofComp_pure`), composed with the handler (`simulate_bind`, `simulate_comp`). Along
+`A`'s run (at most `q(n)` queries) the composite is the logged `fnImpl f` with the state
+abstracted to the encoded queried messages (`simulate_eq_of_abs_bounded`, `macHandler_impl`). Every
+final log has at most `q(n)` entries (`allOutputs_simulate_withLog_length`), so the finalization
+asks `f` at `m*` and tests `f m* = σ*` and freshness (`macHandler_finish`), which is `FnForge` on
+lists (`decide_fnForge`) after transporting the output width (`expect_toCompOn_outLen`). -/
+theorem exists_macReduction (ℓ t q : PolyExpr) (A : NUPPT) :
+    ∃ D : NUPPT, ∀ (n : ℕ) (f : (Fin (ℓ.eval n) → Bool) → (Fin (t.eval n) → Bool)),
+      expect (ProbComp.sample (D.Coins n))
+          (fun c => if (D.toOracleAdversary n (ℓ.eval n) (t.eval n) ((macBudget q).eval n) c).eval
+            f = true then (1 : ℝ) else 0) =
+        expect (ProbComp.sample (A.Coins n)) fun r =>
+          expect (simulate (fnImpl f).withLog
+              (A.toComp (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
+                (ℓ.eval n + t.eval n)) n (q.eval n) r) ((), []))
+            (fun res => if FnForge f res.1 res.2.2 then (1 : ℝ) else 0) := by
+  obtain ⟨A', -, hA'⟩ := exists_toCompOn_of_toComp A
+  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A' q (fun _ => ℓ) (fun _ => t)
+    (fun _ => ℓ) (fun _ => t) (.add ℓ t) (macHandler q ℓ t)
+  obtain ⟨D, -, hD⟩ := exists_toOracleAdversary_of_bitCodec B ℓ t
+  refine ⟨D, fun n f => ?_⟩
+  obtain ⟨φ₀, hφ₀⟩ := hA' n
+  obtain ⟨φ₂, hφ₂⟩ := hB n
+  obtain ⟨φ₄, hφ₄⟩ := hD n
+  have hQ : q.eval n * (macHandler q ℓ t).perCall.eval n + (macHandler q ℓ t).finCall.eval n =
+      (macBudget q).eval n := by
+    rw [macHandler_perCall, macHandler_finCall, macBudget_eval]
+  have hout : (macHandler q ℓ t).outLen.eval n = 1 := by
+    rw [macHandler_outLen, PolyExpr.eval_const]
+  have hd : (PolyExpr.add ℓ t).eval n = ℓ.eval n + t.eval n := PolyExpr.eval_add ℓ t n
+  -- `D`'s coins are a seed and `A`'s coins.
+  rw [← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂, expect_sample_prod,
+    expect_sample_comm, ← expect_sample_equiv φ₀]
+  refine congrArg _ (funext fun r => ?_)
+  have key : ∀ g : Fin 1 → Bool, (if g 0 = true then (1 : ℝ) else 0) =
+      if (List.ofFn g).headD false = true then 1 else 0 := fun g => by rw [headD_ofFn_one]
+  -- One run of `D` is the forgery test of `A`'s run against `fnImpl f`.
+  have hrun : ∀ ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool,
+      (if (D.toOracleAdversary n (ℓ.eval n) (t.eval n) ((macBudget q).eval n)
+          (φ₄ (φ₂ (ω, φ₀ r)))).eval f = true then (1 : ℝ) else 0) =
+        expect (simulate (fnImpl f).withLog
+            (A.toComp (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
+              (ℓ.eval n + t.eval n)) n (q.eval n) r) ((), []))
+          (fun res => if FnForge f res.1 res.2.2 then (1 : ℝ) else 0) := by
+    intro ω
+    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
+        ((macHandler q ℓ t).outLen.eval n)) n
+        (q.eval n * (macHandler q ℓ t).perCall.eval n + (macHandler q ℓ t).finCall.eval n)
+        [] (φ₂ (ω, φ₀ r)) := hφ₂ [] ω (φ₀ r)
+    rw [hφ₄, ← hQ, key, Composability.PRFGame.ofFn_evalFn_toCompOn hout.symm B n _ []
+      (φ₂ (ω, φ₀ r)), ← h2]
+    set c' := A'.toCompOn (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
+      ((PolyExpr.add ℓ t).eval n)) n (q.eval n) ((macHandler q ℓ t).advInput n [] ω) (φ₀ r)
+      with hc'
+    -- The evaluation with `f` is the simulation with `fnImpl f`.
+    have hev := simulate_ofComp_pure (σ := Unit) (spec' := unifSpec)
+      (fun (_ : Fin 1) (x : Fin (ℓ.eval n) → Bool) => f x)
+      ((simulate ((macHandler q ℓ t).impl n [] ω) c' ((macHandler q ℓ t).init n)).bind
+        (fun res => (macHandler q ℓ t).finish n [] ω res.2 res.1)) ()
+    rw [← fnImpl_eq] at hev
+    have h1 := congrArg (fun c => expect c
+      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
+    simp only [expect_pure] at h1
+    refine h1.symm.trans ?_
+    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
+    simp only [OracleComp.pure_bind]
+    -- The composed calls are the logged calls of `fnImpl f`, the state abstracted.
+    have hstep : ∀ (i : Fin 1) (x : Fin (ℓ.eval n) → Bool)
+        (s : Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n))),
+        s.2.length < q.eval n →
+        ∃ (y : Fin (t.eval n) → Bool)
+          (s' : Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n))),
+          (fnImpl f).withLog i x s = .pure (y, s') ∧ s'.2.length ≤ s.2.length + 1 ∧
+          (fnImpl f).comp ((macHandler q ℓ t).impl n [] ω) i x
+              (macState q ℓ t n (queried s.2), ()) =
+            .pure (y, (macState q ℓ t n (queried s'.2), ())) := by
+      intro i x s hs
+      refine ⟨f x, ((), s.2 ++ [⟨i, x, f x⟩]), ?_, by
+        rw [List.length_append, List.length_singleton], ?_⟩
+      · rw [QueryImpl.withLog_apply, fnImpl_apply, OracleComp.pure_bind]
+      · rw [QueryImpl.comp_apply]
+        dsimp only
+        rw [macHandler_impl q ℓ t n [] ω i x _ (by rwa [length_queried])]
+        simp only [simulate_query, fnImpl_apply, OracleComp.pure_bind, simulate_pure,
+          queried_append]
+    have hinit : (macHandler q ℓ t).init n = macState q ℓ t n
+        (queried ([] : QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)))) := by
+      rw [macHandler_init_eq, queried_nil]
+    have hcost := A'.toCompOn_costBoundedBy (bitCodec (fun _ : Fin 1 => ℓ.eval n)
+      (fun _ => t.eval n) ((PolyExpr.add ℓ t).eval n)) n (q.eval n)
+      ((macHandler q ℓ t).advInput n [] ω) (φ₀ r)
+    rw [hinit, simulate_eq_of_abs_bounded ((fnImpl f).comp ((macHandler q ℓ t).impl n [] ω))
+      (fnImpl f).withLog (fun s => (macState q ℓ t n (queried s.2), ())) (fun s => s.2.length)
+      (q.eval n) hstep c' (q.eval n) hcost ((), []) (Nat.zero_add _).le,
+      expect_bind]
+    simp only [expect_pure]
+    -- The finalization tests the forgery, on lists.
+    let G : List Bool × (Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n)
+        (fun _ => t.eval n))) → ℝ := fun p =>
+      if (decide (List.ofFn (f (padFin (ℓ.eval n) (p.1.take (ℓ.eval n)))) =
+          p.1.drop (ℓ.eval n)) &&
+        decide (∀ m ∈ queried p.2.2, List.ofFn m ≠ p.1.take (ℓ.eval n))) = true
+      then (1 : ℝ) else 0
+    have hall := allOutputs_simulate_withLog_length (fnImpl f) c' (q.eval n) hcost () []
+    rw [expect_congr_of_allOutputs hall (g := fun p => G (List.ofFn p.1, p.2)) fun p hp => ?_]
+    · rw [expect_toCompOn_outLen (fnImpl f).withLog A' n (q.eval n) _ (φ₀ r) ((), []) hd G, hφ₀]
+      refine congrArg _ (funext fun p => ?_)
+      show (if _ = true then (1 : ℝ) else 0) = _
+      rw [decide_fnForge]
+      exact if_congr decide_eq_true_iff rfl rfl
+    · rw [List.length_nil, Nat.zero_add] at hp
+      rw [macHandler_finish q ℓ t n [] ω (queried p.2.2) (by rwa [length_queried]) p.1
+        (by rw [hd]; omega)]
+      simp only [simulate_query, fnImpl_apply, OracleComp.pure_bind, simulate_pure, expect_pure]
+      rw [ofFn_padFin_of_length (by rw [List.length_singleton, hout]), List.headD_cons]
+  simp only [hrun]
+  exact expect_const _ _
+
+end TCSlib.Cryptography.Authentication.PRFMAC

## ===== TCSlib/Cryptography/Authentication/MAC/FromPRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Game
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Bound
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Complexity.Randomized.Repetition
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PRF MAC

[PS10, Protocol 134.3]: for a family `{f_s : {0,1}^n → {0,1}^n}`, `Gen(1^n)` samples a uniform
`n`-bit key, `Tag_k(m) = f_k(m)`, and `Ver_k(m, σ)` accepts iff `f_k(m) = σ`. Theorem 135.4: when
the family is pseudorandom, the MAC is secure.

**The construction.** `F` comes with its polynomial-time evaluator `E` on `⟨s, x⟩` (clause (1) of
the ch. 2–4 layer's `PRF`). `Gen` is the ch. 2–4 layer's coin-key machine (its coins are the key,
`runAt_coinKey`). `Tag` applies `E` to its argument, and `Ver` tests `E ⟨k, m⟩ = σ` with
`polyTimeComputable_pairEq`.

## Main definitions

* `Authentication.prfTagFun`, `Authentication.prfVerFun`: the tagging and verification functions.
* `Authentication.prfMAC`: Protocol 134.3 as a `MAC`, with correctness proved.

## Main results

* `Authentication.prfMAC_secure` (Thm 135.4, proved): a PRF gives a secure MAC, with the forgery
  probability at most `prfAdv(F_n, D) + 2^{-n}` at every `n` for a distinguisher `D`.

## Contents

* `MAC/FromPRF/Handler`: the reduction's handler (forwarded and stored queries, the final query).
* `MAC/FromPRF/Reduction`: the distinguisher, accepting against `f` iff the forger forges against
  the tagging oracle `f`.
* `MAC/FromPRF/Random`: forging against a random function succeeds with probability `≤ 2^{-t}`.
* `MAC/FromPRF/Game`: the forgery game of a MAC with a deterministic tag.
* `MAC/FromPRF/Bound`: the bound `Pr[forge] ≤ prfAdv + 2^{-n}` for a MAC whose tag is a keyed
  family.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Protocol 134.3 and Theorem 135.4 (book pp. 134–135).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The tagging function on the raw machine input: `E` applied to the argument `⟨k, m⟩`. -/
def prfTagFun (E : List Bool → List Bool) : List Bool → List Bool := E ∘ NUPPT.inArg

/-- The raw tagging function returns `E (NUPPT.inArg z)` on input `z`. -/
theorem prfTagFun_eq (E : List Bool → List Bool) (z : List Bool) :
    prfTagFun E z = E (NUPPT.inArg z) := rfl

/-- The verification function on `⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩`: `[true]` iff `E ⟨k, m⟩ = σ`. -/
def prfVerFun (E : List Bool → List Bool) : List Bool → List Bool :=
  (fun z => [decide (pairFstD z = pairSndD z)]) ∘ fun w =>
    pairEncode (E (pairEncode (pairFstD (pairSndD w)) (pairFstD (pairSndD (pairSndD w)))))
      (pairSndD (pairSndD (pairSndD w)))

/-- The raw verifier compares `E ⟨k, m⟩` with `σ`, using the three components decoded from
the input `w` [PS10, Protocol 134.3]. -/
theorem prfVerFun_eq (E : List Bool → List Bool) (w : List Bool) :
    prfVerFun E w =
      [decide (E (pairEncode (pairFstD (pairSndD w)) (pairFstD (pairSndD (pairSndD w)))) =
        pairSndD (pairSndD (pairSndD w)))] := by
  simp only [prfVerFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The tagging function is polynomial-time. -/
theorem polyTimeComputable_prfTagFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfTagFun E) :=
  hE.comp NUPPT.polyTimeComputable_inArg

/-- The verification function is polynomial-time. -/
theorem polyTimeComputable_prfVerFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfVerFun E) := by
  refine polyTimeComputable_pairEq.comp ?_
  refine PolyTimeComputable.pairEncode ?_ ?_
  · exact hE.comp (PolyTimeComputable.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
      (polyTimeComputable_pairFstD.comp
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
  · exact polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- **The PRF MAC** [PS10, Protocol 134.3], with `n`-bit messages and tags, for a family `F` with
evaluator `E`. -/
noncomputable def prfMAC (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) : MAC where
  msgLen := .var
  tagLen := .var
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  tag := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfTagFun hE) (.const 0)
  ver := prfVerFun E
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  tag_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  ver_poly := polyTimeComputable_prfVerFun hE
  correct := by
    intro n m rg rt
    simp only [PolyExpr.eval_var] at m ⊢
    have hlen : (NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).coinLen n = n :=
      (NUPPT.coinLen_eq _ n).trans
        ((congrArg (fun p : PolyExpr => p.eval n)
          (NUPPT.coins_ofPolyTimeUniform polyTimeComputable_pairSndD .var)).trans
            (PolyExpr.eval_var n))
    let k : Fin n → Bool := fun j => rg (Fin.cast hlen.symm j)
    have hk : List.ofFn rg = List.ofFn k := List.ofFn_congr hlen rg
    simp only [runAt_coinKey, hk]
    simp only [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform,
      prfTagFun_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
      pairFstD_pairEncode, pairSndD_pairEncode, hFE, padFin_ofFn,
      prfVerFun_eq, atParam_eq, eq_self_iff_true, decide_true]

attribute [simps (config := { isSimp := false }) msgLen tagLen gen tag ver] prfMAC

/-- **Theorem 135.4: a PRF gives a secure MAC** [PS10, Theorem 135.4]: if `F` is a pseudorandom
function family, the PRF MAC is secure.

**Proof sketch** (the source's, with its bound `ε(n) ≤ prfAdv(F_n, D) + 2^{-n}`).
1. Fix a forger `A` with budget `q`; let `ε(n)` be its forgery probability. `Gen` returns its
   coins, the key (`runAt_coinKey`, read at `n` bits by `NUPPT.coinsEquivPoly`); `Tag` returns
   `E ⟨k, m⟩ = f_k(m)` whatever its (empty) coins (`prfTagFun_eq`, `hFE`); `Ver` accepts `(m, σ)`
   iff `f_k(m) = σ` (`prfVerFun_eq`).
2. The distinguisher `D` (`PRFMAC.exists_macReduction`) runs `A` against its own oracle, answering
   each tagging query `m` with the oracle's value and storing `m` in its state. It then queries
   the oracle at `A`'s output message `m` and outputs `1` iff the answer is `σ` and `m` was not
   stored. It is T2 (`Games.exists_interactiveHandlerMachine`) for the handler
   `PRFMAC.macHandler` (`finCall = 1`, `outLen = 1`, budget `q + 1`) on the input-free companion
   of `A` (`Games.exists_toCompOn_of_toComp`), made an oracle adversary by T4
   (`Games.exists_toOracleAdversary_of_bitCodec`).
3. With the oracle `f_k`, `D` outputs `1` exactly when `A` forges (`PRFMAC.accept_forgeGame_eq`):
   probability `ε(n)`.
4. With a random function, a forgery is a guess of a fresh uniform value: probability at most
   `2^{-n}` (`PRFMAC.expect_fnForge_random_le`, sampling the function lazily by table override).
5. So `ε(n) ≤ prfAdv(F_n, D) + 2^{-n}` at every `n`, `n = 0` included
   (`PRFMAC.exists_forgeGame_le`), which is negligible (`PRF.negligible_prfAdv`, `Negligible.add`,
   `negligible_two_pow_neg`).

The PRF advantage is read through `OracleEnsemble.Indist`, in framework form after the F-1
restatement. -/
theorem prfMAC_secure {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfMAC F E hE hFE).Secure := by
  -- `Gen` returns its coins, and `Tag` returns `E` of its argument.
  have hgen : ∀ n (rg : (prfMAC F E hE hFE).gen.Coins n),
      (prfMAC F E hE hFE).gen.runAt n [] rg = List.ofFn rg := by
    intro n
    have h : ∀ G : NUPPT, G = NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var →
        ∀ rg : G.Coins n, G.runAt n [] rg = List.ofFn rg := by
      rintro G rfl rg
      exact runAt_coinKey .var n rg
    exact h _ (prfMAC_gen F E hE hFE)
  have htagE : ∀ n (w : List Bool) (rt : (prfMAC F E hE hFE).tag.Coins n),
      (prfMAC F E hE hFE).tag.runAt n w rt = E w := by
    intro n w
    have h : ∀ T : NUPPT,
        T = NUPPT.ofPolyTimeUniform (polyTimeComputable_prfTagFun hE) (.const 0) →
        ∀ rt : T.Coins n, T.runAt n w rt = E w := by
      rintro T rfl rt
      rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, prfTagFun_eq, NUPPT.inArg_eq,
        NUPPT.advInput_eq, pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode]
    exact h _ (prfMAC_tag F E hE hFE)
  -- The key is `Gen`'s coins, read at `n` bits.
  have hcoins : (prfMAC F E hE hFE).gen.coins = .var := by
    rw [prfMAC_gen, NUPPT.coins_ofPolyTimeUniform]
  let key : ∀ n, (prfMAC F E hE hFE).gen.Coins n ≃ (Fin n → Bool) := fun n =>
    (NUPPT.coinsEquivPoly hcoins n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))
  have hkey : ∀ n rg, List.ofFn (key n rg) = List.ofFn rg := fun n rg => by
    rw [← NUPPT.coinsEquivPoly_ofFn hcoins n rg]
    exact (List.ofFn_congr (PolyExpr.eval_var n) _).symm
  have hmsg : ∀ n, (prfMAC F E hE hFE).msgLen.eval n = n := fun n => by
    rw [prfMAC_msgLen, PolyExpr.eval_var]
  have htl : ∀ n, (prfMAC F E hE hFE).tagLen.eval n = n := fun n => by
    rw [prfMAC_tagLen, PolyExpr.eval_var]
  -- On the key of `rg`, `E` computes `F_{key rg}` (`hFE`).
  have hEF : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool),
      E (pairEncode ((prfMAC F E hE hFE).gen.runAt n [] rg) (List.ofFn m)) =
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) := by
    intro n rg m
    rw [hgen, ← hFE]
    rw [hkey, ofFn_padFin_of_length (by rw [List.length_ofFn, hmsg])]
  have htag : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool)
      (rt : (prfMAC F E hE hFE).tag.Coins n),
      (prfMAC F E hE hFE).tag.runAt n
          (pairEncode ((prfMAC F E hE hFE).gen.runAt n [] rg) (List.ofFn m)) rt =
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) := fun n rg m rt => by
    rw [htagE, hEF]
  have hacc : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool)
      (σ : Fin ((prfMAC F E hE hFE).tagLen.eval n) → Bool),
      (prfMAC F E hE hFE).Accepts n ((prfMAC F E hE hFE).gen.runAt n [] rg) m σ ↔
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) = List.ofFn σ := by
    intro n rg m σ
    rw [MAC.accepts_iff, prfMAC_ver, prfVerFun_eq, atParam_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hEF, List.singleton_inj, decide_eq_true_iff]
  -- The bound of the reduction, negligible.
  rw [MAC.secure_iff]
  intro A q
  obtain ⟨D, hD⟩ := PRFMAC.exists_forgeGame_le (prfMAC F E hE hFE) F hmsg htl key htag hacc A q
  exact ⟨_, (hF.negligible_prfAdv D (PRFMAC.macBudget q)).add negligible_two_pow_neg, hD⟩

end TCSlib.Cryptography.Authentication

## ===== TCSlib/Cryptography/Authentication/MAC/FromPRF/Handler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Forwarding
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the PRF-MAC reduction

The distinguisher of [PS10, Theorem 135.4] runs a MAC forger against its own function oracle: it
answers each tagging query `m` with the oracle's value at `m`, and at the end it asks the oracle at
the forger's output message `m*` and accepts iff the answer is the output tag `σ*` and `m*` was
never queried. This file builds it as a `Games.InteractiveHandler` (`macHandler q ℓ t`) with one
inner and one outer oracle, both with `ℓ(n)`-bit queries and `t(n)`-bit answers.

* **The state** keeps the queried messages, newest first, as blocks `1 ‖ m` of `ℓ(n) + 1` bits,
  followed by zeros, in `q(n) · (ℓ(n) + 1)` bits (`macState`). A query shifts its block in and
  drops the last `ℓ(n) + 1` bits, which are zeros while at most `q(n)` messages are stored.
* **One call** forwards the query and stores it (`macHandler_impl`).
* **The finalization** asks the outer oracle at the first `ℓ(n)` bits `m*` of the forger's output
  and returns the bit `[y = σ*] ∧ [m* fresh]`, where `σ*` is the rest of the output and `y` the
  answer; freshness is read from the state block by block with the chunk map `NMSim.chunkMap`
  (`macHandler_finish`).

## Main definitions

* `PRFMAC.blockLen`, `PRFMAC.macStLen`: the block and state lengths.
* `PRFMAC.blocks`, `PRFMAC.macState`: the encoded state of a list of queried messages.
* `PRFMAC.macHandler q ℓ t`: the handler.

## Main results

* `PRFMAC.finish_of_query_padFin`: a finalization with one outer query (generic).
* `PRFMAC.macHandler_impl`, `PRFMAC.macHandler_finish`: the handler's call and finalization on
  encoded states; `PRFMAC.macHandler_init_eq`: the initial state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 135.4 (book p. 135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rS rI rX rL rAns finA)
open TCSlib.Cryptography.Composability.NMSim (chunkMap chunkMap_flatten polyTimeComputable_chunkMap)

/-! ### A finalization with one outer query -/

section FinishQuery

variable {k k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}

/-- **A finalization with one outer query, on lists:** if the finalization's first round asks
the outer query `x'` to oracle `j`, and its second round, with the answer `y` in the outer log,
returns `⟨[true], b y⟩` with `|b y| = outLen(n)`, then (with `finCall(n) ≥ 1`)
`H.finish n z ω s a = query j x' (fun y => pure (padFin _ (b y)))`.

**Proof sketch.** As `InteractiveHandler.impl_of_query`: unfold the finalization (`finish_eq`) at
the budget `finCall = p + 1`; the first round decodes to the query (`decodeBitMove_query`), which
`buildComp_succ_of_query` asks; after the answer `y` the log encodes as in `hrun₁`
(`bitCodec_encodeEntry`), and the second round decodes to the output `padFin _ (b y)`
(`ofFn_padFin_of_length`, `decodeBitMove_ret`, `buildComp_of_ret`). -/
theorem finish_of_query_padFin (H : InteractiveHandler k din dout k' din' dout') (n : ℕ)
    (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool)
    {d : ℕ} (a : Fin d → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
    (b : (Fin ((dout' j).eval n) → Bool) → List Bool) (hb : ∀ y, (b y).length = H.outLen.eval n)
    (hfc : 1 ≤ H.finCall.eval n)
    (hrun₀ : H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
      []) = pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
    (hrun₁ : ∀ y, H.finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
      (List.ofFn a) (pairEncode (pairEncode (List.replicate j true)
        (pairEncode (List.ofFn x') (List.ofFn y))) [])) = pairEncode [true] (b y)) :
    H.finish n z ω s a = .query j x' fun y => .pure (padFin _ (b y)) := by
  obtain ⟨p, hp⟩ : ∃ p, H.finCall.eval n = p + 1 := ⟨H.finCall.eval n - 1, by omega⟩
  rw [InteractiveHandler.finish_eq, hp,
    buildComp_succ_of_query (i := j) (x := x') (by
      rw [MachineCodec.encodeLog_nil, hrun₀]
      exact decodeBitMove_query (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _ j x')]
  congr 1
  funext y
  have hlog : (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog
      ([] ++ [⟨j, x', y⟩]) = pairEncode (pairEncode (List.replicate j true)
        (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      bitCodec_encodeEntry]
  refine buildComp_of_ret ?_
  have h := decodeBitMove_ret (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
    (H.outLen.eval n) (padFin _ (b y))
  rwa [ofFn_padFin_of_length (hb y), ← hrun₁, ← hlog] at h

end FinishQuery

/-! ### Lengths and the encoded state -/

/-- The length of a state block, a marker bit and a message: `blockLen ℓ = ℓ + 1`. -/
def blockLen (ℓ : PolyExpr) : PolyExpr := .add ℓ (.const 1)

/-- `(blockLen ℓ).eval n = ℓ(n) + 1`. -/
theorem blockLen_eval (ℓ : PolyExpr) (n : ℕ) : (blockLen ℓ).eval n = ℓ.eval n + 1 := by
  rw [blockLen, PolyExpr.eval_add, PolyExpr.eval_const]

/-- The state length, `q` blocks: `macStLen q ℓ = q · (ℓ + 1)`. -/
def macStLen (q ℓ : PolyExpr) : PolyExpr := .mul q (blockLen ℓ)

/-- `(macStLen q ℓ).eval n = q(n) · (ℓ(n) + 1)`. -/
theorem macStLen_eval (q ℓ : PolyExpr) (n : ℕ) :
    (macStLen q ℓ).eval n = q.eval n * (ℓ.eval n + 1) := by
  rw [macStLen, PolyExpr.eval_mul, blockLen_eval]

/-- The blocks of a list of messages, each message `m` as `1 ‖ m`:
`blocks L = (L.map fun m => true :: ⟦m⟧).flatten`. -/
def blocks {a : ℕ} (L : List (Fin a → Bool)) : List Bool :=
  (L.map fun m => true :: List.ofFn m).flatten

/-- `blocks L = (L.map fun m => true :: ⟦m⟧).flatten`. -/
theorem blocks_eq {a : ℕ} (L : List (Fin a → Bool)) :
    blocks L = (L.map fun m => true :: List.ofFn m).flatten :=
  rfl

/-- `blocks (m :: L) = true :: ⟦m⟧ ++ blocks L`. -/
theorem blocks_cons {a : ℕ} (m : Fin a → Bool) (L : List (Fin a → Bool)) :
    blocks (m :: L) = true :: List.ofFn m ++ blocks L := by
  rw [blocks_eq, blocks_eq, List.map_cons, List.flatten_cons]

/-- Each block has `a + 1` bits: `|blocks L| = |L| · (a + 1)`. -/
theorem length_blocks {a : ℕ} (L : List (Fin a → Bool)) :
    (blocks L).length = L.length * (a + 1) := by
  induction L with
  | nil => rw [blocks_eq, List.map_nil, List.flatten_nil, List.length_nil, List.length_nil,
      Nat.zero_mul]
  | cons m L ih =>
    rw [blocks_cons, List.length_append, List.length_cons, List.length_ofFn, ih,
      List.length_cons]
    ring

/-! ### The round and the finalization -/

/-- One round of a call: with an empty outer log, ask the outer oracle the query; with the answer
`y` in the log, return `y` and the state with the block `1 ‖ x` shifted in and cut to `q(n)` blocks.
-/
private def macRun (q ℓ : PolyExpr) (w : List Bool) : List Bool :=
  if decide (rL w = []) then pairEncode [false] (pairEncode (rI w) (rX w))
  else pairEncode [true]
    (rAns w ++ ([true] ++ rX w ++ rS w).take ((macStLen q ℓ).eval (rU w).length))

/-- The round is polynomial-time. -/
private theorem polyTimeComputable_macRun (q ℓ : PolyExpr) : PolyTimeComputable (macRun q ℓ) := by
  have hcut : PolyTimeComputable fun w : List Bool =>
      ([true] ++ rX w ++ rS w).take ((macStLen q ℓ).eval (rU w).length) :=
    ((polyTimeComputable_pairTakePoly (macStLen q ℓ)).comp
      (InteractiveHandler.polyTimeComputable_rU.pairEncode
        (((polyTimeComputable_const [true]).append InteractiveHandler.polyTimeComputable_rX).append
          InteractiveHandler.polyTimeComputable_rS))).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact polyTimeComputable_ite
    (polyTimeComputable_isNil.comp InteractiveHandler.polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode
      (InteractiveHandler.polyTimeComputable_rI.pairEncode
        InteractiveHandler.polyTimeComputable_rX))
    ((polyTimeComputable_const [true]).pairEncode
      (InteractiveHandler.polyTimeComputable_rAns.append hcut))

/-- The output message of a finalization input: the first `ℓ(n)` bits of the forger's output. -/
private def msgOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  (finA w).take (ℓ.eval (rU w).length)

/-- The output tag of a finalization input: the forger's output after its first `ℓ(n)` bits. -/
private def sigOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  (finA w).drop (ℓ.eval (rU w).length)

/-- The emission of the freshness test on a block: `[true]` iff the block is `1 ‖ m*`, where `m*`
is the second component of the context. -/
private def hitEmit (ctx ch : List Bool) : List Bool :=
  if decide (ch = [true] ++ pairSndD ctx) then [true] else []

/-- The blocks of the state equal to `1 ‖ m*`, one `true` each (a chunk map over the state). -/
private def hitsOf (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  chunkMap (blockLen ℓ) hitEmit (pairEncode (pairEncode (rU w) (msgOf ℓ w)) (rS w))

/-- One round of the finalization: with an empty outer log, ask the oracle at `m*`; with the
answer `y` in the log, return the bit `[y = σ*] ∧ [no block is 1 ‖ m*]`. -/
private def macFin (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  if decide (rL w = []) then pairEncode [false] (pairEncode [] (msgOf ℓ w))
  else pairEncode [true]
    (if decide (rAns w = sigOf ℓ w) then [decide (hitsOf ℓ w = [])] else [false])

/-- The finalization round is polynomial-time.

**Proof sketch.** Its pieces are built from the published readers (`rU`, `rL`, `rS`, `rAns`,
`finA`) with the pair primitives: the message and tag by `polyTimeComputable_pairTakePoly` and
`polyTimeComputable_pairDropPoly`, the block test by `polyTimeComputable_pairEq`, the freshness
test by the chunk map (`NMSim.polyTimeComputable_chunkMap`) and `polyTimeComputable_isNil`, and
the branches by `polyTimeComputable_ite`. -/
private theorem polyTimeComputable_macFin (ℓ : PolyExpr) : PolyTimeComputable (macFin ℓ) := by
  have hU := InteractiveHandler.polyTimeComputable_rU
  have hA := InteractiveHandler.polyTimeComputable_finA
  have hmsg : PolyTimeComputable (msgOf ℓ) :=
    ((polyTimeComputable_pairTakePoly ℓ).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, msgOf]
  have hsig : PolyTimeComputable (sigOf ℓ) :=
    ((polyTimeComputable_pairDropPoly ℓ).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, sigOf]
  have hemit : PolyTimeComputable fun z => hitEmit (pairFstD z) (pairSndD z) := by
    have hc : PolyTimeComputable fun z : List Bool =>
        [decide (pairSndD z = [true] ++ pairSndD (pairFstD z))] :=
      (polyTimeComputable_pairEq.comp (polyTimeComputable_pairSndD.pairEncode
        ((polyTimeComputable_const [true]).append
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    exact (polyTimeComputable_ite hc (polyTimeComputable_const [true])
      (polyTimeComputable_const [])).congr fun z => by simp only [hitEmit]
  have hhits : PolyTimeComputable (hitsOf ℓ) :=
    ((polyTimeComputable_chunkMap (blockLen ℓ) hemit).comp
      ((hU.pairEncode hmsg).pairEncode InteractiveHandler.polyTimeComputable_rS)).congr fun w => by
      simp only [Function.comp_apply, hitsOf]
  have hbit : PolyTimeComputable fun w : List Bool =>
      if decide (rAns w = sigOf ℓ w) then [decide (hitsOf ℓ w = [])] else [false] :=
    polyTimeComputable_ite
      ((polyTimeComputable_pairEq.comp
        (InteractiveHandler.polyTimeComputable_rAns.pairEncode hsig)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
      (polyTimeComputable_isNil.comp hhits) (polyTimeComputable_const [false])
  exact polyTimeComputable_ite
    (polyTimeComputable_isNil.comp InteractiveHandler.polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hmsg))
    ((polyTimeComputable_const [true]).pairEncode hbit)

/-! ### The handler -/

/-- **The handler of the PRF-MAC reduction** [PS10, Theorem 135.4, proof], for the query budget
`q` and `ℓ(n)`-bit messages with `t(n)`-bit tags: one inner and one outer oracle, both with these
lengths; the state keeps the queried messages in `q(n) · (ℓ(n) + 1)` bits; no seed; one outer
query per call, which forwards the inner query; the adversary gets the empty input; the
finalization makes one outer query and returns one bit:
`(macHandler q ℓ t).stateLen = macStLen q ℓ`, `seedLen = .const 0`,
`perCall = finCall = outLen = .const 1` and `advIn _ = []` (the `simps` fields). -/
def macHandler (q ℓ t : PolyExpr) :
    InteractiveHandler 1 (fun _ => ℓ) (fun _ => t) 1 (fun _ => ℓ) (fun _ => t) where
  stateLen := macStLen q ℓ
  seedLen := .const 0
  perCall := .const 1
  init _ := zeroBits _
  run := macRun q ℓ
  poly := polyTimeComputable_macRun q ℓ
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  outLen := .const 1
  finCall := .const 1
  finRun := macFin ℓ
  finRun_poly := polyTimeComputable_macFin ℓ

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall]
  macHandler

variable (q ℓ t : PolyExpr)

/-- **The encoded state** of the queried messages `L` (newest first): their blocks `1 ‖ m`,
followed by zeros, read at the state length: `macState q ℓ t n L = padFin _ (blocks L)`. -/
def macState (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) :
    Fin ((macHandler q ℓ t).stateLen.eval n) → Bool :=
  padFin _ (blocks L)

/-- `macState q ℓ t n L = padFin _ (blocks L)`. -/
theorem macState_eq (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) :
    macState q ℓ t n L = padFin _ (blocks L) :=
  rfl

/-- The state has `q(n) · (ℓ(n) + 1)` bits:
`(macHandler q ℓ t).stateLen.eval n = q(n) · (ℓ(n) + 1)`. -/
theorem macHandler_stateLen_eval (n : ℕ) :
    (macHandler q ℓ t).stateLen.eval n = q.eval n * (ℓ.eval n + 1) := by
  rw [macHandler_stateLen, macStLen_eval]

/-- **The initial state stores no message:** `(macHandler q ℓ t).init n = macState q ℓ t n []`. -/
theorem macHandler_init_eq (n : ℕ) : (macHandler q ℓ t).init n = macState q ℓ t n [] := by
  funext j
  rw [macHandler_init, macState_eq, zeroBits_apply, padFin_def, blocks_eq, List.map_nil,
    List.flatten_nil]
  rfl

/-- The encoded state of at most `q(n)` messages is their blocks followed by zeros:
`⟦macState q ℓ t n L⟧ = blocks L ++ 0^{q(n)(ℓ(n)+1) − |L|(ℓ(n)+1)}`. -/
theorem ofFn_macState (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool)) (hL : L.length ≤ q.eval n) :
    List.ofFn (macState q ℓ t n L) = blocks L ++
      List.replicate (q.eval n * (ℓ.eval n + 1) - L.length * (ℓ.eval n + 1)) false := by
  rw [macState_eq, Collection.ofFn_padFin_of_le, length_blocks, macHandler_stateLen_eval]
  rw [macHandler_stateLen_eval, length_blocks]
  exact Nat.mul_le_mul_right _ hL

/-! ### The call -/

/-- **One call forwards the query and stores it:** from the encoded state of `L` with
`|L| < q(n)`, the inner query `x` is the outer query `x`, answered with the outer answer `y` and
the state of `x :: L`: `(macHandler q ℓ t).impl n z ω i x (macState q ℓ t n L) =
query i x (fun y => pure (y, macState q ℓ t n (x :: L)))`.

**Proof sketch.** `InteractiveHandler.impl_of_query_padFin` with one outer query: the first round
has an empty outer log (`rL_input`) and asks `⟨1^i, x⟩` (`rI_input`, `rX_input`); the second reads
the answer (`rAns_input`) and returns it with `(1 ‖ x ‖ ⟦s⟧)` cut to `q(n)(ℓ(n) + 1)` bits. With
`⟦s⟧ = blocks L ‖ 0…0` (`ofFn_macState`) the cut drops `ℓ(n) + 1` zeros (`List.take_append`,
`List.take_replicate`) and leaves the encoded state of `x :: L`. -/
theorem macHandler_impl (n : ℕ) (z : List Bool) (ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool)
    (i : Fin 1) (x : Fin (ℓ.eval n) → Bool) (L : List (Fin (ℓ.eval n) → Bool))
    (hL : L.length < q.eval n) :
    (macHandler q ℓ t).impl n z ω i x (macState q ℓ t n L) =
      .query i x fun y => .pure (y, macState q ℓ t n (x :: L)) := by
  have hN := macHandler_stateLen_eval q ℓ t n
  have hcut : ([true] ++ List.ofFn x ++ List.ofFn (macState q ℓ t n L)).take
      ((macStLen q ℓ).eval (List.replicate n true).length) =
      List.ofFn (macState q ℓ t n (x :: L)) := by
    have hle : (L.length + 1) * (ℓ.eval n + 1) ≤ q.eval n * (ℓ.eval n + 1) :=
      Nat.mul_le_mul_right _ hL
    rw [List.length_replicate, macStLen_eval, ofFn_macState q ℓ t n L hL.le,
      ofFn_macState q ℓ t n (x :: L) hL, blocks_cons, List.length_cons]
    have hB : ([true] ++ List.ofFn x ++ blocks L).length = (L.length + 1) * (ℓ.eval n + 1) := by
      rw [List.length_append, List.length_append, List.length_ofFn, length_blocks]
      simp only [List.length_singleton]
      ring
    rw [← List.append_assoc, List.take_append, List.take_of_length_le (by rw [hB]; exact hle), hB,
      List.take_replicate]
    have hmin : min (q.eval n * (ℓ.eval n + 1) - (L.length + 1) * (ℓ.eval n + 1))
        (q.eval n * (ℓ.eval n + 1) - L.length * (ℓ.eval n + 1)) =
        q.eval n * (ℓ.eval n + 1) - (L.length + 1) * (ℓ.eval n + 1) :=
      Nat.min_eq_left (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _)
    rw [hmin]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine (InteractiveHandler.impl_of_query_padFin _ n z ω i x (macState q ℓ t n L) i x
    (fun y => List.ofFn y) (fun _ => List.ofFn (macState q ℓ t n (x :: L)))
    (fun y => List.length_ofFn) (fun _ => List.length_ofFn)
    (by rw [macHandler_perCall, PolyExpr.eval_const]) ?_ fun y => ?_).trans ?_
  · show macRun q ℓ _ = _
    rw [macRun, InteractiveHandler.rL_input, InteractiveHandler.rI_input,
      InteractiveHandler.rX_input, if_pos (decide_eq_true rfl)]
  · show macRun q ℓ _ = _
    rw [macRun, InteractiveHandler.rL_input, InteractiveHandler.rAns_input,
      InteractiveHandler.rX_input, InteractiveHandler.rS_input, InteractiveHandler.rU_input,
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)), hcut]
  · simp only [padFin_ofFn]

/-! ### The finalization -/

/-- The freshness test on the encoded state of at most `q(n)` messages: no block is `1 ‖ u` iff no
stored message has the list `u`: `chunkMap … ⟨⟨1^n, u⟩, ⟦macState q ℓ t n L⟧⟩ = [] ↔
∀ m ∈ L, ⟦m⟧ ≠ u`.

**Proof sketch.** The state is the concatenation of the blocks `1 ‖ m` and of `q(n) − |L|` zero
blocks, all of `ℓ(n) + 1 > 0` bits (`ofFn_macState`, `List.flatten_replicate_replicate`), so the
chunk map emits `hitEmit` of each block (`NMSim.chunkMap_flatten`), and the result is empty iff
every emission is (`List.flatten_eq_nil_iff`). A block `1 ‖ m` emits iff `⟦m⟧ = u`
(`List.cons_injective`); a zero block starts with `0` and never emits. -/
private theorem hits_nil_iff (n : ℕ) (L : List (Fin (ℓ.eval n) → Bool))
    (hL : L.length ≤ q.eval n) (u : List Bool) :
    chunkMap (blockLen ℓ) hitEmit (pairEncode (pairEncode (List.replicate n true) u)
        (List.ofFn (macState q ℓ t n L))) = [] ↔ ∀ m ∈ L, List.ofFn m ≠ u := by
  have hflat : List.ofFn (macState q ℓ t n L) =
      (L.map (fun m => true :: List.ofFn m) ++
        List.replicate (q.eval n - L.length) (List.replicate (ℓ.eval n + 1) false)).flatten := by
    rw [ofFn_macState q ℓ t n L hL, List.flatten_append, List.flatten_replicate_replicate,
      blocks_eq, Nat.sub_mul]
  have hlen : ∀ ch ∈ L.map (fun m => true :: List.ofFn m) ++
      List.replicate (q.eval n - L.length) (List.replicate (ℓ.eval n + 1) false),
      ch.length = (blockLen ℓ).eval n := by
    intro ch hch
    rw [blockLen_eval]
    rcases List.mem_append.1 hch with h | h
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
      rw [List.length_cons, List.length_ofFn]
    · rw [List.eq_of_mem_replicate h, List.length_replicate]
  rw [hflat, chunkMap_flatten (blockLen ℓ) hitEmit n u _ hlen
    (by rw [blockLen_eval]; omega), List.flatten_eq_nil_iff]
  constructor
  · intro h m hm hmu
    have := h _ (List.mem_map.2 ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩), rfl⟩)
    rw [hitEmit, pairSndD_pairEncode, if_pos (decide_eq_true (by rw [hmu]; rfl))] at this
    exact List.cons_ne_nil _ _ this
  · intro h x hx
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hx
    rcases List.mem_append.1 hch with hc | hc
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
      rw [hitEmit, pairSndD_pairEncode, if_neg]
      intro he
      exact h m hm (List.cons_injective (of_decide_eq_true he))
    · rw [List.eq_of_mem_replicate hc, hitEmit, pairSndD_pairEncode, if_neg]
      intro he
      have := of_decide_eq_true he
      rw [List.replicate_succ] at this
      exact Bool.false_ne_true (List.cons_eq_cons.1 this).1

/-- **The finalization** from the encoded state of `L` with `|L| ≤ q(n)`, after the output `a`
of at least `ℓ(n)` bits: ask the oracle at `m* = a[0, ℓ(n))` and output the bit
`[⟦y⟧ = a[ℓ(n), …)] ∧ [∀ m ∈ L, ⟦m⟧ ≠ ⟦m*⟧]` for its answer `y`:
`(macHandler q ℓ t).finish n z ω (macState q ℓ t n L) a = query 0 (padFin _ (⟦a⟧.take ℓ(n)))
(fun y => pure (padFin _ [decide (⟦y⟧ = ⟦a⟧.drop ℓ(n)) && decide (∀ m ∈ L, ⟦m⟧ ≠ ⟦a⟧.take ℓ(n))]))`.

**Proof sketch.** `finish_of_query_padFin`. The first round has an empty outer log
(`rL_finInput`) and asks the first `ℓ(n)` bits of `a` (`finA_finInput`, `rU_finInput`). The second
reads the answer `y` from the one-entry log (`rAns_eq`, `rL_finInput`) and compares it with the rest
of `a`; the freshness test reads the state block by block (`NMSim.chunkMap_flatten` on the blocks
and the zero blocks, `ofFn_macState`): a zero block never starts with the marker bit. -/
theorem macHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool) (L : List (Fin (ℓ.eval n) → Bool))
    (hL : L.length ≤ q.eval n) {d : ℕ} (a : Fin d → Bool) (hd : ℓ.eval n ≤ d) :
    (macHandler q ℓ t).finish n z ω (macState q ℓ t n L) a =
      .query 0 (padFin _ ((List.ofFn a).take (ℓ.eval n))) fun y =>
        .pure (padFin _ [decide (List.ofFn y = (List.ofFn a).drop (ℓ.eval n)) &&
          decide (∀ m ∈ L, List.ofFn m ≠ (List.ofFn a).take (ℓ.eval n))]) := by
  have htake : ((List.ofFn a).take (ℓ.eval n)).length = ℓ.eval n := by
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left hd]
  have hx : List.ofFn (padFin (ℓ.eval n) ((List.ofFn a).take (ℓ.eval n))) =
      (List.ofFn a).take (ℓ.eval n) := ofFn_padFin_of_length htake
  refine finish_of_query_padFin _ n z ω (macState q ℓ t n L) a 0
    (padFin _ ((List.ofFn a).take (ℓ.eval n))) _ (fun y => by
      rw [List.length_singleton, macHandler_outLen, PolyExpr.eval_const])
    (by rw [macHandler_finCall, PolyExpr.eval_const]) ?_ fun y => ?_
  · show macFin ℓ _ = _
    rw [macFin, InteractiveHandler.rL_finInput, if_pos (decide_eq_true rfl), msgOf,
      InteractiveHandler.finA_finInput, InteractiveHandler.rU_finInput, List.length_replicate, hx]
    rfl
  · show macFin ℓ _ = _
    have hans : rAns (InteractiveHandler.finInput n z (List.ofFn ω)
        (List.ofFn (macState q ℓ t n L)) (List.ofFn a)
        (pairEncode (pairEncode (List.replicate ((0 : Fin 1) : ℕ) true)
          (pairEncode (List.ofFn (padFin (ℓ.eval n) ((List.ofFn a).take (ℓ.eval n))))
            (List.ofFn y))) [])) = List.ofFn y := by
      rw [InteractiveHandler.rAns_eq, InteractiveHandler.rL_finInput, pairFstD_pairEncode,
        pairSndD_pairEncode, pairSndD_pairEncode]
    rw [macFin, InteractiveHandler.rL_finInput,
      if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)), hans, sigOf, hitsOf, msgOf,
      InteractiveHandler.finA_finInput, InteractiveHandler.rU_finInput,
      InteractiveHandler.rS_finInput, List.length_replicate]
    congr 1
    by_cases hy : List.ofFn y = (List.ofFn a).drop (ℓ.eval n)
    · rw [if_pos (decide_eq_true hy), decide_eq_true hy, Bool.true_and]
      congr 1
      exact decide_eq_decide.2 (hits_nil_iff q ℓ t n L hL _)
    · rw [if_neg (fun h => hy (of_decide_eq_true h)), decide_eq_false hy, Bool.false_and]

end TCSlib.Cryptography.Authentication.PRFMAC

## ===== TCSlib/Cryptography/Authentication/MAC/FromPRF/Reduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The distinguisher of the PRF-MAC reduction

Steps 2, 3 and 6 of the proof of [PS10, Theorem 135.4], for a forger with `ℓ(n)`-bit messages and
`t(n)`-bit tags: T2 (`Games.exists_interactiveHandlerMachine`) applied to the handler `macHandler`
(through the input-free companion `Games.exists_toCompOn_of_toComp`), then T4
(`Games.exists_toOracleAdversary_of_bitCodec`), give a next-query machine `D` whose acceptance
probability against any function `f` is the probability that the forger forges against the
tagging oracle `f`: its output `(m, σ)` has `f m = σ` and `m` was never queried
(`exists_macReduction`).

The proof answers the handler's outer queries by `f` (`fnImpl`, `simulate_ofComp_pure`) and composes
the two implementations (`simulate_comp`). From the encoded state of the queried messages, newest
first (`queried`), each composed call is the logged call of `fnImpl f` with the new state abstracted
(`macHandler_impl`); the forger asks at most `q(n)` queries, so this holds along every run
(`Games.simulate_eq_of_abs_bounded`), and the log of every run has at most `q(n)` entries
(`allOutputs_simulate_withLog_length`). The finalization then tests exactly the forgery
(`macHandler_finish`).

## Main definitions

* `PRFMAC.fnImpl f`: the tagging oracle of the function `f`.
* `PRFMAC.FnForge f a log`: the output `a = (m, σ)` is a forgery against `f` given the log.
* `PRFMAC.queried log`: the queried messages of a log, newest first.
* `PRFMAC.macBudget q`: the distinguisher's query budget `q · 1 + 1`.

## Main results

* `PRFMAC.allOutputs_simulate_withLog_length`: the log of a run grows by at most its query count.
* `PRFMAC.exists_macReduction`: the distinguisher (checkpoint 1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 135.4 (book p. 135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.ChallengeSim (expect_sample_prod)

/-! ### The tagging oracle of a function and forgeries against it -/

section Fn

variable {a b : ℕ}

/-- **The tagging oracle of the function `f`**: each query `m` is answered `f m`, the state kept:
`fnImpl f = QueryImpl.ofComp fun _ m => pure (f m)`. -/
def fnImpl (f : (Fin a → Bool) → (Fin b → Bool)) :
    QueryImpl (bitSpec (fun _ : Fin 1 => a) (fun _ => b)) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => .pure (f m)

/-- `fnImpl f = QueryImpl.ofComp fun _ m => pure (f m)`. -/
theorem fnImpl_eq (f : (Fin a → Bool) → (Fin b → Bool)) :
    fnImpl f = QueryImpl.ofComp fun _ m => .pure (f m) :=
  rfl

/-- The tagging oracle of `f` answers `f x`: `fnImpl f i x s = pure (f x, s)`. -/
theorem fnImpl_apply (f : (Fin a → Bool) → (Fin b → Bool)) (i : Fin 1) (x : Fin a → Bool)
    (s : Unit) : fnImpl f i x s = .pure (f x, s) := by
  rw [fnImpl_eq, QueryImpl.ofComp_apply, OracleComp.pure_bind]

/-- **A forgery against `f`** [PS10, Definition 134.2]: the output `w = (m, σ)` (`splitBits`) has
`f m = σ` and `m` is the message of no entry of the log:
`FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1`. -/
def FnForge (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : Prop :=
  f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1

/-- `FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1`.
-/
theorem fnForge_iff (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    FnForge f w log ↔ f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, e.2.1 ≠ (splitBits w).1 :=
  Iff.rfl

/-- Forgeries are decidable, as the conjunction they unfold to (`fnForge_iff`):
`Decidable (FnForge f w log)` from `f (splitBits w).1 = (splitBits w).2 ∧ ∀ e ∈ log, …`. -/
instance (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : Decidable (FnForge f w log) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The queried messages of a log**, newest first: `queried log = (log.map (·.2.1)).reverse`. -/
def queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) : List (Fin a → Bool) :=
  (log.map fun e => e.2.1).reverse

/-- `queried log = (log.map (·.2.1)).reverse`. -/
theorem queried_eq (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    queried log = (log.map fun e => e.2.1).reverse :=
  rfl

/-- `queried [] = []`. -/
theorem queried_nil : queried ([] : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) = [] :=
  rfl

/-- A new entry is the newest message: `queried (log ++ [e]) = e.2.1 :: queried log`. -/
theorem queried_append (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
    (e : Σ i, (bitSpec (fun _ : Fin 1 => a) (fun _ => b)).dom i ×
      (bitSpec (fun _ : Fin 1 => a) (fun _ => b)).rng i) :
    queried (log ++ [e]) = e.2.1 :: queried log := by
  rw [queried_eq, queried_eq, List.map_append, List.reverse_append, List.map_singleton,
    List.reverse_singleton, List.singleton_append]

/-- `|queried log| = |log|`. -/
theorem length_queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    (queried log).length = log.length := by
  rw [queried_eq, List.length_reverse, List.length_map]

/-- `m ∈ queried log ↔ ∃ e ∈ log, e.2.1 = m`. -/
theorem mem_queried (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
    (m : Fin a → Bool) : m ∈ queried log ↔ ∃ e ∈ log, e.2.1 = m := by
  rw [queried_eq, List.mem_reverse, List.mem_map]

/-- **A forgery read on lists:** for an output `w` of `a + b` bits, the list test of the
finalization is the forgery: `(decide (⟦f (padFin a (⟦w⟧.take a))⟧ = ⟦w⟧.drop a) &&
decide (∀ m ∈ queried log, ⟦m⟧ ≠ ⟦w⟧.take a)) = decide (FnForge f w log)`.

**Proof sketch.** `⟦w⟧ = ⟦m⟧ ++ ⟦σ⟧` for `(m, σ) = splitBits w` (`Fin.append_castAdd_natAdd`,
`List.ofFn_fin_append`), so the first `a` bits are `⟦m⟧` and the rest `⟦σ⟧`; `List.ofFn` is
injective, and `queried` lists the logged messages (`mem_queried`). -/
theorem decide_fnForge (f : (Fin a → Bool) → (Fin b → Bool)) (w : Fin (a + b) → Bool)
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b))) :
    (decide (List.ofFn (f (padFin a ((List.ofFn w).take a))) = (List.ofFn w).drop a) &&
      decide (∀ m ∈ queried log, List.ofFn m ≠ (List.ofFn w).take a)) =
      decide (FnForge f w log) := by
  have hw : List.ofFn w = List.ofFn (splitBits w).1 ++ List.ofFn (splitBits w).2 := by
    rw [← List.ofFn_fin_append,
      show (splitBits w).1 = fun i => w (Fin.castAdd b i) from funext (splitBits_fst w),
      show (splitBits w).2 = fun j => w (Fin.natAdd a j) from funext (splitBits_snd w),
      Fin.append_castAdd_natAdd]
  have htake : (List.ofFn w).take a = List.ofFn (splitBits w).1 := by
    rw [hw, List.take_left' List.length_ofFn]
  have hdrop : (List.ofFn w).drop a = List.ofFn (splitBits w).2 := by
    rw [hw, List.drop_left' List.length_ofFn]
  rw [htake, hdrop, padFin_ofFn, ← Bool.decide_and]
  refine decide_eq_decide.2 ?_
  rw [fnForge_iff]
  refine and_congr List.ofFn_inj ⟨fun h e he hm => h e.2.1 ((mem_queried log _).2 ⟨e, he, rfl⟩)
    (by rw [hm]), fun h m hm hl => ?_⟩
  obtain ⟨e, he, rfl⟩ := (mem_queried log m).1 hm
  exact h e he (List.ofFn_inj.1 hl)

end Fn

/-- **The log of a run grows by at most its query count:** for a computation making at most `m`
queries, every output of the logged simulation from `(s, log)` has a log of at most `|log| + m`
entries: `(simulate impl.withLog c (s, log)).AllOutputs fun p => |p.2.2| ≤ |log| + m`.

**Proof sketch.** Induction on `c`: a return keeps the log; a query appends one entry
(`QueryImpl.withLog_apply`) and leaves at most `m - 1` queries (`OracleComp.costBoundedBy_query`).
-/
theorem allOutputs_simulate_withLog_length {ι ι' : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} {σ α : Type} (impl : QueryImpl spec σ spec') (c : OracleComp spec α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).AllOutputs fun p => p.2.2.length ≤ log.length + m := by
  induction c generalizing m s log with
  | pure a =>
    rw [simulate_pure, OracleComp.allOutputs_pure]
    exact Nat.le_add_right _ _
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, QueryImpl.withLog_apply, OracleComp.bind_assoc]
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun ys _ => ?_
    rw [OracleComp.pure_bind]
    refine OracleComp.AllOutputs.mono (fun p hp => ?_) (ih ys.1 (m - 1) (hk ys.1) ys.2 _)
    dsimp only at hp
    rw [List.length_append, List.length_singleton] at hp
    omega

/-- The distinguisher's query budget, `q` forwarded queries and one final query:
`macBudget q = q · 1 + 1`. -/
def macBudget (q : PolyExpr) : PolyExpr := .add (.mul q (.const 1)) (.const 1)

/-- `(macBudget q).eval n = q(n) · 1 + 1`, with the constants read by `PolyExpr.eval`. -/
theorem macBudget_eval (q : PolyExpr) (n : ℕ) :
    (macBudget q).eval n = q.eval n * (PolyExpr.const 1).eval n + (PolyExpr.const 1).eval n := by
  rw [macBudget, PolyExpr.eval_add, PolyExpr.eval_mul]

/-! ### The reduction -/

/-- **The PRF-MAC distinguisher** [PS10, Theorem 135.4, proof, steps 2–3]: for a forger `A` with
budget `q`, `ℓ(n)`-bit messages and `t(n)`-bit tags, there is a next-query machine `D` such that
at every `n` and for every function `f : {0,1}^ℓ(n) → {0,1}^t(n)`, `D` with budget `q · 1 + 1`
accepts against `f` with the probability that `A` forges against the tagging oracle `f`:
`𝔼_c [D^f(c) = 1] = 𝔼_r Pr[FnForge f | simulate (fnImpl f).withLog (A.toComp … r) ((), [])]`.

**Proof sketch.** `D` is T4 applied to T2's machine `B` for `macHandler q ℓ t` and the input-free
companion `A'` of `A`. Its coins are, through the bijections of T4, T2 and the companion, an empty
seed `ω` and `A`'s coins `r` (`expect_sample_equiv`, `ChallengeSim.expect_sample_prod`,
`expect_sample_comm`); the run does not read `ω` (`expect_const`). For fixed `ω` and `r`, T4 and
T2 turn `D`'s run against `f` into the evaluation of the reduction with `f`
(`PRFGame.ofFn_evalFn_toCompOn`), which is its simulation with `fnImpl f`
(`simulate_ofComp_pure`), composed with the handler (`simulate_bind`, `simulate_comp`). Along
`A`'s run (at most `q(n)` queries) the composite is the logged `fnImpl f` with the state
abstracted to the encoded queried messages (`simulate_eq_of_abs_bounded`, `macHandler_impl`). Every
final log has at most `q(n)` entries (`allOutputs_simulate_withLog_length`), so the finalization
asks `f` at `m*` and tests `f m* = σ*` and freshness (`macHandler_finish`), which is `FnForge` on
lists (`decide_fnForge`) after transporting the output width (`expect_toCompOn_outLen`). -/
theorem exists_macReduction (ℓ t q : PolyExpr) (A : NUPPT) :
    ∃ D : NUPPT, ∀ (n : ℕ) (f : (Fin (ℓ.eval n) → Bool) → (Fin (t.eval n) → Bool)),
      expect (ProbComp.sample (D.Coins n))
          (fun c => if (D.toOracleAdversary n (ℓ.eval n) (t.eval n) ((macBudget q).eval n) c).eval
            f = true then (1 : ℝ) else 0) =
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fnImpl f).withLog
              (A.toComp (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
                (ℓ.eval n + t.eval n)) n (q.eval n) r) ((), []))
            (fun res => if FnForge f res.1 res.2.2 then (1 : ℝ) else 0) := by
  obtain ⟨A', -, hA'⟩ := exists_toCompOn_of_toComp A
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A' q (fun _ => ℓ) (fun _ => t)
    (fun _ => ℓ) (fun _ => t) (.add ℓ t) (macHandler q ℓ t)
  obtain ⟨D, -, hD⟩ := exists_toOracleAdversary_of_bitCodec B ℓ t
  refine ⟨D, fun n f => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA' n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  obtain ⟨φ₄, hφ₄⟩ := hD n
  have hQ : q.eval n * (macHandler q ℓ t).perCall.eval n + (macHandler q ℓ t).finCall.eval n =
      (macBudget q).eval n := by
    rw [macHandler_perCall, macHandler_finCall, macBudget_eval]
  have hout : (macHandler q ℓ t).outLen.eval n = 1 := by
    rw [macHandler_outLen, PolyExpr.eval_const]
  have hd : (PolyExpr.add ℓ t).eval n = ℓ.eval n + t.eval n := PolyExpr.eval_add ℓ t n
  -- `D`'s coins are a seed and `A`'s coins.
  rw [← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂, expect_sample_prod,
    expect_sample_comm, ← expect_sample_equiv φ₀]
  refine congrArg _ (funext fun r => ?_)
  have key : ∀ g : Fin 1 → Bool, (if g 0 = true then (1 : ℝ) else 0) =
      if (List.ofFn g).headD false = true then 1 else 0 := fun g => by rw [headD_ofFn_one]
  -- One run of `D` is the forgery test of `A`'s run against `fnImpl f`.
  have hrun : ∀ ω : Fin ((macHandler q ℓ t).seedLen.eval n) → Bool,
      (if (D.toOracleAdversary n (ℓ.eval n) (t.eval n) ((macBudget q).eval n)
          (φ₄ (φ₂ (ω, φ₀ r)))).eval f = true then (1 : ℝ) else 0) =
        expect (simulate (fnImpl f).withLog
            (A.toComp (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
              (ℓ.eval n + t.eval n)) n (q.eval n) r) ((), []))
          (fun res => if FnForge f res.1 res.2.2 then (1 : ℝ) else 0) := by
    intro ω
    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
        ((macHandler q ℓ t).outLen.eval n)) n
        (q.eval n * (macHandler q ℓ t).perCall.eval n + (macHandler q ℓ t).finCall.eval n)
        [] (φ₂ (ω, φ₀ r)) := hφ₂ [] ω (φ₀ r)
    rw [hφ₄, ← hQ, key, Composability.PRFGame.ofFn_evalFn_toCompOn hout.symm B n _ []
      (φ₂ (ω, φ₀ r)), ← h2]
    set c' := A'.toCompOn (bitCodec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)
      ((PolyExpr.add ℓ t).eval n)) n (q.eval n) ((macHandler q ℓ t).advInput n [] ω) (φ₀ r)
      with hc'
    -- The evaluation with `f` is the simulation with `fnImpl f`.
    have hev := simulate_ofComp_pure (σ := Unit) (spec' := unifSpec)
      (fun (_ : Fin 1) (x : Fin (ℓ.eval n) → Bool) => f x)
      ((simulate ((macHandler q ℓ t).impl n [] ω) c' ((macHandler q ℓ t).init n)).bind
        (fun res => (macHandler q ℓ t).finish n [] ω res.2 res.1)) ()
    rw [← fnImpl_eq] at hev
    have h1 := congrArg (fun c => expect c
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
    simp only [expect_pure] at h1
    refine h1.symm.trans ?_
    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind]
    -- The composed calls are the logged calls of `fnImpl f`, the state abstracted.
    have hstep : ∀ (i : Fin 1) (x : Fin (ℓ.eval n) → Bool)
        (s : Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n))),
        s.2.length < q.eval n →
        ∃ (y : Fin (t.eval n) → Bool)
          (s' : Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n))),
          (fnImpl f).withLog i x s = .pure (y, s') ∧ s'.2.length ≤ s.2.length + 1 ∧
          (fnImpl f).comp ((macHandler q ℓ t).impl n [] ω) i x
              (macState q ℓ t n (queried s.2), ()) =
            .pure (y, (macState q ℓ t n (queried s'.2), ())) := by
      intro i x s hs
      refine ⟨f x, ((), s.2 ++ [⟨i, x, f x⟩]), ?_, by
        rw [List.length_append, List.length_singleton], ?_⟩
      · rw [QueryImpl.withLog_apply, fnImpl_apply, OracleComp.pure_bind]
      · rw [QueryImpl.comp_apply]
        dsimp only
        rw [macHandler_impl q ℓ t n [] ω i x _ (by rwa [length_queried])]
        simp only [simulate_query, fnImpl_apply, OracleComp.pure_bind, simulate_pure,
          queried_append]
    have hinit : (macHandler q ℓ t).init n = macState q ℓ t n
        (queried ([] : QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n) (fun _ => t.eval n)))) := by
      rw [macHandler_init_eq, queried_nil]
    have hcost := A'.toCompOn_costBoundedBy (bitCodec (fun _ : Fin 1 => ℓ.eval n)
      (fun _ => t.eval n) ((PolyExpr.add ℓ t).eval n)) n (q.eval n)
      ((macHandler q ℓ t).advInput n [] ω) (φ₀ r)
    rw [hinit, simulate_eq_of_abs_bounded ((fnImpl f).comp ((macHandler q ℓ t).impl n [] ω))
      (fnImpl f).withLog (fun s => (macState q ℓ t n (queried s.2), ())) (fun s => s.2.length)
      (q.eval n) hstep c' (q.eval n) hcost ((), []) (Nat.zero_add _).le,
      expect_bind]
    simp only [expect_pure]
    -- The finalization tests the forgery, on lists.
    let G : List Bool × (Unit × QueryLog (bitSpec (fun _ : Fin 1 => ℓ.eval n)
        (fun _ => t.eval n))) → ℝ := fun p =>
      if (decide (List.ofFn (f (padFin (ℓ.eval n) (p.1.take (ℓ.eval n)))) =
          p.1.drop (ℓ.eval n)) &&
        decide (∀ m ∈ queried p.2.2, List.ofFn m ≠ p.1.take (ℓ.eval n))) = true
      then (1 : ℝ) else 0
    have hall := allOutputs_simulate_withLog_length (fnImpl f) c' (q.eval n) hcost () []
    rw [expect_congr_of_allOutputs hall (g := fun p => G (List.ofFn p.1, p.2)) fun p hp => ?_]
    · rw [expect_toCompOn_outLen (fnImpl f).withLog A' n (q.eval n) _ (φ₀ r) ((), []) hd G, hφ₀]
      refine congrArg _ (funext fun p => ?_)
      show (if _ = true then (1 : ℝ) else 0) = _
      rw [decide_fnForge]
      exact if_congr decide_eq_true_iff rfl rfl
    · rw [List.length_nil, Nat.zero_add] at hp
      rw [macHandler_finish q ℓ t n [] ω (queried p.2.2) (by rwa [length_queried]) p.1
        (by rw [hd]; omega)]
      simp only [simulate_query, fnImpl_apply, OracleComp.pure_bind, simulate_pure, expect_pure]
      rw [ofFn_padFin_of_length (by rw [List.length_singleton, hout]), List.headD_cons]
  simp only [hrun]
  exact expect_const _ _

end TCSlib.Cryptography.Authentication.PRFMAC

## ===== TCSlib/Cryptography/Authentication/MAC/FromPRF/Random.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Forging against a random function

Step 4 of the proof of [PS10, Theorem 135.4]: against a uniform random function `R`, a forgery
`(m, σ)` with `m` never queried is a guess of the value `R m`, which is uniform and independent of
everything the forger saw, so every forger (whatever its number of queries) forges with probability
at most `2^{-t}` for `t`-bit tags (`expect_fnForge_random_le`).

The proof samples `R` lazily along the run, with the table override `ETTGame.ovr` of the
encrypt-then-tag proof: a new query `x` reads `R x`, which `ETTGame.expect_sample_ovr` moves into
the table; a repeated query reads the table. Every table key is a queried message, so at the end a
fresh message is not a key, and its value is `R` there, uniform (`expect_sample_coord`,
`expect_sample_mem_le`).

## Main results

* `PRFMAC.expect_fnForge_random_le`: the forgery probability against a random function is at most
  `2^{-t}` (checkpoint 2).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 135.4 (book p. 135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.ETTGame (ovr ovr_nil ovr_of_mem ovr_of_not_mem
  expect_sample_ovr)

variable {a b : ℕ}

/-- A fresh message's value under a random function is a guess: for an output `w` whose message is
no key of the table `M` and was not queried, the forgery probability against `ovr M R`, averaged
over a uniform `R`, is at most `2^{-b}`; a queried message is no forgery:
`𝔼_R [FnForge (ovr M R) w log] ≤ 2^{-b}` when every key of `M` is queried.

**Proof sketch.** If the message `m = (splitBits w).1` was queried, there is no forgery
(`mem_queried`). Otherwise it is no key of `M`, so `ovr M R m = R m` (`ovr_of_not_mem`) and a
forgery needs `R m = σ`; the coordinate `R m` of a uniform table is uniform
(`expect_sample_coord`), and hits the one value `σ` with probability `1 / 2^b`
(`expect_sample_mem_le`, `Fintype.card_fun`). This re-derives, from the published `ovr` readers,
the fresh-point case of the private `ETTGame.expect_hitW_le` (disclosed). -/
private theorem expect_forge_pure_le (w : Fin (a + b) → Bool)
    (M : List ((Fin a → Bool) × (Fin b → Bool)))
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
    (hM : ∀ p ∈ M.map Prod.fst, p ∈ queried log) :
    expect (sample ((Fin a → Bool) → (Fin b → Bool)))
        (fun R => if FnForge (ovr M R) w log then (1 : ℝ) else 0) ≤ ((2 : ℝ) ^ b)⁻¹ := by
  have hδ : (0 : ℝ) ≤ ((2 : ℝ) ^ b)⁻¹ := by positivity
  by_cases hq : (splitBits w).1 ∈ queried log
  · have h0 : (fun R => if FnForge (ovr M R) w log then (1 : ℝ) else 0) = fun _ => 0 := by
      funext R
      refine if_neg fun h => ?_
      obtain ⟨e, he, hem⟩ := (mem_queried log _).1 hq
      exact ((fnForge_iff _ _ _).1 h).2 e he hem
    rw [h0, expect_const]
    exact hδ
  · have hk : (splitBits w).1 ∉ M.map Prod.fst := fun h => hq (hM _ h)
    have hle : ∀ R : (Fin a → Bool) → (Fin b → Bool),
        (if FnForge (ovr M R) w log then (1 : ℝ) else 0) ≤
          if R (splitBits w).1 ∈ [(splitBits w).2] then 1 else 0 := by
      intro R
      by_cases h : FnForge (ovr M R) w log
      · rw [if_pos h, if_pos]
        rw [List.mem_singleton, ← ovr_of_not_mem hk R]
        exact ((fnForge_iff _ _ _).1 h).1
      · rw [if_neg h]
        split <;> norm_num
    refine (expect_mono _ hle).trans ?_
    rw [expect_sample_coord (splitBits w).1 (fun y (_ : (Fin a → Bool) → (Fin b → Bool)) =>
      if y ∈ [(splitBits w).2] then (1 : ℝ) else 0) (fun _ _ _ => rfl)]
    simp only [expect_const]
    refine (expect_sample_mem_le _).trans (le_of_eq ?_)
    rw [List.length_singleton, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    rw [one_div]

/-- **Lazy forging against a random function:** from a log `log` and a table `M` whose keys are
all queried, the forgery probability against `ovr M R`, averaged over a uniform `R`, is at most
`2^{-b}`:
`𝔼_R Pr[FnForge (ovr M R) | simulate (fnImpl (ovr M R)).withLog c ((), log)] ≤ 2^{-b}`.

**Proof sketch.** Induction on `c`. A return is `expect_forge_pure_le`. A query `x` that is a key
reads the table (`ovr_of_mem`); the continuation starts from the longer log with the same table. A
new query reads `R x` (`ovr_of_not_mem`), which `expect_sample_ovr` moves into the table as a
uniform `y`; the new key `x` is queried, and the continuation's bound holds for every `y`. -/
private theorem expect_forge_ovr_le
    (c : OracleComp (bitSpec (fun _ : Fin 1 => a) (fun _ => b)) (Fin (a + b) → Bool))
    (M : List ((Fin a → Bool) × (Fin b → Bool)))
    (log : QueryLog (bitSpec (fun _ : Fin 1 => a) (fun _ => b)))
    (hM : ∀ p ∈ M.map Prod.fst, p ∈ queried log) :
    expect (sample ((Fin a → Bool) → (Fin b → Bool))) (fun R =>
      expect (simulate (fnImpl (ovr M R)).withLog c ((), log))
        (fun res => if FnForge (ovr M R) res.1 res.2.2 then (1 : ℝ) else 0)) ≤
      ((2 : ℝ) ^ b)⁻¹ := by
  induction c generalizing M log with
  | pure w =>
    simp only [simulate_pure, expect_pure]
    exact expect_forge_pure_le w M log hM
  | query i x k ih =>
    simp only [simulate_query, QueryImpl.withLog_apply, fnImpl_apply, OracleComp.pure_bind]
    by_cases hx : x ∈ M.map Prod.fst
    · have e : ∀ R : (Fin a → Bool) → (Fin b → Bool),
          ovr M R x = ovr M (fun _ _ => false) x := fun R => ovr_of_mem hx R _
      simp only [e]
      refine ih _ M _ fun p hp => ?_
      rw [queried_append]
      exact List.mem_cons_of_mem _ (hM p hp)
    · have e : ∀ R : (Fin a → Bool) → (Fin b → Bool), ovr M R x = R x :=
        fun R => ovr_of_not_mem hx R
      simp only [e]
      have hF := expect_sample_ovr M hx
        (fun (y : Fin b → Bool) (g : (Fin a → Bool) → (Fin b → Bool)) =>
          expect (simulate (fnImpl g).withLog (k y) ((), log ++ [⟨i, x, y⟩]))
            (fun res => if FnForge g res.1 res.2.2 then (1 : ℝ) else 0))
      rw [hF]
      refine (expect_mono _ fun y => ih y ((x, y) :: M) _ fun p hp => ?_).trans
        (le_of_eq (expect_const _ _))
      rw [queried_append]
      rw [List.map_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hM p hp)

/-- **Forging against a random function** [PS10, Theorem 135.4, proof, step 4]: every forger
computation `c` with `a`-bit messages and `b`-bit tags, run against the tagging oracle of a uniform
random function `R`, forges with probability at most `2^{-b}`:
`𝔼_R Pr[FnForge R | simulate (fnImpl R).withLog c ((), [])] ≤ 2^{-b}`.

**Proof sketch.** `expect_forge_ovr_le` from the empty table and the empty log (`ovr_nil`). -/
theorem expect_fnForge_random_le
    (c : OracleComp (bitSpec (fun _ : Fin 1 => a) (fun _ => b)) (Fin (a + b) → Bool)) :
    expect (sample ((Fin a → Bool) → (Fin b → Bool))) (fun R =>
      expect (simulate (fnImpl R).withLog c ((), []))
        (fun res => if FnForge R res.1 res.2.2 then (1 : ℝ) else 0)) ≤ ((2 : ℝ) ^ b)⁻¹ := by
  refine le_of_eq_of_le (congrArg _ (funext fun R => ?_))
    (expect_forge_ovr_le c [] [] fun p hp => by
      rw [List.map_nil] at hp
      exact absurd hp List.not_mem_nil)
  rw [ovr_nil]

end TCSlib.Cryptography.Authentication.PRFMAC

## ===== TCSlib/Cryptography/Authentication/MAC/FromPRF/Game.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The forgery game of a MAC with a deterministic tag

Step 3 of the proof of [PS10, Theorem 135.4], on the game side: when a MAC's tagging algorithm
returns, on the key of the generator coins `rg`, a tag `g rg m` that does not depend on its own
coins, and verification accepts `(m, σ)` exactly when `g rg m = σ`, the forgery probability is the
average over the coins `rg` of the probability that the forger forges against the tagging oracle of
the function `g rg` (`accept_forgeGame_eq`). The forger's codec is the bit codec
(`forgerCodec_eq_bitCodec`).

## Main results

* `PRFMAC.forgerCodec_eq_bitCodec`: the forger codec of a MAC is the bit codec.
* `PRFMAC.accept_forgeGame_eq`: the forgery game with a deterministic tag.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 134.2 and Theorem 135.4 (book pp. 134–135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-- **The MAC forger codec is the bit codec** with message-length queries, tag-length answers and
a message-plus-tag-length output: `M.forgerCodec n = bitCodec (fun _ => msgLen(n))
(fun _ => tagLen(n)) (msgLen(n) + tagLen(n))`.

**Proof sketch.** Codec extensionality (`MachineCodec.ext_of_fields`) on the published decoding,
entry-encoding and timeout equations (`forgerCodec_decodeMove`, `forgerCodec_encodeEntry`,
`forgerCodec_timeout`) and those of the bit codec. -/
theorem forgerCodec_eq_bitCodec (M : MAC) (n : ℕ) :
    M.forgerCodec n =
      bitCodec (fun _ : Fin 1 => M.msgLen.eval n) (fun _ : Fin 1 => M.tagLen.eval n)
        (M.msgLen.eval n + M.tagLen.eval n) := by
  apply MachineCodec.ext_of_fields
  · funext w
    exact (M.forgerCodec_decodeMove n w).trans
      (bitCodec_decodeMove (fun _ : Fin 1 => M.msgLen.eval n)
        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) w).symm
  · funext e
    exact (M.forgerCodec_encodeEntry n e).trans
      (bitCodec_encodeEntry (fun _ : Fin 1 => M.msgLen.eval n)
        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) e).symm
  · exact (M.forgerCodec_timeout n).trans
      (bitCodec_timeout (fun _ : Fin 1 => M.msgLen.eval n)
        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n)).symm

/-- **The forgery game with a deterministic tag** [PS10, Definition 134.2]: if, on the key of the
generator coins `rg`, tagging `m` returns `g rg m` whatever its coins, and verification accepts
`(m, σ)` exactly when `g rg m = σ`, then
`Pr[forgeGame A b n] = 𝔼_rg 𝔼_r Pr[FnForge (g rg) | simulate (fnImpl (g rg)).withLog (A.toComp … r)
((), [])]`.

**Proof sketch.** Unfold the game (`forgeGame_eq`, `prob_bind`) and the codec
(`forgerCodec_eq_bitCodec`). Each call of the logged tagging oracle draws tag coins and returns
`g rg m` (`tagImpl_eq`, `htag`), so it has the law of the logged `fnImpl (g rg)`
(`expect_const`), and so do whole runs (`expect_simulate_congr`). The winning test is `FnForge` by
`hacc`. -/
theorem accept_forgeGame_eq (M : MAC) (A : NUPPT) (b n : ℕ)
    (g : M.gen.Coins n → (Fin (M.msgLen.eval n) → Bool) → (Fin (M.tagLen.eval n) → Bool))
    (htag : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
      padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m))
        rt) = g rg m)
    (hacc : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
      M.Accepts n (M.gen.runAt n [] rg) m σ ↔ g rg m = σ) :
    accept (M.forgeGame A b n) =
      expect (sample (M.gen.Coins n)) fun rg => expect (sample (A.Coins n)) fun r =>
        expect (simulate (fnImpl (g rg)).withLog
            (A.toComp (bitCodec (fun _ : Fin 1 => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
              (M.msgLen.eval n + M.tagLen.eval n)) n b r) ((), []))
          (fun res => if FnForge (g rg) res.1 res.2.2 then (1 : ℝ) else 0) := by
  rw [accept_eq, MAC.forgeGame_eq, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind, forgerCodec_eq_bitCodec,
    expect_simulate_congr (M.tagImpl n (M.gen.runAt n [] rg)).withLog (fnImpl (g rg)).withLog
      (fun i x s G => ?_)]
  · refine congrArg _ (funext fun res => ?_)
    rw [prob_pure]
    exact if_congr (by rw [decide_eq_true_iff, fnForge_iff, hacc]) rfl rfl
  · simp only [QueryImpl.withLog_apply, MAC.tagImpl_eq, QueryImpl.ofComp_apply, fnImpl_apply,
      expect_bind, expect_pure, OracleComp.pure_bind, htag, expect_const]

end TCSlib.Cryptography.Authentication.PRFMAC

## ===== TCSlib/Cryptography/Authentication/MAC/FromPRF/Bound.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Game
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bound of the PRF-MAC reduction

Step 5 of the proof of [PS10, Theorem 135.4], for any MAC whose tag is a keyed function family
`F` (`n`-bit messages and tags, the key read off the generator's coins, a deterministic tag
`F_k(m)` and verification `F_k(m) = σ`): for every forger `A` and budget `q` there is a
distinguisher `D` with, at every `n`,
`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D^{q(n) · 1 + 1}) + 2^{-n}` (`exists_forgeGame_le`).

The forgery probability is the acceptance probability of `D` against `F_k` (`accept_forgeGame_eq`,
`exists_macReduction`), and its acceptance probability against a uniform random function is at
most `2^{-n}` (`exists_macReduction`, `expect_fnForge_random_le`). The functions of the scheme's
widths are those of `n` bits read through `padFin` (`eval_toOracleAdversary_width₂`).

## Main results

* `PRFMAC.eval_toOracleAdversary_width₂`: an oracle adversary read at equal widths.
* `PRFMAC.exists_forgeGame_le`: the bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 135.4 (book p. 135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-- **An oracle adversary read at equal widths:** for `m₁ = n` and `m₂ = n`, running
`D.toOracleAdversary n n n q c` against `f` is running `D.toOracleAdversary n m₁ m₂ q c` against
`f` with its inputs and outputs read at the widths `m₁`, `m₂`:
`(D^{n,n} c).eval f = (D^{m₁,m₂} c).eval (fun x => padFin m₂ ⟦f (padFin n ⟦x⟧)⟧)`.

**Proof sketch.** Substitute `m₁ = n` and `m₂ = n`; the readings are identities (`padFin_ofFn`). -/
theorem eval_toOracleAdversary_width₂ (D : NUPPT) (n q : ℕ) (c : D.Coins n) {m₁ m₂ : ℕ}
    (h₁ : m₁ = n) (h₂ : m₂ = n) (f : (Fin n → Bool) → (Fin n → Bool)) :
    (D.toOracleAdversary n n n q c).eval f =
      (D.toOracleAdversary n m₁ m₂ q c).eval
        (fun x => padFin m₂ (List.ofFn (f (padFin n (List.ofFn x))))) := by
  subst h₁ h₂
  simp only [padFin_ofFn]

/-- The functions `{0,1}^n → {0,1}^n` read at the widths `m₁ = n` and `m₂ = n`: `R` becomes
`fun x => padFin m₂ ⟦R (padFin n ⟦x⟧)⟧`. -/
private def padFunEquiv {n m₁ m₂ : ℕ} (h₁ : m₁ = n) (h₂ : m₂ = n) :
    ((Fin n → Bool) → (Fin n → Bool)) ≃ ((Fin m₁ → Bool) → (Fin m₂ → Bool)) where
  toFun R x := padFin m₂ (List.ofFn (R (padFin n (List.ofFn x))))
  invFun R' y := padFin n (List.ofFn (R' (padFin m₁ (List.ofFn y))))
  left_inv R := by
    funext y
    simp only
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn,
      ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn]
  right_inv R' := by
    funext x
    simp only
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn,
      ofFn_padFin_of_length (by rw [List.length_ofFn]; omega), padFin_ofFn]

/-- **The bound of the PRF-MAC reduction** [PS10, Theorem 135.4, proof, step 5]: let `M` be a
MAC with `n`-bit messages and tags (`hℓ`, `ht`) and `F` a keyed family, with a bijection `key n`
from the generator's coins to `n`-bit keys, such that tagging `m` on the key of `rg` returns
`F_{key rg}(m)` (`htag`) and verification accepts `(m, σ)` iff `F_{key rg}(m) = σ` (`hacc`), the
messages read at `n` bits. Then for every forger `A` and budget `q` there is a next-query machine
`D` with, at every `n`,
`Pr[forgeGame A q(n) n] ≤ prfAdv (F n) (D.toOracleAdversary n n n (q(n) · 1 + 1)) + 2⁻ⁿ`.

**Proof sketch.** `D` is `exists_macReduction` at the widths `msgLen`, `tagLen`.
1. *With `F_k`.* The tag is deterministic, so the forgery probability is the average over `rg`
   of the forgery probability against `fnImpl (g rg)`, `g rg` being `F_{key rg}` read at the
   scheme's widths (`accept_forgeGame_eq`); by `exists_macReduction` it is `D`'s acceptance
   probability against `g rg`, which is `D`'s against `F_{key rg}` at `n` bits
   (`eval_toOracleAdversary_width₂`); `key` relabels the coins (`expect_sample_equiv`).
2. *With a random function.* `D`'s acceptance probability against a uniform `R` is, through the
   widths (`padFunEquiv`, `expect_sample_equiv`) and `exists_macReduction`, the average over `A`'s
   coins (`expect_sample_comm`) of the forgery probability against a random function, at most
   `2^{-n}` (`expect_fnForge_random_le`).
3. *The PRF advantage* is the absolute gap between the two (`prfAdv_def`, `distAdv_def`,
   `Bridge.acceptProb_eq`, `Bridge.acceptGame_eq`, `oracleDist_apply`); this is the published
   `TCSlib.Cryptography.prfAdv_eq_expect`. -/
theorem exists_forgeGame_le (M : MAC) (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hℓ : ∀ n, M.msgLen.eval n = n) (ht : ∀ n, M.tagLen.eval n = n)
    (key : ∀ n, M.gen.Coins n ≃ (Fin n → Bool))
    (htag : ∀ n rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
      M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m)) rt =
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))))
    (hacc : ∀ n rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
      M.Accepts n (M.gen.runAt n [] rg) m σ ↔
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) = List.ofFn σ)
    (A : NUPPT) (q : PolyExpr) :
    ∃ D : NUPPT, ∀ n, accept (M.forgeGame A (q.eval n) n) ≤
      prfAdv (F n) (D.toOracleAdversary n n n ((macBudget q).eval n)) + (2 : ℝ)⁻¹ ^ n := by
  obtain ⟨D, hD⟩ := exists_macReduction M.msgLen M.tagLen q A
  refine ⟨D, fun n => ?_⟩
  -- The tag function at the scheme's widths.
  let g : M.gen.Coins n → (Fin (M.msgLen.eval n) → Bool) → (Fin (M.tagLen.eval n) → Bool) :=
    fun rg m => padFin _ (List.ofFn (F n (key n rg) (padFin n (List.ofFn m))))
  have hg_tag : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
      padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m))
        rt) = g rg m := fun rg m rt => by
    rw [htag]
  have hg_acc : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
      M.Accepts n (M.gen.runAt n [] rg) m σ ↔ g rg m = σ := fun rg m σ => by
    rw [hacc]
    constructor
    · intro h
      show padFin _ (List.ofFn (F n (key n rg) (padFin n (List.ofFn m)))) = σ
      rw [h, padFin_ofFn]
    · intro h
      rw [← h]
      exact (ofFn_padFin_of_length (by rw [List.length_ofFn, ht])).symm
  -- With `F_k`: the forgery probability.
  have hreal : accept (M.forgeGame A (q.eval n) n) =
      expect (sample (Fin n → Bool)) fun k => expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval (F n k) = true
        then (1 : ℝ) else 0 := by
    rw [accept_forgeGame_eq M A (q.eval n) n g hg_tag hg_acc, ← expect_sample_equiv (key n)]
    refine congrArg _ (funext fun rg => ?_)
    rw [← hD n (g rg)]
    refine congrArg _ (funext fun c => ?_)
    rw [eval_toOracleAdversary_width₂ D n _ c (hℓ n) (ht n) (F n (key n rg))]
  -- With a random function: at most `2⁻ⁿ`.
  have hrand : expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
      expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
        then (1 : ℝ) else 0) ≤ (2 : ℝ)⁻¹ ^ n := by
    have he : ∀ R : (Fin n → Bool) → (Fin n → Bool),
        (expect (sample (D.Coins n)) fun c =>
          if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
          then (1 : ℝ) else 0) =
        expect (sample (D.Coins n)) fun c =>
          if (D.toOracleAdversary n (M.msgLen.eval n) (M.tagLen.eval n) ((macBudget q).eval n)
            c).eval (padFunEquiv (hℓ n) (ht n) R) = true then (1 : ℝ) else 0 := fun R => by
      refine congrArg _ (funext fun c => ?_)
      rw [eval_toOracleAdversary_width₂ D n _ c (hℓ n) (ht n) R]
      rfl
    simp only [he]
    rw [expect_sample_equiv (padFunEquiv (hℓ n) (ht n)) (fun R' =>
      expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n (M.msgLen.eval n) (M.tagLen.eval n) ((macBudget q).eval n)
          c).eval R' = true then (1 : ℝ) else 0)]
    simp only [hD n]
    rw [expect_sample_comm]
    refine (expect_mono _ fun r => expect_fnForge_random_le _).trans (le_of_eq ?_)
    rw [expect_const, ht n, inv_pow]
  -- The PRF advantage is the gap.
  rw [hreal, TCSlib.Cryptography.prfAdv_eq_expect (F n) (D.toOracleAdversary n n n _)]
  linarith [le_abs_self ((expect (sample (Fin n → Bool)) fun k => expect (sample (D.Coins n))
    fun c => if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval (F n k) = true
      then (1 : ℝ) else 0) -
    expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
      expect (sample (D.Coins n)) fun c =>
        if (D.toOracleAdversary n n n ((macBudget q).eval n) c).eval R = true
        then (1 : ℝ) else 0))]

end TCSlib.Cryptography.Authentication.PRFMAC

## ===== TCSlib/Cryptography/Authentication/MAC/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Authentication.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Message authentication codes and their forgery game

## Main definitions

`MAC` gives the fixed-width scheme interface with uniform key generation and tagging,
polynomial-time verification, and perfect correctness for every coin string. At parameter
`n`, messages and tags have lengths given by the scheme's polynomials, and tagging output is
read with `padFin`.

`MAC.forgeGame` runs a machine against a logged tagging oracle. A forgery succeeds when
verification accepts the output and the message is fresh. `MAC.Secure` bounds the forgery
probability by a negligible function for each non-uniform PPT forger and polynomial query
budget.

## Main results

`MAC.forgeGame_eq` exposes the experiment. `MAC.secure_iff` states its security bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definitions 134.1 and 134.2.
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- A **message authentication code** over `ℓ(n)`-bit messages with `t(n)`-bit tags
[PS10, Definition 134.1]: a key generator `Gen(1^n)`, a tagging algorithm `Tag_k(m)` (activated on
`⟨k, m⟩`, its output read as `t(n)` bits), and a deterministic polynomial-time `Ver` on
`⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩`, with perfect correctness. -/
structure MAC where
  /-- The message length `ℓ(n)`. -/
  msgLen : PolyExpr
  /-- The tag length `t(n)`. -/
  tagLen : PolyExpr
  /-- The key generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- The tagging algorithm `Tag_k(m)`. -/
  tag : NUPPT
  /-- The verification algorithm; `[true]` is "accept". -/
  ver : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Tag` is a PPT. -/
  tag_uniform : tag.Uniform
  /-- `Ver` is deterministic polynomial-time. -/
  ver_poly : PolyTimeComputable ver
  /-- Perfect correctness, for every coin string [PS10, Definition 134.1 (4)]. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (rt : tag.Coins n),
    ver (atParam n (pairEncode (gen.runAt n [] rg) (pairEncode (List.ofFn m)
      (List.ofFn (padFin (tagLen.eval n) (tag.runAt n (pairEncode (gen.runAt n [] rg)
        (List.ofFn m)) rt)))))) = [true]

namespace MAC

variable (M : MAC)

/-- `Ver_k(m, σ)` accepts. -/
def Accepts (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) : Prop :=
  M.ver (atParam n (pairEncode k (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true]

/-- A MAC accepts `(m, σ)` exactly when its verifier on `⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩` returns
`[true]` [PS10, Definition 134.1]. -/
theorem accepts_iff (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) :
    M.Accepts n k m σ ↔
      M.ver (atParam n (pairEncode k (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] :=
  Iff.rfl

instance (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) : Decidable (M.Accepts n k m σ) :=
  inferInstanceAs (Decidable (_ = _))

/-- The one tagging oracle at parameter `n`. -/
abbrev oracleSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)

/-- The tagging oracle has message-length queries and tag-length answers:
`oracleSpec n = bitSpec (fun _ => msgLen(n)) (fun _ => tagLen(n))`. -/
theorem oracleSpec_eq (n : ℕ) :
    M.oracleSpec n = bitSpec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n) := rfl

/-- The **tagging oracle** `Tag_k(·)`: each query `m` is answered by `Tag_k(m)` with fresh coins. -/
noncomputable def tagImpl (n : ℕ) (k : List Bool) : QueryImpl (M.oracleSpec n) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => (ProbComp.sample (M.tag.Coins n)).bind fun rt =>
    .pure (padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode k (List.ofFn m)) rt))

/-- The tagging implementation samples fresh tag coins and returns the tag padded to its
declared length, using `QueryImpl.ofComp` [PS10, Definition 134.2]. -/
theorem tagImpl_eq (n : ℕ) (k : List Bool) :
    M.tagImpl n k =
      QueryImpl.ofComp (fun _ m => (ProbComp.sample (M.tag.Coins n)).bind fun rt =>
        .pure (padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode k (List.ofFn m)) rt))) :=
  rfl

/-- The codec of forgers: one oracle, and a final output of `ℓ(n) + t(n)` bits read as `(m, σ)`. -/
def forgerCodec (n : ℕ) :
    MachineCodec (M.oracleSpec n) (Fin (M.msgLen.eval n + M.tagLen.eval n) → Bool) :=
  bitCodec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n)

/-- The MAC forger codec decodes moves with `decodeBitMove` at message and tag lengths. -/
theorem forgerCodec_decodeMove (n : ℕ) (w : List Bool) :
    (M.forgerCodec n).decodeMove w =
      decodeBitMove (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
        (M.msgLen.eval n + M.tagLen.eval n) w :=
  bitCodec_decodeMove (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
    (M.msgLen.eval n + M.tagLen.eval n) w

/-- The MAC forger codec encodes a log entry `(i, m, σ)` as `⟨1^i, ⟨m, σ⟩⟩`. -/
theorem forgerCodec_encodeEntry (n : ℕ)
    (e : Σ i, (M.oracleSpec n).dom i × (M.oracleSpec n).rng i) :
    (M.forgerCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
    (M.msgLen.eval n + M.tagLen.eval n) e

/-- When its query budget expires, the MAC forger codec returns `zeroBits (msgLen(n) +
tagLen(n))`. -/
theorem forgerCodec_timeout (n : ℕ) :
    (M.forgerCodec n).timeout = zeroBits (M.msgLen.eval n + M.tagLen.eval n) :=
  bitCodec_timeout (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
    (M.msgLen.eval n + M.tagLen.eval n)

/-- **The MAC forgery game** [PS10, Definition 134.2] at parameter `n`, for the forger `A` with
query budget `b`: sample a key `k ← Gen(1^n)` and `A`'s coins, run `A` against the logged tagging
oracle, and win when `A`'s output `(m, σ)` is accepted and `m` was not queried. -/
noncomputable def forgeGame (A : NUPPT) (b n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (M.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (M.tagImpl n (M.gen.runAt n [] rg)).withLog (A.toComp (M.forgerCodec n) n b r)
      ((), [])).bind fun res =>
    .pure (decide (M.Accepts n (M.gen.runAt n [] rg) (splitBits res.1).1 (splitBits res.1).2 ∧
      ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))

/-- The MAC forgery game samples the key and forger coins, runs the logged tagging oracle,
and tests acceptance and message freshness [PS10, Definition 134.2]. -/
theorem forgeGame_eq (A : NUPPT) (b n : ℕ) :
    M.forgeGame A b n =
      (ProbComp.sample (M.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (M.tagImpl n (M.gen.runAt n [] rg)).withLog (A.toComp (M.forgerCodec n) n b r)
          ((), [])).bind fun res =>
        .pure (decide (M.Accepts n (M.gen.runAt n [] rg) (splitBits res.1).1 (splitBits res.1).2 ∧
          ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))) := rfl

/-- **A secure MAC** [PS10, Definition 134.2]: for every non-uniform PPT forger and every
polynomial query budget, the forgery probability is negligible. -/
def Secure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, accept (M.forgeGame A (q.eval n) n) ≤ ε n

/-- A MAC is secure exactly when every machine and polynomial query budget have a negligible
upper bound on forgery acceptance [PS10, Definition 134.2]. -/
theorem secure_iff :
    M.Secure ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, accept (M.forgeGame A (q.eval n) n) ≤ ε n := Iff.rfl

end MAC

end TCSlib.Cryptography.Authentication

## ===== TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import TCSlib.Cryptography.Games.Bridges.Experiments
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Keyed function families, random functions and the PRF advantage

At one fixed value of the security parameter, a function ensemble [Gar26, Definition 3.6]
is a random variable ranging over functions `I → O`. Following the concrete-layer
convention, random variables are pushforwards of uniform seeds, so an efficiently
computable ensemble [Gar26, Definition 3.8] is a *keyed family* `F : K → I → O`, sampled
by drawing a uniform key `k : K` and outputting `F k`. The random function ensemble
[Gar26, Definition 3.7] is the uniform distribution on the finite type `I → O`, sampled
by the identity.

The PRF advantage of an oracle adversary `A` [Gar26, Definition 3.9] is
`|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|`. It is the distinguishing advantage
`distAdv` of the oracle adversary viewed as a distinguisher of whole functions; the
adversary only ever sees the values at its queries, which is what makes the advantage
meaningful for bounded-query adversaries.

The efficiency conditions of Definition 3.8 (a polynomial-time key generator and
evaluator) and the quantification over non-uniform PPT adversaries of Definition 3.9
belong to the asymptotic layer; here the only resource tracked is the query bound
`OracleAdversary.BoundedBy`.

## Main definitions

* `randomFunction I O`: the sampler of a uniform random function `I → O`.
* `prfAdv F A`: the PRF advantage of the oracle adversary `A` against the keyed family `F`.

## Main results

* `prfAdv_eq`: the advantage written out as a difference of two probabilities.
* `prfAdv_nonneg`.
* `prfAdv_eq_expect`: the advantage as the gap between two nested expectations of the
  game-hopping layer (`Games.ProbComp.expect`), keys or function table outside, coins inside.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.1, Definitions 3.6–3.9.
-/

namespace TCSlib.Cryptography

variable {K ρ σ σ' γ : Type*} {I O : Type}

/-- The sampler of a uniformly random function `I → O`: the seed is the function table
itself, a uniform element of the finite type `I → O`. This is the random function
ensemble `R_n` of [Gar26, Definition 3.7] at one value of the security parameter; its
seed has `|I| · log |O|` bits, `n · 2^n` for `I = O = {0,1}^n`. -/
def randomFunction (I O : Type*) : (I → O) → I → O := id

/-- The random-function sampler returns its seed, the function table itself:
`randomFunction I O f = f`. -/
theorem randomFunction_apply (I O : Type*) (f : I → O) : randomFunction I O f = f :=
  rfl

/-- The PRF advantage of the oracle adversary `A` against the keyed function family
`F : K → I → O` (a function ensemble [Gar26, Definitions 3.6 and 3.8], keys uniform in
`K`): `|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|` with `R` a uniform random
function, [Gar26, Definition 3.9] at one value of the security parameter. `F` is
pseudorandom when this is negligible for every efficient adversary; the concrete layer
bounds it by explicit reductions instead. -/
noncomputable def prfAdv [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : ℝ :=
  distAdv F (randomFunction I O) (oracleDist A)

/-- The defining equation of `prfAdv`: the distinguishing advantage of `oracleDist A` between
the keyed family and the random-function sampler,
`prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`. -/
theorem prfAdv_def [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) :
    prfAdv F A = distAdv F (randomFunction I O) (oracleDist A) :=
  rfl

/-- The PRF advantage written out: the difference between the probability that `A`
accepts with oracle `F k` for uniform `k` and coins `r`, and the probability that it
accepts with a uniform random function `R` as oracle. [Gar26, Definition 3.9]. -/
theorem prfAdv_eq [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) :
    prfAdv F A = |uprob (fun z : K × ρ => (A z.2).eval (F z.1) = true) -
      uprob (fun z : (I → O) × ρ => (A z.2).eval z.1 = true)| := by
  rw [prfAdv_def, distAdv_def, acceptProb_def, acceptProb_def]
  simp only [oracleDist_apply, randomFunction_apply]

/-- The PRF advantage is nonnegative. -/
theorem prfAdv_nonneg [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : 0 ≤ prfAdv F A := by
  rw [prfAdv_def, distAdv_def]
  exact abs_nonneg _

section Expect

open Games ProbComp

/-- **The PRF advantage as expectations**: for a keyed family `F : K → I → O` and an oracle
adversary `A` with coins in `ρ`, all finite and nonempty,
`prfAdv F A = |𝔼_k 𝔼_c [A(c)^{F k} = 1] − 𝔼_R 𝔼_c [A(c)^R = 1]|`, where `k` is a uniform key,
`R` a uniform random function `I → O` and `c` uniform coins ([Gar26, Definition 3.9] in the
expectation form of the game-hopping layer).

**Proof sketch.** Unfold to the distinguishing advantage of `oracleDist A` (`prfAdv_def`,
`distAdv_def`). Each acceptance probability is the acceptance of the game that samples the seed
(the key, resp. the function table) and then the coins (`Bridge.acceptProb_eq`, `accept_eq`,
`Bridge.acceptGame_eq`); `prob_bind` and `prob_pure` turn the game into the nested expectation,
and `oracleDist_apply`, `randomFunction_apply` read off the verdict. -/
theorem prfAdv_eq_expect {K ρ : Type} [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
    [Fintype O] [Nonempty O] [Fintype ρ] [Nonempty ρ] (F : K → I → O)
    (A : OracleAdversary ρ I O) :
    prfAdv F A =
      |expect (sample K)
          (fun k => expect (sample ρ) fun c => if (A c).eval (F k) = true then (1 : ℝ) else 0) -
        expect (sample (I → O))
          (fun R => expect (sample ρ) fun c => if (A c).eval R = true then (1 : ℝ) else 0)| := by
  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
  congr 2
  · refine congrArg _ (funext fun k => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply]
  · refine congrArg _ (funext fun R => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]

end Expect

/-- Two samplers producing the same sample from every seed have the same acceptance
probability. -/
theorem acceptProb_congr [Fintype σ] [Fintype ρ] {X Y : σ → γ} (h : ∀ s, X s = Y s)
    (D : γ → ρ → Bool) : acceptProb X D = acceptProb Y D := by
  rw [funext h]

end TCSlib.Cryptography
