# Gate 38 · PRGs put BPP in subexponential time (`derand`, [PS10, §8.2, Theorem 180.1]) and the seed-majority host H17

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #326](https://github.com/Shilun-Allan-Li/tcslib/pull/326) at
  `c27005d67298f79c785a4e8ac1648da0a67d3614` (branch `land/pass-shelat-derand`, tree
  `7ea8bf7eebce9ed3be8403a80b96a1f79cc8216e`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `6ce4658db08a1dc2a03a149987197660db078011` (the merge base).
  - The fill was issued (`issued-r2`) on `01de2d8baed9113e4a099e13c5d50c81e6dbc66f`, the records tip after #303,
    #305–#309, #311 and #312. The 15 PR paths are byte-identical at the issue base and at `6ce4658d`
    (`pack-checks/rebase.txt`). The Lean delta between them (#314–#317, 16 files) is covered by the review's build.
  - The records tip is now `c2f6adeb3f3de2a21352a57e64c6a11a79cc220e`. Since `6ce4658d` it has merged #313
    (learning) and, on 2026-11-16, #318 (sc-ot), #319 (canonizer) and #323 (sc-garble).
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...c27005d6`, which equals `6ce4658d..c27005d6`
    byte for byte (15 paths, 1741 insertions, 36 deletions).
  - **Open PRs and the tip.** `git merge-tree --write-tree` of the head with the tip, #324 and #327 (and with the merged
    heads of #318, #319, #323) is clean in each case, and no path is shared. The combined build of all open PRs covers
    the merged state (question 8). **Pending merge condition** (not an audit item): the merge order, #324 last.
- **Commits:** 5 (`pack-checks/rebase.txt`), all committed by Claude and SSH-signed.
  - The Codex worker's 4 commits (on Seyoon's Mac), author Seyoon Ragavan kept. They were applied with `git am` with
    the delivered committer data; the 4 worker hashes reproduce unsigned. Then rebased onto `6ce4658d`:
    `git range-diff 01de2d8b..5e12a169 6ce4658d..941b5a1e` is 4/4 `=`. At `941b5a1e` the 15 files are byte-identical
    to the worker's `src/` (exchange `186ffb99`).
  - Landing edit **LE-doc** `c27005d67298f79c785a4e8ac1648da0a67d3614` (F-04): the formula docstring of
    `Randomized.inBPP_iff`, docstring only. Author and committer Claude.
- **Scope:** a **proof audit** of three admitted, frozen statements:
  - `Complexity.exists_seedMajorityTM`, **host H17** (`Randomized/SeedMajority.lean:207`; [AB09, §7.1, p. 126];
    [PS10, §8.2, Theorem 180.1, step 4]): one finite machine decides the strict-majority-over-seeds language within
    `c · (2^{w(n)} (n+1)^e)` and keeps every head within the same envelope;
  - `Complexity.seedMajority_mem_DTIME`, its `DTIME` corollary (`:251`);
  - `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp`, **[PS10, Theorem 180.1]** (`Randomness/Derandomization.lean:113`):
    a secure PRG puts BPP in `DTIME(⌈2^{n^ε}⌉)` for every `ε > 0`.

  Theorem 180.1 passed the prong D statement phase (ruling D-6) and Gate 06. The host and its corollary passed Gate
  28 (round 1 HOLD, round 2 CLEAR). All three are frozen.
- **Brief:** `fills/derand/issued-r2/brief.md` on the records branch (SHA-256 `5375acb0…`), in `verification.zip`
  under `records/`. Two checkpoints (the harvest E1–E3 and the corollary; the host) and the final (Theorem 180.1). It
  sets the owned files and their helper directories, the three named scope exceptions, the frozen-statement rule, the
  Gate 28 route notes, the edge cases, Rule 10 (projection coercions and `PolyExpr.eval` as notation, coe seals
  canonical), the docstring and sketch rules, the G26-N1 error count and the evidence-completeness rule.

Lean paths below are under `TCSlib/Complexity/` or `TCSlib/Cryptography/`; `Rz/` is `Randomized/`, `Dz/` is
`Randomness/Derandomization/`.

## What changed

15 Lean files (`source-head.json`; every line at most 99 characters):

| Files (lines at the head) | Role |
|---|---|
| `ClassP/DTIME` (117 → 135) | shared, frozen: **E2** `mem_DTIME_iff` and **E3** `FinTM.decidesInTime_iff` |
| `Rz/Build/IterateFind` (556 → 801) | shared, frozen: **E1** `IterateFind.computesFunInTime_find` |
| `Rz/Classes` (1403 → 1415) | shared, frozen: **SR-01** `Randomized.inBPP_iff` |
| `Rz/SeedMajority` (261), with `Rz/SeedMajority/{Words, State, Enumeration, Envelope}` (172, 233, 127, 63) | owned: the host H17 and its corollary; the state word, the counting loop and the envelope |
| `Randomness/Derandomization` (127), with `Dz/{RootSchedule, AdviceGap, Expanded, CoinGap, Majority, TimeBound}` (173, 139, 70, 95, 159, 142) | owned: Theorem 180.1; the integer root, the bad-input advice, the expanded generator, the coin gap, the majority identification, the time bound |

**The proof** (review § *Content*; `evidence/logs/duplication-review.txt`; the worker's REPORT § *Checkpoints and proof
route*):
- **H17** takes **one** machine `M` from `SeedMajority.exists_countingTM`. The decision clause comes through
  `FinTM.decidesInTime_iff`, `computesFunInTime_iff` and `indicator_def`, and the envelope through
  `envelope_of_computesInTime` of the same computation, both at `B(n) = c · (2^{w(n)} (n+1)^e)`.
  - **The Gate 28 route:** binary fuel `Nat.bits (2^w)`; the state `⟨x, ⟨i, a⟩⟩` from `⟨x, ⟨0, 0⟩⟩`; the terminal rank
    `R = 2^w` in range (`2^w + 1` ranks); the direct bound `2^w + 2 ≤ 3 · 2^w`, without `final_bound`; no admitted loop
    or timed-conditional spec.
  - **E1** supplies the generic-fuel search with the size-guarded invariant closed under the total step.
- **The corollary** is `⟨e, mem_DTIME_iff.mpr ⟨c, M, hM⟩⟩`. It reads neither `DTIME`, `DecidesInTime` nor
  `DecidesInTimeVia` by definition (the Gate 28 round-2 revert).
- **Theorem 180.1** follows the paper route checked at Gate 28:
  - the verifier from `inBPP_iff` and `polyTimeModel_eff_iff`;
  - an integer `d ≥ 2` with `1/d < min(ε, 1)` and the integer ceiling root `ℓ(n) = min{t | n ≤ t^d}`;
  - the expanded generator `P(s) = a(s^d + 1)^k + s + 1` by `prg_expand` and truncation;
  - non-uniform bad-input advice at gap `1/12`, contradicted by `PRG.secure_iff`, giving a threshold `n₀`;
  - the piecewise width and test (true coins below `n₀`, the generator from `n₀` on);
  - margins **7/12 and 5/12**, with `half_lt_randProb_iff` identifying `L` with the strict-majority language of
    `(V'', w)`. There is **no finite table**;
  - the host through `seedMajority_mem_DTIME`, the eventual time bound `log₂(2^{w(n)} (n+1)^e) ≤ n^ε`, one constant for
    the finitely many exceptions, `DTIME.mono` and `Randomized.DTIME_const_mul_subset`.

**Statements** (`evidence/statements/`, re-checked in `pack-checks/headers.txt`, `shared.txt` and `decls2-*.tsv`):
- decls2 from the issue base and from `6ce4658d` to the head gives **53 ADDED, 0 CHANGED, 0 REMOVED**; 0 rows for
  LE-doc (`941b5a1e..c27005d6`).
- The frozen check (`landing/frozen-check.txt`, the five pre-existing files) finds headers and every definition body
  identical, in order. It has **3 PROSE** differences, the three targets' docstrings: their *Status* and sketch, which the
  brief allows.
- Re-checked from git objects:
  - `SeedMajority` has 3 declarations and `Derandomization` 4, with identical headers; only the targets' docstrings
    change.
  - `DTIME` goes from 4 to 6 declarations, `IterateFind` from 21 to 22 and `Classes` from 61 to 62. Every base header
    and definition block is identical.
- `touched`: 3 CHANGED (the targets), 4 ADDED in existing files (E1, E2, E3, SR-01), 50 new-file declarations, 90
  UNCHANGED.

## Rulings and records in force

1. **The pre-approved scope exceptions (Seyoon, 2026-11-15): exactly three**, as in the brief. **E1**: one public
   generic-fuel `IterateFind.computesFunInTime_find`, reusing the private helpers in place. **E2**: `mem_DTIME_iff`
   beside `DTIME`. **E3**: `FinTM.decidesInTime_iff` beside `DecidesInTime`. E2 and E3 are `Iff.rfl`, with formula
   docstrings and no attribute. E3 is Gate 28's ruling N28-R2-01.
2. **SR-01, confirmed by Seyoon (2026-11-16)** (review F-02). `Randomized.inBPP_iff` (`Iff.rfl`) in the frozen
   `Rz/Classes.lean`, together with the inherited file-size exception: 1403 → **1415 lines**. The worker's request
   and the recorded answer are `worker/evidence/worker/scope-request/SR-01/`.
3. **F-01 is ruled debt (Seyoon, 2026-11-16: "debt now, fix after"), DW-5** in `deferred-work.md`.
   - E1 reads `hostTM`'s `k`/`State` fields by definition. That gives **9 new Rule-10 seal failures**, line-for-line
     copies of the **11** that the frozen `polyTimeComputable_find` already has at the base.
   - The worker disclosed this (EX-02) and proposed SR-02, typed-view readers, which went unanswered.
   - A maintainer follow-up PR will add the SR-02 readers (`ModuleHost`/`IterateFindHost`) and re-derive E1 and
     `polyTimeComputable_find` through them, clearing all 20. That re-derivation is pre-approved.
   - **Not a finding:** the 20 failures attributed in question 3.
4. **The fourth pre-approval (decision log, 2026-11-15)** was to re-derive the frozen `polyTimeComputable_find` from
   E1, proof only. It **did not reach the worker**: the issued brief, its dispatch and the Codex prompt all say
   "exactly three" (review note, `evidence/logs/duplication-review.txt` item 1).
   - So `polyTimeComputable_find` is unchanged, and E1's proof repeats 196 of its 228 stripped lines (review F-03,
     disclosed in the REPORT's *Overlap and reuse*).
   - The repetition is part of the DW-5 follow-up. **Not a finding.**
5. **Rule 10 notation** (as the brief):
   - `PolyExpr.eval` (Q1, the user, 2026-11-07): seal A exempts it and is canonical;
   - reducible abbreviations;
   - projection coercions such as `FinDist`'s `⟨FinDist.prob⟩` (Seyoon, 2026-11-14). **coe-A is canonical**; the
     strict variant is run and its differences attributed.
6. **F-05 (environment, not a delivery finding).** The shared pinned Mathlib build lacks
   `Pow/NthRootLemmas.olean`, imported by `Dz/RootSchedule`. The review compiled that one module from the pinned source
   into an overlay, and the first build's 8 failures were retried. Integration builds do the same.
7. **LE-doc (the maintainer's landing edit, F-04): docstrings only.** The 4-line prose of `inBPP_iff` is replaced by
   4 lines stating its statement, with the [AB09, Definition 7.3] tag, so the file stays at 1415 lines. Evidence
   `landing-ledoc/` (`977bbe89…`).
8. **The worker was Codex**, on Seyoon's Mac, single-agent, with a host-wide 3-slot Lean cap (Seyoon, 2026-11-15;
   `records/…/fills/codex-host-2026-11-15/`). The review's slot check: never above 3.
9. **The facade-completeness lint baseline (#305):** 92 FAIL / 101 WARN (Cryptography), 25 / 391 (Complexity).

## What is frozen

- **The three targets' statements** and statement prose, and every pre-existing declaration of the five pre-existing
  files (`ClassP/DTIME`, `Rz/Build/IterateFind`, `Rz/Classes`, `Rz/SeedMajority`, `Randomness/Derandomization`): header
  bytes and order, and whole definitions. In particular `polyTimeComputable_find` and `final_bound`, whose whole text is
  byte-identical at the head (`pack-checks/shared.txt`).
- **Every other file.** In particular `Games/Efficiency.lean`, `Rz/PolyTimeModel.lean`, the `ModuleHost`/`IterateFindHost`
  layer and `Pseudorandom/Generators/*`.
- **The landing edit:** LE-doc, one docstring.

## Questions for the audit

**1. Correctness against the frozen statements and the book**
- **H17:** is it **one** machine for both clauses, with the decision clause and the envelope from the same
  computation, at `c · (2^{w(n)} (n+1)^e)`?
  - Is the Gate 28 route as noted: binary fuel `Nat.bits (2^w)`; both counters at most `w(n) + 1` bits, including the
    terminal value; the terminal rank in range; `2^w + 2 ≤ 3 · 2^w`; no `final_bound` for exponential fuel?
  - Is the invariant closed under the **total** step (the size guard), with no fixed state bound assumed after
    termination?
- **The corollary:** is it a pure transport through `mem_DTIME_iff` (no definitional read of `DTIME`/`DecidesInTime`)?
- **Theorem 180.1:**
  - the PRG expansion, with `P(s) > s` and `m(n) ≤ P(ℓ(n))` at every length, `0` included;
  - the advice argument, with infinitely many bad seed lengths from infinitely many bad input lengths, and
    `|x_s| ≤ s^d`;
  - the piecewise width and test, polynomial-time, without a finite table;
  - the **margins 7/12 and 5/12**, and `half_lt_randProb_iff`;
  - the eventual time bound and the constant absorbing the exceptions.

  Does the proof follow [PS10, Theorem 180.1] and the route Gate 28 checked?
- **The edge cases of the brief:** ties (the host rejects them; the `1/12` margin keeps the probabilities off `1/2`);
  `w(n) = 0`; `m = 0` coins; `n = 0` and small `n`; `ε ≥ 1` (`d = 2`); seed lengths shared by many input lengths; the
  generator's envelope at `s = ℓ(n)`; the terminal rank `R` in the search range; a witness `c = 0` (impossible,
  `FinTM.not_computesInTime_zero`). Do the rewritten sketches describe the delivered proof?

**2. Frozen-statement integrity and the shared files**
- Are the five pre-existing files' headers and definitions byte-identical, in order (`landing/frozen-check.txt`,
  `pack-checks/headers.txt`)? Is decls2 **53 ADDED / 0 CHANGED / 0 REMOVED**?
- **Are the shared-file additions exactly E1–E3 plus SR-01?** Re-checked from git objects (`pack-checks/shared.txt`):

  | File | Added declarations | Diff | The base file is the head with lines inserted only |
  |---|---|---|---|
  | `ClassP/DTIME` | `decidesInTime_iff` (:83), `mem_DTIME_iff` (:105) | +18/−0, two hunks | yes |
  | `Rz/Build/IterateFind` | `computesFunInTime_find` (:575) | +245/−0: E1's 3-line bullet in the module docstring's list (line 76) and the theorem after `polyTimeComputable_find` | yes |
  | `Rz/Classes` | `inBPP_iff` (:299) | +12/−0, one hunk; 1415 lines | yes |

  - E2 and E3 equal the brief's draft signatures and bodies (whitespace-normalised).
  - SR-01's added lines before LE-doc equal the worker's scope-request patch; its code is unchanged by LE-doc.
  - `polyTimeComputable_find` and `final_bound` are byte-identical in whole (header line 334 at the head, 331 at
    the base).
  - The owned files only add imports of their helper directories (and `Rz/QuasiPolyHierarchy` in `Derandomization`).
    The 10 new files are under `Rz/SeedMajority/` and `Dz/`.

  The brief allows module-docstring changes, so E1's bullet at `IterateFind.lean:76` is in scope. Check that nothing
  else was added.

**3. Rule 10: is F-01's attribution exact, and does nothing else fail?**
- The seals cover the 15 files at the head and the base files at the base, in four variants (strict and coe, A and B),
  run with `-DmaxErrors=0`, with install and EOF records in every row (`evidence/logs/seal-head-*.tsv`,
  `seal-base-*.tsv`).
  - The 20 Derandomization-family probes (2787–3928 requests) overflowed Lean's stack unchunked. They were regenerated
    with `SEAL_CHUNK=2200`, every part with install and EOF records (`evidence/logs/seal-chunk-records.txt`).
  - Coe probes byte-identical to their strict ones were not re-run (`seal-coe-identical.txt`).
- **The only failing probe is `IterateFind`**: 20 errors in A and in B, strict = coe. At the base it has 11 errors.
  Re-checked from git objects (`pack-checks/rule10.txt`), mapping each failing line of `evidence/logs/seal-iteratefind-lines.txt`
  to the declaration containing it at the sealed tree (`IterateFind.lean` blob = the head's):
  - lines 362 ×2, 380, 382, 389, 390, 433, 434, 539, 555, 556 → `polyTimeComputable_find` (**11**, pre-existing, the
    same lines at the base);
  - lines 602 ×2, 622, 624, 631, 632, 676, 677, 799 → `computesFunInTime_find` (**9**, E1).
  - Every other head probe in every variant has 0 errors; at the base only `IterateFind` fails (11). New failing
    declarations: exactly E1.
- Is the attribution exact, and does any other declaration read a foreign definition outside a published reader? The
  rows to know:
  - the explicit-unfold scan (`evidence/logs/scan2-head.log`): 743 items, 1 "foreign", which is a local
    `let P : PolyExpr` resolved by name to the class `Complexity.P` (a false positive);
  - the controls (`evidence/logs/ctlcheck.log` ALL_OK). Coe has 16 probes and 22 sealed negatives; strict has 20 and
    33, and `ctlCoeReader` fails in the 2 strict sealed AdviceGap probes (the harness effect,
    `controls-strict-attribution.txt`). Rows: `PolyExpr.eval`, the `FinDist` CoeFun instance, `DTIME`/`mem_DTIME_iff`,
    `DecidesInTime`/`decidesInTime_iff`, `InBPP`/`inBPP_iff`, `ModuleHost.hostTM`/`hostTM_k`,
    `SeedMajority.word`/`word_eq` and `Derand.ceilRoot`/`ceilRoot_eq`.

**4. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the worker's `## Overlap and reuse` table (`worker-report.md`) and the review's notes
  (`evidence/logs/duplication-review.txt`)? **Anything undisclosed is a major.**
- The recorded relations: E1 repeating `polyTimeComputable_find` (ruling 4); `envelope_of_computesInTime` beside
  `ModuleHost.Clean.envelope` and `MultiTapeTM.abs_workTapePos_runFrom_sub_le` (same argument, different
  hypotheses); `SeedMajority.count_all` beside `Randomized.randProb_bitsVal` (card form; not disclosed by the worker,
  no restatement); the private `Derand.short_poly` specializing `StateLoop.lenLe_comp` (disclosed, promotion
  requested); the `ceilRoot` family on Mathlib's `Nat.nthRoot`; `eff_mapCoins` beside `Classes.lean:387/445`. Are these
  near relatives, not restatements?
- Mechanical aids (`pack-checks/dupscan.txt`): no line added since the base uses a DL-47-class reader. A statement scan
  (binders and type, whitespace-normalised) of the 46 new theorems has **0 hits**, both against the files the tip and
  #324, #327 changed and against all 20668 theorems of the other 1275 TCSlib files. No new name is declared in a file
  any comparator changed (`pack-checks/namecheck.txt`).

**5. The landing edit**
- **LE-doc (ruling 7):** `941b5a1e..c27005d6` changes one file, `Rz/Classes.lean`, +4/−4. The file is identical with
  doc comments deleted; 1 docstring changes; 1415 lines; max width 97 (`pack-checks/lecheck.txt`;
  `landing-ledoc/`: `landing/derand-le-doc.diff`, `checks/derand-doconly.txt`).
  - Does the new docstring state `inBPP_iff`'s statement in the header's order?
  - The post-edit docaudit (`statements/derand-post/docaudit.tsv` there) gives 49 OK and 7 NO-FORMULA: six
    `polyTimeComputable_*` and `eff_mapCoins`, Prop formulas without a relation symbol (a tool limitation). Are those
    7 acceptable?
- **The build ran at `941b5a1e`, before LE-doc.** Of its 565 built sources, 564 equal the head's blobs; the one that
  differs is `Rz/Classes`, by the LE-doc docstring (`pack-checks/srcequality.txt`). LE-doc's build is the combined build:
  `Rz/Classes` rc 0 there, and the solo tip + #326 check rebuilt it (question 8).

**6. The docstring and sketch rules**
- Does every new public declaration's docstring state its formula, with arguments in the Lean order and a source tag
  where it comes from the source? Does every proof of 15 lines or more carry a `**Proof sketch.**`
  (`evidence/statements/sketchaudit.txt`: 12 such proofs, all sketched)? A misstated formula or sketch is a minor.
- Does every new public `def` land with its `_eq`/`_iff` reader (lint check 8; Complexity 25/391 → 25/390, the
  removed WARN is DTIME's `DecidesInTime`, now with E3)? Is nothing new `@[simp]` or an instance?

**7. Axioms**
- The three targets, E1–E3, `inBPP_iff`, `polyTimeComputable_find`, `polyTimeComputable_iterateFind` and the helper
  endpoints print `[propext, Classical.choice, Quot.sound]` (`landing/census-head.log`).
- The census has 320 stored constants, the axiom union is the standard three, and there is no `sorryAx`. Against the
  base (`evidence/logs/census-base-vs-head.tsv`): 202 → 320, removed 0, type-changed 0, axioms-changed 3 (the
  targets, `sorryAx` dropped). The combined probe confirms the targets.

**8. The merge interaction**
- `git merge-tree --write-tree c27005d6 <x>` is clean, and no path is shared (`pack-checks/mergetrees.txt`):

  | `<x>` | head | merged tree | downstream of both (`pack-checks/downstream.txt`) |
  |---|---|---|---|
  | the tip | `c2f6adeb` | `aad4171f` | 259 (#319's `CodeFormat` and #323's `DAGCircuit` are in the unit closure) |
  | #324 (sc-compose) | `4bd2d80b` | `fa624a7e` | 16 |
  | #327 (seq-zk) | `bd19c433` | `029cdc65` | 52 |
  | #318 (merged) | `b0bad23a` | `22f2e3e1` | 10 |
  | #319 (merged) | `47daa907` | `eb90bfa5` | 57 |
  | #323 (merged) | `8c3f3e3f` | `e4be8aaf` | 228 |

  `ClassP/DTIME` is deep, so the unit's downstream is large (585 modules in the combined tree). None of the 54 new short
  names is declared in a file another comparator changed (`pack-checks/namecheck.txt`).
- **The integration evidence** (`integration/`, `4f8cb374…`): the combined build of the records tip of that time
  `b0ebd475` plus all six PRs, with #326 at this head, as tree `3fb05ea0`. **694/694 rc 0**, 0 errors in both forms.
  - Re-checked (`pack-checks/integration.txt`): `b0ebd475..c2f6adeb` changes Lean paths only through #318, #319 and #323.
  - Merging #324, #326 and #327 onto the current tip, in all six orders, gives `TCSlib` and `audits` trees equal to
    the built tree, and all 694 built sources equal their blobs there.
  - Its solo check of tip + #326 (on `b0ebd475`) rebuilt the 89 modules downstream of `Rz/Classes` and #313's Learning
    files: 91/91 rc 0, every module byte-identical to a reference.
- **Pending merge condition (not an audit item):** the merge order, **#324 last**. The intermediate states with the
  current tip (tip + #326, and tip + #326 + #327) are not built as such; any rebuild for whichever of #326 and #327
  merges second is the maintainer's, if required. What you can raise: a concrete reason a merged tree cannot build, or
  a name or instance interaction.

## Known dispositions (not findings)

- **F-01** (major, ruled debt; ruling 3), **F-02** (SR-01, confirmed), **F-03** (E1's repetition; ruling 4), **F-04**
  (fixed by LE-doc), **F-05** (environment; ruling 6), **F-06** (info): six unused-simp-argument warnings copied from
  the old proof into E1 (`IterateFind` 6 → 12 warnings, `evidence/logs/warnings-vs-base.txt`); the near relatives of
  question 4.
- **Admissions:** 26 in 12 modules → 23 in 10; only `Rz/SeedMajority` (2 → 0) and `Randomness/Derandomization` (1 → 0)
  differ (`evidence/logs/sorry-census.txt`).
- **The build:** 565 modules (the downstream of every module changed since `eff2dcd0`, through root `TCSlib` and both
  `audits/*/Checks`), rc 0, 0 errors in both forms, 5534 s (`landing/root-checks.jsonl` and
  `landing/build-retry-results.jsonl`; `build/results.jsonl` records the first attempt's 8 failures from F-05, which
  the retry overrides). Whole-tree check at the head: 1259 modules, OK (`landing/tree-check-head.txt`). The olean tree
  was restored to `457ba704…`.
- **The PR description** predates LE-doc: it names the head `941b5a1e` and says there are no landing edits yet
  (`pr-description.md`, fetched from the GitHub API on 2026-11-16). The maintainer updates it before #326 is marked
  ready.
- **The brief's "Worker Claude"** header line is from issue; Seyoon moved the fill to Codex on 2026-11-15 (ruling 8).

## Evidence

- **`review.md`:** the maintainer's delivery review: REVISE on F-01, then accepted under Seyoon's ruling (F-01–F-06).
- **`verification.zip`:** every file the review cites and the pack uses, as byte-identical originals. `SHA256SUMS` lists
  every other entry, and `PROVENANCE.txt` gives each source.
  - `review-evidence.zip` (`fills/derand/final-r1/`, SHA-256 `ef0776d5…`) and `review-evidence-SHA256SUMS`, its
    manifest: 1318 entries, exactly the 1317 manifest paths plus `SHA256SUMS`; every hash verifies;
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `records/`: the issue package `fills/derand/issued-r2/` and, at records
    `e4f8729f32d9efd8744b77cfb4abe5dd37157457` (local, unpushed: the tip `c2f6adeb` plus the Gate 37 round-2 records), the duplication ledger, the decision log, the deferred-work register,
    the Codex host addendum and dispatch, and Gate 28's resolutions;
  - `evidence/`: byte copies of the review-evidence entries the pack cites;
  - `worker/`: byte copies from the exchange delivery `186ffb99` (`inbox/fills/derand/`): `COMMITS.tsv` and the
    scope-request files (EX-01, EX-02, SR-01, SR-02), each equal to the review's `logs/delivery-extracts/` copy;
  - `pack-checks/`: the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `186ffb99`, under `inbox/fills/derand/` (manifests 3146/3146 and
  3124/3124 in the review).
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`),
  `build-retry-results.jsonl`, `build-summary.txt` (= `logs/build-summary.txt`), `census-head.log`
  (= `probe-runs/mods/PlProbe_CensusHead.log`), `frozen-check.txt` (= `statements/frozen/frozen-check.txt`) and
  `tree-check-head.txt`.
- **`landing-ledoc/`:** LE-doc for derand (F-04) and seq-zk (S-02): `ledoc-derand-seqzk-evidence.zip` (`977bbe89…`;
  70 entries, its 59 files the 58 manifest paths plus `SHA256SUMS`), its manifest and PROVENANCE.
- **`integration/`:** the combined build of all open PRs (`4f8cb374…`; 1296 entries, its 1249 files the 1248 manifest
  paths plus `SHA256SUMS`), its manifest and PROVENANCE.
- **`worker-report.md`:** the worker's final `REPORT.md`, at exchange `186ffb99`.
- **`pr-description.md`:** the PR #326 description as fetched from the GitHub REST API on 2026-11-16 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (15 paths, 1741 insertions, 36 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 15 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 207 files.
- **The bundle** adds, at the head, the five pre-existing files.

## Findings delivery

Return `gate38-derand-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings (F-01's
  20 failures are covered), an undisclosed copied private lemma or undisclosed re-proof of a public one, or necessary
  evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
