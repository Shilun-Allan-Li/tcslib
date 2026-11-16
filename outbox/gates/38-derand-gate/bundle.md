## ===== briefs/pass-shelat-ch5-8/gates/38-derand/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/38-derand/review.md =====

# derand (issued-r2) · maintainer delivery review (r1)

**Verdict: REVISE on F-01, then accepted under Seyoon's ruling (2026-11-16): "debt now, fix after".** No landing edit has
been made yet. F-04, a docstring LE-doc, is pending. Draft [PR #326](https://github.com/Shilun-Allan-Li/tcslib/pull/326).

## Delivery and landing
- **Delivery.** Codex on Seyoon's Mac. The final is exchange `186ffb99`; the checkpoints are `d90a0363` and `aa23fc19`. The issue base is `01de2d8b`.
- **Landing.** `land/pass-shelat-derand`, head `941b5a1e5116b1ecf3afa56188abd88159389600`, tree `ee97571a`, on `6ce4658d`. The range-diff is 4/4 identical.
  - **Commits:** `255f3e48` (checkpoint 1), `09f32f0b` (Theorem 180.1), `4afde165` (the host) and `941b5a1e` (the final).
- **Files.** 15 files, +1741/−36.
  - **Modified:** `ClassP/DTIME.lean`, `Randomized/Build/IterateFind.lean`, `Randomized/Classes.lean`, `Randomized/SeedMajority.lean` and `Randomness/Derandomization.lean`.
  - **New:** `SeedMajority/{Words,State,Enumeration,Envelope}` and `Derandomization/{RootSchedule,AdviceGap,Expanded,CoinGap,Majority,TimeBound}`.
- **Evidence.** `review-evidence.zip`, SHA-256 `ef0776d5b100fdb1b183d4f47a34e54fba70a8b099bd2998e759be4982f4cfcb`, 1318 entries.

## Checks
- **Integrity.** The manifests verify 3146/3146 and 3124/3124. `git am` reproduces all 4 hashes unsigned. `src/` equals the 15 paths. The package verifies 7/7 and the sources 377/377. Never more than 3 slots were held at once.
- **Build.** 565 modules give rc 0 and 0 errors in both forms. That covers the full downstream of `ClassP/DTIME` and `IterateFind`, through root `TCSlib` and both `Checks`, in 5534 s; the slowest module is `DetMod`, at 1510 s. The whole-tree check covers 1259 modules: OK.
- **Statements.** Headers and definition bodies are identical; only the three targets' docstrings change. decls2 gives 53 ADDED, 0 CHANGED, 0 REMOVED. E2 and E3 are byte-identical to their approved drafts.
- **Axioms.** All three targets, E1–E3, `inBPP_iff` and the helpers use only the standard three. 320 constants; no `sorryAx`.
- **Rule 10.** Only `IterateFind` fails (F-01); strict and coe agree. The coe controls are ALL_OK. The scan finds 0 foreign definitions.
- **Admissions.** 26 → 23.
- **Lint.** 92/101. Complexity goes from 25/391 to 25/390.
- **Content.**
  - **One machine gives both clauses, per H17.** The time bound comes through `decidesInTime_iff`/`computesFunInTime_iff`, and the envelope through `envelope_of_computesInTime`.
  - **The corollary** reads neither `DTIME` nor `DecidesInTime` by definition.
  - **The Gate 28 route** uses binary fuel `Nat.bits (2^w)`, a terminal rank in range, and `2^w+2 ≤ 3·2^w`.
  - **Theorem 180.1** has margins 7/12 and 5/12, with no finite table.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | major | Rule 10. E1 `computesFunInTime_find` reads `hostTM`'s `k`/`State` fields by definition, giving 9 new seal failures. They are line-for-line copies of the 11 failures that the frozen `polyTimeComputable_find` already has at the base. The worker disclosed this (EX-02), and its proposed fix SR-02 went unanswered. | **Ruling (Seyoon, 2026-11-16): debt now, fix after.** Land as is. A maintainer follow-up PR will add SR-02-style typed-view readers (`ModuleHost`/`IterateFindHost`) and re-derive both E1 and `polyTimeComputable_find` through them, clearing all 20 failures. The re-derivation is already pre-approved. |
| F-02 | minor | SR-01 adds `Randomized.inBPP_iff` (`Iff.rfl`) to the frozen `Classes.lean`, which grows from 1403 to 1415 lines. Seyoon's approval had been recorded only in the delivery. | **Confirmed by Seyoon (2026-11-16)**, together with the inherited file-size exception. Accepted. |
| F-03 | info | The pre-approved re-derivation of `polyTimeComputable_find` was not taken up. E1 repeats 196 of the old proof's 228 lines (disclosed). | It is part of the F-01 follow-up. |
| F-04 | minor | The `inBPP_iff` docstring has no formula. | LE-doc, pending. |
| F-05 | info | The shared Mathlib cache lacks `Pow/NthRootLemmas.olean`, which `RootSchedule` imports. | Integration builds must fetch that root, using a narrowed cache get. |
| F-06 | info | Six unused-simp-argument warnings were copied from the old proof. There are near-relatives `randProb_bitsVal` and `abs_workTapePos_runFrom_sub_le`, but nothing is restated. | None. |

## ===== briefs/pass-shelat-ch5-8/gates/38-derand/worker-report.md =====

# derand · final

## Status and review disposition

All three frozen targets are **proved with only `propext`, `Classical.choice`, and
`Quot.sound`**. No target is proved modulo an admission in this payload. The exact
final source passes the complete 387-module replay with zero errors; its sorry list
is the issued baseline minus precisely the three requested targets: **23 declarations
in 10 modules**. No statement is weakened.

**Rule 10 disposition: HOLD, disclosed exception EX-02.** The canonical seals of the
harvest E1 retain nine new diagnostics, alongside eleven inherited diagnostics in
the unchanged old theorem, in each of four variants. All 56 variants for the other
14 changed/new files pass. This delivery does not claim seal clearance. A proposed
reader fix in two further frozen providers was rejected by automatic approval review
and was not applied. The maintainer must assess this exception before landing.

Worker: external Codex, the worker called “Claude” in issued-r2. The host addendum
overrides the environment addendum where stated. The r2 issue replaces r1.

* Issued exchange pin: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
* Source base: `01de2d8baed9113e4a099e13c5d50c81e6dbc66f` on `cryptography/pass-shelat-ch2-4`.
* Final source tip: `5e12a169e671dc16b6766e21067b79c16835af67` on local-only branch `fill/derand`.
* Lean: 4.25.0, arm64 macOS; Mathlib pin
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
* The source branch is never pushed; delivery is only `inbox/fills/derand/`.

| Frozen target | Final status |
|---|---|
| `Complexity.exists_seedMajorityTM` | proved; standard axioms |
| `Complexity.seedMajority_mem_DTIME` | proved from the contract through `mem_DTIME_iff`; standard axioms |
| `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` | proved; standard axioms |

## Checkpoints and proof route

Checkpoint 1 delivered E1, E2, E3, approved SR-01, and the corollary from the still
admitted host; its full 377-module replay passed. This payload completes checkpoint
2's host as well as Theorem 180.1. The consumer was developed first modulo the host,
as the issued proved-modulo rule expressly permits. Filling the host removed that
dependency, verified by both the all-constant axiom census and a kernel dependency
path audit. No mathematical work was delegated; all proofs and checks were run by
this worker. Other-worker messages concerned shared resource scheduling only.

The host retains `x` in the paired state `⟨x, ⟨i, a⟩⟩`. Binary ranks enumerate all
`2^w` seeds using the existing `bitsEquiv`; the finite prefix count supplies the
induction invariant. The generic-fuel harvest uses the existing total length guard
and its closed `Inv`. The terminal rank is included in `range (R+1)`; no bound is
assumed for an unguarded increment past termination. Fuel is binary `Nat.bits (2^w)`,
never an exponential unary word. Published arithmetic and pairing machines compute
each round, and the explicit polynomial per-round budget yields
`c * (2^w * (n+1)^e)`. The native initial-configuration envelope follows from the
public head-position interval bound before halting and the public halt/run readers
after halting. A zero time coefficient is impossible by `not_computesInTime_zero`.

The consumer uses `ceilRoot d n = 0` for `n=0`, and
`Nat.nthRoot d (n-1)+1` otherwise. The unary word is computed using the published
bounded state search and fixed unary powers, not a copied root machine. A secure
generator is truncated and expanded to the syntactic envelope
`a*(s^d+1)^k+s+1`. Non-uniform advice chooses a bad input at each seed length and
security gives a uniform `1/12` gap threshold directly; this is the quantified
threshold form of the paper's infinite-bad-length contradiction. Published
`verifier_toNUPPT`, probability and uniform-prefix identities identify the advantage.
Below the threshold, both width and test use true coins; above it they use generated
coins. Thus the acceptance margins are `7/12` and `5/12`, and the strict-majority
reader identifies the language. There is no finite table. Logarithm/rpow limits and
one finite-exception constant give the time comparison, followed by the published
DTIME monotonicity and constant-factor transports.

## Source files, scope, and sketch edits

| File | Base lines | Final lines | Maximum width |
|---|---:|---:|---:|
| `TCSlib/Complexity/ClassP/DTIME.lean` | 117 | 135 | 90 |
| `TCSlib/Complexity/Randomized/Build/IterateFind.lean` | 556 | 801 | 99 |
| `TCSlib/Complexity/Randomized/Classes.lean` | 1403 | 1415 | 97 |
| `TCSlib/Complexity/Randomized/SeedMajority.lean` | 234 | 261 | 98 |
| `TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean` | 0 | 127 | 87 |
| `TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean` | 0 | 63 | 86 |
| `TCSlib/Complexity/Randomized/SeedMajority/State.lean` | 0 | 233 | 95 |
| `TCSlib/Complexity/Randomized/SeedMajority/Words.lean` | 0 | 172 | 92 |
| `TCSlib/Cryptography/Randomness/Derandomization.lean` | 97 | 127 | 99 |
| `TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean` | 0 | 139 | 85 |
| `TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean` | 0 | 95 | 87 |
| `TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean` | 0 | 70 | 84 |
| `TCSlib/Cryptography/Randomness/Derandomization/Majority.lean` | 0 | 159 | 93 |
| `TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean` | 0 | 173 | 90 |
| `TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean` | 0 | 142 | 87 |

Every changed/new Lean line has Python `len` at most 100. Every file has at most
1000 lines except `Classes.lean`, whose inherited 1403→1415 length was specifically
approved with SR-01. E1 stays at 801 lines. No new `@[simp]` attribute is added and
imports are precise. The source audit verifies each file's SHA256 against the final
commit. Four host helpers and six consumer helpers are inserted before consumers
in the final order; the original 377-module relative order is preserved, without
cycles. No parent facade or other frozen provider is edited.

The two owned module titles/Main results/Contents and target Status/sketch paragraphs
describe the delivered proofs. The helper docstrings give their formulas and source
tags; every proof of at least 15 nonblank proof lines has a proof sketch. The explicit
`advance` formula was clarified in the final comment-only commit. All 93 original
declaration headers, whole definitions, declaration order, and frozen proofs in the
five affected existing files are preserved byte for byte; the one-character header
control reports exactly one difference. This includes leaving the original
`polyTimeComputable_find` and `final_bound` unchanged.

## New declarations and final signatures

There are 54 source declarations (53 public, one private). The complete kernel-type
signatures are listed below; section variables are included by the elaborated
universal quantifiers. `source-audit/signatures.json` also records the actual kernel
name of the private lemma. Generated auxiliary constants are included in the separate
321-constant census, rather than mistaken for additional source declarations.

E1's source signature, in full, is:

```lean
theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    {init : List Bool → List Bool} (hinit : PolyTimeComputable init)
    (R : ℕ → ℕ) (P : PolyExpr)
    (hbound : ∀ x : List Bool, (init x).length ≤ P.eval x.length)
    (F : FinTM Bool) (aF dF : ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length))
      (fun n => aF * (n + 1) ^ dF)) :
    ∃ (M : FinTM Bool) (c A D : ℕ),
      M.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) with
          | some i => out (pairSndD ((step g P x)^[i] (pairEncode x (init x))))
          | none => [])
        (fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2))
```

This is one public generic-fuel addition. It accepts arbitrary numerical `R` via a
fuel machine for `Nat.bits (R |x|)` and gives
`c*(A*(2*n+2+P.eval n+5)^D+1)*(R n+2)`. It reuses the private helpers in place,
retains the total guard/invariant, and uses an arbitrary FP initializer so that the
host can carry `x`. It never applies `final_bound` to exponential fuel. E2 and E3
use the issued signatures without binder-style changes; SR-01 is the only additional
approved shared-file declaration.

```lean
-- TCSlib/Complexity/Randomized/Build/IterateFind.lean:575
Complexity.IterateFind.computesFunInTime_find :
∀ {g : List Bool → List Bool},
  Complexity.PolyTimeComputable g →
    ∀ {acc : List Bool → Bool},
      (Complexity.PolyTimeComputable fun s => [acc s]) →
        ∀ {out : List Bool → List Bool},
          Complexity.PolyTimeComputable out →
            ∀ {init : List Bool → List Bool},
              Complexity.PolyTimeComputable init →
                ∀ (R : ℕ → ℕ) (P : Complexity.PolyExpr),
                  (∀ (x : List Bool), (init x).length ≤ P.eval x.length) →
                    ∀ (F : Turing.FinTM Bool) (aF dF : ℕ),
                      (F.ComputesFunInTime (fun x => (R x.length).bits) fun n => aF * (n + 1) ^ dF) →
                        ∃ M c A D,
                          M.ComputesFunInTime
                            (fun x =>
                              match
                                List.find?
                                  (fun i =>
                                    acc
                                      (Complexity.pairSndD
                                        ((Complexity.IterateFind.step g P x)^[i] (Turing.pairEncode x (init x)))))
                                  (List.range (R x.length + 1)) with
                              | some i =>
                                out
                                  (Complexity.pairSndD
                                    ((Complexity.IterateFind.step g P x)^[i] (Turing.pairEncode x (init x))))
                              | none => [])
                            fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)
```
```lean
-- TCSlib/Complexity/ClassP/DTIME.lean:83
Turing.FinTM.decidesInTime_iff :
∀ (M : Turing.FinTM Bool) (L : Language Bool) (T : ℕ → ℕ),
  M.DecidesInTime L T ↔ ∀ (x : List Bool), M.ComputesInTime x [Turing.MultiTapeTM.indicator L x] (T x.length)
```
```lean
-- TCSlib/Complexity/ClassP/DTIME.lean:105
Complexity.mem_DTIME_iff :
∀ {T : ℕ → ℕ} {L : Language Bool}, L ∈ Complexity.DTIME T ↔ ∃ c M, M.DecidesInTime L fun n => c * T n
```
```lean
-- TCSlib/Complexity/Randomized/Classes.lean:299
Randomized.inBPP_iff :
∀ (E : Randomized.VerifierModel) (L : Language Bool),
  Randomized.InBPP E L ↔
    ∃ M a k,
      E.Eff (Randomized.boolVerifier M) ∧
        ∀ (x : List Bool),
          (x ∈ L → 2 / 3 ≤ Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = true) ∧
            (x ∉ L → 2 / 3 ≤ Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = false)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean:54
Complexity.SeedMajority.exists_countingTM :
∀ {V : Language Bool},
  V ∈ Complexity.P →
    ∀ (w : ℕ → ℕ),
      (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
        ∃ M c e,
          M.ComputesFunInTime
            (fun x => [decide (2 ^ w x.length < 2 * {u | Turing.pairEncode x (List.ofFn u) ∈ V}.card)]) fun n =>
            c * (2 ^ w n * (n + 1) ^ e)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean:43
Complexity.SeedMajority.envelope_of_computesInTime :
∀ {M : Turing.FinTM Bool} {x y : List Bool} {t : ℕ},
  M.ComputesInTime x y t →
    ∀ (v : ℕ) (j : Fin M.k), |(Turing.MultiTapeTM.runFrom (Turing.MultiTapeTM.initCfg x) v).workTapePos j| ≤ ↑t
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:51
Complexity.SeedMajority.seedFor :
(ℕ → ℕ) → List Bool → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:57
Complexity.SeedMajority.seedFor_eq :
∀ (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.seedFor w z =
    List.take (w (Complexity.pairFstD z).length)
      (Complexity.pairFstD (Complexity.pairSndD z) ++ (2 ^ w (Complexity.pairFstD z).length).bits)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:64
Complexity.SeedMajority.seedFor_state :
∀ (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.seedFor w (Complexity.SeedMajority.state x i a) = Complexity.SeedMajority.word (w x.length) i
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:71
Complexity.SeedMajority.polyTimeComputable_seedFuel :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable fun x => (2 ^ w x.length).bits
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:84
Complexity.SeedMajority.polyTimeComputable_seedFor :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable (Complexity.SeedMajority.seedFor w)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:100
Complexity.SeedMajority.advance :
Language Bool → (ℕ → ℕ) → List Bool → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:110
Complexity.SeedMajority.advance_eq :
∀ (V : Language Bool) (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.advance V w z =
    Turing.pairEncode (Complexity.pairFstD z)
      (Turing.pairEncode
        (Complexity.BinArith.add (Turing.pairEncode (Complexity.pairFstD (Complexity.pairSndD z)) (Nat.bits 1)))
        (Complexity.BinArith.add
          (Turing.pairEncode (Complexity.pairSndD (Complexity.pairSndD z))
            (if
                Turing.MultiTapeTM.indicator V
                    (Turing.pairEncode (Complexity.pairFstD z) (Complexity.SeedMajority.seedFor w z)) =
                  true then
              Nat.bits 1
            else Nat.bits 0))))
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:125
Complexity.SeedMajority.polyTimeComputable_advance :
∀ {V : Language Bool},
  V ∈ Complexity.P →
    ∀ {w : ℕ → ℕ},
      (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
        Complexity.PolyTimeComputable (Complexity.SeedMajority.advance V w)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:143
Complexity.SeedMajority.advance_state :
∀ (V : Language Bool) (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.advance V w (Complexity.SeedMajority.state x i a) =
    Complexity.SeedMajority.state x (i + 1)
      (a + if Turing.pairEncode x (Complexity.SeedMajority.word (w x.length) i) ∈ V then 1 else 0)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:156
Complexity.SeedMajority.finished :
(ℕ → ℕ) → List Bool → Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:161
Complexity.SeedMajority.finished_eq :
∀ (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.finished w z =
    Complexity.BinArith.beq
      (Turing.pairEncode (Complexity.pairFstD (Complexity.pairSndD z)) (2 ^ w (Complexity.pairFstD z).length).bits)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:167
Complexity.SeedMajority.polyTimeComputable_finished :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable fun z => [Complexity.SeedMajority.finished w z]
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:176
Complexity.SeedMajority.finished_state :
∀ (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.finished w (Complexity.SeedMajority.state x i a) = decide (i = 2 ^ w x.length)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:184
Complexity.SeedMajority.payload :
(ℕ → ℕ) → List Bool → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:190
Complexity.SeedMajority.payload_eq :
∀ (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.payload w z =
    [Complexity.BinArith.lt
        (Turing.pairEncode (2 ^ w (Complexity.pairFstD z).length).bits
          (Complexity.BinArith.add
            (Turing.pairEncode (Complexity.pairSndD (Complexity.pairSndD z))
              (Complexity.pairSndD (Complexity.pairSndD z)))))]
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:196
Complexity.SeedMajority.polyTimeComputable_payload :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable (Complexity.SeedMajority.payload w)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:207
Complexity.SeedMajority.payload_state :
∀ (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.payload w (Complexity.SeedMajority.state x i a) = [decide (2 ^ w x.length < 2 * a)]
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:213
Complexity.SeedMajority.polyTimeComputable_initial :
Complexity.PolyTimeComputable fun x => Complexity.SeedMajority.state x 0 0
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:221
Complexity.SeedMajority.length_state_le :
∀ (x : List Bool) (m i a : ℕ),
  i ≤ 2 ^ m → a ≤ i → (Complexity.SeedMajority.state x i a).length ≤ 2 * x.length + 3 * m + 7
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:46
Complexity.SeedMajority.word :
ℕ → ℕ → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:50
Complexity.SeedMajority.word_eq :
∀ (m i : ℕ), Complexity.SeedMajority.word m i = List.take m (i.bits ++ (2 ^ m).bits)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:54
Complexity.SeedMajority.length_word :
∀ (m i : ℕ), (Complexity.SeedMajority.word m i).length = m
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:67
Complexity.SeedMajority.word_eq_ofFn :
∀ (m i : ℕ) (hi : i < 2 ^ m), Complexity.SeedMajority.word m i = List.ofFn ((Randomized.bitsEquiv m).symm ⟨i, hi⟩)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:89
Complexity.SeedMajority.count :
Language Bool → List Bool → ℕ → ℕ → ℕ
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:95
Complexity.SeedMajority.count_eq :
∀ (V : Language Bool) (x : List Bool) (m i : ℕ),
  Complexity.SeedMajority.count V x m i =
    {j ∈ Finset.range i | Turing.pairEncode x (Complexity.SeedMajority.word m j) ∈ V}.card
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:100
Complexity.SeedMajority.count_zero :
∀ (V : Language Bool) (x : List Bool) (m : ℕ), Complexity.SeedMajority.count V x m 0 = 0
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:106
Complexity.SeedMajority.count_le :
∀ (V : Language Bool) (x : List Bool) (m i : ℕ), Complexity.SeedMajority.count V x m i ≤ i
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:117
Complexity.SeedMajority.count_succ :
∀ (V : Language Bool) (x : List Bool) (m i : ℕ),
  Complexity.SeedMajority.count V x m (i + 1) =
    Complexity.SeedMajority.count V x m i + if Turing.pairEncode x (Complexity.SeedMajority.word m i) ∈ V then 1 else 0
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:136
Complexity.SeedMajority.count_all :
∀ (V : Language Bool) (x : List Bool) (m : ℕ),
  Complexity.SeedMajority.count V x m (2 ^ m) = {u | Turing.pairEncode x (List.ofFn u) ∈ V}.card
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:164
Complexity.SeedMajority.state :
List Bool → ℕ → ℕ → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:169
Complexity.SeedMajority.state_eq :
∀ (x : List Bool) (i a : ℕ), Complexity.SeedMajority.state x i a = Turing.pairEncode x (Turing.pairEncode i.bits a.bits)
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean:46
TCSlib.Cryptography.Randomness.Derand.eff_mapCoins :
∀ {M : List Bool → List Bool → Bool},
  Randomized.polyTimeModel.Eff (Randomized.boolVerifier M) →
    ∀ {C : List Bool → List Bool},
      Complexity.PolyTimeComputable C →
        Randomized.polyTimeModel.Eff (Randomized.boolVerifier fun x r => M x (C (Turing.pairEncode x r)))
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean:80
TCSlib.Cryptography.Randomness.Derand.exists_verifier_gap_bound :
∀ {M : List Bool → List Bool → Bool},
  Randomized.polyTimeModel.Eff (Randomized.boolVerifier M) →
    ∀ (w : ℕ → ℕ) (p : Complexity.PolyExpr),
      (∀ (n : ℕ), n ≤ p.eval (w n)) →
        ∀ (G : TCSlib.Cryptography.PRG),
          G.Secure →
            ∃ S,
              ∀ (x : List Bool),
                S ≤ w x.length →
                  |(TCSlib.Cryptography.uprob fun r => M x (List.ofFn (G.G (w x.length) r)) = true) -
                        TCSlib.Cryptography.uprob fun r => M x (List.ofFn r) = true| ≤
                    1 / 12
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean:50
TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold :
(∃ G, G.Secure) →
  ∀ {M : List Bool → List Bool → Bool},
    Randomized.polyTimeModel.Eff (Randomized.boolVerifier M) →
      ∀ (a k d : ℕ),
        0 < d →
          ∃ F n₀,
            Complexity.PolyTimeComputable F ∧
              ∀ (x : List Bool),
                n₀ ≤ x.length →
                  |↑(Randomized.randProb (TCSlib.Cryptography.Randomness.Derand.ceilRoot d x.length) fun u =>
                            M x (List.take (Randomized.polyLen a k x.length) (F u)) = true) -
                        ↑(Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = true)| ≤
                    1 / 12
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean:47
TCSlib.Cryptography.Randomness.Derand.exists_secure_cover :
(∃ G, G.Secure) →
  ∀ (a k d : ℕ),
    0 < d →
      ∃ G F,
        G.Secure ∧
          Complexity.PolyTimeComputable F ∧
            (∀ (n : ℕ) (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G.G n s)) ∧
              ∀ (n : ℕ), Randomized.polyLen a k n ≤ G.stretch.eval (TCSlib.Cryptography.Randomness.Derand.ceilRoot d n)
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/Majority.lean:39 (private)
TCSlib.Cryptography.Randomness.Derand.short_poly :
∀ {f : List Bool → List Bool},
  Complexity.PolyTimeComputable f → ∀ (N : ℕ), Complexity.PolyTimeComputable fun z => [decide ((f z).length < N)]
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/Majority.lean:63
TCSlib.Cryptography.Randomness.Derand.exists_seed_majority :
(∃ G, G.Secure) →
  ∀ {L : Language Bool},
    Randomized.InBPP Randomized.polyTimeModel L →
      ∀ (d : ℕ),
        0 < d →
          ∃ V w n₀,
            V ∈ Complexity.P ∧
              (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) ∧
                (∀ (n : ℕ), n₀ ≤ n → w n = TCSlib.Cryptography.Randomness.Derand.ceilRoot d n) ∧
                  L = {x | 2 ^ w x.length < 2 * {u | Turing.pairEncode x (List.ofFn u) ∈ V}.card}
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:44
TCSlib.Cryptography.Randomness.Derand.ceilRoot :
ℕ → ℕ → ℕ
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:48
TCSlib.Cryptography.Randomness.Derand.ceilRoot_eq :
∀ (d n : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d n = if n = 0 then 0 else d.nthRoot (n - 1) + 1
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:53
TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff :
∀ {d : ℕ}, 0 < d → ∀ (n t : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ≤ t ↔ n ≤ t ^ d
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:65
TCSlib.Cryptography.Randomness.Derand.le_ceilRoot_pow :
∀ {d : ℕ}, 0 < d → ∀ (n : ℕ), n ≤ TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ^ d
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:69
TCSlib.Cryptography.Randomness.Derand.ceilRoot_zero :
∀ (d : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d 0 = 0
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:75
TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_nat :
∀ {d : ℕ}, 0 < d → ∀ (n : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ≤ n
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:86
TCSlib.Cryptography.Randomness.Derand.lt_ceilRoot_iff :
∀ {d : ℕ}, 0 < d → ∀ (n t : ℕ), t < TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ↔ t ^ d < n
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:98
TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_real :
∀ {d : ℕ}, 0 < d → ∀ (n : ℕ), ↑(TCSlib.Cryptography.Randomness.Derand.ceilRoot d n) ≤ ↑n ^ (1 / ↑d) + 1
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:128
TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot :
∀ {d : ℕ},
  0 < d →
    Complexity.PolyTimeComputable fun x =>
      List.replicate (TCSlib.Cryptography.Randomness.Derand.ceilRoot d x.length) true
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean:40
TCSlib.Cryptography.Randomness.Derand.exists_root_degree :
∀ {ε : ℝ}, 0 < ε → ∃ d, 2 ≤ d ∧ 1 / ↑d < ε ∧ 1 / ↑d < 1
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean:64
TCSlib.Cryptography.Randomness.Derand.seed_time_le_subexp :
∀ {d : ℕ},
  0 < d →
    ∀ {ε : ℝ},
      0 < ε →
        1 / ↑d < ε →
          ∀ (w : ℕ → ℕ) (n₀ : ℕ),
            (∀ (n : ℕ), n₀ ≤ n → w n = TCSlib.Cryptography.Randomness.Derand.ceilRoot d n) →
              ∀ (e : ℕ), ∃ C, ∀ (n : ℕ), 2 ^ w n * (n + 1) ^ e ≤ C * ⌈2 ^ ↑n ^ ε⌉₊
```

## Overlap and reuse

All 54 additions are disclosed below, including technical specializations and the
private lemma. Unless marked “new”, TCSlib path/line references are at the issue base;
Mathlib references are at the pinned revision. New own-definition references are at
the final tip. No private foreign lemma is silently copied.

| New declaration | Nearest relative | Relation and reuse decision |
|---|---|---|
| `Complexity.IterateFind.computesFunInTime_find` | `TCSlib/Complexity/Randomized/Build/IterateFind.lean:331` | Generalizes polyTimeComputable_find to binary numerical fuel and an arbitrary initializer. The brief requires this assembly repetition in place; all private helpers and the old theorem/final_bound are retained unchanged. |
| `Turing.FinTM.decidesInTime_iff` | `TCSlib/Complexity/ClassP/DTIME.lean:75` | Required home-file reader of DecidesInTime by Iff.rfl (E3); no existing reader has this contract. |
| `Complexity.mem_DTIME_iff` | `TCSlib/Complexity/ClassP/DTIME.lean:88` | Required home-file reader of DTIME by Iff.rfl (E2); no existing reader has this contract. |
| `Randomized.inBPP_iff` | `TCSlib/Complexity/Randomized/Classes.lean:288` | SR-01 approved home-file reader of InBPP by Iff.rfl; no existing reader exposed these witnesses. |
| `Complexity.SeedMajority.exists_countingTM` | `TCSlib/Complexity/ClassNP/EXP.lean:2419; TCSlib/Complexity/Randomized/Build/IterateFind.lean:575 (new E1)` | The existential projection decider accepts some witness and does not count acceptances or give this linear-in-2^w bound. The new host instead reuses E1. H16 is unary-counter driven and would require exponential unary fuel; it is not copied. |
| `Complexity.SeedMajority.envelope_of_computesInTime` | `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:244; TCSlib/Complexity/TuringMachine/Finite.lean:471` | Generalizes the envelope argument to a native initial configuration with only a completed computation. Clean.envelope requires a clean seam contract, absent for the composite machine. Reuses the public interval/run readers; promotion to Finite.lean is requested. |
| `Complexity.SeedMajority.seedFor` | `TCSlib/Complexity/ClassNP/PolyTimePrefix.lean:46` | Specializes the total prefix operation to a raw counting state and its unary width; reuses the existing prefix machine. |
| `Complexity.SeedMajority.seedFor_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:51 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.seedFor_state` | `TCSlib/Complexity/TuringMachine/Encoding.lean:325` | Representation-specific bridge from the raw-state seed to word; all projections use published pair readers. |
| `Complexity.SeedMajority.polyTimeComputable_seedFuel` | `TCSlib/Complexity/ClassP/BinaryArith/Unary.lean:43` | Composition of polyTimeComputable_powerOfTwo with the FP unary width; no exponential unary fuel or competing evaluator is introduced. |
| `Complexity.SeedMajority.polyTimeComputable_seedFor` | `TCSlib/Complexity/ClassNP/PolyTimePrefix.lean:355` | Reuses polyTimeComputable_takePrefixByLength, pairing, and the published binary-fuel composition for the new state. |
| `Complexity.SeedMajority.advance` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:147` | Counting-state-specific round using the published binary adder and P indicator. No arithmetic implementation or private loop lemma is copied. |
| `Complexity.SeedMajority.advance_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:100 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.polyTimeComputable_advance` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:162` | Composes published FP addition, indicator, branching, pairing, and seedFor; the input is an arbitrary raw word. |
| `Complexity.SeedMajority.advance_state` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:147` | Specializes add_pairEncode and the indicator reader to the new state representation. |
| `Complexity.SeedMajority.finished` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:206` | Terminal-rank comparison expressed using the existing binary equality test. |
| `Complexity.SeedMajority.finished_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:156 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.polyTimeComputable_finished` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:227` | Reuses the existing FP equality comparator and binary fuel on projected state words. |
| `Complexity.SeedMajority.finished_state` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:206` | Specializes the equality comparator reader to the terminal rank; no new equality algorithm. |
| `Complexity.SeedMajority.payload` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:198` | Strict-majority bit using existing addition and strict comparison; ties reject. |
| `Complexity.SeedMajority.payload_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:184 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.polyTimeComputable_payload` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:211` | Reuses FP strict comparison and addition; only the counting-state wiring is new. |
| `Complexity.SeedMajority.payload_state` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:198` | Representation-specific interpretation of the existing strict comparator and doubled binary count. |
| `Complexity.SeedMajority.polyTimeComputable_initial` | `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:71; TCSlib/Complexity/ClassNP/PolyTimePairing.lean:129` | Pairs the input with two constant zero words using existing FP closure. |
| `Complexity.SeedMajority.length_state_le` | `TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean:123` | Applies the public binary-width bound to both counters, including rank 2^m, then the pairing-length reader. The result is specific to the new state layout. |
| `Complexity.SeedMajority.word` | `TCSlib/Complexity/TuringMachine/Encoding.lean:325` | Uses the published binary power-of-two padding. This names the fixed-width rank word; it does not define another binary encoding engine. |
| `Complexity.SeedMajority.word_eq` | `TCSlib/Complexity/Randomized/SeedMajority/Words.lean:46 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.length_word` | `TCSlib/Complexity/TuringMachine/Encoding.lean:325` | Specializes binary padding and Mathlib List.length_take to the new rank word; both published operations are reused. |
| `Complexity.SeedMajority.word_eq_ofFn` | `TCSlib/Complexity/Randomized/RandomBits.lean:228; TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:300` | Reuses bitsEquiv_apply and eq_bits_append_replicate. The new glue identifies the padded word with the inverse of the existing bijection; no bijection is re-proved. |
| `Complexity.SeedMajority.count` | `TCSlib/Complexity/Randomized/SeedMajority.lean:147` | Defines the finite prefix of accepted ranks needed by the machine. The existing majority reader counts all tuples, not rank prefixes. |
| `Complexity.SeedMajority.count_eq` | `TCSlib/Complexity/Randomized/SeedMajority/Words.lean:89 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.count_zero` | `Mathlib/Data/Finset/Card.lean:163` | Specializes the empty range/filter cardinality to the new prefix count through its reader. |
| `Complexity.SeedMajority.count_le` | `Mathlib/Data/Finset/Card.lean:62; Mathlib/Data/Finset/Card.lean:163` | Direct application of card_le_card and card_range to the new count. |
| `Complexity.SeedMajority.count_succ` | `Mathlib/Data/Finset/Card.lean:100` | Specializes card_insert_of_notMem after range_add_one/filter_insert; this is the machine-count recurrence, not a new cardinality identity. |
| `Complexity.SeedMajority.count_all` | `Mathlib/Data/Finset/Card.lean:337; TCSlib/Complexity/Randomized/RandomBits.lean:224` | Applies card_bij using the existing bitsEquiv. The language predicate is preserved by word_eq_ofFn; no separate rank bijection is constructed. |
| `Complexity.SeedMajority.state` | `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:129` | Retained-input binary rank/count representation built from the published pairing; existing clean-host stateWord is a tape layout, not this payload. |
| `Complexity.SeedMajority.state_eq` | `TCSlib/Complexity/Randomized/SeedMajority/Words.lean:164 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `TCSlib.Cryptography.Randomness.Derand.eff_mapCoins` | `TCSlib/Complexity/Randomized/PolyTimeModel.lean:86; TCSlib/Complexity/ClassNP/PClosure.lean:69` | Generic verifier-level wrapper around the existing efficiency reader and P-preimage closure. No identical published coin-map wrapper was found; promotion to PolyTimeModel.lean is requested. |
| `TCSlib.Cryptography.Randomness.Derand.exists_verifier_gap_bound` | `TCSlib/Cryptography/Randomness/BPPBridge.lean:80; TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Defs.lean:186` | New non-uniform bad-advice threshold argument. Reuses verifier_toNUPPT, secure_iff, negligible_iff, prgAdv/acceptance readers and uprob_fst. No advantage/expectation or uniform-projection identity is re-proved. |
| `TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold` | `TCSlib/Cryptography/Randomness/BPPBridge.lean:113; TCSlib/Complexity/Randomized/Classes.lean:238` | Reuses randProb_eq_uprob and randProb_take to identify the generic gap. The new content is the root/input threshold and generator envelope. |
| `TCSlib.Cryptography.Randomness.Derand.exists_secure_cover` | `TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean:209; TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean:397` | Specializes the existing secure one-bit truncation/expansion to the syntactic envelope and extracts its existing evaluator. |
| `TCSlib.Cryptography.Randomness.Derand.short_poly` | `TCSlib/Complexity/Randomized/Build/StateLoop.lean:79` | Private specialization of lenLe_comp to |f z|+1≤N. No length-comparison machine is copied. A generic threshold-wrapper promotion beside StateLoop.lenLe_comp is requested. |
| `TCSlib.Cryptography.Randomness.Derand.exists_seed_majority` | `TCSlib/Complexity/Randomized/SeedMajority.lean:147; TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean:179` | Reuses the majority-probability reader. Existing blockMajorityTest handles polynomially many blocks, not this full seed-space majority with piecewise PRG/true coins. No block-majority engine is copied. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | A ceiling root from the existing floor root of n-1; no root algorithm is copied. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_eq` | `TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:44 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Transports nthRoot_lt_iff to the new ceiling convention, with zero handled separately. |
| `TCSlib.Cryptography.Randomness.Derand.le_ceilRoot_pow` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Immediate least-root specialization through ceilRoot_le_iff, not a separate root construction. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_zero` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Zero-case equation of the new ceiling schedule, through its own reader. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_nat` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Least-root specialization using n≤n^d. The schedule is ceiling, unlike the floor-root provider. |
| `TCSlib.Cryptography.Randomness.Derand.lt_ceilRoot_iff` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Strict-order dual of the new least-root reader; no new arithmetic algorithm. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_real` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:57; Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:562` | Reuses pow_nthRoot_le and the real inverse-power comparison, then adds the ceiling increment. |
| `TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot` | `TCSlib/Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean:171; TCSlib/Complexity/Randomized/Repetition.lean:241` | The existing evaluator returns a shifted binary floor root; this needs an exact unary ceiling root of input length. Reuses the published stateFind search and unary fixed-power/length comparisons, with no binary-root implementation copied. |
| `TCSlib.Cryptography.Randomness.Derand.exists_root_degree` | `Mathlib/Algebra/Order/Archimedean/Basic.lean:175` | Specializes exists_nat_gt to reciprocal exponent bounds, including ε≥1. |
| `TCSlib.Cryptography.Randomness.Derand.seed_time_le_subexp` | `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:323; TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean:279` | Uses existing logarithm/rpow limits and the existing DTIME constant-factor transport later in the consumer. The new inequality combines the ceiling-root time and finite exceptions; no new general asymptotic or DTIME transport theorem is re-proved. |

E1's generalized assembly is deliberate repetition explicitly required by the brief.
Its own-file private `Inv`, `inv_*`, `verdictWord`, `stepWord`, and `outWord` are reused
in place. The existing theorem is not re-derived or modified. The machine assembly
uses proved `exists_loopFindTM`/`loopHost_contracts` and the published clean-module
host interfaces; it does not consume admitted loop-host or timed-conditional specs.
The existential projection engine does not count witnesses with the required time
bound, the unary H16 counter is unsuitable as exponential unary fuel, and polynomial
block-majority tests do not supply this full seed-space host. No competing loop or
binary-arithmetic engine is introduced.

Searches used `rg`/`rg --files` across TCSlib and pinned Mathlib before each cluster.
The complete raw search records and probe sources are retained. The searched shapes
include `exists_proj_decider`, `enumMachine_contracts`, H16/counter loops,
`polyTimeComputable_find`, `Clean.envelope`, `Nat.bits`, `Nat.testBit`, `bitsEquiv`,
`finFunctionFinEquiv`, `eq_bits_append_replicate`, binary arithmetic, `Nat.sqrt`,
`Nat.nthRoot`, unary/stateFind searches, and EXP/BPP inclusions. Before the probability
argument, searches included `prfAdv_eq_expect`, `prgAdv_*`, `uexp_*`, `uprob_*`,
`uprob_comp_equiv`, `uprob_comp_eq_sum_map`, `uprob_eq_one_div_card`,
`HardcoreBit.pushesUniform_restrict`, `randProb_eq`, `randProb_eq_uprob`, and
`abs_uexp_sub_le_uprob`. The implementation reuses published probability/expectation
and uniform-prefix identities; it introduces no replacement identity of those kinds.

## Scope requests

### SR-01: specifically approved

Exact session request and answer:

```text
User reply received in this Codex chat, 2026-11-15 PST:

Question:
Approve SR-01: add only `Randomized.inBPP_iff` beside `InBPP` in `TCSlib/Complexity/Randomized/Classes.lean`, proved by `Iff.rfl`? It exposes the existing verifier, coin-schedule, efficiency, and 2/3 correctness witnesses without changing any definition or existing statement. The concrete patch is `/private/tmp/derand-worker/scope-inbpp-reader.patch`. The brief’s Scope rule requires your approval for this fourth shared-file addition; it also needs an exception for Classes.lean’s inherited length above 1000 lines. The three pre-approved additions and checkpoint-1 work continue while this is pending.

Answer:
Approve SR-01 and the inherited file-size exception
```

The reader is beside `InBPP`, proved by `Iff.rfl`, with a formula docstring and no
attribute. It changes no definition or existing statement. The exact diff/search
record is under `evidence/worker/scope-request/SR-01/`.

### Standing exception instruction

```text
User instruction received in this Codex chat, 2026-11-15 PST, verbatim:

I am going to be asleep and away from the keyboard. Use your best judgment when it comes to exceptions, and disclose them completely and transparently in your checkpoints and delivery. You are free to message other workers to coordinate access to shared Mac resources (and the cap of 3 Lean processes) as you see fit.

Worker interpretation:
Narrowly necessary exceptions may be decided without a further keyboard approval,
with exact changes, reasons, and validation disclosed in checkpoints and delivery.
The frozen target statements, shared three-Lean-process cap, own-tree isolation,
delivery-path restriction, and no-force-push rule remain in force.
SR-01 already has separate explicit approval; no additional exception is made here.
```

### SR-02: proposal not applied; specific human answer pending

```text
# Scope request SR-02: typed views of the two bundled constructors

Status: proposed, NOT applied. Automatic approval review rejected application.

The new generic-fuel harvest elaborates and has only the standard axioms, but
the full closure seals add nine diagnostics in its new proof. Eight arise from
the hidden tape/state fields of `ModuleHost.hostTM` and `IterateFind.copyTM`;
one needs an explicit local-budget simplification. The untouched original
`polyTimeComputable_find` independently has eleven baseline diagnostics. No
existing proof or definition is changed to hide any of those findings.

Prototype 3 validates the solution with both constructors still sealed. Prototypes
1 and 2 demonstrate why whole-machine equalities and raw run equalities alone
do not repair the dependent carrier types. Every source and raw log is retained.

## Exact proposed addition

`typed-views.patch` adds 84 lines to
`TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean` (672 → 756):

* `Turing.ModuleHost.hostTMView`, a reducible abbreviation whose explicit fields
  are `k := K`, `State := State C M`, and the original host's underlying machine;
* `hostTMView_eq` and `hostTMView_q₀`;
* `hostTMView_step_inl`, `host_call_view`, and `host_clean_view`, proved directly
  from the existing public contracts in the same file.

It adds 22 lines to
`TCSlib/Complexity/Randomized/Build/IterateFindHost.lean` (362 → 384):

* `Complexity.IterateFind.copyTMView`, with explicit one-tape, `Fin 2` fields;
* `copyTMView_eq` and `copy_clean_view`, reusing the existing copier contract.

Every existing declaration, definition, proof, and attribute remains byte-for-byte
unchanged. There is no transition-table copy, time-bound change, new admission,
or `simp` attribute. Both proposed files remain below 1000 lines and width 100.
The risk is expansion of the frozen shared-provider/rebuild scope; the purpose
is to remove implicit type-field reads in E1 while preserving all operational
seals. Header, clash, full-source seal, axiom, lint, and replay evidence would
cover both providers if approved.

## Authorization and automatic review

Seyoon delegated judgment over exceptions while away (see
`standing-discretion.txt`). The worker interpreted this as allowing these narrowly
necessary reader additions and attempted to apply/check them. Automatic approval
review rejected the action because it requires a specific scope approval for
these two provider files. No provider mutation occurred. The exact rejection is
in `automatic-review-rejection.txt`. Specific SR-02 approval is now requested;
independent final-consumer work continues in the meantime.

Answer: PENDING.
```

Automatic review rejected applying/checking the provider patch. Exact recorded reason:

```text
Automatic approval review rejected applying/checking the typed provider views.
No command or provider mutation ran.

Verbatim reason:
This would modify two additional frozen provider files beyond the three pre-approved additions, but the brief requires a specific scope request to Seyoon for any such change and none authorizes these typed-view readers.
Do not bypass this rejection through a workaround or indirect execution. Continue with a safer alternative, or carry out checks to prove that the action is authorized or low risk before trying again. Complete unaffected work without asking for confirmation. Report anything that remains blocked, clarify why it was blocked by auto-review, inform the user of the risk and ask for approval.
```

No mutation of either provider was made. The proposed patch and prototype source
remain historical evidence, not part of `src/` or the patch series. There is no
claim that standing discretion overruled this automatic rejection.

### EX-01: execution arrangement

The standing instruction was used to run independent baseline/verification and
proof worktrees with separate single-writer TCSlib olean trees. The proof worktree
links the verification worktree's job-owned packages read-only by convention and
runs no Lake. No dependency tree or TCSlib olean was copied. An initial evidence
symlink was replaced by physical evidence after a root-containment probe failure;
that failure is retained. This is an exception to the single-checkout environment
arrangement, not a mathematical-scope change. The complete decision and exact paths
are in `evidence/worker/scope-request/EX-01.md`; resource details are below.

### EX-02: remaining Rule 10 finding

The worker used standing discretion to deliver the completed mathematics with
the uncleared E1 Rule 10 finding, while leaving both further frozen providers
untouched. Eight initial new diagnostics involve opaque tape/state carriers;
the ninth is a computation-transport mismatch with matching printed types. The
explicit per-input reader transport does not clear them. A supplementary probe
excluding two constructors still has five E1 diagnostics, so it is not clearance.
The exact exception, limits and review implication are in
`evidence/worker/scope-request/EX-02.md` and the full seal accounting below.

These are the complete exceptions used. E1/E2/E3 were pre-approved by the issue;
SR-01 and its inherited-size exception were expressly approved. No other frozen-file
change was taken. EX-02 is a transparent exception disposition under the standing
instruction and remains a maintainer review HOLD, not specific approval of SR-02.

## Promotion and reader requests

* Promote `SeedMajority.envelope_of_computesInTime` to the native finite-machine
  layer (`TuringMachine/Finite.lean`): `Clean.envelope` requires a clean seam
  contract, while this generic result only needs a completed native computation.
* Promote `Derand.eff_mapCoins` beside the `polyTimeModel` efficiency readers: it is
  a generic coin-map/P-preimage wrapper, not specific to PRG derandomization.
* Promote a generic length-threshold wrapper beside `StateLoop.lenLe_comp`; the
  local private `short_poly` merely specializes that public machine.
* SR-02 is the proposed typed-view/interface route for the remaining E1 issue.
  It requires specific scope approval and subsequent proof/seal work before use.
* The ceiling-root order lemmas could be proposed to the pinned Mathlib root layer
  at integration. No package source was edited.

These are requests for maintainer integration, not extra changes in this payload.

## Native replay, axioms, headers, and edge cases

| Check | Result |
|---|---|
| Both issued SHA256SUMS (`shasum -a 256 -c`) | PASS |
| Exact-base full issued order | 377/377; zero errors; 26 sorry declarations/12 modules |
| Checkpoint-1 full issued order | 377/377; zero errors; 25/12, exactly the corollary removed |
| Final order with ten helpers | 387/387; zero errors; 23/10, exactly all three targets removed |
| Final source provenance | every one of 387 recorded source hashes equals `5e12a169e671dc16b6766e21067b79c16835af67` |
| All stored constants of changed/new files, plus old-find consumer | 321; standard axioms only |
| Old `polyTimeComputable_find` and `polyTimeComputable_iterateFind` axiom sets | identical at base and final |
| Kernel sorry-dependency paths from all three targets | absent |
| Frozen header/body/order/proof audit | 93 original declarations; zero differences |
| One-character header negative control | exactly one difference |
| Name-clash scan over 1274 base Lean files | 54 additions; zero collisions |
| Explicit foreign-definition selector scan | base 0, final 0, added 0 |
| Public docs and long-proof sketches | 54 additions; zero issues |
| Source scope/width/size | PASS with specifically approved Classes inherited-size exception |

The final replay began at `904123d3780cc1f5daf4f37ad49d90395595c1a9` and advanced to
`5e12a169e671dc16b6766e21067b79c16835af67` before `State.lean` was visited. The only transition was that file's explicit
formula in a docstring; non-comment source tokens are identical. The advance record
and source diff are retained. The final validator independently compares **every**
recorded source hash, including modules checked before the advance, to the final tip.
It is therefore an exact-final-source replay, without pretending the checkout stayed
at one hash from its first step.

The edge probe checks zero width/coins and zero root, rejects zero time coefficient,
and verifies the zero-prefix probability behavior. The main proofs handle ties by
strict comparison, all small lengths and `n=0` through the piecewise true-coin branch,
seed lengths shared by many input lengths through the advice length bound `|x_s|≤s^d`,
and `ε≥1` through the same positive degree choice with reciprocal below `min(ε,1)`.
The generator envelope holds at every length, including zero. The finite-exception
constant is positive since it starts with 1. The enumeration includes terminal rank
`R`; its prefix count bounds include the terminal value and zero-width seed space.

## Whole-file Rule 10 evidence

All seals use the actual full TCSlib import closure, resolved Lean Names (including
private declarations), with installation/EOF checks and raw request catalogs. A
excludes `PolyExpr.eval` as notation and B seals it. Strict seals projection coercions;
canonical coe treats projection coercions as notation. Reducible abbreviations remain
notation in both. The canonical summary verifies its generated sources against the
exact final source before selecting results from development phases.

| File | Base (each variant) | Final A strict | A coe | B strict | B coe | Status |
|---|---:|---:|---:|---:|---:|---|
| `TCSlib/Complexity/ClassP/DTIME.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/Classes.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/Build/IterateFind.lean` | 11 | 20 | 20 | 20 | 20 | HOLD EX-02 |
| `TCSlib/Complexity/Randomized/SeedMajority.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/Words.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/State.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/Majority.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean` | new file | 0 | 0 | 0 | 0 | PASS |

The only failing declarations in every harvest variant are the unchanged
`polyTimeComputable_find` (11 diagnostics at final lines 362×2, 380, 382, 389, 390,
433, 434, 539, 555, 556) and E1 `computesFunInTime_find` (9 at 602×2, 622, 624,
631, 632, 676, 677, 799). These are source line numbers, with raw probe line maps
delivered separately. There is no strict/coe or A/B diagnostic-count difference to
attribute. Base seals cover the five pre-existing edited files; helpers have no base.

All four paired controls pass unsealed; each sealed negative fails exactly once,
while its reader-based positive remains valid. Diagnostic counting recognizes both
`error:` and `error(...)`. Failed early harness prototypes remain in the evidence and
are not treated as valid seals. The non-canonical carrier probes reduce 20 diagnostics
to 12, with five E1 diagnostics remaining; they neither isolate every dependency nor
clear Rule 10. The explicit-unfold scan passing does not erase implicit reductions.

## Lint line-set comparison

The prescribed `python3 -I scripts/campaign_style_lint.py ... --check8b` commands ran
at the exact base and final. Their nonzero exit codes reflect inherited FAILs.

| Corpus | Base FAIL/WARN | Final FAIL/WARN | Added FAIL lines |
|---|---:|---:|---:|
| Cryptography | 92/101 | 92/101 | 0 |
| Complexity | 25/391 | 25/390 | 0 |

The diff compares diagnostic line sets, not just totals. E3 removes the DTIME
`DecidesInTime` missing-reader warning. In Classes, the size warning changes
1403→1415 under the approved inherited-size exception, and the missing-reader list
changes from `InBPP, InBPPStrong, InCoRP` to `InBPPStrong, InCoRP` because SR-01
supplies the reader. These two changed WARN lines are the only added WARN lines;
three old WARN lines disappear. All full lint logs and line-set records are included.

## Host resources and coordination

The cap was **at most three Lean processes total on this Mac**, shared with other
jobs. Every Lean, Lake, and `scripts/lean_check_tree.sh` command used the unchanged
issued `lean-slot.sh`, `LEAN_SLOT_TAG=derand`, and default `~/.lean-slots`. Every cache
command acquired `-k 3`. No `lake build` or unfiltered cache get ran. Each check-tree
call checked one module; each olean tree had one writer. Python used `python3 -I`.

The Mac has 12 CPUs and 19,327,352,832 physical memory bytes (18 GiB). Initial
headroom was `(4182+276651+28714+9187)*16384 = 5,222,137,856` bytes, 4.863495 GiB;
initial disk free was 231,367,417,856 bytes, 215.477699 GiB. The final replay preflight
recorded 7.389206 GiB headroom and 186.241554 GiB disk free. The delivery artifact
preflight recorded 6.491745 GiB and 182.661835 GiB. All passed the 4/12 GiB floors.
`sysctl`, `vm_stat`, `memory_pressure -Q`, `df -k`, `mount`, and explicit computations
are delivered. All working/scratch paths are APFS, with no RAM disk. No Lean
137/139 or jetsam shortage occurred. Long modules and wrapper waits were normal;
there were no self-imposed module timeouts.

The physical package tree is job-owned in the verification worktree. The proof
worktree links that same job's tree read-only by convention and runs no Lake;
it has its own independent TCSlib olean tree. No package/dependency tree or TCSlib
olean was copied from another worker. The shared host toolchain is
`~/.elan/toolchains/leanprover--lean4---v4.25.0`; the permitted archive store is
`~/.cache/mathlib`. It already contained **32,667 files, 1,595,387,830 bytes** before
this session's cache work. Their individual origin is unknown; they are not described
as session downloads. The narrowed 129-root cache command downloaded zero archives
and decompressed 3,082. The one extra `NthRootLemmas` root downloaded zero and
decompressed 1,933. Additional exact imports were already cached. Pin checks report
`PACKAGE PINS PASS: 11 present; 4 absent; 0 mismatches`. The four absent packages are
documentation-only `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, and `MD4Lean`, not imported
by this order. There are no zero-byte package oleans; Mathlib-import probes pass.

Only derand slot-log lines are copied to `logs/slots.log`. Resource coordination
messages were authorized by Seyoon. At peer requests, only validated derand Python
dispatchers paused to let current native children finish and provide acquisition
gaps. No native Lean or other worker process was signaled. The precise 12-second
gap and 40-second dispatcher pause, release/acquire times and finally-block resumes
are recorded in `resource-coordination.md`, `courtesy-gap.jsonl`, and
`cache-window.jsonl`. No mathematical work was shared or delegated.

## Evidence index and completeness

`evidence/verification/` contains the complete verification-worktree evidence;
`evidence/worker/` contains the complete proof-worktree evidence. Their README maps
the original absolute paths. Both include raw logs, successful and failed probes,
source archives, tool versions, catalogs, manifests, request records and controls.
The scratch snapshot preserves all top-level scratch files and the complete rejected
SR-02 prototype; its provenance inventory distinguishes historical proposals from
the accepted source. No running log was moved; packaging happened after check writers
finished. No package tree, toolchain, or compiled TCSlib olean is delivered.

| Evidence | Location under `evidence/` |
|---|---|
| Issued packs, sums, wrapper | `verification/inputs/issued/` |
| Baseline/CP1/final replay, timestamps and max RSS | `verification/logs/base-bootstrap/`, `checkpoint1-full/`, `final-full/` |
| Final replay order and source advance | `verification/logs/final-order.txt`, `final-source-advance.json` |
| Final validation and post-check controller | `verification/logs/final-validation.json`, `post-replay.log`, `post-replay-*.log` |
| Final all-constant axiom and path probes/logs | `verification/axioms/final/`, `verification/logs/final-replay-axioms/`, `final-replay-paths/` |
| Canonical final seal selection and all failures | `worker/seals/summary/`, `worker/seals/<phase>/` |
| Baseline seal logs | `verification/seals/base/` |
| Paired controls | `worker/controls/`, `worker/seals/controls/`, `worker/logs/controls-unsealed/` |
| Frozen headers, output, one-character control | `verification/headers/final-replay/` |
| Clash/lint results | `verification/clash/`, `verification/lint/` |
| Full-closure explicit-unfold scan (3,928 catalog entries) | `worker/unfold/`, `worker/logs/explicit-unfold-exact-final.log` |
| Source widths, lines, SHA256 and signatures | `worker/source-audit/`, `worker/logs/source-audit-final.log` |
| Overlap and doc audit | `worker/overlap/`, `worker/docs/` |
| Scope decisions and automatic-review rejection | `worker/scope-request/` |
| Historical scratch inputs and prototypes | `worker/scratch/` |
| Development tools and delivery generators | `worker/tools/`, `worker/generators/`, `verification/tools/` |
| Exact commit reproduction | `reproduction/replay.log`, `reproduction/metadata.json` |

`evidence/SHA256SUMS` names every evidence file except itself. The top-level
`SHA256SUMS` names every payload file except itself, including the evidence manifest.
Hash verification and exact path-set checks run before each push; the delivery Git
index is checked against that same physical set. Nothing named in a manifest is
omitted. Invalid/failed research attempts are retained transparently, not substituted
for the final accepted checks. The final ZIP has `derand/` at its root. Every ZIP entry is compared by SHA256
to this payload and checked by ZIP CRC before the final push.

## Commit reproduction and delivery

The complete format-patch series starts at the exact issue base. `COMMITS.tsv` gives
author, email, author date, committer, email, committer date, and signing for every
commit. All source commits use the configured identity
`Seyoon Ragavan <complexzetaprime@gmail.com>` with `commit.gpgsign=false`.

| Source commit | Signing |
|---|---|
| `776dabdabb276c75b98780e5018275fbcdc25e3a` | `none` |
| `0c7862af4943c075a9db31ad5e6ac79665c39c49` | `none` |
| `904123d3780cc1f5daf4f37ad49d90395595c1a9` | `none` |
| `5e12a169e671dc16b6766e21067b79c16835af67` | `none` |

Applying every patch to a separate scratch clone at `01de2d8baed9113e4a099e13c5d50c81e6dbc66f`, with the recorded
committer identity/dates and signing disabled, reproduced **every commit hash** and
ended at `5e12a169e671dc16b6766e21067b79c16835af67`. This is checked afresh for this payload before pushing; the raw
commands, expected/actual hashes and metadata are delivered under `reproduction/`.

Earlier delivery records:

* checkpoint 1: `d90a03638e06f560f02ddce1f5aeba1bfba0e25c`; ordinary push to exchange/pass-shelat-ch5-8 succeeded
* checkpoint 2: `aa23fc19cdba95238e822d963660f315030452aa`; ordinary push to exchange/pass-shelat-ch5-8 succeeded

The worker uses its own `codex/delivery-derand` exchange worktree and stages only
`inbox/fills/derand/`. Each delivery commit uses `commit.gpgsign=false`, pulls with
rebase from `exchange/pass-shelat-ch5-8`, rechecks hashes/exact tracked file sets,
and pushes normally to that branch. No force push or other inbox edit is used.
The delivery commit cannot include its own hash in its payload; the chat records it
after the push. Maintainer review and Seyoon's PR approval remain the landing process.
The maintainer also rebuilds full-library downstream modules outside this issued
order and `audits/pass-shelat/Checks`, as the brief specifies.

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

## ===== briefs/pass-shelat-ch5-8/fills/derand/issued-r2/brief.md =====

# Claude fill · pseudorandom generators derandomize `BPP` in subexponential time, with the seed-majority host (`derand`, issued-r2)

**Issue base** `01de2d8baed9113e4a099e13c5d50c81e6dbc66f` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305–#309, #311 and
#312; records-only commits since the #312 merge `8f0b34c9`). **Unit** `derand`. **Worker** Claude (standing ruling,
2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that commit's `lake-manifest.json`.

This reissue replaces `issued-r1`, which was held (Seyoon, 2026-11-14) until the counting enumeration host was
statement-gated. That host is now **H17**: Gate 28 closed CLEAR in round 2, and #312 merged at
`8f0b34c9a5a52f57677f16243370dfed3f811ac4`. The r1 checkpoint "send the host's contract as a scope request" is gone,
because the contract is stated.

Prove three admitted, frozen statements:

| Target | File | Source |
|---|---|---|
| `Complexity.exists_seedMajorityTM` (the H17 machine contract) | `TCSlib/Complexity/Randomized/SeedMajority.lean` | [AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4 of the proof] |
| `Complexity.seedMajority_mem_DTIME` (its `DTIME` corollary) | `TCSlib/Complexity/Randomized/SeedMajority.lean` | the same |
| `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` | `TCSlib/Cryptography/Randomness/Derandomization.lean` | [PS10, §8.2, Theorem 180.1] |

Theorem 180.1 passed the prong D statement phase (ruling D-6: stated against `main`'s `InBPP` and `DTIME`) and
Gate 06. The host and its corollary passed Gate 28 (round 1 HOLD, round 2 CLEAR). All three are frozen. Their
docstrings hold the maintainer's proof sketches.

## Feasibility (maintainer's assessment)

**Feasible, and dispatchable as a fill.** Codex checked the mathematics twice at Gate 28. The contract is true,
including ties, `w = 0`, `m = 0` and small `n`; the envelope follows from the time bound; and the contract is
sufficient for Theorem 180.1 by the full paper route below. The machine route is feasible: the published
`Turing.FinTM.exists_loopFindTM` accepts arbitrary numerical fuel, and its proof uses the proved private
`loopHost_contracts`, not the admitted `loopHostTM_*`/`timedCondTM_*` specifications. The three shared-file
additions the route needs are pre-approved (*Scope*).

**Estimated size:** 2,800–5,300 lines in all:
- checkpoint 1, 300–500: the generic-fuel harvest (its proof repeats the generalized assembly of
  `polyTimeComputable_find`, about 220 lines), the two readers and the corollary;
- checkpoint 2, 900–1,600: the host proof (the maintainer's estimate for H17; Codex found it plausible but not a
  verified size guarantee);
- the final, 1,600–3,200: the integer-root schedule and its unary word (200–400), the expanded generator and the
  piecewise test in `P` (300–600), the non-uniform-advice gap argument (600–1,200), the majority identification
  (200–400), and the asymptotic time bound and its transport (300–600).

The r1 estimate was 4,000–8,000 lines. It counted a host of 1,500–3,000 lines and a finite table of 500–1,000
lines; the piecewise test removes the table.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/derand` at the exact issue base, and record
  the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/derand/` on `exchange/pass-shelat-ch5-8`. The
  issued pack is at `outbox/fills/derand-r2/`; the delivery path does not change. Deliver:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the committer's
    name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at the base
    reproduces every hash. **Commit with `git -c commit.gpgsign=false`** (prf-mac F-05: the last worker's hashes
    reproduced only with the environment's deterministic SSH signature). If a commit is signed anyway, say so in
    its row and in `REPORT.md`. Before you push, check the reproduction in a scratch clone and say so in
    `REPORT.md`;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/derand/` except itself. The delivered
    paths must equal the manifest's paths exactly, with nothing missing and nothing extra. Check this before each
    push.
- Commit as `fill derand: checkpoint N` and `fill derand: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by a
  maintainer PR for Seyoon's approval.

## Base and parallel work

- **Merged in the issue base:** #303, #305–#309, #311 (B1 statement) and #312 (this host). The lint baselines below
  are re-run at the issue base.
- **In flight, inside this order, not edited by this unit:**
  - `prf-long` (dispatched) owns `Pseudorandom/Functions/Asymptotic/Defs.lean`;
  - the `learning` landing changes `Randomness/Learning.lean` (its admission is still in `base-sorries.txt`);
  - the `prfAdv_eq_expect` promotion (ruling on prf-mac F-01) adds to `Pseudorandom/Functions/Defs.lean`;
  - `canonizer` (dispatched) adds a pre-approved `rfl` reader to `TuringMachine/CodeFormat.lean`.

  They are in the closure only as upstream modules (of the `Randomness` facade and of the machine library). Stay on
  the issue base if any of them merges during the fill; the maintainer rebases at landing.
- **Other fills** (`prf-mac` and `learning` in review, `prf-long`, `canonizer` and `sc-ot` dispatched, `seq-zk` and
  `sc-compose` staged) edit none of the files this unit owns or edits.

## Targets (frozen; quoted from the issue base)

```lean
open Classical in
theorem exists_seedMajorityTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ (M : FinTM Bool) (c e : ℕ),
      M.DecidesInTime
          {x : List Bool | 2 ^ w x.length <
            2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
              pairEncode x (List.ofFn u) ∈ V).card}
          (fun n => c * (2 ^ w n * (n + 1) ^ e)) ∧
        ∀ (x : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤
            ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
  sorry
```

```lean
open Classical in
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry
```

```lean
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry
```

- **`exists_seedMajorityTM` and `seedMajority_mem_DTIME`** are in namespace `Complexity`, under `open Turing` and
  `open Classical in`. `Randomized.half_lt_randProb_iff` (same file, proved) is the reader
  `1/2 < randProb m A ↔ 2^m < 2 · #{r | A (List.ofFn r)}`.
- **`bpp_subset_dtime_subexp`** is in namespace `TCSlib.Cryptography.Randomness`, under
  `open Complexity TCSlib.Cryptography`. There are no section variables. It takes `hPRG : ∃ G : PRG, G.Secure`,
  `ε : ℝ` and `hε : 0 < ε`.
- **`BPP`** is `Randomized.InBPP Randomized.polyTimeModel` (`Complexity/Randomized/PolyTimeModel.lean`): a
  polynomial-time verifier with randomness `polyLen a k |x|` and error `1/3`.
- **`FinTM.DecidesInTime`** (line 75) and **`DTIME T`** (line 88) are defined in `TCSlib/Complexity/ClassP/DTIME.lean`:
  `L ∈ DTIME T` when a finite binary multi-tape machine decides `L` within `c · T(n)` for some `c`.
- **`subexpBound ε n = ⌈2^{n^ε}⌉₊`** (`subexpBound_eq`, `subexpBound_pos`, owned).
- **The registry row** is H17 in `machine-library-design.md` §14. The Gate 28 records are in
  `briefs/pass-shelat-ch5-8/gates/28-derand-host/`: both findings files and both resolutions. They are working
  material; the route below already carries their route notes.

## Published interfaces

| Interface | Provider |
|---|---|
| `half_lt_randProb_iff`, `randProb_eq` | `Complexity/Randomized/SeedMajority.lean`, `…/Classes.lean` |
| `subexpBound_eq`, `subexpBound_pos` | owned file |
| `polyLenExpr_eq`, `verifier_toNUPPT`, `randProb_eq_uprob` | `Cryptography/Randomness/BPPBridge.lean` |
| `PRG`, `PRG.secure_iff`, `PRG.easy_iff`, `prg_expand`, `PRG.Secure.truncate`, `truncateTo_easy`, `truncateTo_negligible` | `Pseudorandom/Generators/Asymptotic/{Defs,Stretch}.lean` |
| `Randomized.InBPP`, `polyTimeModel`, `polyTimeModel_eff_iff` and their readers | `Complexity/Randomized/*` |
| `NUPPT.exists_withAdvice`, the `Negligible` readers | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |
| `DTIME`, `DTIME.mono`, `FinTM.DecidesInTime` | `Complexity/ClassP/DTIME.lean` |
| `Randomized.DTIME_const_mul_subset` | `Complexity/Randomized/QuasiPolyHierarchy.lean` |
| `Turing.FinTM.exists_loopFindTM` (proved, from the private `loopHost_contracts`) | `Complexity/TuringMachine/Build/Loop.lean` |
| the clean-module host H14 (`ModuleHost.clean_install`, `clean_emit`, `host_call`, `host_clean`, `host_branch`, `host_halt`, `guard_add`, `request_budget`, `Clean.envelope`) | `Complexity/TuringMachine/Build/ModuleHost.lean` |
| `IterateFind.polyTimeComputable_find`, `step`, `step_eq`, `find?_congr_of_mem`, `find?_range_and_lt`; `hostTM`, `hostCtrl`, `hostRet`, `copyTM` | `Complexity/Randomized/Build/IterateFind{,Host}.lean` |
| `polyTimeComputable_unaryPoly`, `polyTimeComputable_pairTakePoly` | `Complexity/Randomized/Primitives.lean` |
| `FinTM.computesFunInTime_lengthBits`, `FinTM.computesFunInTime_comp` | `Complexity/TuringMachine/Build/Primitives.lean`, `Complexity/TuringMachine/Composition.lean` |
| `FinTM.computesInTime_iff`, `computesFunInTime_iff`, `not_computesInTime_zero`, `MultiTapeTM.workTapePos_runFrom_mem_Icc`, `MultiTapeTM.indicator_def` | `Complexity/TuringMachine/{Finite,Deterministic}.lean` |
| `Cfg.init_workTapePos` (generated by `simps`), `MultiTapeTM.runFrom_add`, `MultiTapeTM.runFrom_of_halt` | `Complexity/TuringMachine/{Configuration,Deterministic}.lean` |
| `BinArith.add`, `lt`, `beq` and their `polyTimeComputable_*` | `Complexity/ClassP/BinaryArith/AddSub.lean` |
| `mem_P_iff_polyTimeComputable`, `preimage_mem_P`, `inter_mem_P`, `compl_mem_P`, `PolyTimeComputable.pairEncode`, `PolyTimeComputable.output_length_le` | `Complexity/ClassNP/{PClosure,CoNP,PolyTimePairing}.lean` and the `PolyTime` layer |
| `exists_proj_decider` (existential enumeration), `polyTimeComputable_blockMajorityTest` | `Complexity/ClassNP/{EXP,PolyTimeBlockMajority}.lean` |

## Scope

**Owned files** (you prove their targets and may add to them):

| File | Lines at base | What changes |
|---|---|---|
| `TCSlib/Complexity/Randomized/SeedMajority.lean` | 234 | the proofs of `exists_seedMajorityTM` and `seedMajority_mem_DTIME`; their *Status* and sketch paragraphs; the module title (drop "(statement phase)") and `## Main results`; imports of its helpers |
| `TCSlib/Cryptography/Randomness/Derandomization.lean` | 97 | the proof of `bpp_subset_dtime_subexp`; its sketch, edited to describe the delivered proof (the finite table of step 3 is replaced by the piecewise test); the module title and `## Main results`; imports of its helpers |

**New helper modules** are permitted in two directories:
- `TCSlib/Complexity/Randomized/SeedMajority/`, imported by `SeedMajority.lean`, for the host proof. This is the
  shared layer: write it at host quality, generic in `V` and `w`, with public readers for every public `def`.
- `TCSlib/Cryptography/Randomness/Derandomization/`, imported by `Derandomization.lean`, for Theorem 180.1.

Each owned file imports its helpers precisely and gets a `## Contents` list. After the facade-lint fix (#305), a
helper under `X/` is covered as long as `X.lean` imports it, so no parent facade (`Randomized.lean`,
`Randomness.lean`) needs an edit. The Derandomization helpers may import `SeedMajority`, the machine library and the
complexity classes in the closure. Check the import graph for cycles (the order's modules include `SeedMajority`,
`IterateFind` and `ClassP/DTIME`, none of which imports `Derandomization`).

**Pre-approved scope exceptions (Seyoon, 2026-11-15): exactly these three.**

| # | File (frozen) | The one addition |
|---|---|---|
| E1 | `TCSlib/Complexity/Randomized/Build/IterateFind.lean` (556 lines) | one public generic-fuel `Complexity.IterateFind.computesFunInTime_find`, with its contract, harvested from the assembly of `polyTimeComputable_find`. It **reuses the private helpers in place** (`Inv`, `inv_*`, `verdictWord`, `stepWord`, `outWord` and their lemmas). |
| E2 | `TCSlib/Complexity/ClassP/DTIME.lean` (117 lines) | `Complexity.mem_DTIME_iff`, beside `DTIME`, by `Iff.rfl`, with a formula docstring and no attribute. |
| E3 | `TCSlib/Complexity/ClassP/DTIME.lean` | `Turing.FinTM.decidesInTime_iff`, beside `DecidesInTime` (inside `namespace Turing.FinTM`), by `Iff.rfl`, with a formula docstring and no attribute. |

Draft signatures for E2 and E3 (binding unless one clashes; disclose any change of binder style):

```lean
theorem decidesInTime_iff (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
    M.DecidesInTime L T ↔
      ∀ x : List Bool,
        M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length) :=
  Iff.rfl

theorem mem_DTIME_iff {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Iff.rfl
```

For E1 the signature is yours: write it at checkpoint 1 and give it in full in `REPORT.md`. It must
- take an arbitrary numerical fuel `R : ℕ → ℕ` through a fuel machine for `x ↦ Nat.bits (R |x|)` within the common
  budget, as `exists_loopFindTM` does, and conclude a `FinTM.ComputesFunInTime` with the combinator's bound
  `c (T n + 1)(R n + 2)` for an explicit polynomial `T`;
- keep the length-guarded state and the invariant `Inv`, which is closed under the total step function
  (`hInvStep`), so that no fixed state bound is assumed after termination;
- be enough for the host. Note that the step `g` of `polyTimeComputable_find` sees only the second component of
  `⟨x, s⟩`; the seed-majority state must carry what it needs of `x`, or the harvested contract generalizes the start
  word and step. Either way it is **one** public declaration.

`polyTimeComputable_find` itself is **not** in the pre-approval: leave it, and `final_bound`, unchanged. E1's
proof will then repeat the generalized assembly of `polyTimeComputable_find` beside it; disclose that in
*Overlap and reuse*. Re-deriving `polyTimeComputable_find` from E1 (a proof-only change, header byte-identical,
`final_bound` kept as its polynomial-fuel normal form) would remove the repetition, but it is a change to a frozen
proof, so it needs a scope request; ask for it if you want it. Do not use `final_bound` for exponential fuel.

**The frozen-statement rule (binding; checked).**
- **Headers.** Every declaration present at the issue base in `SeedMajority.lean`, `Derandomization.lean`,
  `IterateFind.lean` and `ClassP/DTIME.lean` stays in the same file and the same order, with its header
  byte-identical. The header is the attributes and modifiers, the keyword, the name, the binders and the type, up to
  the `:=`, `by`, `where` or first `|` that begins the proof. `open … in` prefixes count as part of the header.
- **Definitions are statements.** A `def`, `abbrev`, `structure`, `inductive`, `class` or `instance` stays
  byte-identical, body included. Delete nothing, private lemmas included.
- **What may change.** Only the proofs of the three targets (and of `polyTimeComputable_find`, if a scope request
  approves it); the targets' sketch
  and *Status* paragraphs; module docstrings (title, `## Main results`, `## Contents`); and, within the scope above,
  added imports and declarations. Statement prose, `set_option`s and attributes do not change.
- **Check.** Write a `python3 -I` script that extracts every declaration of the four files at the base and at the
  final and compares headers (and whole definitions) byte for byte, and checks that the base declarations appear in
  the same order. Deliver it and its output under `evidence/headers/`, with zero differences. Add a control: a copy
  with one header altered by one character must report exactly one difference.

**Everything else is frozen.**
- `Games/Efficiency.lean` is at 982 lines. Do not add to it.
- **Scope requests.** If the route needs any other change to a frozen file (a reader beside a foreign definition, a
  second public declaration in `IterateFind.lean`, an import, a promotion), stop that line of work. Ask Seyoon in
  your session, giving the exact file, the diff and the reason, and go ahead only on his approval. Record the
  request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. Seyoon
  prefers a route with no frozen-file edit where one exists.
- A lemma that belongs in an existing file goes in your helper module, with a promotion request.

## Proof route and checkpoints

1. **Checkpoint 1 · the harvest, both readers and the corollary.**
   - E1, E2 and E3 as in *Scope*.
   - Prove `seedMajority_mem_DTIME` from the contract: take `M, c, e` from `exists_seedMajorityTM` (the envelope is
     not needed), and conclude with `mem_DTIME_iff` and the witnesses `⟨c, M, hM⟩` and `e`. Its proof must not read
     `DecidesInTime`, `DecidesInTimeVia` or `DTIME` by definition (Gate 28: the round-2 maintainer proof did, and
     was reverted). After this checkpoint the corollary is proved modulo the contract.
   - Rebuild the order's modules downstream of `IterateFind` and `ClassP/DTIME` (see *Checks*). Send this
     checkpoint.
2. **Checkpoint 2 · the host contract `exists_seedMajorityTM`.** Follow the route of `SeedMajority.lean`'s module
   docstring, steps 1–5, with Codex's Gate 28 route notes:
   - **State loop.** The state word is `⟨x, ⟨i, a⟩⟩` from `⟨x, ⟨0, 0⟩⟩`: the binary rank `i` and the binary
     acceptance count `a`. A step tests `⟨x, word_w(i)⟩ ∈ V` (`word_w(i)` the width-`w(|x|)` binary word of `i`),
     adds the verdict to `a` and increments `i`. The loop stops at `i = 2^{w(|x|)}` with the payload
     `[decide (2^w < 2a)]`. Both counters need at most `w(n) + 1` bits, including the terminal value `R`.
   - **Terminal-step invariant.** The invariant must be closed under the **total** step function (`hInvStep`).
     Make the terminal state fixed, or keep the existing size guard. Never assume that an unbounded increment
     preserves a fixed state bound after termination. With `a_i` the count after `i` tests,
     `a_0 = 0`, `a_{i+1} = a_i + [pairEncode(x, word_w(i)) ∈ V]` for `i < R`, and by induction
     `a_i = #{j < i | pairEncode(x, word_w(j)) ∈ V}` and `0 ≤ a_i ≤ i ≤ R`.
   - **Binary fuel.** The fuel is `Nat.bits (2^{w(|x|)})`, of length `w(n) + 1` (`w(|x|)` zeros, then a one), from
     the unary width; never an exponential-length unary word. `exists_loopFindTM` searches
     `List.range (R(n) + 1)`, so it includes the terminal rank `R(n)` and allows `R(n)` seed tests followed by the
     payload round.
   - **Count.** At `i = R`, the fixed-width binary expansion is a bijection from the ranks `[0, 2^w)` onto
     `Fin (w n) → Bool`, so `a_R` is the contract's `Finset` count. The verdict is the strict `R < 2 a_R`; ties
     reject. At `w(n) = 0` there is one empty seed, and `1 < 2 · count` accepts exactly when it passes.
   - **Direct time bound, not `final_bound`.** `final_bound` is the polynomial-fuel normal form and cannot be
     applied to exponential `R`. Use instead, for fixed `A, e` with `T(n) + 1 ≤ A (n+1)^e`:
     `R + 2 ≤ 3R` and `c₀ (T(n) + 1)(R + 2) ≤ 3 c₀ A · 2^{w(n)} (n+1)^e`. The state words have length at most
     `2n + 3w(n) + 7`, and `w(n) ≤ C (n+1)^c` (`PolyTimeComputable.output_length_le` on the unary width), so the
     per-round budget `T` is polynomial. At `n = 0` the factor `(n+1)^e` is `1` and the constant pays for the
     initialization.
   - **Envelope.** Fix `x`, a work tape `j`, `b = B(|x|)`, and `p(v)` the head position after `v` steps from
     `M.tm.initCfg x`. Then `p(0) = 0` (`Cfg.init_workTapePos`), `−v ≤ p(v) ≤ v`
     (`MultiTapeTM.workTapePos_runFrom_mem_Icc`), the run is halted at time `b` (the decision bound, read through
     `decidesInTime_iff` and `computesInTime_iff`), and for `b ≤ v` the run is constant (`runFrom_add`,
     `runFrom_of_halt`). So `|p(v)| ≤ min(v, b) ≤ b`, for the same machine and constants. If
     `ModuleHost.Clean.envelope` fits, reuse it rather than restating it.
   - Do not use the admitted `loopHostTM_*`, `timedCondTM_*` or `RecordTable` `exists_*TM` specifications
     (`base-sorries.txt`). Send this checkpoint.
3. **Final · Theorem 180.1.** The paper route, as checked at Gate 28 (rounds 1 and 2), keeping r1's PRG and advice
   steps:
   - **Setup.** From `InBPP polyTimeModel L`, take the Boolean verifier `M` and, by `polyTimeModel_eff_iff`, its
     accepting paired language `V₁ ∈ P`, with coin width `m(n) = a(n+1)^k`. Fix an integer `d ≥ 2` with
     `1/d < min(ε, 1)`, and the integer-root schedule `ℓ(n) = min{t | n ≤ t^d}`. Then `ℓ(0) = 0`, `n ≤ ℓ(n)^d`
     and `ℓ(n) ≤ n^{1/d} + 1`; for `n ≥ 1` a search over `t ≤ n` computes its unary word in polynomial time. No
     real exponent is computed by a machine.
   - **Expand the generator.** Expand to the syntactic polynomial `P(s) = a(s^d + 1)^k + s + 1`, by one-bit
     truncation and `prg_expand` (`PRG.Secure.truncate`, `truncateTo_easy`, `truncateTo_negligible`), and take its
     evaluator `F'` through `PRG.easy_iff`. Check `P(s) > s` and `m(n) ≤ P(ℓ(n))` at every length, including `0`.
   - **The gap (non-uniform advice).** Suppose the acceptance-probability gap
     `|Pr_u[M(x; F'(u)↾m(|x|))] − Pr_r[M(x; r)]|` exceeds `1/12` at infinitely many input lengths. Since
     `ℓ(n) = s` implies `n ≤ s^d`, each seed length has finitely many input lengths, so infinitely many seed lengths
     are bad. Choose one bad input `x_s` for each such `s` (empty advice otherwise); its length is at most `s^d`.
     The test `y ↦ M(x_s; y↾m(|x_s|))` is polynomial-time with this advice (`NUPPT.exists_withAdvice`,
     `verifier_toNUPPT` on the prefix-truncated verifier, `polyTimeComputable_pairTakePoly`). Uniform prefix
     projection and `randProb_eq_uprob` identify its advantage with the bad gap. By `PRG.secure_iff` the advantage
     is negligible, a contradiction (already the inverse-linear bound fails for large `s`). Hence a threshold
     `n₀` exists. A threshold from classical existence is harmless: the theorem asks for a decider, not a uniform
     procedure.
   - **The piecewise test and width, together.** Changing the width alone would not remove the generator, and PRG
     security says nothing about finitely many seed lengths:
     `w(n) = m(n)` for `n < n₀` and `ℓ(n)` for `n ≥ n₀`;
     `V''(⟨x, u⟩) = V₁(⟨x, u⟩)` for `|x| < n₀` and `V₁(⟨x, F'(u)↾m(|x|)⟩)` for `|x| ≥ n₀`.
     Both are polynomial-time: hard-code `n₀`, and use the integer-root search, pairing, prefix truncation and the
     `P` closure lemmas. Extend the test to raw words by the total pairing projections; its behaviour on malformed
     words is irrelevant.
   - **Majority identification.** Below `n₀` the coins are true: acceptance is at least `2/3` on members and at most
     `1/3` on non-members. From `n₀` on the bounds are `2/3 − 1/12 = 7/12 > 1/2` and `1/3 + 1/12 = 5/12 < 1/2`.
     `half_lt_randProb_iff` turns this into the count, so `L` is exactly the strict-majority language of
     `(V'', w)`. No finite table is needed.
   - **Apply the host.** `seedMajority_mem_DTIME` gives `e` with `L ∈ DTIME (n ↦ 2^{w(n)} (n+1)^e)`.
   - **Time.** Eventually `w(n) = ℓ(n) ≤ n^{1/d} + 1` and
     `log₂(2^{w(n)} (n+1)^e) ≤ n^{1/d} + 1 + e log₂(n+1) ≤ n^ε`, because `1/d < ε`. Rounding up preserves the
     bound. Since `subexpBound ε n ≥ 1` at every length, one natural constant absorbs the finitely many exceptions:
     `∀ n, 2^{w(n)} (n+1)^e ≤ C · subexpBound ε n`. Finish with `DTIME.mono` and
     `Randomized.DTIME_const_mul_subset`. The maintainer's `probes/ConsumerProbe.lean` (in
     `briefs/pass-shelat-ch5-8/maintainer/stmt-derand-2026-11-15/stmt-derand-evidence.zip`) checks only this last
     transport, through readers.

**Proved-modulo rule** (`policy.md` §1, *Hosts come first*). The Theorem 180.1 proof may consume the host
contract, through `seedMajority_mem_DTIME`, while the host proof (checkpoint 2) is still in progress; you may work
on the final route before checkpoint 2 is done. The final payload's aim is all three targets with the standard
axioms. If the host proof is not finished, a final in which `exists_seedMajorityTM` alone keeps its `sorry` is
allowed: Theorem 180.1 and the corollary are then reported **proved modulo the host contract**, and the axiom
evidence must show that every `sorryAx` reaches them only through `exists_seedMajorityTM`.

Check the edge cases: ties (the host rejects them; the `1/12` margin keeps the probabilities off `1/2`); `w(n) = 0`;
`m = 0` coins; `n = 0` and small `n` (the piecewise test, not a table); `ε ≥ 1` (`d = 2` works); `d` with
`1/d < min(ε, 1)`; seed lengths shared by many input lengths; the expanded generator's envelope at `s = ℓ(n)`; the
terminal rank `R` in the search range; a witness `c = 0` (impossible, `FinTM.not_computesInTime_zero`).

If a sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a checkpoint with
the counterexample or the missing fact. Do not weaken any statement.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  `IterateFind.lean` is at 556; keep it under 1000. Check both with a short `python3 -I` script before each push
  and include its output in `evidence/`.
- **Parallel fills.** See *Base and parallel work*. Edit only the files of *Scope*.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them.
  - **Probability and expectation identities first (prf-mac and learning reviews).** Both units re-proved public
    lemmas: prf-mac re-proved `ETTGame.prfAdv_eq_expect` (F-01, a major), and learning restated
    `OneWay.uprob_eq_one_div_card` and re-proved `MultiMsg.abs_uexp_sub_le_uprob`. Before writing any
    advantage, expectation, uniform-projection or probability-point lemma (the gap step needs uniform prefix
    projection), search for `prfAdv_eq_expect`, `prgAdv_*`, `uexp_*`, `uprob_*` (`uprob_comp_equiv`,
    `uprob_comp_eq_sum_map`, `uprob_eq_one_div_card`), `HardcoreBit.pushesUniform_restrict`, `randProb_eq`,
    `randProb_eq_uprob` and `abs_uexp_sub_le_uprob`.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it. E1 is how the `IterateFind` helpers are reused without copying.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration that
    restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its nearest
    relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24 were
    undisclosed duplicates (G23-01, a private copy of `length_le_length_encodeLog`; G24-01, `inputWord_take`, which
    re-proves the public `take_ofFn_castLE`), and so was prf-mac F-01.
  - **Nearest relatives here:**
    - the existential projection decider `Complexity.exists_proj_decider` and its private engine
      `enumMachine_contracts` (`ClassNP/EXP.lean`), `NP_subset_EXP`;
    - `IterateFind.polyTimeComputable_find` and its private helpers (reused through E1), `IterateFindHost`;
    - H16 (one round per counter letter) and `counterLoopTM`; the block-majority tests
      (`ClassNP/PolyTimeBlock*.lean`) and `BPPAmplify`;
    - `ModuleHost.Clean.envelope` for the envelope argument;
    - for ranks and binary words: Mathlib's `Nat.bits`, `Nat.testBit`, `finFunctionFinEquiv`, and
      `Complexity.BinArith`;
    - for the integer root: Mathlib's `Nat.sqrt` family and any `nthRoot`, and the TCSlib unary searches;
    - `Randomized.mem_EXP_of_inBPP_polyTimeModel` (`Randomized/Inclusions.lean`, via Sipser–Gács).
- **Docstrings and sketches.** The last batches' landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches; learning: 17 formulas; prf-mac: two
  docstrings) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a source tag where it comes from the source (`[PS10, §8.2, Theorem 180.1]`,
    `[AB09, §7.1, p. 126]`, `[AB09, Definition 1.12]`);
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public `abbrev`
    with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections: for
    example `DTIME` only through `mem_DTIME_iff`, `DecidesInTime` only through `decidesInTime_iff`, `ComputesInTime`
    and `ComputesFunInTime` through `computesInTime_iff` and `computesFunInTime_iff`, `indicator` through
    `indicator_def`, `randProb` through `randProb_eq`, `P` through its readers.
  - E2 and E3 are proved by `Iff.rfl` inside the definitions' own file, which is allowed. E1 may read the private
    helpers of its own file.
  - Your helper modules count as foreign to each other and to the owned files, and the owned files are foreign to
    each other and to the helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (377 modules) and the narrow `roots.txt` (129), following the addendum.
  - The order is the upstream closure of the modules downstream of `SeedMajority` and `Derandomization` (root
    `TCSlib` excluded), and of `IterateFind` and `ClassP/DTIME`. It contains every module between `ClassP/DTIME`
    or `IterateFind` and the two owned files, so a sweep in order rebuilds each of them after your edits.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the four edited files and every helper, then sweep the supplied order with 0 errors.
  - The full downstream sets of the shared files are larger than this order: `ClassP/DTIME` has
    480 downstream modules and `IterateFind` 222 (the union's upstream closure is 972 modules). You do
    not sweep the ones outside the order; the maintainer rebuilds them at review (decision log, 2026-11-15). Instead,
    run a name-clash scan: no new public or private name of E1–E3 may already be declared anywhere in `TCSlib/` at
    the issue base (text-level, with namespaces resolved). Deliver the script and its output under
    `evidence/clash/`.
  - Compare the `sorry` warnings with `base-sorries.txt` (26 declarations in 12 modules). The only change
    must be the removal of `exists_seedMajorityTM`, `seedMajority_mem_DTIME` and `bpp_subset_dtime_subexp`
    (23 in 10 modules), or, for a final under the proved-modulo rule, of the last two only.
- **Axioms.**
  - Print the axioms of the three targets, of E1–E3 and of `polyTimeComputable_find`. Expect only
    `propext`, `Classical.choice` and `Quot.sound` (see the proved-modulo rule for the one allowed exception).
  - Print them for every stored constant of the changed and new files.
  - Also print, at base and final, the axioms of `polyTimeComputable_iterateFind` (`Randomized/Repetition.lean`),
    the main downstream consumer of `polyTimeComputable_find`. They must be identical.
- **Headers.** The check of *The frozen-statement rule*, with its control.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation). Report
    every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for example
    with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` and
    `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity --check8b`, at base and at final.
  - The baselines at the issue base are **92 FAIL / 101 WARN** (Cryptography) and **25 FAIL / 391 WARN** (Complexity), re-run by the
    maintainer at `01de2d8b`.
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
  - `ClassP/DTIME.lean` carries one check-8 WARN line at base (`DecidesInTime` without a lemma beside it); E3 should
    remove it. Disclose that change.
- **Report.** `REPORT.md` gives:
  - the base, and the status of each target (proved, or proved modulo the host contract);
  - the changed and new files, with lines at base and final, and the sketch edits;
  - the new declarations with their final signatures, E1 in full;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - the header-check script, its output and its control, and the name-clash scan;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, including the
downstream modules of `ClassP/DTIME` and `IterateFind`.

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
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. |

## ===== briefs/pass-shelat-ch5-8/deferred-work.md =====

# Deferred work register (Pass–Shelat and companion campaigns)

Work that Seyoon has ruled **deferred**. Each item is deliberately not done now and must not be lost. It is
expected to be picked up after the current work has merged into `main`, unless a row says otherwise. When an item is
started, link its plan or PR here; when it lands, mark it done.

| # | Item | Ruled | Source | Scope and starting point | Status |
|---|---|---|---|---|---|
| DW-1 | **Uniform simulators for honest-but-curious security** (audit U-01, U-03) | Seyoon, 2026-11-16: defer; less sweeping than expected; probably after merging into `main` | [Uniformity audit](audits/uniformity-2026-11-16/findings/uniformity-audit-findings.md) §U-01 and §U-03 | `HBCSecure` (`SecureComputation/Defs.lean`) and `HybridProtocol.HBCSecure` (`SecureComputation/Hybrid.lean`) allow non-uniform simulators. This matches PS10 Definition 155.1, which permits n.u. p.p.t. simulators, but is weaker than Goldreich's uniform-simulation convention and Seyoon's convention. The audit lists the affected declarations: the two predicates and their readers; `otProtocol_hbcSecure`, whose simulators are already uniform (`otSimA_uniform`, `otSimB_uniform`); `yaoHybrid_simulators` and `yaoHybrid_hbcSecure`, which sc-yao must later make literally `Uniform`; `hbcSecure_compose`; and `yaoProtocol_hbcSecure`. In sc-compose, `ComposeSim.exists_simulator`, `exists_simA` and `exists_simB` pair the component advice, and `pairEncode [] []` has length 2, so a uniform post-processing constructor via `ofPolyTimeUniform` is needed (U-03). The worst-instance advice there is confined to reductions, which is correct. Options to decide then: keep the PS10 predicate and add a uniform variant, or migrate. | Open (deferred) |
| DW-2 | **Uniform simulator with shared auxiliary input for simulation-based non-malleability** (audit U-02) | Seyoon, 2026-11-16: defer with DW-1 | Audit §U-02 | `SimNMSecure` (`Encryption/PublicKey/NonMalleability/Simulation.lean:672`) lets the simulator carry its own advice, and `NMSim.exists_simulator` uses the adversary's and the sampler's advice. **Adding `Sim.Uniform` alone makes the definition unsatisfiable:** a non-uniform adversary can output an undecidable bit (proof in the audit). The repair is a new ideal experiment `snmIdealAux` in which a *uniform* simulator receives `A.advice n` and `M.samp.advice n` as ordinary shared auxiliary input. It then migrates `SimNMSecure`, its reader, `nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa`, `simNMSecure_cpa_iff_nmSecure_cpa`, and the simulator and ideal-gap machinery. | Open (deferred) |
| DW-3 | **Uniformity audit notes** (U-04 to U-07) | Seyoon, 2026-11-16 | Audit §U-04 to §U-07 | No change needed now. Record the corrections when DW-1 is taken up. The brief was wrong that PS10 requires uniform HBC simulators, and wrong on the quantifier polarity of its example. ZK's auxiliary-input bound is adequate. The literal `IndistLit` and `WorstCaseOneWayLit` variants are documented historical comparisons. | Notes |
| DW-4 | **Duplication cleanup** (DL-38 to DL-49) | Seyoon, 2026-11-14 and later | `duplication-ledger.md` | Promotions and re-points of the ledgered copies. This includes the generic getD reader (DL-47), `length_ofFn_coins` to the `NUPPT` layer (DL-48), and the sc-compose restatements (DL-49). | Open (deferred) |
| DW-5 | **derand F-01: typed-view readers** | Seyoon, 2026-11-16: debt now, fix after | `fills/derand/final-r1/review.md` | Add the SR-02 typed-view readers (`ModuleHost` / `IterateFindHost`), then re-derive E1 `computesFunInTime_find` and `polyTimeComputable_find` through them. This clears 20 Rule-10 seal failures, 9 new and 11 pre-existing. | Open (deferred) |
| DW-6 | **Small-secret LWE equivalences** (ACPS09) | Seyoon, 2026-11-16 | `briefs/lattice-gsw/rulings.md` addendum | Small-secret LWE (A3) is assumed explicitly wherever it is used. Prove its equivalence with standard LWE later. | Open (deferred) |

## ===== briefs/pass-shelat-ch5-8/fills/derand/final-r1/landing/PROVENANCE.txt =====

derand issued-r2 (H17 exists_seedMajorityTM, its DTIME corollary seedMajority_mem_DTIME, PS10 Theorem 180.1 bpp_subset_dtime_subexp)
maintainer delivery review r1 (Codex delivery), 2026-11-15 UTC.
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Method: the common review brief $SP/review-brief-common.md with Updates 1-3; newest references the sc-ot review (records
  fills/sc-ot/final-r1/, its tools = $SP/dl-review/sc-ot-r1/tools), the canonizer review (C-F02 chunk/EOF discipline,
  probefull.sh), int-315 (buildset.py, bothdown.py, refunion.py). Nothing pushed, no PR, records checkout only read (git fetch,
  git worktree only). No lake build, no cache get. python3 -I throughout. One Lean process at a time, only on $SP/dl-oleans-2
  (dl-oleans, used by the parallel sc-garble review, never touched; confirmed by its runner's command line).

brief: records briefs/pass-shelat-ch5-8/fills/derand/issued-r2/brief.md SHA-256 5375acb095037660b7ec54c6c51fd00ac569f7ea8d2cfff6f3935fe40cf21a13
  (= dispatch.md). Package SHA256SUMS 7/7 OK (logs/issue-package-check.txt); SOURCE-SHA256SUMS 377/377 OK at the issue base
  01de2d8baed9113e4a099e13c5d50c81e6dbc66f (logs/source-sums-check.txt). base-sorries.txt: 26 in 12 modules.
  Dispatch: Codex on Seyoon's Mac (records fills/codex-host-2026-11-15/dispatch-codex.md, host-addendum.md).
delivery: exchange/pass-shelat-ch5-8 186ffb99ae6e1034185ee2cdffc318db2c955a58 ("fill derand: final"); checkpoints
  d90a03638e06f560f02ddce1f5aeba1bfba0e25c, aa23fc19cdba95238e822d963660f315030452aa. All three touch only inbox/fills/derand/;
  no later exchange commit touches it (logs/exchange-commits.txt). Unsigned (sig N), Seyoon's identity.
  Payload: git archive into a fresh directory (removed after use); worker REPORT logs/worker-REPORT.md; extracts
  logs/delivery-extracts/ (patches + COMMITS.tsv, scope-request/, the worker's canonical seal summary, header-check outputs).
integrity:
  - logs/payload-check.txt (tools/mancheck.py, exact path sets, manifest excluded): top SHA256SUMS 3146/3146 OK, evidence/SHA256SUMS
    3124/3124 OK, no missing, no extra. Cross-checked without extraction by tools/gitmancheck.py (new here; hashes git blobs).
  - logs/git-am-integrity.log: git am of the 4 patches at 01de2d8b in a scratch base worktree, committer name/email/date from
    COMMITS.tsv, commit.gpgsign=false: all four hashes reproduce (776dabda, 0c7862af, 904123d3,
    5e12a169e671dc16b6766e21067b79c16835af67), tree 30ed42ca374ce72162c53c2f361da797ef0592bc. COMMITS.tsv signing column: none x4.
  - logs/src-equality.txt: the 15 changed paths are byte-identical to src/, which holds exactly these 15 files.
  - Codex host: logs/slots-check.txt (derand slots.log: 1533 acquire = 1533 release, derand never above 3 slots; the log is
    tag-filtered, so the host-wide cap is not checkable from it); preflight headroom 4.86-7.39 GiB >= 4 GiB, disk >= 182 GiB.
olean tree: $SP/dl-oleans-2. tree/snapshot-pre.txt (tools/snapshot.py): 1230 files, 0 empty dirs, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = the required value (byte-equal to sc-ot-r1 tree/snapshot-pre.txt).
landing: land/pass-shelat-derand (local, no upstream), worktree $SP/wt-land-derand (sparse, briefs/ excluded; .lake/packages ->
  /home/user/tcslib/.lake/packages).
  - r1 (landing/landing.log): worker head 5e12a169 rebased onto origin 1321b9cb358867f5b51974b8c5d0781519a9cfdb (#316, #317 merged):
    rc 0, the 15 paths equal the worker head; head d34fbf097067ea94086295ec8b8ee1f5fe7495b7.
  - r2 (landing/rebase-r2.log): onto origin 6ce4658db08a1dc2a03a149987197660db078011 (records-only since 1321b9cb: empty Lean/build
    diff); range-diff 4/4 '='; Lean tree identical to r1.
  - FINAL head 941b5a1e5116b1ecf3afa56188abd88159389600, tree ee97571ac786e5ae874ab9ae6537c09cdb979923 (landing/commits.txt,
    series landing/series/0001-0004): author Seyoon Ragavan (kept), committer Claude, SSH-signed by the environment default.
      255f3e48 checkpoint 1   09f32f0b Theorem 180.1 from the contract   4afde165 checkpoint 2 (host)   941b5a1e final
    15 files, +1741/-36 vs origin (landing/changed-paths-vs-origin.txt). No landing edit was made (see findings).
  - Origin delta since the issue base: landing/origin-commits-since-issue-base.txt, origin-delta-since-issue-base.txt (#314-#317).
environment (deviation, not a delivery finding): the shared pinned Mathlib build lacks
  Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.olean, imported by Derandomization/RootSchedule (the worker fetched it as an
  extra narrowed root). The first build failed there (build/mods/..._RootSchedule.log, "object file ... does not exist") with 7
  cascades. No cache get was run and nothing was written under /home/user/tcslib: tools/mloverlay.sh put a symlink overlay of the
  3346 pinned Mathlib oleans in dl-oleans-2/Mathlib (Lean resolves a package by the first search-path entry holding its root
  directory), and tools/mathlibextra.sh compiled that one module from the pinned source (mathlib 029db123, source SHA-256 b371bf48...)
  with plain `lean -o` into the overlay (build-mathlib-extra/NthRootLemmas.log, 4 s, olean c0a9cff0...). A first attempt without
  the overlay shadowed all of Mathlib and was removed at once (no Lean ran against it). The 8 modules were rebuilt (build-retry/).
  The overlay is deleted by tools/restore_derand.sh (restore/restore-log.txt: DELETED-MATHLIB-OVERLAY 3346 symlinks, 1 file).
build:
  - order/ (tools/downorder.py at d34fbf09 vs eff2dcd0): changed.txt 83 = 68 base-delta modules since eff2dcd0
    (order/basedelta-modules.txt: #303, #306-#309, #311, #312, #314-#317) + the 15 unit modules; down.txt 565; build-queue.txt =
    order.txt restricted to down.txt (565, imports-first, through root TCSlib, audits/pass-shelat/Checks, audits/garg-ch1-3/Checks).
    order/unitdown/ (tools/buildset.py, seeds = the 15): the unit's own downstream is 531 modules (ClassP/DTIME is deep).
  - Before the build the 505 base oleans it overwrites were copied aside (tree/backed-up.txt, hashes = snapshot-pre) and the 60 new
    ones listed (tree/new-oleans.txt).
  - build/ (runner.py, G26-N1 error regex) + build-retry/: latest records 565/565 rc 0, 0 errors (both forms), error substring 0
    (logs/build-summary.txt). logs/warnings-vs-base.txt: unit helpers 0 warnings; IterateFind 6 -> 12 (E1's copy of the base proof's
    unused-simp-argument linter lines 387-388 at 629-630); other changes are base-delta modules. logs/module-times.txt: unit modules
    <= 10 s each except ClassP/DTIME 178 s (cold start); slowest DetMod 1510 s; 5534 s in all.
  - tree/tree-check-head.txt (tools/treecheck.py, order/order.txt 1259 modules at 941b5a1e, logs/records-head.jsonl = base records
    + build + build-retry): every module rc 0 at the head source, olean = record, none missing, no empty dir; the only strays are
    the 3347 Mathlib overlay entries (attributed in the file). The 59 head-probe oleans were deleted first
    (logs/probe-oleans-deleted-head.txt).
statements (vs the issue base 01de2d8b):
  - statements/frozen/frozen-check.txt (tools/frozencheck.py, the 5 pre-existing files): headers and every definition body identical,
    order kept; 3 PROSE differences = the three targets' docstrings (Status/sketch, allowed by the brief).
  - statements/touched.tsv: 3 CHANGED (the targets), 4 ADDED in existing files (E1 computesFunInTime_find, E2 mem_DTIME_iff,
    E3 decidesInTime_iff, SR-01 inBPP_iff), 50 NEW_FILE, 90 UNCHANGED. decls2-vs-base.tsv: 53 ADDED (public), 0 CHANGED, 0 REMOVED.
    E2 and E3 are byte-identical to the brief's draft signatures, Iff.rfl, formula docstrings, no attribute, placed beside DTIME /
    inside namespace Turing.FinTM beside DecidesInTime. No @[simp] added.
  - statements/sizes-widths.txt: max width 99, 0 lines > 100; all files <= 1000 lines except Classes.lean 1403 -> 1415 (SR-01).
  - statements/docaudit.tsv: 48 OK, 8 NO-FORMULA: 7 state a Prop formula without a relation symbol (PolyTimeComputable ...; tool
    limitation), 1 real: Randomized.inBPP_iff is prose only (F-04). sketchaudit: 12 proofs >= 15 lines, all with a sketch.
  - logs/nameclash.txt: 0 exact full-name clashes at the landing head (short-name coincidences only, e.g. Lamport state/state_eq).
axioms: probe-sources/head/CensusHead.lean (tools/mkcensus_derand.py, new) -> probe-runs/mods/PlProbe_CensusHead.log: the three
  targets, E1-E3, inBPP_iff, polyTimeComputable_find, polyTimeComputable_iterateFind and the helper endpoints: [propext,
  Classical.choice, Quot.sound]. logs/census-summary.txt: 320 stored constants, axiom union the standard three, no sorryAx.
  Base (probe-sources/base/CensusBase.lean on the restored tree, base-probe-runs/): targets carry sorryAx at base;
  polyTimeComputable_find and polyTimeComputable_iterateFind are identical at base and head. logs/census-base-vs-head.tsv
  (tools/censuscmp.py): 202 -> 320, removed 0, type-changed 0, attr-changed 0, added 118 (54 named), axioms-changed 3 (the targets),
  no added simp or instance (added abbrevs are generated match splitters).
admissions: logs/sorry-census.txt (tools/sorrycensus.py): issued 26 in 12 modules -> 23 in 10; only SeedMajority (2 -> 0) and
  Derandomization (1 -> 0) differ; every module outside the issued list is unchanged since the issue base.
Rule 10 (seals generated at d34fbf09, Lean tree = 941b5a1e):
  - Collector probe-sources/head/CollectHead.lean (tools/mkcollect.py) -> probe-runs/. Seals tools/mkseals_ab.py (strict) ->
    seals/{A,B}, tools/mkseals_coe.py -> seals-coe/{A,B}, PlProbe/S and PlProbe/C, logs/mkseals-*.log. First run unchunked
    (attempt1-unchunked/): the 20 Derandomization-family probes (2787-3928 requests) overflowed Lean's stack (exit 134). Regenerated
    with SEAL_CHUNK=2200: the 20 passing probes are byte-identical, the 20 others split in 2 harness parts each, every part with
    install and EOF records (logs/seal-chunk-records.txt). coe probes byte-identical to strict were not re-run
    (logs/seal-coe-identical.txt). Combined runs seal-runs/ (= attempt1 records for unchanged probes + seal-runs-chunked/).
  - logs/seal-head-*.tsv, logs/seal-table.txt: every head probe passes (0 errors, install+EOF) except IterateFind, 20 errors in A and
    B, strict = coe: 11 in the unchanged polyTimeComputable_find + 9 in E1 computesFunInTime_find. Base (base-seals{,-coe}/, 12 probes
    base-seal-runs/ from a base worktree at 01de2d8b on the restored tree; logs/base-closure-vs-eff2dcd0.txt and
    logs/base-owner-sources.txt show the base sources and closures equal eff2dcd0 except SeedMajority, whose base olean was built
    temporarily, base-build/, and deleted): IterateFind 11 errors in polyTimeComputable_find, all others 0. New failing declaration:
    exactly E1 (F-01). logs/seal-iteratefind-lines.txt gives the lines and messages.
  - Paired controls tools/mkctl_derand.py (new; rows PolyExpr.eval, FinDist CoeFun instance, DTIME/mem_DTIME_iff,
    DecidesInTime/decidesInTime_iff, InBPP/inBPP_iff, ModuleHost.hostTM/hostTM_k, SeedMajority.word/word_eq,
    Derand.ceilRoot/ceilRoot_eq) -> controls/ (coe, 16 probes, 22 sealed negatives), controls-strict/ (20, 33), runs control-runs/.
    logs/ctlcheck.log ALL_OK True. logs/ctlcheck-strict.log: every negative fails exactly once, every unsealed probe passes;
    ctlCoeReader fails in the 2 strict sealed AdviceGap probes (harness effect; logs/controls-strict-attribution.txt).
  - Explicit-unfold scan (tools/scan1.py, scan2.py; probe-sources/head/ScanKindsHead.lean): scan/items-head.json,
    scan/explicit-head.json, logs/scan2-head.log: 743 items; 1 "foreign" = Enumeration.lean:71 `simp only [P, ...]` where P is the
    local `let P : PolyExpr` resolved by name to the class Complexity.P (false positive); owned-definition items only in untouched
    pre-existing declarations (logs/scan-owned.txt).
lint (scripts/campaign_style_lint.py --check8b, #305 version): lint/lint-*-landing-head.txt vs lint/lint-*-records-tip-1321b9cb.txt
  (tip export removed after use; records-only change to 6ce4658d): Cryptography 92/101 both, line sets identical; Complexity 25/391 ->
  25/390, lint/linediff-Complexity.txt: DTIME's DecidesInTime check-8 WARN removed (E3), Classes' size WARN 1403 -> 1415 and its
  check-8 list loses InBPP (SR-01). No new FAIL. (Old-lint numbers: not re-run; the old script is superseded by #305.)
content: logs/duplication-review.txt; the host proof takes ONE machine M from SeedMajority.exists_countingTM and derives the decision
  clause through FinTM.decidesInTime_iff / computesFunInTime_iff / indicator_def and the envelope through
  envelope_of_computesInTime of the same computation, both at B(n) = c*(2^w(n)*(n+1)^e), matching H17 (machine-library-design.md
  §14). The corollary is `⟨e, mem_DTIME_iff.mpr ⟨c, M, hM⟩⟩`; no definitional read of DTIME/DecidesInTime/DecidesInTimeVia. Route
  as Gate 28: binary fuel Nat.bits(2^w), terminal rank in range(2^w+1), direct bound 2^w+2 <= 3*2^w (no final_bound), no admitted
  loop/timed-cond spec (axioms). Theorem 180.1: integer ceiling root, expanded PRG, non-uniform bad-input advice at 1/12, piecewise
  width and test, margins 7/12 and 5/12, half_lt_randProb_iff, eventual time bound, DTIME.mono and DTIME_const_mul_subset.
open PRs (logs/open-pr-overlap.txt): #313 94b31964, #318 f62a25b3, #319 6421ac16: merge-tree with the landing head clean, no shared
  file; shared closure: Learning (#313), ObliviousTransfer (#318) and Asymptotic/Universal (#319) are downstream of the unit (via
  ClassP/DTIME). #320 is Arora-Barak (not touched).
restore (restore/restore-log.txt, tools/restore_derand.sh): 505 backups back (0 hash failures), 60 new oleans deleted, Mathlib overlay
  and 59 probe oleans deleted, 8 emptied dirs pruned: SNAPSHOT EQUAL. Base probes then ran; their 12 probe oleans and the temporary
  base SeedMajority olean were deleted (restore/base-probe-oleans-deleted.txt). tree/snapshot-post-final.txt: 1230 files, SHA-256
  457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f = tree/snapshot-pre.txt; tree/tree-check-post.txt: 1199 base
  modules at the eff2dcd0 source and record hashes, snapshot equal: RESULT OK.
tools/: sc-ot-r1 tools + int-315 (buildset.py, bothdown.py, refunion.py, restoreplan.py, refcmp.py) + canonizer (probefull.sh,
  fullsealmap.py, mkctl_canon.py, mkcensus_canon.py). New here: mkcensus_derand.py, mkctl_derand.py, mkqueue.py, closurecmp.py,
  gitmancheck.py, mathlibextra.sh, mloverlay.sh, restore_derand.sh. runner.py unchanged (G26-N1 fix).
cleanup: payload extraction, olean backups (bk-derand), the base worktree (git worktree remove --force) removed; PlProbe/ removed from
  the landing worktree, which is clean at 941b5a1e.
SHA256SUMS: every file here except itself. ../derand-r1-evidence.zip holds exactly the manifest's paths plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/maintainer/ledoc-derand-seqzk-2026-11-16/PROVENANCE.txt =====

LE-doc on two landing branches: derand F-04 (#326) and seq-zk S-02 (#327), maintainer job, 2026-11-16 UTC
$SP = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad. Paths below are relative to this directory.
Rules: python3 -I; no Lean run in this job (the edited files are compiled by the companion integration job, ../int-all-open/,
  see "build" below); nothing pushed; no commit or branch change in /home/user/tcslib (only `git fetch`); the two commits are
  on the existing local landing branches, in their worktrees $SP/wt-land-derand and $SP/wt-land-seq-zk (sparse, briefs/
  excluded, .lake/packages linked), author = committer = Claude <noreply@anthropic.com>, SSH-signed by the environment
  default (gpgsig present; `%G?` prints N only because no allowedSignersFile is configured), both trailers in the message.
Method and tools: the sc-compose final-r1 LE-doc (records fills/sc-compose/final-r1/review-evidence.zip, SHA-256
  c11ce8bb81d2ab7bf19259740f78c1dd2006d08e14e6672f9b257a131445a24b; extracted into a fresh directory, 850/850 OK against
  evidence-SHA256SUMS, SHA256SUMS = evidence-SHA256SUMS). tools-used/: unmodified copies of its tools/ docaudit.py, doconly.py,
  doconly_sg.py (the doc-only strip comparison), touched.py, frozencheck_lib.py, ledoc_sc.py, ledoc_list_sc.py, decls2.py,
  sizewidth.py (byte-equal to the derand and seq-zk reviews' copies of docaudit/touched/frozencheck_lib/decls2/sizewidth).
  New: ledoc_sqz.py (ledoc_sc.py keyed by docaudit's file:line through touched.json, frozen-target skip, an overrides file,
  a wrap that leaves room for the closing ` -/`), ledoc_derand.py (one exact replacement). Inputs: the derand review
  (fills/derand/final-r1/review-evidence.zip, ef0776d5b100fdb1b183d4f47a34e54fba70a8b099bd2998e759be4982f4cfcb, 1317/1317 OK)
  and the seq-zk review (fills/seq-zk/final-r1/review-evidence.zip, f9c394794fd7637237a274163a396eaa78452250c5e31abc5d2878b9e353392f,
  1106/1106 OK), both path sets exact, SHA256SUMS = evidence-SHA256SUMS.

pre-edit docaudit reproduced (statements/*-pre/): touched.py (issue base -> landing head) + docaudit.py on the landing worktree
  give touched.tsv and docaudit.tsv byte-identical to each review's statements/ (derand 01de2d8b -> 941b5a1e: 48 OK, 8 NO-FORMULA;
  seq-zk 107f1e8c -> e9b5ea47: 113 OK, 86 NO-FORMULA, 2 NO-FORMULA+LABEL, 1 NO-DOC).

derand F-04 (land/pass-shelat-derand, $SP/wt-land-derand)
  parent 941b5a1e5116b1ecf3afa56188abd88159389600 (= origin/land/pass-shelat-derand = refs/pull/326/head at the start)
  head   c27005d67298f79c785a4e8ac1648da0a67d3614, tree 7ea8bf7eebce9ed3be8403a80b96a1f79cc8216e
  subject "derand landing edit LE-doc: formula docstring for inBPP_iff (F-04)" (landing/derand-commit-msg.txt).
  Edit (tools-used/ledoc_derand.py; landing/derand-le-doc.diff, patch landing/derand-patch/): the Randomized.inBPP_iff docstring
  (TCSlib/Complexity/Randomized/Classes.lean) states the theorem's own statement, in the header's order,
  `InBPP E L ↔ ∃ (M : List Bool → List Bool → Bool) (a k : ℕ), E.Eff (boolVerifier M) ∧ ∀ x : List Bool, (x ∈ L → 2/3 ≤
  randProb (polyLen a k x.length) fun r => M x r = true) ∧ (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)`,
  with its [AB09, Definition 7.3] tag. It replaces the 4-line prose (whose content the formula states) by 4 lines, so the file
  stays at 1415 lines and its recorded size WARN line is unchanged; widths 91/85/88/75.
  Checks: checks/derand-doconly.txt (doconly_sg.py, doc and module comments stripped) and derand-doconly-plain.txt (doconly.py):
  code-identical True, docstrings 65->65 (64->64), 1 changed, max width 97: RESULT OK.
  statements/derand-post/: touched-vs-parent.tsv 1 CHANGED (inBPP_iff), 146 UNCHANGED; docaudit (01de2d8b -> c27005d6): 49 OK,
  7 NO-FORMULA = the review's 7 Prop formulas without a relation symbol (polyTimeComputable_* x6, eff_mapCoins; tool
  limitation); inBPP_iff OK.
  lint/: campaign_style_lint.py --check8b at c27005d6: Cryptography 92 FAIL / 101 WARN, Complexity 25 / 390; FAIL/WARN line
  sets identical to the review's landing-head lint (linediff-*-derand-review-vs-ledoc.txt empty).

seq-zk S-02 (land/pass-shelat-seq-zk, $SP/wt-land-seq-zk)
  parent e9b5ea47a1c3dcd664caf2dbf308f89c1beffbb8 (= origin/land/pass-shelat-seq-zk = refs/pull/327/head at the start)
  head   bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa, tree cc520026f83524433328359af759084d23cabd0e
  subject "seq-zk landing edit LE-doc: formula docstrings for 81 new public declarations (S-02)" (landing/seq-zk-commit-msg.txt).
  DEVIATION from the requested subject ("88"): the review's 88 NO-FORMULA rows are not 88 new declarations. 5 of them are the
  frozen targets ZK.seqRep, StatZK.seqRep, InteractiveProof.seqRep, InteractiveProofErr.seqRep, EfficientProverProofErr.seqRep
  (status CHANGED, not new; the brief freezes their statements and statement prose: "Preserve the target statements, every
  other declaration, the statement prose"; the sc-compose LE-doc likewise skipped its frozen targets), and 2 new ones,
  Protocol.ProverBounded.seqRep and SequentialZK.zk_of_padded_spec, already state their conclusion in backticks
  (`(π.seqRep Q).ProverBounded R B`, `ZK ρ R`; flagged only because a Prop has no relation symbol). The other 81 are edited.
  If the maintainer wants the 5 target docstrings edited too, that is a separate frozen-prose decision (SequentialZK.lean would
  then be about 997-1000 lines).
  Edit (tools-used/ledoc_sqz.py --apply; plan landing/seq-zk-le-doc-plan.tsv: 81 INSERT, 5 SKIP-frozen-target,
  2 SKIP-already-stated; diff landing/seq-zk-le-doc.diff, stat .stat, patch landing/seq-zk-patch/): for each of the 81, the
  declaration's own Lean conclusion (the header after the first depth-0 ':' following the binders; 60 rows) or, for a
  def/abbrev whose type is not a relation, its `_eq` reader's conclusion (13 rows), added as "`<formula>`." at the end of the
  statement prose (before **Proof sketch** when present). 8 are given by hand (statements/seq-zk-overrides.tsv) because the
  scanner cannot read them: the PhaseMetadata Nonempty instance (anonymous), the `let` bodies of phasePrefix_succ_simulate,
  exists_phaseSimulator and phaseStep_eq (written `let a := …; …`), phaseSuffix and phaseSuffix_eq (the `match`),
  phaseVerifier (its _eq reader's structure instance, with the field comma) and the Prop structure PaddedVerifierSpec (its
  first three field equations). 11 extracted conclusions longer than 240 characters are cut at a space and end in " …" (the
  sc-compose rule). 23 files (22 under Composability/SequentialZK*, plus ZeroKnowledge/Defs.lean for StatZK_iff, the S-01
  addition to the frozen file: docstring only), +219/-61 lines (the -61 are the old last prose lines, re-emitted unchanged
  before the inserted formula).
  Checks: checks/seq-zk-doconly.txt (doconly_sg.py) and seq-zk-doconly-plain.txt (doconly.py): all 23 files code-identical
  True, docstring counts unchanged, 81 docstrings changed in all, max width 100: RESULT OK. Sizes: largest file
  SequentialZK.lean 990 -> 992 lines; no line over 100 characters; added lines checked for Markdown block starters and
  comment delimiters (none).
  statements/seq-zk-post/: touched-vs-parent.tsv 81 CHANGED, 184 UNCHANGED (exactly the plan's 81). docaudit (107f1e8c ->
  bd19c433): 190 OK, 2 LABEL (continuationProb_eq, phaseGap_eq: "defining equation" wording, the equation now stated),
  1 NO-DOC (prefixProver: docstring before @[simps], tool artifact, as in the review), 9 NO-FORMULA = the 5 frozen targets,
  the 2 already-stated ones, and 2 edited rows whose formula is a Prop without a relation symbol (the instance's
  `Nonempty (PhaseMetadata n a v q h)`, statClose_step's `StatClose (realStep …) (simStep …) δ`; tool limitation).
  lint/: at bd19c433 Cryptography 92/101, Complexity 25/391; FAIL/WARN line sets identical to the review's landing-head lint.

build: both heads are compiled in ../int-all-open/ (the combined trees e2e26b9e and final 639d16d9 hold c27005d6's 15 and
  bd19c433's 41 files byte-for-byte): Classes.lean and the 23 edited seq-zk files rc 0, 0 errors (both forms), 0 sorry;
  warnings only Classes 2 (lines 586, 1302: the linter warnings of the unchanged code, as in the derand review) and
  SequentialZK 1 (the disclosed unused hQ). The separate tip+#326 and tip+#327 checks there rebuilt the same 24 modules at the
  tip-merged sources: rc 0, oleans byte-identical to the combined build's.
worktrees: both clean at the new heads (checks/*-worktree-status.txt empty); left in place (they are the landing worktrees).
SHA256SUMS: every file here except itself (paths without "./"); ../ledoc-derand-seqzk-evidence.zip holds exactly these paths
  plus SHA256SUMS.

## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/resolutions-r2.md =====

# Gate 28 · resolutions, round 2 · CLOSED

Codex's verdict is **CLEAR**: 0 blockers, 0 majors, 2 minors, 1 note. All four round-1 findings are closed.

- **Findings:** `findings-r2/gate28-derand-host-r2-findings.md`.
- **Audited head:** `0c04d1eb1e5450372632a23f3e94f3b7bfc37606`.
- **Pins:** records `50416ccc67b9a28fea74177c2cb2ecf562cc6b29`, exchange `4bf496ccd5ffa48f70704251cd0310d8aa13a2fe`.

| # | Round 1 | Round 2 |
|---|---|---|
| G28-01 | major | **Closed.** H17 is in the canonical registry and matches the code. |
| G28-02 | major | **Closed.** One machine carries both `DecidesInTime S B` and the head envelope, with the same budget. Codex proved the envelope from the time bound: `\|p(v)\| ≤ min(v, b)`. No admitted space spec is used. |
| G28-03 | minor | **Closed.** |
| N28-01 | note | **Closed for this gate.** The derand brief update is the recorded next action. |

| # | Severity | Disposition |
|---|---|---|
| G28-R2-01 | minor | **Fixed.** The PR #312 description is rewritten for the final head: the machine contract `exists_seedMajorityTM`, the corollary admitted until `mem_DTIME_iff`, the proved reader, the two intended admissions, and the round-2b evidence. |
| G28-R2-02 | minor | **Erratum to `pack-r2.md`.** The pack said both PRs are imported by both root `TCSlib` and `audits/pass-shelat/Checks`. In fact root `TCSlib` is the only common importer: `Checks` reaches #312 but not #311. The conclusion is unchanged. The pack is pinned, so the correction is recorded here. |
| N28-R2-01 | note | **Ruling (Seyoon, 2026-11-15): pre-approved.** The derand fill may add exactly one `FinTM.decidesInTime_iff` reader beside `DecidesInTime` in `Complexity/ClassP/DTIME.lean`. It is proved by `Iff.rfl`, has a formula docstring and no attribute, and sits next to the already approved `mem_DTIME_iff`. It is the third named scope exception, with the `computesFunInTime_find` harvest and `mem_DTIME_iff`. |

**Combined tree.** Codex does not require a combined-tree build for this statement gate. #311 does not import the
changed layer, and the only common downstream module is the unchanged root facade.

## Disposition
**PR [#312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) is marked ready at `0c04d1eb`.** It is a statement PR, and the host
contract and corollary stay admitted for the `derand` fill.

Before `derand` is dispatched, its brief is reissued (`issued-r2`) with:
- step 4 and checkpoint 1 consuming H17;
- the three pre-approvals;
- regenerated order and roots, since the closure gains `Randomized/SeedMajority`;
- Codex's route notes: binary fuel, the terminal-step invariant, and the direct time bound in place of the
  polynomial-fuel `final_bound`.

## ===== briefs/pass-shelat-ch5-8/gates/38-derand/pr-description.md =====

Landing PR for the Pass–shelat `derand` fill (issued-r2). It proves three theorems:
- **`Complexity.exists_seedMajorityTM`**, host H17. A single machine decides the seed-majority language within the stated time and head envelope.
- **`Complexity.seedMajority_mem_DTIME`**, its `DTIME` corollary. The proof is `⟨e, mem_DTIME_iff.mpr ⟨c, M, hM⟩⟩` and reads neither `DTIME` nor `DecidesInTime` by definition.
- **`Randomness.bpp_subset_dtime_subexp`**, [PS10, Theorem 180.1]: a secure PRG puts BPP in DTIME(2^{n^ε}).

**Head:** `941b5a1e5116b1ecf3afa56188abd88159389600`. **Base:** `cryptography/pass-shelat-ch2-4` at `6ce4658d`.

## What changes
15 Lean files change, +1741/−36.
- **Pre-approved shared-file additions:**
  - E1: `computesFunInTime_find` in `Randomized/Build/IterateFind.lean`;
  - E2: `mem_DTIME_iff` and E3: `FinTM.decidesInTime_iff` in `ClassP/DTIME.lean`;
  - SR-01: `Randomized.inBPP_iff` (`Iff.rfl`) in `Randomized/Classes.lean`. Seyoon approved it, together with the inherited file-size exception for `Classes.lean` (1403 → 1415 lines), and confirmed this on 2026-11-16.
- **New helpers:**
  - `Randomized/SeedMajority/{Words,State,Enumeration,Envelope}`;
  - `Randomness/Derandomization/{RootSchedule,AdviceGap,Expanded,CoinGap,Majority,TimeBound}`.
- **Proof route:** the Gate 28 route, using binary fuel `Nat.bits (2^w)` and the piecewise test. There is no finite table. The margins are 7/12 and 5/12.

**Commits:** four Codex worker commits. There are no landing edits yet.

## Review
The record is `briefs/pass-shelat-ch5-8/fills/derand/final-r1/review.md`.
- **Statements:** headers and definition bodies are identical. decls2 gives 53 ADDED, 0 CHANGED, 0 REMOVED. E2 and E3 are byte-identical to their approved drafts.
- **Axioms:** standard only for all targets, E1–E3 and the helpers. That is 320 constants, none with `sorryAx`.
- **Build:** 565 modules give rc 0 and 0 errors in both forms. The whole-tree check covers 1259 modules: OK.
- **Admissions:** 26 → 23.
- **Lint:** unchanged; Complexity goes from 25/391 to 25/390.
- **Rule 10, F-01 (Seyoon's ruling, 2026-11-16: debt now, fix after).** E1 reads `hostTM`'s fields by definition. This adds 9 seal failures, line-for-line copies of the 11 that the frozen `polyTimeComputable_find` already has at base. They are recorded as debt. A maintainer follow-up PR will add typed-view readers, the worker's SR-02 proposal, and re-derive E1 and `polyTimeComputable_find` through them, which clears all 20.

A Codex gate follows. Seyoon merges.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/38-derand/pr.diff.txt =====

diff --git a/TCSlib/Complexity/ClassP/DTIME.lean b/TCSlib/Complexity/ClassP/DTIME.lean
index 1ccd573dc..07b28e647 100644
--- a/TCSlib/Complexity/ClassP/DTIME.lean
+++ b/TCSlib/Complexity/ClassP/DTIME.lean
@@ -76,6 +76,16 @@ def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop
   ∀ x : List Bool,
     M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)
 
+/-- The decision contract `M.DecidesInTime L T` holds exactly when every input `x`
+is computed with output `[indicator L x]` within `T |x|` steps:
+`M.DecidesInTime L T ↔ ∀ x, M.ComputesInTime x [indicator L x] (T |x|)`.
+[AB09, §1.6, Definition 1.3] -/
+theorem decidesInTime_iff (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
+    M.DecidesInTime L T ↔
+      ∀ x : List Bool,
+        M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length) :=
+  Iff.rfl
+
 end Turing.FinTM
 
 namespace Complexity
@@ -88,6 +98,14 @@ open Turing
 def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
   {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}
 
+/-- Membership `L ∈ DTIME T` is exactly a constant `c` and a finite machine `M`
+deciding `L` within `n ↦ c * T n`:
+`L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L (fun n => c * T n)`.
+[AB09, Definition 1.12] -/
+theorem mem_DTIME_iff {T : ℕ → ℕ} {L : Language Bool} :
+    L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n :=
+  Iff.rfl
+
 /-- `DTIME` is monotone in the time bound.
 
 **Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
diff --git a/TCSlib/Complexity/Randomized/Build/IterateFind.lean b/TCSlib/Complexity/Randomized/Build/IterateFind.lean
index b3c828402..27bf3615d 100644
--- a/TCSlib/Complexity/Randomized/Build/IterateFind.lean
+++ b/TCSlib/Complexity/Randomized/Build/IterateFind.lean
@@ -73,6 +73,9 @@ assembly through `Turing.FinTM.exists_loopFindTM`.
 
 ## Main results
 
+* `Complexity.IterateFind.computesFunInTime_find` — the finite machine with arbitrary
+  numerical fuel supplied in binary, a chosen initial state, and an explicit polynomial
+  per-round budget.
 * `Complexity.IterateFind.polyTimeComputable_find` — the loop-level form of the repetition
   lemma: the first accepted orbit point's payload along the guarded orbit of `⟨x, x⟩` is
   polynomial-time computable.
@@ -553,4 +556,246 @@ theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComp
   exact final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length)
     (hCP _) (hCR _)
 
+/-- A guarded search with arbitrary numerical fuel `R` and initial state `init` has a
+finite machine computing the first accepted payload (or `[]` on exhaustion) within
+`c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)` steps, for constants
+`c, A, D`. The step `g`, acceptance word `[acc s]`, payload `out s`, and initial state are
+polynomial-time computable; `|init x| ≤ P.eval |x|`. A fuel machine computes
+`Nat.bits (R |x|)` within `aF * (|x| + 1) ^ dF`. The displayed common per-round budget
+`T n = A * (2 * n + 2 + P.eval n + 5) ^ D` is polynomial; no polynomial bound on `R`
+is assumed. [AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4]
+
+**Proof sketch.** Reuse the invariant and guarded-step modules of
+`polyTimeComputable_find`, installing `⟨x, init x⟩` at startup. The size guard preserves
+the invariant under every step, including steps after the search terminates. Install the
+verdict and step modules, emit the payload, and compose their clean calls through the
+same five-module host. A common polynomial budget pays for startup, each round, and the
+given binary fuel machine. The result-bearing loop combinator then supplies the stated
+bound directly, without using the polynomial-fuel normal form `final_bound`. -/
+theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
+    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
+    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
+    {init : List Bool → List Bool} (hinit : PolyTimeComputable init)
+    (R : ℕ → ℕ) (P : PolyExpr)
+    (hbound : ∀ x : List Bool, (init x).length ≤ P.eval x.length)
+    (F : FinTM Bool) (aF dF : ℕ)
+    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length))
+      (fun n => aF * (n + 1) ^ dF)) :
+    ∃ (M : FinTM Bool) (c A D : ℕ),
+      M.ComputesFunInTime
+        (fun x => match (List.range (R x.length + 1)).find?
+            (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) with
+          | some i => out (pairSndD ((step g P x)^[i] (pairEncode x (init x))))
+          | none => [])
+        (fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)) := by
+  -- Build the four clean calls and their shared host.
+  obtain ⟨S, aS, dS, hS⟩ := ModuleHost.clean_install (polyTimeComputable_id.pairEncode hinit)
+  obtain ⟨V, aV, dV, hV⟩ := ModuleHost.clean_install (verdictWord_poly hacc)
+  obtain ⟨I, aI, dI, hI⟩ := ModuleHost.clean_install (stepWord_poly hg P)
+  obtain ⟨E, aE, dE, hE⟩ := ModuleHost.clean_emit (outWord_poly hout)
+  let M : Fin 5 → FinTM Bool := fun i => match i.val with
+    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
+  let K := S.k + V.k + I.k + E.k
+  have hk : ∀ i, (M i).k ≤ K + 1 := by
+    intro i; fin_cases i <;> simp [M, K, copyTM_k] <;> omega
+  let H := hostTM M K hk
+  let anchor : H.State := .inl 0
+  have hclean := ModuleHost.host_clean M (K + 1) hk (hostCtrl M K) (hostRet M)
+    (ModuleHost.entry M 0)
+  let D := dS + dV + dI + dE + dF + 1
+  let A := aS + aV + aI + aE + aF + 5
+  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
+  let T (n : ℕ) := A * pow n
+  have hpow (n : ℕ) : n + 1 ≤ pow n := by
+    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
+      (show 1 ≤ D by dsimp [D]; omega)
+    simp only [Nat.pow_one] at h
+    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
+  -- Startup copies the input and installs the chosen initial state.
+  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
+      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
+      H.tm.runFrom (H.tm.initCfg x) t =
+        Cfg.ofWords anchor (stateWord H.k (pairEncode x (init x))) := by
+    intro x
+    obtain ⟨hcg, hce⟩ := copy_clean x
+    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call M (K + 1) hk (hostCtrl M K) (hostRet M)
+      (ModuleHost.entry M 0) 0 (by simp [M, copyTM_k]) x [] x [] [] (0 : Fin 2)
+      (2 * x.length + 2) hcg (by simpa using hce)
+    have hi : H.tm.initCfg x = Cfg.ofWords (ModuleHost.entry M 0) (stateWord (K + 1) []) := by
+      refine Cfg.ext ?_ rfl ?_ rfl rfl
+      · exact congrArg some (ModuleHost.hostTM_tm_q₀ M (K + 1) hk (hostCtrl M K) (hostRet M)
+          (ModuleHost.entry M 0))
+      funext i z
+      simp [MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes,
+          Cfg.init_workTapePos, Cfg.init_output, Cfg.ofWords_def, stateWord_eq]
+    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 0) (stateWord (K + 1) []))
+      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
+    rw [hostRet_zero] at hcEnd
+    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := hclean 1
+      (fun x => pairEncode x (init x)) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
+      (by simpa [M] using hS) x x []
+    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 1) (stateWord (K + 1) x))
+      ts = Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x (init x))) at hsEnd
+    rw [hostRet_one] at hsEnd
+    have hsB := ModuleHost.request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
+      (by dsimp [D]; omega) (by omega)
+    have hp := hpow x.length
+    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
+    · dsimp only [T, A, pow]
+      simp only [Nat.add_mul]
+      dsimp only [pow] at hp
+      omega
+    · rw [hi]
+      exact ModuleHost.guard_add H.tm anchor _ _ _ ts (fun v hv => hcGuard v hv 0) hcEnd
+        (fun v hv => hsGuard v hv 0)
+    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
+      rfl
+  -- A positive round either emits its payload or advances the guarded state.
+  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
+      (∀ t', 0 < t' → t' < t →
+        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
+          ≠ some anchor) ∧
+      if acc (pairSndD w) then
+        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
+        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
+          out (pairSndD w)
+      else
+        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
+          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
+    intro x w hw
+    obtain ⟨s, rfl, hs⟩ := hw
+    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
+      rw [length_pairEncode]; omega
+    have hw'len : (verdictWord acc (pairEncode x s)).length =
+        (pairEncode x s).length + 4 := verdictWord_length acc _
+    have hpow' := hpow x.length
+    -- the dispatch, the verdict call, the branch
+    have hdisp := host_dispatch M K hk x (pairEncode x s)
+    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := hclean 2 (verdictWord acc)
+      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
+    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2) (stateWord (K + 1)
+      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
+        (verdictWord acc (pairEncode x s))) at hvEnd
+    rw [hostRet_two] at hvEnd
+    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
+      (by rw [verdictWord_head, pairSndD_pairEncode])
+    have hvB := ModuleHost.request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
+      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
+    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
+        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
+        Cfg.ofWords (ModuleHost.entry M (if acc s then 4 else 3))
+          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
+      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
+    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
+        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
+      refine ModuleHost.guard_add H.tm anchor _ _ tv 1 (fun v hv => hvGuard v hv 0) hvEnd ?_
+      intro v hv
+      have hv0 : v = 0 := by omega
+      subst hv0
+      simp [Cfg.ofWords_def, anchor]
+    by_cases hb : acc s = true
+    · -- accepting round: the payload call, then the halt
+      rw [if_pos hb] at hseg
+      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := hclean 4 id (outWord out)
+        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
+        (verdictWord acc (pairEncode x s)) []
+      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 4) (stateWord (K + 1)
+        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
+          (verdictWord acc (pairEncode x s))) with
+            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
+      rw [hostRet_four, List.nil_append, outWord_verdictWord] at heEnd
+      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
+      have heB := ModuleHost.request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
+        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
+      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
+          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
+          {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1)
+            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
+        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
+      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
+          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
+        refine ModuleHost.guard_add H.tm anchor _ {Cfg.ofWords (input := x)
+          (.inl 2 : ModuleHost.State (Fin 3) M)
+          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
+          (tv + 1 + te) 1 ?_ ?_ ?_
+        · exact ModuleHost.guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg
+            (fun v hv => heGuard v hv 0)
+        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
+        · intro v hv
+          have hv0 : v = 0 := by omega
+          subst hv0
+          simp [Cfg.ofWords_def, anchor]
+      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
+      · dsimp only [T, A, pow]
+        simp only [Nat.add_mul]
+        dsimp only [pow] at hpow'
+        omega
+      · intro v hv hvt
+        have hvform : v = (v - 1) + 1 := by omega
+        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
+          (pairEncode x s))) v).state ≠ some anchor
+        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
+        exact hallGuard (v - 1) (by omega)
+      · rw [pairSndD_pairEncode, if_pos hb]
+        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
+            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
+          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
+            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
+        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
+        exact ⟨rfl, rfl⟩
+    · -- advancing round: the step call returns to the anchor
+      rw [if_neg hb] at hseg
+      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := hclean 3 (stepWord g P)
+        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
+        (verdictWord acc (pairEncode x s)) []
+      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 3) (stateWord (K + 1)
+        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
+          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
+      rw [hostRet_three, stepWord_verdictWord] at hiEnd
+      have hiB := ModuleHost.request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
+        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
+      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
+          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
+          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
+        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
+      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
+          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
+        ModuleHost.guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg
+          (fun v hv => hiGuard v hv 0)
+      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
+      · dsimp only [T, A, pow]
+        simp only [Nat.add_mul]
+        dsimp only [pow] at hpow'
+        omega
+      · intro v hv hvt
+        have hvform : v = (v - 1) + 1 := by omega
+        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
+          (pairEncode x s))) v).state ≠ some anchor
+        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
+        exact hallGuard (v - 1) (by omega)
+      · rw [pairSndD_pairEncode, if_neg hb]
+        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
+            (pairEncode x s))) (tv + 1 + ti + 1) =
+          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
+        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
+  -- Pay for binary fuel in the same polynomial budget, then apply the host.
+  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T := by
+    apply (FinTM.computesFunInTime_iff _ _ _).2
+    intro x
+    apply ((FinTM.computesFunInTime_iff _ _ _).1 hF x).mono
+    have h := ModuleHost.request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
+      (by dsimp [D]; omega) (by omega)
+    have hp := hpow x.length
+    dsimp only [T, A, pow]
+    simp only [Nat.add_mul]
+    dsimp only [pow] at hp
+    omega
+  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
+    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x (init x))
+    R T hFuel (fun x => ⟨init x, rfl, hbound x⟩)
+    (fun x w h => inv_step g P x w h) hstart hround
+  refine ⟨L, c, A, D, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
+  have hx := (FinTM.computesFunInTime_iff _ _ _).mp hL x
+  simpa only [T, pow] using hx
+
 end Complexity.IterateFind
diff --git a/TCSlib/Complexity/Randomized/Classes.lean b/TCSlib/Complexity/Randomized/Classes.lean
index df6d49b14..cc04b0d27 100644
--- a/TCSlib/Complexity/Randomized/Classes.lean
+++ b/TCSlib/Complexity/Randomized/Classes.lean
@@ -292,6 +292,18 @@ def InBPP (L : Language Bool) : Prop :=
       (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
       (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)
 
+/-- Membership of `L` in `BPP` for the verifier model `E`, unfolded [AB09, Definition 7.3]:
+`InBPP E L ↔ ∃ (M : List Bool → List Bool → Bool) (a k : ℕ), E.Eff (boolVerifier M) ∧
+∀ x : List Bool, (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
+(x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)`. -/
+theorem inBPP_iff (L : Language Bool) :
+    InBPP E L ↔ ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
+      E.Eff (boolVerifier M) ∧
+      ∀ x : List Bool,
+        (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
+        (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false) :=
+  Iff.rfl
+
 /-- `L ∈ RP`: one-sided error — inputs in `L` are accepted with probability
 at least `2/3`, inputs outside `L` are *never* accepted.  [AB09, Def 7.6] -/
 def InRP (L : Language Bool) : Prop :=
diff --git a/TCSlib/Complexity/Randomized/SeedMajority.lean b/TCSlib/Complexity/Randomized/SeedMajority.lean
index bf1da1009..ca7471f0a 100644
--- a/TCSlib/Complexity/Randomized/SeedMajority.lean
+++ b/TCSlib/Complexity/Randomized/SeedMajority.lean
@@ -7,13 +7,17 @@ import TCSlib.Complexity.ClassP.P
 import TCSlib.Complexity.ClassNP.PolyTime
 import TCSlib.Complexity.TuringMachine.Encoding
 import TCSlib.Complexity.Randomized.Classes
+import TCSlib.Complexity.Randomized.SeedMajority.Words
+import TCSlib.Complexity.Randomized.SeedMajority.State
+import TCSlib.Complexity.Randomized.SeedMajority.Enumeration
+import TCSlib.Complexity.Randomized.SeedMajority.Envelope
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Deterministic majority over all seeds (statement phase)
+# Deterministic majority over all seeds
 
 The counting enumeration host: a deterministic machine that, on input `x`, runs a
 polynomial-time test on `⟨x, u⟩` for **every** seed `u ∈ {0,1}^{w(|x|)}`, counts the accepting
@@ -56,14 +60,21 @@ Theorem 180.1 (`TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp`).
   `Turing.FinTM.DecidesInTime`, `Turing.FinTM.DecidesInTimeVia` and `DTIME` by their
   definitions (Rule 10).
 
+## Contents
+
+* `Complexity.Randomized.SeedMajority.Words`: binary seed words and prefix counts.
+* `Complexity.Randomized.SeedMajority.State`: the FP counting round and terminal tests.
+* `Complexity.Randomized.SeedMajority.Enumeration`: the finite binary-fuel machine.
+* `Complexity.Randomized.SeedMajority.Envelope`: the all-times work-head bound.
+
 ## Main results
 
 * `Complexity.exists_seedMajorityTM` — the host's machine-level contract: correctness, time and
-  head envelope of one machine (stated; a `sorry` under the route below, for the `derand` fill).
+  head envelope of one machine, proved through the generic binary-fuel harvest.
   [AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4 of the proof]
 * `Complexity.seedMajority_mem_DTIME` — the decision-class corollary
-  `∃ e, {x | 2^{w(|x|)} < 2 · count} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)` (stated; a `sorry`
-  until the `derand` fill adds `mem_DTIME_iff`, then read off the contract).
+  `∃ e, {x | 2^{w(|x|)} < 2 · count} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)`, proved from
+  the host contract through `mem_DTIME_iff`.
 * `Randomized.half_lt_randProb_iff` — majority as a probability:
   `1/2 < randProb m A ↔ 2^m < 2 · #{r | A r}` (proved).
 
@@ -175,7 +186,11 @@ open Classical in
 `Fin (w |x|) → Bool`, the numerator of `Randomized.randProb` (`Randomized.half_lt_randProb_iff`).
 The head envelope is not in the source; it is the host clause of `policy.md` §1.
 
-**Proof sketch** (the route of the module docstring; the `derand` fill).
+**Status.** Proved through `SeedMajority.exists_countingTM` and
+`SeedMajority.envelope_of_computesInTime`, using only the published decision and
+computation readers.
+
+**Proof sketch** (the route of the module docstring; implemented in the helpers).
 1. Run the state loop `⟨x, ⟨i, a⟩⟩ ↦ ⟨x, ⟨i + 1, a + [⟨x, word_w(i)⟩ ∈ V]⟩⟩` from
    `⟨x, ⟨0, 0⟩⟩`, stopping at `i = 2^{w(|x|)}` with the payload `[2^w < 2a]`; each piece is a
    polynomial-time word function of the state.
@@ -200,7 +215,20 @@ theorem exists_seedMajorityTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → 
         ∀ (x : List Bool) (v : ℕ) (j : Fin M.k),
           |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤
             ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
-  sorry
+  obtain ⟨M, c, e, hM⟩ := SeedMajority.exists_countingTM hV w hw
+  refine ⟨M, c, e, ?_, ?_⟩
+  · apply (FinTM.decidesInTime_iff _ _ _).mpr
+    intro x
+    have hx := (FinTM.computesFunInTime_iff _ _ _).mp hM x
+    rw [MultiTapeTM.indicator_def]
+    by_cases h : 2 ^ w x.length <
+        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
+          pairEncode x (List.ofFn u) ∈ V).card
+    · simpa only [Set.mem_setOf_eq, if_pos h, decide_eq_true h] using hx
+    · simpa only [Set.mem_setOf_eq, if_neg h, decide_eq_false h] using hx
+  · intro x v j
+    exact SeedMajority.envelope_of_computesInTime
+      ((FinTM.computesFunInTime_iff _ _ _).mp hM x) v j
 
 open Classical in
 /-- **Deterministic majority over all seeds: the decision class** [AB09, §7.1, p. 126];
@@ -211,11 +239,9 @@ puts the strict-majority language in `DTIME (n ↦ 2^{w(n)} · (n+1)^e)`:
 ∈ DTIME (fun n => 2^{w(n)} · (n+1)^e)`. Ties (`2 · count = 2^w`) reject. It is the corollary
 of the machine contract `exists_seedMajorityTM` that the consumers of the class read.
 
-**Status.** Admitted (a `sorry`). It follows from `exists_seedMajorityTM` through the reader
-`Complexity.mem_DTIME_iff`, which the `derand` fill adds beside `DTIME` (`ClassP/DTIME.lean`)
-under its pre-approval (Seyoon, 2026-11-15). The `derand` fill proves both the contract and
-this corollary. Until the reader exists, a proof would read `Turing.FinTM.DecidesInTime`,
-`Turing.FinTM.DecidesInTimeVia` and `DTIME` by their definitions, which Rule 10 forbids.
+**Status.** Proved from `exists_seedMajorityTM`. The proof reads the machine contract
+through `Complexity.mem_DTIME_iff`, added beside `DTIME` under the pre-approval of
+2026-11-15. It uses no definitional reading of either `DTIME` or `DecidesInTime`.
 
 **Proof sketch.** Take the machine `M` and constants `c, e` of `exists_seedMajorityTM` (the
 envelope is not needed here). `M` decides the language within
@@ -229,6 +255,7 @@ theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → 
           2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
             pairEncode x (List.ofFn u) ∈ V).card} ∈
         DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
-  sorry
+  obtain ⟨M, c, e, hM, _⟩ := exists_seedMajorityTM hV w hw
+  exact ⟨e, mem_DTIME_iff.mpr ⟨c, M, hM⟩⟩
 
 end Complexity
diff --git a/TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean b/TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean
new file mode 100644
index 000000000..ef3da4e3a
--- /dev/null
+++ b/TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean
@@ -0,0 +1,127 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Complexity.Randomized.SeedMajority.State
+import TCSlib.Complexity.Randomized.Build.IterateFind
+import TCSlib.Complexity.Randomized.Build.StateLoop
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The finite seed-enumeration machine
+
+Instantiate the generic binary-fuel harvest with a retained-input counting
+state. The size guard stays in the total step; it never fires on a genuine
+prefix of at most `2^w` rounds. The terminal rank is included in the search.
+
+## Main results
+
+* `Complexity.SeedMajority.exists_countingTM`: a finite machine computes
+  the strict seed-majority bit in time `c * 2^w(n) * (n+1)^e`.
+
+## References
+
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009, §7.1, p. 126.
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1, step 4.
+-/
+
+namespace Complexity.SeedMajority
+
+open Turing
+
+open Classical in
+/-- A finite machine computes the seed-majority bit with the claimed time:
+`M.ComputesFunInTime (x ↦ [decide (2^(w |x|) < 2 * count_all)])`
+`(n ↦ c * (2^(w n) * (n+1)^e))` for some `M,c,e`.
+[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4]
+
+**Proof sketch.** Bound the unary width by a polynomial. Then the retained
+input and the two counters, including their terminal values, fit in a
+fixed polynomial state bound. Induct along the guarded orbit: its rank is
+`i`, and its count is `count V x (w |x|) i`. The guard never fires up to the
+fuel rank. The terminal test is false before that rank and true there,
+so the inclusive first-hit search returns it. Apply the generic-fuel
+harvest with the shared binary power-of-two evaluator. The rank bijection
+identifies the final prefix count with the count over all seed tuples.
+Finally bound the per-round polynomial with `PolyExpr.eval_le` and use
+`2^w+2 ≤ 3*2^w` to obtain the required time normal form. -/
+theorem exists_countingTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
+    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
+    ∃ (M : FinTM Bool) (c e : ℕ), M.ComputesFunInTime
+      (fun x => [decide (2 ^ w x.length <
+        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
+          pairEncode x (List.ofFn u) ∈ V).card)])
+      (fun n => c * (2 ^ w n * (n + 1) ^ e)) := by
+  obtain ⟨C, c, hwidth⟩ := hw.output_length_le
+  have hwlen (x : List Bool) : w x.length ≤ C * (x.length + 1) ^ c := by
+    simpa only [List.length_replicate] using hwidth x
+  let P : PolyExpr := .add (.add (.mul (.const 2) .var)
+    (.mul (.const (3 * C)) (.pow (.add .var (.const 1)) c))) (.const 7)
+  have hstate (x : List Bool) (i : ℕ) (hi : i ≤ 2 ^ w x.length) :
+      (state x i (count V x (w x.length) i)).length ≤ P.eval x.length := by
+    have hs := length_state_le x (w x.length) i (count V x (w x.length) i) hi
+      (count_le V x (w x.length) i)
+    have hwx := hwlen x
+    simp only [P, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+      PolyExpr.eval_pow, PolyExpr.eval_var]
+    nlinarith
+  have hinit (x : List Bool) : (state x 0 0).length ≤ P.eval x.length := by
+    simpa only [count_zero] using hstate x 0 (Nat.zero_le _)
+  have horbit (x : List Bool) (i : ℕ) (hi : i ≤ 2 ^ w x.length) :
+      (IterateFind.step (advance V w) P x)^[i] (pairEncode x (state x 0 0)) =
+        pairEncode x (state x i (count V x (w x.length) i)) := by
+    induction i with
+    | zero => simp only [Function.iterate_zero_apply, count_zero]
+    | succ i ih =>
+        rw [Function.iterate_succ_apply', ih (by omega), IterateFind.step_eq,
+          pairSndD_pairEncode, advance_state, ← count_succ]
+        rw [if_pos (hstate x (i + 1) hi)]
+  have hfind (x : List Bool) :
+      (List.range (2 ^ w x.length + 1)).find?
+        (fun i => finished w (pairSndD
+          ((IterateFind.step (advance V w) P x)^[i] (pairEncode x (state x 0 0))))) =
+        some (2 ^ w x.length) := by
+    apply StateLoop.find?_range_eq_some le_rfl
+    · intro i hi
+      rw [horbit x i hi.le, pairSndD_pairEncode, finished_state]
+      exact decide_eq_false (by omega)
+    · rw [horbit x (2 ^ w x.length) le_rfl, pairSndD_pairEncode, finished_state]
+      exact decide_eq_true rfl
+  obtain ⟨F, aF, dF, hF⟩ :=
+    (polyTimeComputable_iff _).mp (polyTimeComputable_seedFuel hw)
+  obtain ⟨M, c₀, A, D, hM⟩ := IterateFind.computesFunInTime_find
+    (polyTimeComputable_advance hV hw) (polyTimeComputable_finished hw)
+    (polyTimeComputable_payload hw) polyTimeComputable_initial (fun n => 2 ^ w n)
+    P hinit F aF dF hF
+  have hcomputed (x : List Bool) : M.ComputesInTime x
+      [decide (2 ^ w x.length <
+        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
+          pairEncode x (List.ofFn u) ∈ V).card)]
+      (c₀ * (A * (2 * x.length + 2 + P.eval x.length + 5) ^ D + 1) *
+        (2 ^ w x.length + 2)) := by
+    have hx := (FinTM.computesFunInTime_iff _ _ _).mp hM x
+    simpa only [hfind, horbit x (2 ^ w x.length) le_rfl, pairSndD_pairEncode,
+      payload_state, count_all] using hx
+  let Q : PolyExpr := .add (.mul (.const A) (.pow
+    (.add (.add (.add (.mul (.const 2) .var) (.const 2)) P) (.const 5)) D)) (.const 1)
+  obtain ⟨B, b, hB⟩ := Q.eval_le
+  have hbudget (n : ℕ) : A * (2 * n + 2 + P.eval n + 5) ^ D + 1 ≤ B * (n + 1) ^ b := by
+    simpa only [Q, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+      PolyExpr.eval_pow, PolyExpr.eval_var] using hB n
+  refine ⟨M, c₀ * B * 3, b, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
+  apply (hcomputed x).mono
+  calc
+    c₀ * (A * (2 * x.length + 2 + P.eval x.length + 5) ^ D + 1) *
+        (2 ^ w x.length + 2) ≤
+        c₀ * (B * (x.length + 1) ^ b) * (3 * 2 ^ w x.length) :=
+      Nat.mul_le_mul (Nat.mul_le_mul_left c₀ (hbudget x.length))
+        (by have hpos := Nat.two_pow_pos (w x.length); omega)
+    _ = c₀ * B * 3 * (2 ^ w x.length * (x.length + 1) ^ b) := by ring
+
+end Complexity.SeedMajority
diff --git a/TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean b/TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean
new file mode 100644
index 000000000..e8ea8b6ad
--- /dev/null
+++ b/TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean
@@ -0,0 +1,63 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Complexity.TuringMachine.Finite
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# A timed computation bounds every work head
+
+The coarse head envelope follows from a completed computation: before its
+time bound every head is within that many cells of its initial position;
+afterward the halted run is constant. This is the native-initial-configuration
+version of the clean-module envelope, stated without a clean seam hypothesis.
+
+## Main results
+
+* `Complexity.SeedMajority.envelope_of_computesInTime`: the all-times head bound.
+
+## References
+
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009, §1.2, multitape machines.
+-/
+
+namespace Complexity.SeedMajority
+
+open Turing
+
+/-- A finite machine computing `y` on `x` by time `t` keeps each work head
+within `t` cells at every time `v`:
+`|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ)`.
+[AB09, §1.2]
+
+**Proof sketch.** The published interval bound puts the head within `u`
+cells of its start after `u ≤ t` steps, and `Cfg.init_workTapePos` makes the
+start zero. For `v > t`, the computation reader says the configuration at
+`t` is halted; split the run there and use `runFrom_of_halt`. -/
+theorem envelope_of_computesInTime {M : FinTM Bool} {x y : List Bool} {t : ℕ}
+    (h : M.ComputesInTime x y t) (v : ℕ) (j : Fin M.k) :
+    |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ) := by
+  have bound (u : ℕ) (hu : u ≤ t) :
+      |(M.tm.runFrom (M.tm.initCfg x) u).workTapePos j| ≤ (t : ℤ) := by
+    have hp := M.tm.workTapePos_runFrom_mem_Icc (M.tm.initCfg x) u j
+    rw [Finset.mem_Icc] at hp
+    simp only [MultiTapeTM.initCfg_eq, Cfg.init_workTapePos, zero_sub, zero_add] at hp
+    have hut : (u : ℤ) ≤ t := by exact_mod_cast hu
+    rw [MultiTapeTM.initCfg_eq]
+    exact abs_le.mpr ⟨by omega, by omega⟩
+  by_cases hv : v ≤ t
+  · exact bound v hv
+  · have hh := ((FinTM.computesInTime_iff M x y t).mp h).1
+    have heq : M.tm.runFrom (M.tm.initCfg x) v = M.tm.runFrom (M.tm.initCfg x) t := by
+      rw [show v = t + (v - t) by omega, MultiTapeTM.runFrom_add,
+        MultiTapeTM.runFrom_of_halt _ hh]
+    rw [heq]
+    exact bound t le_rfl
+
+end Complexity.SeedMajority
diff --git a/TCSlib/Complexity/Randomized/SeedMajority/State.lean b/TCSlib/Complexity/Randomized/SeedMajority/State.lean
new file mode 100644
index 000000000..c5d7331de
--- /dev/null
+++ b/TCSlib/Complexity/Randomized/SeedMajority/State.lean
@@ -0,0 +1,233 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Complexity.Randomized.SeedMajority.Words
+import TCSlib.Complexity.ClassNP.PClosure
+import TCSlib.Complexity.ClassNP.PolyTimePrefix
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The counting state of the seed-majority host
+
+Each state retains the original input and two binary counters. The total
+step reads one padded seed word, increments the rank, and increments the
+acceptance count by the test bit. The outer iteration keeps its length guard,
+so no fixed state bound is claimed after termination.
+
+## Main definitions
+
+* `Complexity.SeedMajority.seedFor`: the seed read from a raw counting state.
+* `Complexity.SeedMajority.advance`: one counting round.
+* `Complexity.SeedMajority.finished`: the terminal-rank test.
+* `Complexity.SeedMajority.payload`: the strict-majority bit.
+
+## Main results
+
+* The four maps are polynomial-time when the test is in `P` and the width
+  has an FP unary word.
+* `Complexity.SeedMajority.length_state_le`: the counters fit in `w+1` bits
+  up to and including the terminal rank.
+
+## References
+
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009, §7.1, p. 126.
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1, step 4.
+-/
+
+namespace Complexity.SeedMajority
+
+open Turing
+
+/-- The seed extracted from `z` is the first `w |fst z|` letters of its raw
+rank word followed by the binary power-of-two padding. On counting states,
+`seedFor w (state x i a) = word (w |x|) i`. [AB09, §7.1, p. 126] -/
+def seedFor (w : ℕ → ℕ) (z : List Bool) : List Bool :=
+  (pairFstD (pairSndD z) ++ Nat.bits (2 ^ w (pairFstD z).length)).take
+    (w (pairFstD z).length)
+
+/-- The raw-state seed reader satisfies
+`seedFor w z = (fst(snd z) ++ bits(2^(w |fst z|))).take (w |fst z|)`. -/
+theorem seedFor_eq (w : ℕ → ℕ) (z : List Bool) :
+    seedFor w z =
+      (pairFstD (pairSndD z) ++ Nat.bits (2 ^ w (pairFstD z).length)).take
+        (w (pairFstD z).length) := rfl
+
+/-- On a counting state the extracted seed is its width-`w |x|` rank word:
+`seedFor w (state x i a) = word (w |x|) i`. -/
+theorem seedFor_state (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
+    seedFor w (state x i a) = word (w x.length) i := by
+  simp only [seedFor_eq, state_eq, pairFstD_pairEncode, pairSndD_pairEncode, word_eq]
+
+/-- Binary exponential fuel is FP when the width has an FP unary word:
+`x ↦ bits(2^(w |x|))` is FP. This reuses the shared power-of-two evaluator.
+[PS10, Theorem 180.1, step 4] -/
+theorem polyTimeComputable_seedFuel {w : ℕ → ℕ}
+    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
+    PolyTimeComputable fun x => Nat.bits (2 ^ w x.length) := by
+  convert BinArith.polyTimeComputable_powerOfTwo.comp hw using 1
+  funext x
+  simp only [Function.comp_apply, List.length_replicate]
+
+/-- Reading the rank seed is FP:
+`PolyTimeComputable (seedFor w)` when the unary width is FP.
+
+**Proof sketch.** Compose the unary width and binary fuel evaluators with
+the first projection. Append the raw rank to the padding word and apply
+the existing prefix-by-length machine to the pair of unary width and data. -/
+theorem polyTimeComputable_seedFor {w : ℕ → ℕ}
+    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
+    PolyTimeComputable (seedFor w) := by
+  have hwidth := hw.comp polyTimeComputable_pairFstD
+  have hpad := (polyTimeComputable_seedFuel hw).comp polyTimeComputable_pairFstD
+  have hrank := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
+  have hdata := hrank.append hpad
+  convert polyTimeComputable_takePrefixByLength.comp (hwidth.pairEncode hdata) using 1
+  funext z
+  simp only [Function.comp_apply, seedFor_eq, PrefixByLength.take_def,
+    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
+
+/-- One total counting round keeps the input and increments the binary counters:
+`advance V w (state x i a) = state x (i+1) (a + [⟨x,word (w |x|) i⟩ ∈ V])`.
+The step is total; the outer host retains its size guard after termination.
+[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
+noncomputable def advance (V : Language Bool) (w : ℕ → ℕ) (z : List Bool) : List Bool :=
+  pairEncode (pairFstD z)
+    (pairEncode (BinArith.add (pairEncode (pairFstD (pairSndD z)) (Nat.bits 1)))
+      (BinArith.add (pairEncode (pairSndD (pairSndD z))
+        (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (seedFor w z))
+          then Nat.bits 1 else Nat.bits 0))))
+
+/-- The counting-round reader exposes the binary additions and indicator:
+`advance V w z = ⟨fst z, ⟨add(⟨fst(snd z),bits 1⟩),
+add(⟨snd(snd z), if indicator V ⟨fst z,seedFor w z⟩ then bits 1 else bits 0⟩)⟩⟩`. -/
+theorem advance_eq (V : Language Bool) (w : ℕ → ℕ) (z : List Bool) :
+    advance V w z = pairEncode (pairFstD z)
+      (pairEncode (BinArith.add (pairEncode (pairFstD (pairSndD z)) (Nat.bits 1)))
+        (BinArith.add (pairEncode (pairSndD (pairSndD z))
+          (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (seedFor w z))
+            then Nat.bits 1 else Nat.bits 0)))) := rfl
+
+/-- Each counting round is FP for `V ∈ P` and an FP unary width:
+`PolyTimeComputable (advance V w)`.
+
+**Proof sketch.** Read the input and counters with total pair projections.
+The seed is `polyTimeComputable_seedFor`; apply the `P` indicator to its
+pair with the input. Its Boolean result selects the constant increment
+zero or one. Pairing and the published binary adder assemble the next state.
+This proof establishes FP for every raw word, including malformed states. -/
+theorem polyTimeComputable_advance {V : Language Bool} (hV : V ∈ P) {w : ℕ → ℕ}
+    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
+    PolyTimeComputable (advance V w) := by
+  have hrank := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
+  have hcount := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
+  have htest := (mem_P_iff_polyTimeComputable.mp hV).comp
+    (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_seedFor hw))
+  have hbit := polyTimeComputable_ite htest
+    (polyTimeComputable_const (Nat.bits 1)) (polyTimeComputable_const (Nat.bits 0))
+  have hi := BinArith.polyTimeComputable_add.comp
+    (hrank.pairEncode (polyTimeComputable_const (Nat.bits 1)))
+  have ha := BinArith.polyTimeComputable_add.comp (hcount.pairEncode hbit)
+  convert polyTimeComputable_pairFstD.pairEncode (hi.pairEncode ha) using 1
+
+open Classical in
+/-- On a counting state one round has its intended arithmetic meaning:
+`advance V w (state x i a) = state x (i+1) (a + [⟨x,word(w |x|) i⟩ ∈ V])`.
+[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4] -/
+theorem advance_state (V : Language Bool) (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
+    advance V w (state x i a) = state x (i + 1)
+      (a + if pairEncode x (word (w x.length) i) ∈ V then 1 else 0) := by
+  rw [advance_eq, seedFor_state]
+  simp only [state_eq, pairFstD_pairEncode, pairSndD_pairEncode, BinArith.add_pairEncode,
+    MultiTapeTM.indicator_def]
+  by_cases h : pairEncode x (word (w x.length) i) ∈ V
+  · simp only [if_pos h, ↓reduceIte, BinArith.add_pairEncode]
+  · simp only [if_neg h, Bool.false_eq_true, ↓reduceIte, BinArith.add_pairEncode, Nat.add_zero]
+
+/-- The terminal test compares the rank with its binary fuel:
+`finished w z = beq ⟨fst(snd z), bits(2^(w |fst z|))⟩`.
+[PS10, Theorem 180.1, step 4] -/
+def finished (w : ℕ → ℕ) (z : List Bool) : Bool :=
+  BinArith.beq (pairEncode (pairFstD (pairSndD z)) (Nat.bits (2 ^ w (pairFstD z).length)))
+
+/-- The terminal test satisfies
+`finished w z = beq ⟨fst(snd z),bits(2^(w |fst z|))⟩`. -/
+theorem finished_eq (w : ℕ → ℕ) (z : List Bool) :
+    finished w z = BinArith.beq
+      (pairEncode (pairFstD (pairSndD z)) (Nat.bits (2 ^ w (pairFstD z).length))) := rfl
+
+/-- The terminal test is FP:
+`z ↦ [finished w z]` is FP when the unary width is FP. -/
+theorem polyTimeComputable_finished {w : ℕ → ℕ}
+    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
+    PolyTimeComputable fun z => [finished w z] := by
+  have hrank := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
+  have hpower := (polyTimeComputable_seedFuel hw).comp polyTimeComputable_pairFstD
+  convert BinArith.polyTimeComputable_beq.comp (hrank.pairEncode hpower) using 1
+
+/-- A counting state is terminal exactly at the fuel rank:
+`finished w (state x i a) = decide (i = 2^(w |x|))`. -/
+theorem finished_state (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
+    finished w (state x i a) = decide (i = 2 ^ w x.length) := by
+  simp only [finished_eq, state_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    BinArith.beq_pairEncode]
+
+/-- The output bit tests whether the doubled count exceeds the fuel:
+`payload w z = [lt ⟨bits(2^(w |fst z|)),add ⟨snd(snd z),snd(snd z)⟩⟩]`.
+[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4] -/
+def payload (w : ℕ → ℕ) (z : List Bool) : List Bool :=
+  [BinArith.lt (pairEncode (Nat.bits (2 ^ w (pairFstD z).length))
+    (BinArith.add (pairEncode (pairSndD (pairSndD z)) (pairSndD (pairSndD z)))))]
+
+/-- The output reader satisfies
+`payload w z = [lt ⟨bits(2^(w |fst z|)),add ⟨snd(snd z),snd(snd z)⟩⟩]`. -/
+theorem payload_eq (w : ℕ → ℕ) (z : List Bool) :
+    payload w z = [BinArith.lt (pairEncode (Nat.bits (2 ^ w (pairFstD z).length))
+      (BinArith.add (pairEncode (pairSndD (pairSndD z)) (pairSndD (pairSndD z)))))] := rfl
+
+/-- The payload is FP: `PolyTimeComputable (payload w)` for an FP unary width.
+It composes binary doubling by addition with the shared strict comparator. -/
+theorem polyTimeComputable_payload {w : ℕ → ℕ}
+    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
+    PolyTimeComputable (payload w) := by
+  have hcount := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
+  have hdouble := BinArith.polyTimeComputable_add.comp (hcount.pairEncode hcount)
+  have hpower := (polyTimeComputable_seedFuel hw).comp polyTimeComputable_pairFstD
+  convert BinArith.polyTimeComputable_lt.comp (hpower.pairEncode hdouble) using 1
+
+/-- On a counting state, the payload is the strict majority test:
+`payload w (state x i a) = [decide (2^(w |x|) < 2*a)]`.
+Equality of the two sides of the comparison rejects. -/
+theorem payload_state (w : ℕ → ℕ) (x : List Bool) (i a : ℕ) :
+    payload w (state x i a) = [decide (2 ^ w x.length < 2 * a)] := by
+  simp only [payload_eq, state_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    BinArith.add_pairEncode, BinArith.lt_pairEncode, two_mul]
+
+/-- The initial state `x ↦ state x 0 0` is FP, by pairing with two constant words. -/
+theorem polyTimeComputable_initial : PolyTimeComputable fun x => state x 0 0 := by
+  simpa only [state_eq] using polyTimeComputable_id.pairEncode
+    ((polyTimeComputable_const (Nat.bits 0)).pairEncode
+      (polyTimeComputable_const (Nat.bits 0)))
+
+/-- Through the terminal rank, the state has linear width in the input and
+seed length: `|state x i a| ≤ 2|x|+3m+7` if `a ≤ i ≤ 2^m`.
+[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4] -/
+theorem length_state_le (x : List Bool) (m i a : ℕ) (hi : i ≤ 2 ^ m) (ha : a ≤ i) :
+    (state x i a).length ≤ 2 * x.length + 3 * m + 7 := by
+  have hlen (j : ℕ) (hj : j ≤ 2 ^ m) : (Nat.bits j).length ≤ m + 1 := by
+    apply LogProg.length_bits_le
+    have hp : 0 < 2 ^ m := Nat.two_pow_pos m
+    rw [pow_succ]
+    omega
+  have hi' := hlen i hi
+  have ha' := hlen a (ha.trans hi)
+  rw [state_eq, length_pairEncode, length_pairEncode]
+  omega
+
+end Complexity.SeedMajority
diff --git a/TCSlib/Complexity/Randomized/SeedMajority/Words.lean b/TCSlib/Complexity/Randomized/SeedMajority/Words.lean
new file mode 100644
index 000000000..db8b7b7c9
--- /dev/null
+++ b/TCSlib/Complexity/Randomized/SeedMajority/Words.lean
@@ -0,0 +1,172 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Complexity.Randomized.RandomBits
+import TCSlib.Complexity.SpaceComplexity.Codec.Word
+import TCSlib.Complexity.ClassP.BinaryArith.Unary
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Binary seed words for the majority host
+
+The rank encoding and finite prefix count used by the counting enumeration host H17.
+The existing `Randomized.bitsEquiv` identifies ranks with fixed-width Boolean tuples;
+the configuration codec's binary normalization lemma identifies its inverse with the
+word computed by padding and prefix truncation.
+
+## Main definitions
+
+* `Complexity.SeedMajority.word`: the width-`m` low bits of a natural rank.
+
+## Main results
+
+* `Complexity.SeedMajority.length_word`: every encoded seed has exactly its width.
+
+## References
+
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009, §7.1, p. 126.
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1.
+-/
+
+namespace Complexity.SeedMajority
+
+open Turing
+
+/-- The width-`m` seed word for rank `i` is the first `m` bits of `Nat.bits i`
+followed by the binary word for `2 ^ m`, whose first `m` letters are zero:
+`word m i = (Nat.bits i ++ Nat.bits (2 ^ m)).take m`.
+[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
+def word (m i : ℕ) : List Bool := (Nat.bits i ++ Nat.bits (2 ^ m)).take m
+
+/-- The rank encoder satisfies
+`word m i = (Nat.bits i ++ Nat.bits (2 ^ m)).take m`. -/
+theorem word_eq (m i : ℕ) :
+    word m i = (Nat.bits i ++ Nat.bits (2 ^ m)).take m := rfl
+
+/-- The rank encoder has its declared width: `(word m i).length = m`. -/
+theorem length_word (m i : ℕ) : (word m i).length = m := by
+  rw [word_eq, bits_two_pow_eq_replicate, List.length_take, List.length_append,
+    List.length_append, List.length_replicate, List.length_singleton]
+  exact Nat.min_eq_left (by omega)
+
+/-- For `i < 2 ^ m`, `word m i` is the tuple of the existing rank bijection:
+`word m i = List.ofFn ((Randomized.bitsEquiv m).symm ⟨i, hi⟩)`.
+
+**Proof sketch.** Decode the inverse tuple with `bitsEquiv_apply`. Its value is `i`
+and its length is `m`. The codec's normalization theorem therefore writes it as
+`Nat.bits i` padded by exactly `m - |Nat.bits i|` zeros. Taking `m` letters of
+`Nat.bits i` followed by `m` zeros gives this same word, since `i < 2 ^ m` bounds
+the normalized binary length by `m`. -/
+theorem word_eq_ofFn (m i : ℕ) (hi : i < 2 ^ m) :
+    word m i = List.ofFn ((Randomized.bitsEquiv m).symm ⟨i, hi⟩) := by
+  let u := (Randomized.bitsEquiv m).symm ⟨i, hi⟩
+  have hv : LogProg.bitsVal (List.ofFn u) = i := by
+    rw [← Randomized.bitsEquiv_apply]
+    exact congrArg Fin.val ((Randomized.bitsEquiv m).apply_symm_apply ⟨i, hi⟩)
+  have hnorm := Codec.eq_bits_append_replicate (List.ofFn u)
+  rw [hv, List.length_ofFn] at hnorm
+  have hlen := LogProg.length_bits_le hi
+  calc
+    word m i = Nat.bits i ++ List.replicate (m - (Nat.bits i).length) false := by
+      rw [word_eq, List.take_append, List.take_of_length_le hlen,
+        bits_two_pow_eq_replicate,
+        List.take_append_of_le_length (by simp),
+        List.take_replicate,
+        Nat.min_eq_left (Nat.sub_le m _)]
+    _ = List.ofFn u := hnorm.symm
+
+open Classical in
+/-- The prefix acceptance count is
+`count V x m i = #{j ∈ Finset.range i | pairEncode x (word m j) ∈ V}`.
+[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
+noncomputable def count (V : Language Bool) (x : List Bool) (m i : ℕ) : ℕ :=
+  (Finset.range i |>.filter fun j => pairEncode x (word m j) ∈ V).card
+
+open Classical in
+/-- The prefix count satisfies
+`count V x m i = #{j ∈ Finset.range i | pairEncode x (word m j) ∈ V}`. -/
+theorem count_eq (V : Language Bool) (x : List Bool) (m i : ℕ) :
+    count V x m i = (Finset.range i |>.filter fun j => pairEncode x (word m j) ∈ V).card :=
+  rfl
+
+/-- The empty prefix has no accepted ranks: `count V x m 0 = 0`. -/
+theorem count_zero (V : Language Bool) (x : List Bool) (m : ℕ) : count V x m 0 = 0 := by
+  classical
+  rw [count_eq]
+  simp
+
+/-- At most `i` ranks are accepted in the first `i` tests: `count V x m i ≤ i`. -/
+theorem count_le (V : Language Bool) (x : List Bool) (m i : ℕ) : count V x m i ≤ i := by
+  classical
+  rw [count_eq]
+  calc
+    _ ≤ (Finset.range i).card := Finset.card_le_card (Finset.filter_subset _ _)
+    _ = i := Finset.card_range i
+
+open Classical in
+/-- One more seed increases the prefix count by its acceptance bit:
+`count V x m (i + 1) = count V x m i + if pairEncode x (word m i) ∈ V then 1 else 0`.
+[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
+theorem count_succ (V : Language Bool) (x : List Bool) (m i : ℕ) :
+    count V x m (i + 1) =
+      count V x m i + if pairEncode x (word m i) ∈ V then 1 else 0 := by
+  rw [count_eq, count_eq, Finset.range_add_one, Finset.filter_insert]
+  by_cases h : pairEncode x (word m i) ∈ V
+  · have hnot : i ∉ (Finset.range i).filter (fun j => pairEncode x (word m j) ∈ V) := by
+      intro hi
+      exact (Nat.lt_irrefl i) (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
+    rw [if_pos h, if_pos h, Finset.card_insert_of_notMem hnot]
+  · rw [if_neg h, if_neg h, Nat.add_zero]
+
+open Classical in
+/-- Counting every rank is counting every width-`m` Boolean tuple:
+`count V x m (2 ^ m) = #{u : Fin m → Bool | pairEncode x (List.ofFn u) ∈ V}`.
+[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4]
+
+**Proof sketch.** Map an accepted rank to the inverse of `Randomized.bitsEquiv`.
+`word_eq_ofFn` preserves its test result. Injectivity follows by applying that
+equivalence, and every accepted tuple has its rank as a preimage. -/
+theorem count_all (V : Language Bool) (x : List Bool) (m : ℕ) :
+    count V x m (2 ^ m) =
+      (Finset.univ.filter fun u : Fin m → Bool => pairEncode x (List.ofFn u) ∈ V).card := by
+  rw [count_eq]
+  refine Finset.card_bij (fun i hi => (Randomized.bitsEquiv m).symm
+    ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩) ?_ ?_ ?_
+  · intro i hi
+    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
+    rw [← word_eq_ofFn m i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)]
+    exact (Finset.mem_filter.mp hi).2
+  · intro i hi j hj hij
+    have := congrArg (fun u => ((Randomized.bitsEquiv m) u).val) hij
+    simpa only [Equiv.apply_symm_apply] using this
+  · intro u hu
+    let i := ((Randomized.bitsEquiv m) u).val
+    have hi : i < 2 ^ m := ((Randomized.bitsEquiv m) u).isLt
+    have hiFin : (⟨i, hi⟩ : Fin (2 ^ m)) = (Randomized.bitsEquiv m) u := by
+      apply Fin.ext
+      rfl
+    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩, ?_⟩
+    · rw [word_eq_ofFn m i hi, hiFin, Equiv.symm_apply_apply]
+      exact (Finset.mem_filter.mp hu).2
+    · exact (congrArg (Randomized.bitsEquiv m).symm hiFin).trans
+        ((Randomized.bitsEquiv m).symm_apply_apply u)
+
+/-- The state word stores the input, binary rank, and binary acceptance count:
+`state x i a = pairEncode x (pairEncode (Nat.bits i) (Nat.bits a))`.
+[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
+def state (x : List Bool) (i a : ℕ) : List Bool :=
+  pairEncode x (pairEncode (Nat.bits i) (Nat.bits a))
+
+/-- The state encoder satisfies
+`state x i a = pairEncode x (pairEncode (Nat.bits i) (Nat.bits a))`. -/
+theorem state_eq (x : List Bool) (i a : ℕ) :
+    state x i a = pairEncode x (pairEncode (Nat.bits i) (Nat.bits a)) := rfl
+
+end Complexity.SeedMajority
diff --git a/TCSlib/Cryptography/Randomness/Derandomization.lean b/TCSlib/Cryptography/Randomness/Derandomization.lean
index 251191e53..42ea99345 100644
--- a/TCSlib/Cryptography/Randomness/Derandomization.lean
+++ b/TCSlib/Cryptography/Randomness/Derandomization.lean
@@ -5,13 +5,20 @@ Released under Apache 2.0 license as described in the file LICENSE.
 import TCSlib.Cryptography.Randomness.BPPBridge
 import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
 import TCSlib.Complexity.ClassP.DTIME
+import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
+import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
+import TCSlib.Cryptography.Randomness.Derandomization.Expanded
+import TCSlib.Cryptography.Randomness.Derandomization.CoinGap
+import TCSlib.Cryptography.Randomness.Derandomization.Majority
+import TCSlib.Cryptography.Randomness.Derandomization.TimeBound
+import TCSlib.Complexity.Randomized.QuasiPolyHierarchy
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Derandomization from pseudorandom generators (statement phase)
+# Derandomization from pseudorandom generators
 
 [PS10, Theorem 180.1]: if pseudorandom generators exist, then `BPP ⊆ DTIME(2^{n^ε})` for every
 constant `ε > 0`.
@@ -36,10 +43,20 @@ constant `ε > 0`.
 
 * `Randomness.subexpBound`: `n ↦ ⌈2^{n^ε}⌉`.
 
+## Contents
+
+* `Randomness.Derandomization.RootSchedule`: the integer-root seed schedule.
+* `Randomness.Derandomization.AdviceGap`: the non-uniform advice gap bound.
+* `Randomness.Derandomization.Expanded`: the secure polynomial output envelope.
+* `Randomness.Derandomization.CoinGap`: the uniform prefix probability identification.
+* `Randomness.Derandomization.Majority`: the piecewise verifier and strict majority.
+* `Randomness.Derandomization.TimeBound`: the asymptotic estimate and finite exceptions.
+
 ## Main results
 
 * `Randomness.subexpBound_pos`: the bound is positive.
-* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1, stated; a `sorry` under the source's sketch).
+* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1), proved through the shared
+  seed-majority machine contract and its DTIME corollary.
 
 ## References
 
@@ -69,29 +86,42 @@ theorem subexpBound_pos (ε : ℝ) (n : ℕ) : 0 < subexpBound ε n :=
 [PS10, Theorem 180.1]: if a secure PRG exists, then every language of `main`'s `BPP` is in
 `DTIME(2^{n^ε})` for every `ε > 0`.
 
-**Proof sketch** (the source's, with the steps it leaves implicit; route note S3c).
-1. Let `L ∈ BPP` have verifier `M` and randomness `m(n) = a(n+1)^k`. Fix an integer `d ≥ 2`
-   with `1/d < min(ε,1)`. Compute `ℓ(n)` as the least natural `t` with `n ≤ t^d`, using integer
-   comparisons and powers. Then `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^{1/d}+1`. No computation of an
-   arbitrary real exponent is required. Expand the PRG to the syntactic polynomial envelope
-   `P(s) = a(s^d+1)^k+s+1`, which exceeds `s` and covers `m(n)` whenever `s = ℓ(n)`.
-2. Let `M'(x; u) = M(x; G(u)↾m(|x|))`, with seed length `ℓ(|x|)`. If infinitely many lengths
-   have an input with acceptance-probability gap `> 1/12`, choose one corresponding bad input
-   at each bad seed length. Its advice length is at most `s^d`. The verifier bridge, composed
-   with prefix truncation, is therefore a distinguisher polynomial in `s`; the probabilities
-   agree through `randProb_eq_uprob`. Each seed length has only finitely many corresponding
-   input lengths, so infinitely many bad input lengths give infinitely many bad seed lengths,
-   contradicting PRG security. The fixed `1/12` threshold leaves an explicit majority margin.
-3. Eventually every input has probability gap at most `1/12`. Since `M` is correct with
-   probability at least `2/3`, `M'` is correct with probability at least `7/12 > 1/2`.
-   The majority over all seeds is correct. A finite table handles the remaining input lengths.
-4. Construct a deterministic multi-tape machine enumerating the seeds, running `G` and `M`,
-   and counting, using the shared TM construction layer. For some constants `C,C'`, its time
-   is at most `2^{ℓ(n)} · poly(n) ≤ 2^{n^{1/d}+1+C log₂(n+1)+C'}`. Since `1/d < ε`, this is
-   eventually at most `2^{n^ε}`; a constant factor absorbs the finite exceptions. This machine
-   construction is the substantive remaining fill obligation, not supplied by the sketch. -/
+**Status.** Proved through `Complexity.exists_seedMajorityTM` and
+`Complexity.seedMajority_mem_DTIME`; the helpers introduce no admissions.
+
+**Proof sketch** ([PS10, Theorem 180.1], with an explicit piecewise test).
+1. Choose an integer `d ≥ 2` with `1/d < min(ε,1)`. The least natural root
+   `ℓ(n) = min{t | n ≤ t^d}` has an FP unary word and satisfies
+   `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^(1/d)+1`, including at zero.
+2. Expand a secure generator to `a(s^d+1)^k+s+1` and extract its FP evaluator.
+   Apply the verifier bridge to one bad input at each bad seed length, with
+   advice bound `s^d`. The published probability bridge and prefix projection
+   identify its PRG advantage with the verifier gap. Negligibility's inverse-linear
+   bound rules out every gap above `1/12` beyond a seed threshold, hence beyond
+   some input threshold `n₀`.
+3. Below `n₀`, use the original verifier with its true polynomial coin width;
+   from `n₀` on, use the generated prefix and width `ℓ(n)`. Both this paired
+   test and its unary width are polynomial-time. Acceptance is above `1/2`
+   exactly on members, with margins at least `7/12` and at most `5/12` in the
+   generated case. `half_lt_randProb_iff` identifies `L` with the strict seed
+   majority, including ties and zero widths. No exceptional-input table is used.
+4. Apply `seedMajority_mem_DTIME`. The logarithm of `2^w(n)(n+1)^e`, divided
+   by `n^ε`, tends to zero because `1/d < ε`; thus the time is eventually at
+   most `2^(n^ε)`. A natural constant absorbs all earlier lengths, since the
+   rounded bound is positive. Finish through `DTIME.mono` and
+   `Randomized.DTIME_const_mul_subset`. -/
 theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
     {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
-  sorry
+  intro L hL
+  obtain ⟨d, hd, hdε, _⟩ := Derand.exists_root_degree hε
+  have hdpos : 0 < d := by omega
+  obtain ⟨V, w, n₀, hV, hw, hevent, hmajority⟩ :=
+    Derand.exists_seed_majority hPRG hL d hdpos
+  obtain ⟨e, htime⟩ := seedMajority_mem_DTIME hV w hw
+  rw [← hmajority] at htime
+  obtain ⟨C, hbound⟩ := Derand.seed_time_le_subexp hdpos hε hdε w n₀ hevent e
+  apply Randomized.DTIME_const_mul_subset C (subexpBound ε)
+  apply DTIME.mono (fun n => ?_) htime
+  simpa only [subexpBound_eq] using hbound n
 
 end TCSlib.Cryptography.Randomness
diff --git a/TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean b/TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean
new file mode 100644
index 000000000..e86499bff
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean
@@ -0,0 +1,139 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.Randomness.BPPBridge
+import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# A non-uniform advice bound for verifier gaps
+
+The bad input in [PS10, Theorem 180.1] is advice for a distinguisher. A
+polynomial bound on its length in the seed parameter suffices to rule out
+every large-parameter gap, including when several input lengths share that
+parameter. No computable choice of advice is required by non-uniform security.
+
+## Main results
+
+* `TCSlib.Cryptography.Randomness.Derand.eff_mapCoins`: efficient coin reindexing.
+* `TCSlib.Cryptography.Randomness.Derand.exists_verifier_gap_bound`: a uniform
+  constant bound on the verifier's PRG gap beyond a seed threshold.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1.
+-/
+
+namespace TCSlib.Cryptography.Randomness.Derand
+
+open Complexity Turing
+
+/-- An efficient Boolean verifier remains efficient after an FP coin map:
+if `C` is FP on encoded pairs, then `(x,r) ↦ M x (C ⟨x,r⟩)` is efficient.
+This is `P`-preimage closure for the existing true and false languages.
+[PS10, §8.2, Theorem 180.1]
+
+**Proof sketch.** Extract the verifier's two `P` languages with the published
+efficiency reader. Take their preimages under `z ↦ ⟨fst z,C z⟩`, which is FP
+by pairing. The Boolean-verifier and pair-projection readers identify the
+resulting true and false events on every encoded pair. -/
+theorem eff_mapCoins {M : List Bool → List Bool → Bool}
+    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
+    {C : List Bool → List Bool} (hC : PolyTimeComputable C) :
+    Randomized.polyTimeModel.Eff
+      (Randomized.boolVerifier fun x r => M x (C (pairEncode x r))) := by
+  obtain ⟨V₁, V₀, h₁, h₀, hV⟩ :=
+    (Randomized.polyTimeModel_eff_iff (Randomized.boolVerifier M)).mp hM
+  let f : List Bool → List Bool := fun z => pairEncode (pairFstD z) (C z)
+  have hf : PolyTimeComputable f := polyTimeComputable_pairFstD.pairEncode hC
+  refine (Randomized.polyTimeModel_eff_iff _).mpr
+    ⟨f ⁻¹' V₁, f ⁻¹' V₀, preimage_mem_P h₁ hf, preimage_mem_P h₀ hf, ?_⟩
+  intro x r
+  change
+    (Randomized.boolVerifier (fun x r => M x (C (pairEncode x r))) x r = some true ↔
+      f (pairEncode x r) ∈ V₁) ∧
+    (Randomized.boolVerifier (fun x r => M x (C (pairEncode x r))) x r = some false ↔
+      f (pairEncode x r) ∈ V₀)
+  simpa only [Randomized.boolVerifier_apply, f, pairFstD_pairEncode]
+    using hV x (C (pairEncode x r))
+
+/-- For a secure PRG, any efficient Boolean verifier has gap at most `1/12`
+on every input whose seed parameter is sufficiently large, provided the input
+length is polynomial in that parameter:
+`|Pr[M(x;G(U_s))=1] - Pr[M(x;U_stretch(s))=1]| ≤ 1/12` for `s = w |x| ≥ S`.
+[PS10, §8.2, Theorem 180.1]
+
+**Proof sketch.** At each seed length with a gap above `1/12`, choose one bad
+input as advice. Else use the empty word. The hypothesis bounds this advice
+by `p`, so `verifier_toNUPPT` gives one non-uniform distinguisher for all seed
+lengths. Its advantage is exactly the selected gap: use the published PRG,
+acceptance-probability and distinguisher readers, then `uprob_fst` to remove
+the unused coins. Security bounds that advantage by `1/s` eventually, which
+is at most `1/12` for `s ≥ 12`. Hence no such bad input exists beyond the
+maximum of these two thresholds. -/
+theorem exists_verifier_gap_bound {M : List Bool → List Bool → Bool}
+    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
+    (w : ℕ → ℕ) (p : PolyExpr) (hsize : ∀ n, n ≤ p.eval (w n))
+    (G : PRG) (hG : G.Secure) :
+    ∃ S : ℕ, ∀ x : List Bool, S ≤ w x.length →
+      |uprob (fun r : Fin (w x.length) → Bool =>
+          M x (List.ofFn (G.G (w x.length) r)) = true) -
+        uprob (fun r : Fin (G.stretch.eval (w x.length)) → Bool =>
+          M x (List.ofFn r) = true)| ≤ (1 : ℝ) / 12 := by
+  classical
+  let gap (x : List Bool) (s : ℕ) : ℝ :=
+    |uprob (fun r : Fin s → Bool => M x (List.ofFn (G.G s r)) = true) -
+      uprob (fun r : Fin (G.stretch.eval s) → Bool => M x (List.ofFn r) = true)|
+  let bad (s : ℕ) : Prop := ∃ x : List Bool, w x.length = s ∧ (1 : ℝ) / 12 < gap x s
+  let xs (s : ℕ) : List Bool := if h : bad s then Classical.choose h else []
+  have hselected (s : ℕ) (hs : bad s) :
+      w (xs s).length = s ∧ (1 : ℝ) / 12 < gap (xs s) s := by
+    dsimp only [xs]
+    rw [dif_pos hs]
+    exact Classical.choose_spec hs
+  have hxs (s : ℕ) : (xs s).length ≤ p.eval s := by
+    by_cases hs : bad s
+    · have h := hsize (xs s).length
+      rw [(hselected s hs).1] at h
+      exact h
+    · simp only [xs, dif_neg hs, List.length_nil]
+      exact Nat.zero_le _
+  obtain ⟨D, _, hD⟩ := verifier_toNUPPT hM xs p hxs
+  have hadv (s : ℕ) :
+      prgAdv (G.G s) (D.distinguisher s (G.stretch.eval s)) = gap (xs s) s := by
+    rw [prgAdv_eq, distAdv_def]
+    dsimp only [gap]
+    congr 1
+    congr 1
+    · rw [acceptProb_def]
+      simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, hD,
+        List.cons.injEq, and_true, decide_eq_true_eq]
+      exact uprob_fst (α := Fin s → Bool) (β := D.Coins s)
+        (fun r => M (xs s) (List.ofFn (G.G s r)) = true)
+    · rw [acceptProb_def]
+      simp only [id_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, hD,
+        List.cons.injEq, and_true, decide_eq_true_eq]
+      exact uprob_fst (α := Fin (G.stretch.eval s) → Bool) (β := D.Coins s)
+        (fun r => M (xs s) (List.ofFn r) = true)
+  have hneg := ((PRG.secure_iff G).mp hG).2 D
+  obtain ⟨N, hN⟩ := (negligible_iff _).mp hneg 1
+  refine ⟨max N 12, fun x hx => ?_⟩
+  change gap x (w x.length) ≤ (1 : ℝ) / 12
+  by_contra hgap
+  have hb : bad (w x.length) := ⟨x, rfl, lt_of_not_ge hgap⟩
+  have hlow := (hselected (w x.length) hb).2
+  have hhigh := hN (w x.length) ((le_max_left N 12).trans hx)
+  rw [hadv, abs_of_nonneg (abs_nonneg _), pow_one] at hhigh
+  have hs : (12 : ℝ) ≤ (w x.length : ℝ) := by
+    exact_mod_cast (le_max_right N 12).trans hx
+  have hinv : 1 / (w x.length : ℝ) ≤ (1 : ℝ) / 12 :=
+    one_div_le_one_div_of_le (by norm_num) hs
+  linarith
+
+end TCSlib.Cryptography.Randomness.Derand
diff --git a/TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean b/TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean
new file mode 100644
index 000000000..0fa9736b0
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean
@@ -0,0 +1,95 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
+import TCSlib.Cryptography.Randomness.Derandomization.Expanded
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Replacing a verifier's coins by generated bits
+
+The expanded generator and the non-uniform advice bound give a single FP
+evaluator whose acceptance gap is at most `1/12` on every sufficiently long
+input. The probability identification reuses the published counting bridge
+and uniform prefix projection, including zero coin lengths.
+
+## Main results
+
+* `TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold`: the
+  input-length threshold needed by the piecewise verifier.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1.
+-/
+
+namespace TCSlib.Cryptography.Randomness.Derand
+
+open Complexity Turing
+
+/-- There are an FP generator evaluator `F` and a threshold `n₀` such that,
+for every `|x| ≥ n₀`,
+`|randProb (ceilRoot d |x|) (M x (F(u)↾m)) - randProb m (M x)| ≤ 1/12`,
+where the rational probabilities are cast to `ℝ` and `m = polyLen a k |x|`.
+[PS10, §8.2, Theorem 180.1]
+
+**Proof sketch.** Expand a secure generator to cover the verifier's entire
+coin width. Apply the advice-gap theorem to the prefix-truncated verifier,
+which stays efficient by `eff_mapCoins` and `polyTimeComputable_pairTakePoly`.
+Advice has bound `s^d` because `|x| ≤ (ceilRoot d |x|)^d`. If the seed threshold
+is `S`, input lengths from `S^d+1` on have root greater than `S`. Identify the
+generated probability with the first advantage term using the evaluator's
+typed contract and `randProb_eq_uprob`; identify the uniform term using
+`randProb_take`. No new expectation or probability-reindexing identity is used. -/
+theorem exists_coin_gap_threshold (hPRG : ∃ G : PRG, G.Secure)
+    {M : List Bool → List Bool → Bool}
+    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
+    (a k d : ℕ) (hd : 0 < d) :
+    ∃ (F : List Bool → List Bool) (n₀ : ℕ), PolyTimeComputable F ∧
+      ∀ x : List Bool, n₀ ≤ x.length →
+        |(Randomized.randProb (ceilRoot d x.length)
+            (fun u => M x ((F u).take (Randomized.polyLen a k x.length)) = true) : ℝ) -
+          (Randomized.randProb (Randomized.polyLen a k x.length)
+            (fun r => M x r = true) : ℝ)| ≤ (1 : ℝ) / 12 := by
+  classical
+  obtain ⟨G, F, hG, hF, hFs, hcover⟩ := exists_secure_cover hPRG a k d hd
+  let M' : List Bool → List Bool → Bool :=
+    fun x r => M x (r.take (Randomized.polyLen a k x.length))
+  have hM' : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M') := by
+    simpa only [pairFstD_pairEncode, pairSndD_pairEncode, eval_polyLenExpr, M'] using
+      eff_mapCoins hM (polyTimeComputable_pairTakePoly (polyLenExpr a k))
+  have hsize (n : ℕ) : n ≤ (PolyExpr.pow .var d).eval (ceilRoot d n) := by
+    simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using le_ceilRoot_pow hd n
+  obtain ⟨S, hS⟩ := exists_verifier_gap_bound hM' (ceilRoot d) (.pow .var d) hsize G hG
+  refine ⟨F, S ^ d + 1, hF, fun x hx => ?_⟩
+  have hs : S ≤ ceilRoot d x.length :=
+    ((lt_ceilRoot_iff hd x.length S).mpr (by omega)).le
+  have h := hS x hs
+  have hgen :
+      (Randomized.randProb (ceilRoot d x.length)
+        (fun u => M x ((F u).take (Randomized.polyLen a k x.length)) = true) : ℝ) =
+        uprob (fun r : Fin (ceilRoot d x.length) → Bool =>
+          M' x (List.ofFn (G.G (ceilRoot d x.length) r)) = true) := by
+    rw [randProb_eq_uprob]
+    congr 1
+    funext r
+    rw [hFs]
+  have huniform :
+      uprob (fun r : Fin (G.stretch.eval (ceilRoot d x.length)) → Bool =>
+        M' x (List.ofFn r) = true) =
+        (Randomized.randProb (Randomized.polyLen a k x.length)
+          (fun r => M x r = true) : ℝ) := by
+    rw [← randProb_eq_uprob (G.stretch.eval (ceilRoot d x.length))
+      (fun r => M' x r = true)]
+    exact congrArg (fun q : ℚ => (q : ℝ))
+      (Randomized.randProb_take (hcover x.length) (fun r => M x r = true))
+  rw [hgen, ← huniform]
+  exact h
+
+end TCSlib.Cryptography.Randomness.Derand
diff --git a/TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean b/TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean
new file mode 100644
index 000000000..03df855ef
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean
@@ -0,0 +1,70 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
+import TCSlib.Cryptography.Randomness.BPPBridge
+import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Stretch
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Expanding a PRG to cover the verifier's coins
+
+The polynomial stretch `a(s^d+1)^k+s+1` exceeds the seed length even at zero.
+At the ceiling-root schedule it covers `a(n+1)^k` true random bits.
+
+## Main results
+
+* `TCSlib.Cryptography.Randomness.Derand.exists_secure_cover`: a secure
+  generator with an FP evaluator and the required output-length envelope.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, Lemma 80.5 and Theorem 180.1.
+-/
+
+namespace TCSlib.Cryptography.Randomness.Derand
+
+open Complexity
+
+/-- A secure PRG can cover every polynomial coin schedule at the integer-root
+seed length: there are a secure `G` and an FP evaluator `F` such that
+`F(ofFn s) = ofFn(G n s)` and
+`polyLen a k n ≤ G.stretch.eval (ceilRoot d n)` for every `n`.
+[PS10, Lemma 80.5 and Theorem 180.1]
+
+**Proof sketch.** Truncate the given generator to one-bit stretch and use
+`prg_expand` at the syntactic polynomial `a(s^d+1)^k+s+1`. The last two terms
+make its expansion clause strict at every seed length. Extract the existing
+FP evaluator through `PRG.secure_iff` and `PRG.easy_iff`. Finally
+`n ≤ (ceilRoot d n)^d` gives the verifier's length bound by monotonicity of
+fixed natural powers and multiplication. -/
+theorem exists_secure_cover (hPRG : ∃ G : PRG, G.Secure) (a k d : ℕ) (hd : 0 < d) :
+    ∃ (G : PRG) (F : List Bool → List Bool),
+      G.Secure ∧ PolyTimeComputable F ∧
+      (∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G.G n s)) ∧
+      ∀ n, Randomized.polyLen a k n ≤ G.stretch.eval (ceilRoot d n) := by
+  obtain ⟨G₀, hG₀⟩ := hPRG
+  let p : PolyExpr := .add (.add
+    (.mul (.const a) (.pow (.add (.pow .var d) (.const 1)) k)) .var) (.const 1)
+  have hp (s : ℕ) : s < p.eval s := by
+    simp only [p, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+      PolyExpr.eval_pow, PolyExpr.eval_var]
+    omega
+  let G := PRG.expand G₀.truncate p hp
+  have hG : G.Secure := prg_expand G₀.truncate p hp hG₀.truncate
+  obtain ⟨F, hF, hFs⟩ := (PRG.easy_iff G).mp ((PRG.secure_iff G).mp hG).1
+  refine ⟨G, F, hG, hF, hFs, fun n => ?_⟩
+  rw [show G.stretch = p from PRG.expand_stretch G₀.truncate p hp]
+  simp only [p, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
+    PolyExpr.eval_pow, PolyExpr.eval_var, Randomized.polyLen_eq]
+  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (le_ceilRoot_pow hd n) 1) k
+  have hmul := Nat.mul_le_mul_left a hpow
+  omega
+
+end TCSlib.Cryptography.Randomness.Derand
diff --git a/TCSlib/Cryptography/Randomness/Derandomization/Majority.lean b/TCSlib/Cryptography/Randomness/Derandomization/Majority.lean
new file mode 100644
index 000000000..91a3b5a76
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Derandomization/Majority.lean
@@ -0,0 +1,159 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import Mathlib.Data.Rat.Cast.Order
+import TCSlib.Cryptography.Randomness.Derandomization.CoinGap
+import TCSlib.Complexity.Randomized.SeedMajority
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The piecewise verifier and its seed majority
+
+Below the security threshold, both the verifier and its width use the true
+random coins. At and above the threshold, they use the expanded generator
+and the ceiling-root seed length. The `1/12` gap gives a strict majority in
+both cases, so no finite table of exceptional input words is needed.
+
+## Main results
+
+* `TCSlib.Cryptography.Randomness.Derand.exists_seed_majority`: a `P` test
+  and an FP unary width whose strict seed majority equals the BPP language.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1.
+-/
+
+namespace TCSlib.Cryptography.Randomness.Derand
+
+open Complexity Turing
+
+/-- A fixed upper threshold on the length of an FP word is an FP test.
+The existing length comparison tests `|f z| + 1 ≤ N`. -/
+private theorem short_poly {f : List Bool → List Bool} (hf : PolyTimeComputable f) (N : ℕ) :
+    PolyTimeComputable fun z => [decide ((f z).length < N)] := by
+  convert StateLoop.lenLe_comp (polyTimeComputable_const (List.replicate N true))
+    (hf.append (polyTimeComputable_const [true])) using 1
+  funext z
+  simp only [List.length_append, List.length_singleton, List.length_replicate,
+    Nat.add_one_le_iff]
+
+open Classical in
+/-- A BPP language is the strict seed-majority language of a `P` test with an
+FP unary width `w`, where `w n = ceilRoot d n` beyond some threshold:
+`L = {x | 2^(w |x|) < 2 * #{u | ⟨x,ofFn u⟩ ∈ V}}`.
+[PS10, §8.2, Theorem 180.1]
+
+**Proof sketch.** Extract the efficient Boolean verifier and polynomial coin
+schedule through `inBPP_iff`. Use the coin-gap threshold and hard-code it
+in a polynomial-time branch. Below it, the test uses the original coins and
+the width is the original polynomial schedule. Above it, the test uses the
+generated prefix and the width is the ceiling root. The test stays efficient
+by `eff_mapCoins`; its accepting language is therefore in `P`. The unary
+width is FP by the same fixed length branch. The true-coin acceptance bound
+`2/3` and the gap bound give acceptance above `1/2` on members and below
+`1/2` on nonmembers. Finally `half_lt_randProb_iff` identifies exactly the
+strict seed count, with ties rejected and zero widths included. -/
+theorem exists_seed_majority (hPRG : ∃ G : PRG, G.Secure)
+    {L : Language Bool} (hL : Randomized.InBPP Randomized.polyTimeModel L)
+    (d : ℕ) (hd : 0 < d) :
+    ∃ (V : Language Bool) (w : ℕ → ℕ) (n₀ : ℕ), V ∈ P ∧
+      PolyTimeComputable (fun x => List.replicate (w x.length) true) ∧
+      (∀ n, n₀ ≤ n → w n = ceilRoot d n) ∧
+      L = {x : List Bool | 2 ^ w x.length <
+        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
+          pairEncode x (List.ofFn u) ∈ V).card} := by
+  classical
+  obtain ⟨M, a, k, hM, hcorrect⟩ :=
+    (Randomized.inBPP_iff Randomized.polyTimeModel L).mp hL
+  obtain ⟨F, n₀, hF, hgap⟩ := exists_coin_gap_threshold hPRG hM a k d hd
+  let w (n : ℕ) := if n < n₀ then Randomized.polyLen a k n else ceilRoot d n
+  let C (z : List Bool) := if (pairFstD z).length < n₀ then pairSndD z
+    else (F (pairSndD z)).take (Randomized.polyLen a k (pairFstD z).length)
+  let M' (x u : List Bool) := M x (C (pairEncode x u))
+  have hprefix : PolyTimeComputable fun z =>
+      (F (pairSndD z)).take (Randomized.polyLen a k (pairFstD z).length) := by
+    convert (polyTimeComputable_pairTakePoly (polyLenExpr a k)).comp
+      (polyTimeComputable_pairFstD.pairEncode (hF.comp polyTimeComputable_pairSndD)) using 1
+    funext z
+    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+      eval_polyLenExpr]
+  have hC : PolyTimeComputable C := by
+    simpa only [C, decide_eq_true_eq] using
+      polyTimeComputable_ite (short_poly polyTimeComputable_pairFstD n₀)
+        polyTimeComputable_pairSndD hprefix
+  have hM' : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M') := eff_mapCoins hM hC
+  obtain ⟨V, _, hV, _, hMV⟩ :=
+    (Randomized.polyTimeModel_eff_iff (Randomized.boolVerifier M')).mp hM'
+  have hVeq (x u : List Bool) : M' x u = true ↔ pairEncode x u ∈ V := by
+    simpa only [Randomized.boolVerifier_apply, Option.some.injEq] using (hMV x u).1
+  have hw : PolyTimeComputable fun x => List.replicate (w x.length) true := by
+    have h := polyTimeComputable_ite (short_poly polyTimeComputable_id n₀)
+      (polyTimeComputable_unaryPoly (polyLenExpr a k)) (polyTimeComputable_ceilRoot hd)
+    convert h using 1
+    funext x
+    simp only [id_eq, decide_eq_true_eq, eval_polyLenExpr, w]
+    split_ifs <;> rfl
+  have hclose (x : List Bool) :
+      |(Randomized.randProb (w x.length) (fun u => M' x u = true) : ℝ) -
+        (Randomized.randProb (Randomized.polyLen a k x.length)
+          (fun r => M x r = true) : ℝ)| ≤ (1 : ℝ) / 12 := by
+    by_cases hx : x.length < n₀
+    · have heq : Randomized.randProb (w x.length) (fun u => M' x u = true) =
+          Randomized.randProb (Randomized.polyLen a k x.length) (fun r => M x r = true) := by
+        simp only [w, if_pos hx]
+        apply Randomized.randProb_congr
+        intro u
+        simp only [M', C, pairFstD_pairEncode, pairSndD_pairEncode, if_pos hx]
+      rw [heq, sub_self, abs_zero]
+      norm_num
+    · simpa only [w, if_neg hx, M', C, pairFstD_pairEncode, pairSndD_pairEncode]
+        using hgap x (by omega)
+  have hmajority (x : List Bool) : x ∈ L ↔
+      (1 / 2 : ℚ) < Randomized.randProb (w x.length) (fun u => M' x u = true) := by
+    have hb := abs_le.mp (hclose x)
+    constructor
+    · intro hx
+      have htrue : (2 : ℝ) / 3 ≤
+          (Randomized.randProb (Randomized.polyLen a k x.length)
+            (fun r => M x r = true) : ℝ) := by
+        rw [show (2 : ℝ) / 3 = ((2 / 3 : ℚ) : ℝ) by norm_num, Rat.cast_le]
+        exact (hcorrect x).1 hx
+      have hhalf : (1 : ℝ) / 2 <
+          (Randomized.randProb (w x.length) (fun u => M' x u = true) : ℝ) := by
+        linarith
+      apply (Rat.cast_lt (K := ℝ)).mp
+      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hhalf
+    · intro hx
+      by_contra hnot
+      have hfalse := (hcorrect x).2 hnot
+      rw [Randomized.randProb_bool_false] at hfalse
+      have htrue :
+          (Randomized.randProb (Randomized.polyLen a k x.length)
+            (fun r => M x r = true) : ℝ) ≤ (1 : ℝ) / 3 := by
+        rw [show (1 : ℝ) / 3 = ((1 / 3 : ℚ) : ℝ) by norm_num, Rat.cast_le]
+        linarith
+      have hhalf : (1 : ℝ) / 2 <
+          (Randomized.randProb (w x.length) (fun u => M' x u = true) : ℝ) := by
+        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
+          (Rat.cast_lt (K := ℝ)).mpr hx
+      linarith
+  refine ⟨V, w, n₀, hV, hw, fun n hn => if_neg (Nat.not_lt_of_ge hn), ?_⟩
+  ext x
+  change x ∈ L ↔ 2 ^ w x.length <
+    2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
+      pairEncode x (List.ofFn u) ∈ V).card
+  rw [← Randomized.half_lt_randProb_iff (w x.length) (fun u => pairEncode x u ∈ V)]
+  have hp := Randomized.randProb_congr (m := w x.length)
+    (A := fun u => M' x u = true) (B := fun u => pairEncode x u ∈ V)
+    (fun u => hVeq x (List.ofFn u))
+  rw [← hp]
+  exact hmajority x
+
+end TCSlib.Cryptography.Randomness.Derand
diff --git a/TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean b/TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean
new file mode 100644
index 000000000..21cfd102e
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean
@@ -0,0 +1,173 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
+import TCSlib.Complexity.Randomized.Repetition
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# An integer-root seed schedule
+
+The schedule in the proof of [PS10, Theorem 180.1] is the least natural `t` with
+`n ≤ t ^ d`. It uses the existing natural `nthRoot`; its unary implementation
+searches through `0, …, n` with integer length comparisons and fixed powers.
+
+## Main definitions
+
+* `TCSlib.Cryptography.Randomness.Derand.ceilRoot`: a ceiling root, defined over naturals.
+
+## Main results
+
+* `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff`: its least-root property.
+* `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_real`: the real-root upper bound.
+* `TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot`: its FP unary word.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1.
+-/
+
+namespace TCSlib.Cryptography.Randomness.Derand
+
+open Complexity Turing
+
+/-- The natural ceiling-root schedule is zero at zero and otherwise one more than
+the existing floor root of `n - 1`:
+`ceilRoot d n = if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1`.
+For `0 < d`, this is `min {t | n ≤ t ^ d}`. [PS10, §8.2, Theorem 180.1] -/
+def ceilRoot (d n : ℕ) : ℕ := if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1
+
+/-- The ceiling-root schedule satisfies
+`ceilRoot d n = if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1`. -/
+theorem ceilRoot_eq (d n : ℕ) :
+    ceilRoot d n = if n = 0 then 0 else Nat.nthRoot d (n - 1) + 1 := rfl
+
+/-- For `0 < d`, the root is at most `t` exactly when `n ≤ t ^ d`:
+`ceilRoot d n ≤ t ↔ n ≤ t ^ d`. [PS10, §8.2, Theorem 180.1] -/
+theorem ceilRoot_le_iff {d : ℕ} (hd : 0 < d) (n t : ℕ) :
+    ceilRoot d n ≤ t ↔ n ≤ t ^ d := by
+  rw [ceilRoot_eq]
+  by_cases hn : n = 0
+  · subst n
+    simp
+  · rw [if_neg hn]
+    have h := Nat.nthRoot_lt_iff (n := d) (a := n - 1) (b := t) hd.ne'
+    omega
+
+/-- For `0 < d`, the scheduled seed length covers the input:
+`n ≤ (ceilRoot d n) ^ d`. [PS10, §8.2, Theorem 180.1] -/
+theorem le_ceilRoot_pow {d : ℕ} (hd : 0 < d) (n : ℕ) : n ≤ (ceilRoot d n) ^ d :=
+  (ceilRoot_le_iff hd n (ceilRoot d n)).mp le_rfl
+
+/-- The zero input has zero seed length: `ceilRoot d 0 = 0`. -/
+theorem ceilRoot_zero (d : ℕ) : ceilRoot d 0 = 0 := by
+  rw [ceilRoot_eq, if_pos rfl]
+
+
+/-- The schedule is bounded by the input length:
+`ceilRoot d n ≤ n` when `0 < d`. [PS10, §8.2, Theorem 180.1] -/
+theorem ceilRoot_le_nat {d : ℕ} (hd : 0 < d) (n : ℕ) : ceilRoot d n ≤ n := by
+  apply (ceilRoot_le_iff hd n n).mpr
+  by_cases hn : n = 0
+  · subst n
+    exact Nat.zero_le _
+  · calc
+      n = n ^ 1 := (pow_one n).symm
+      _ ≤ n ^ d := Nat.pow_le_pow_right (by omega) hd
+
+/-- The strict lower-bound form of the least-root property is
+`t < ceilRoot d n ↔ t ^ d < n` when `0 < d`. -/
+theorem lt_ceilRoot_iff {d : ℕ} (hd : 0 < d) (n t : ℕ) :
+    t < ceilRoot d n ↔ t ^ d < n := by
+  have h := ceilRoot_le_iff hd n t
+  omega
+
+/-- The integer schedule is within one of the real root:
+`(ceilRoot d n : ℝ) ≤ (n : ℝ) ^ (1 / d) + 1` for `0 < d`.
+[PS10, §8.2, Theorem 180.1]
+
+**Proof sketch.** Handle zero separately. At a positive input the floor root
+of `n-1` has `d`th power at most `n`. Cast this bound to the reals, apply
+the monotonic inverse-power comparison, and add one on both sides. -/
+theorem ceilRoot_le_real {d : ℕ} (hd : 0 < d) (n : ℕ) :
+    (ceilRoot d n : ℝ) ≤ (n : ℝ) ^ (1 / (d : ℝ)) + 1 := by
+  by_cases hn : n = 0
+  · subst n
+    rw [ceilRoot_zero]
+    simpa only [Nat.cast_zero] using
+      add_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) (1 / (d : ℝ)))
+        zero_le_one
+  · have hpow : ((Nat.nthRoot d (n - 1) : ℕ) : ℝ) ^ d ≤ (n : ℝ) := by
+      exact_mod_cast (Nat.pow_nthRoot_le (n := d) (a := n - 1) (Or.inl hd.ne')).trans
+        (Nat.sub_le n 1)
+    have hr := (Real.le_rpow_inv_iff_of_pos
+      (show 0 ≤ ((Nat.nthRoot d (n - 1) : ℕ) : ℝ) from Nat.cast_nonneg _)
+      (show 0 ≤ (n : ℝ) from Nat.cast_nonneg _)
+      (show 0 < (d : ℝ) by exact_mod_cast hd)).mpr
+        (by simpa only [Real.rpow_natCast] using hpow)
+    rw [ceilRoot_eq, if_neg hn, Nat.cast_add, Nat.cast_one]
+    simpa only [one_div] using add_le_add_right hr 1
+
+/-- The unary ceiling-root word is polynomial-time computable:
+`x ↦ 1 ^ (ceilRoot d |x|)` belongs to `FP` for each fixed positive `d`.
+[PS10, §8.2, Theorem 180.1]
+
+**Proof sketch.** Use `polyTimeComputable_stateFind` with the unary counter as
+state. Each round appends one token. The test compares `|x|` with the fixed
+power of the counter length, using `StateLoop.unaryPoly_comp` and
+`StateLoop.lenLe_comp`. The least-root property makes the test false before
+`ceilRoot d |x|` and true there. All states up to that round have length at
+most `|x|` by `ceilRoot_le_nat`, so both the iteration and state bounds are
+the identity polynomial. The output is the counter itself. -/
+theorem polyTimeComputable_ceilRoot {d : ℕ} (hd : 0 < d) :
+    PolyTimeComputable fun x => List.replicate (ceilRoot d x.length) true := by
+  let start : List Bool → List Bool := fun _ => []
+  let step : List Bool → List Bool := fun z => pairSndD z ++ [true]
+  let acc : List Bool → Bool := fun z =>
+    decide ((pairFstD z).length ≤ (pairSndD z).length ^ d)
+  have hstart : PolyTimeComputable start := polyTimeComputable_const []
+  have hstep : PolyTimeComputable step :=
+    polyTimeComputable_pairSndD.append (polyTimeComputable_const [true])
+  have hpower : PolyTimeComputable fun z =>
+      List.replicate ((pairSndD z).length ^ d) true := by
+    simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using
+      StateLoop.unaryPoly_comp (.pow .var d) polyTimeComputable_pairSndD
+  have hacc : PolyTimeComputable fun z => [acc z] := by
+    simpa only [acc, List.length_replicate] using
+      StateLoop.lenLe_comp hpower polyTimeComputable_pairFstD
+  have horbit (x : List Bool) (i : ℕ) :
+      StateLoop.orbit start step x i = List.replicate i true := by
+    induction i with
+    | zero => rw [StateLoop.orbit_zero]; rfl
+    | succ i ih =>
+        rw [StateLoop.orbit_succ, ih]
+        simp only [step, pairSndD_pairEncode]
+        change List.replicate i true ++ List.replicate 1 true = _
+        rw [← List.replicate_add]
+  have hN (x : List Bool) : ceilRoot d x.length ≤ PolyExpr.var.eval x.length := by
+    simpa only [PolyExpr.eval_var] using ceilRoot_le_nat hd x.length
+  have hbound (x : List Bool) (i : ℕ) (hi : i ≤ ceilRoot d x.length) :
+      (StateLoop.orbit start step x i).length ≤ PolyExpr.var.eval x.length := by
+    rw [horbit, List.length_replicate]
+    exact hi.trans (hN x)
+  have hfirst (x : List Bool) (i : ℕ) (hi : i < ceilRoot d x.length) :
+      acc (pairEncode x (StateLoop.orbit start step x i)) = false := by
+    simp only [acc, horbit, pairFstD_pairEncode, pairSndD_pairEncode,
+      List.length_replicate, decide_eq_false_iff_not]
+    exact Nat.not_le_of_lt ((lt_ceilRoot_iff hd x.length i).mp hi)
+  have hlast (x : List Bool) :
+      acc (pairEncode x (StateLoop.orbit start step x (ceilRoot d x.length))) = true := by
+    simp only [acc, horbit, pairFstD_pairEncode, pairSndD_pairEncode,
+      List.length_replicate, decide_eq_true_eq]
+    exact le_ceilRoot_pow hd x.length
+  have h := polyTimeComputable_stateFind hstart hstep hacc polyTimeComputable_pairSndD
+    .var .var (fun x => ceilRoot d x.length) hN hbound hfirst hlast
+  simpa only [horbit, pairSndD_pairEncode] using h
+
+end TCSlib.Cryptography.Randomness.Derand
diff --git a/TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean b/TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean
new file mode 100644
index 000000000..4ecbaba98
--- /dev/null
+++ b/TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean
@@ -0,0 +1,142 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
+import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The subexponential seed-enumeration bound
+
+A ceiling-root seed width eventually satisfies `w(n) ≤ n^(1/d)+1`.
+For `1/d < ε`, its exponential times any fixed polynomial is eventually
+below `2^(n^ε)`. A single natural constant absorbs every earlier length.
+
+## Main results
+
+* `TCSlib.Cryptography.Randomness.Derand.exists_root_degree`: a positive
+  integer degree valid for every real `ε > 0`.
+* `TCSlib.Cryptography.Randomness.Derand.seed_time_le_subexp`: the global
+  time bound, including the finite exceptional lengths.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
+  3rd ed., January 2010, §8.2, Theorem 180.1.
+-/
+
+namespace TCSlib.Cryptography.Randomness.Derand
+
+open Filter Topology
+
+/-- Every positive real exponent admits a fixed integer degree:
+`∃ d ≥ 2, 1 / (d : ℝ) < ε ∧ 1 / (d : ℝ) < 1`.
+[PS10, §8.2, Theorem 180.1] -/
+theorem exists_root_degree {ε : ℝ} (hε : 0 < ε) :
+    ∃ d : ℕ, 2 ≤ d ∧ 1 / (d : ℝ) < ε ∧ 1 / (d : ℝ) < 1 := by
+  obtain ⟨d, hd⟩ := exists_nat_gt (max (1 / ε) 1)
+  have hd1 : (1 : ℝ) < d := (le_max_right _ _).trans_lt hd
+  have hdp : (0 : ℝ) < d := lt_trans zero_lt_one hd1
+  have hde : 1 / ε < (d : ℝ) := (le_max_left _ _).trans_lt hd
+  have hmul := (div_lt_iff₀ hε).mp hde
+  refine ⟨d, ?_, (div_lt_iff₀ hdp).mpr (by nlinarith), (div_lt_one hdp).mpr hd1⟩
+  have : 1 < d := by exact_mod_cast hd1
+  omega
+
+/-- If `w n = ceilRoot d n` from some length onward and `1/d < ε`, then
+`2^(w n) * (n+1)^e ≤ C * ⌈2^(n^ε)⌉₊` for one natural `C` and every `n`.
+[PS10, §8.2, Theorem 180.1]
+
+**Proof sketch.** Divide the logarithmic upper bound
+`(n^(1/d)+1) log 2 + e(log 2 + log n)` by `n^ε`. Its root term tends to zero
+as `n^(1/d-ε)`, its constant term does so because `n^ε → ∞`, and its logarithm
+term does so by Mathlib's `isLittleO_log_rpow_atTop`. Eventually the quotient
+is below `log 2`. For `n ≥ 1`, use `n+1 ≤ 2n`, the ceiling-root bound and
+monotonicity of logarithms to bound the actual enumeration time. Exponentiating
+gives the desired real bound, and rounding up preserves it. For earlier lengths,
+one plus the sum of their time bounds is enough, because the rounded bound
+is positive at every length. -/
+theorem seed_time_le_subexp {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
+    (hr : 1 / (d : ℝ) < ε) (w : ℕ → ℕ) (n₀ : ℕ)
+    (hw : ∀ n, n₀ ≤ n → w n = ceilRoot d n) (e : ℕ) :
+    ∃ C : ℕ, ∀ n, 2 ^ w n * (n + 1) ^ e ≤
+      C * ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := by
+  let r : ℝ := 1 / (d : ℝ)
+  have hratio : Tendsto (fun x : ℝ => x ^ r / x ^ ε) atTop (𝓝 0) := by
+    apply (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).congr'
+    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
+    rw [show -(ε - r) = r - ε by ring, Real.rpow_sub hx]
+  have hconst : Tendsto (fun x : ℝ => 1 / x ^ ε) atTop (𝓝 0) := by
+    simpa only [one_div] using (tendsto_rpow_atTop hε).inv_tendsto_atTop
+  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (𝓝 0) :=
+    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
+  have hsum : Tendsto (fun x : ℝ => Real.log 2 * (x ^ r / x ^ ε) +
+      (((e : ℝ) + 1) * Real.log 2) * (1 / x ^ ε) +
+      (e : ℝ) * (Real.log x / x ^ ε)) atTop (𝓝 0) := by
+    simpa only [mul_zero, zero_add, add_zero] using
+      ((hratio.const_mul (Real.log 2)).add
+        (hconst.const_mul (((e : ℝ) + 1) * Real.log 2))).add (hlog.const_mul (e : ℝ))
+  have hlim : Tendsto (fun x : ℝ =>
+      ((x ^ r + 1) * Real.log 2 + (e : ℝ) * (Real.log 2 + Real.log x)) / x ^ ε)
+      atTop (𝓝 0) := by
+    apply hsum.congr'
+    exact Eventually.of_forall fun x => by ring
+  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
+  obtain ⟨N, hN⟩ := eventually_atTop.mp
+    ((hlim.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hlog2))
+  let K := max N (max n₀ 1)
+  let f (n : ℕ) := 2 ^ w n * (n + 1) ^ e
+  have hevent (n : ℕ) (hn : K ≤ n) : f n ≤ ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := by
+    have hnN : N ≤ n := (le_max_left _ _).trans hn
+    have hnn₀ : n₀ ≤ n := (le_max_left n₀ 1).trans ((le_max_right _ _).trans hn)
+    have hn1 : 1 ≤ n := (le_max_right n₀ 1).trans ((le_max_right _ _).trans hn)
+    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
+    have hnp : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnr
+    have hbudget := (div_lt_iff₀ (Real.rpow_pos_of_pos hnp ε)).mp (hN n hnN)
+    have hroot : (w n : ℝ) ≤ (n : ℝ) ^ r + 1 := by
+      rw [hw n hnn₀]
+      exact ceilRoot_le_real hd n
+    have hsucc : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := by
+      calc
+        Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
+          Real.log_le_log (by positivity) (by linarith)
+        _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num) hnp.ne'
+    have hactual : Real.log (f n : ℝ) ≤ Real.log 2 * (n : ℝ) ^ ε := by
+      calc
+        Real.log (f n : ℝ) = (w n : ℝ) * Real.log 2 +
+            (e : ℝ) * Real.log ((n : ℝ) + 1) := by
+          simp only [f, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
+            Nat.cast_ofNat]
+          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
+        _ ≤ ((n : ℝ) ^ r + 1) * Real.log 2 +
+            (e : ℝ) * (Real.log 2 + Real.log (n : ℝ)) :=
+          add_le_add (mul_le_mul_of_nonneg_right hroot hlog2.le)
+            (mul_le_mul_of_nonneg_left hsucc (Nat.cast_nonneg e))
+        _ ≤ Real.log 2 * (n : ℝ) ^ ε := hbudget.le
+    have hreal : (f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
+      apply (Real.log_le_log_iff (by dsimp only [f]; positivity)
+        (Real.rpow_pos_of_pos (by norm_num) _)).mp
+      rw [Real.log_rpow (by norm_num)]
+      nlinarith [hactual]
+    exact_mod_cast hreal.trans (Nat.le_ceil _)
+  let C := 1 + ∑ i ∈ Finset.range K, f i
+  refine ⟨C, fun n => ?_⟩
+  have hC : 1 ≤ C := by dsimp only [C]; omega
+  by_cases hn : K ≤ n
+  · exact (hevent n hn).trans (Nat.le_mul_of_pos_left _ hC)
+  · have hsmall : f n ≤ ∑ i ∈ Finset.range K, f i :=
+      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
+    have hb : 1 ≤ ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ :=
+      Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
+    have hsmallC : f n ≤ C := by
+      dsimp only [C]
+      omega
+    exact hsmallC.trans
+      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hb)
+
+end TCSlib.Cryptography.Randomness.Derand

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

/-- The decision contract `M.DecidesInTime L T` holds exactly when every input `x`
is computed with output `[indicator L x]` within `T |x|` steps:
`M.DecidesInTime L T ↔ ∀ x, M.ComputesInTime x [indicator L x] (T |x|)`.
[AB09, §1.6, Definition 1.3] -/
theorem decidesInTime_iff (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
    M.DecidesInTime L T ↔
      ∀ x : List Bool,
        M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length) :=
  Iff.rfl

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- Membership `L ∈ DTIME T` is exactly a constant `c` and a finite machine `M`
deciding `L` within `n ↦ c * T n`:
`L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L (fun n => c * T n)`.
[AB09, Definition 1.12] -/
theorem mem_DTIME_iff {T : ℕ → ℕ} {L : Language Bool} :
    L ∈ DTIME T ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n :=
  Iff.rfl

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity

## ===== TCSlib/Complexity/Randomized/Build/IterateFind.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.Randomized.Build.IterateFindHost
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine behind the repetition lemma

The finite machine behind `Complexity.polyTimeComputable_iterateFind`
(`TCSlib.Complexity.Randomized.Repetition`, the load-bearing lemma of the Pass–shelat campaign,
foundation decision D11 of `PassShelatChapter2-4Plan.md`): iterate a polynomial-time step `g`
at most `R(|x|)` times on a polynomially bounded orbit and return the payload `out` of the first
orbit point accepted by `acc` (`[]` on exhaustion). Every theorem of [PS10, ch. 2–4] that
repeats an adversary — Algorithm 38.5's `2nm²p(n)` attempts with first success
[PS10, Theorem 35.1], the `n(2^k − 1)` calls of Goldreich–Levin [PS10, Theorem 87.3], the
truncated simulators [PS10, Algorithms 123.4 and 128.7] — reduces to this machine.

## Construction (DESIGN.md §2.6, the three panel repairs built in)

The machine is an instance of the result-bearing loop combinator
`Turing.FinTM.exists_loopFindTM` (`TCSlib.Complexity.TuringMachine.Build.Loop`).

1. *State word.* The loop state is the pair `⟨x, s⟩` (`Turing.pairEncode x s`) of the input
   and the current orbit point; the loop invariant `Inv` says the word *is* such a pair with
   `|s| ≤ P|x|`; the step is the length-guarded `Complexity.IterateFind.step`
   (`⟨x, g s⟩` if `|g s| ≤ P|x|`, else unchanged), under which the invariant is closed for
   every admissible word; on the orbit the guard never fires (the pure lemmas of
   `TCSlib.Complexity.Randomized.Repetition`).
2. *Modules.* Three clean-call modules over the state word, from
   `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM` applied to FP functions: the
   **verdict** install `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell of the installed
   word), the **step** install `w' ↦ step` on the pair carried by `w'`, and the **payload** emit
   `w' ↦ out (snd (snd w'))`; plus the startup module `x ↦ ⟨x, x⟩`
   (`Turing.FinTM.computesFunInTime_pairDup`) and a two-state copier that puts the native
   input on tape 0 first.
3. *Gluing.* Each module is converted into a first-halting source (a release flag stops it one
   silent step after its first positive exit), padded to the common tape count, and embedded
   into one finite host through the forwarding transformer `Turing.emitAction`; the host's own
   control has three fresh states — the loop **anchor** (never a module-internal state), a
   **branch** state reading the verdict cell of tape 0, and a **halt** state. Modules return
   to fixed host states: copier → startup install → anchor; verdict → branch; branch → payload
   emit (verdict `true`) or step install (verdict `false`); payload emit → halt; step → anchor.
4. *Budgets.* All requests are state words of length at most `Q n + 4` with
   `Q n = 2n + 2 + P n`; every module's polynomial budget on its argument is majorised by one
   common `A · (Q n + 5)^D`, which also pays for the fuel machine `x ↦ Nat.bits (R|x|)`
   (`Complexity.polyTimeComputable_unaryPoly R` composed with
   `Turing.FinTM.computesFunInTime_lengthBits`, so that the `find?` range is exactly
   `R|x| + 1`). The loop combinator returns a machine within `c (T n + 1)(R n + 2)`, which
   `PolyExpr.eval_le` puts in the normal form of `Complexity.PolyTimeComputable`.

The clean modules and the finite host (steps 2–3: release-flag stop, padding, forwarding host,
first-halt cutting) are the public clean-module host
`TCSlib.Complexity.TuringMachine.Build.ModuleHost` (host H14 of `machine-library-design.md` §14);
its instance for this machine (the copier, the control table, the return states) lives in
`TCSlib.Complexity.Randomized.Build.IterateFindHost`.
This file supplies the pure step, the FP functions of the modules, the budget arithmetic, and the
assembly through `Turing.FinTM.exists_loopFindTM`.

## Main definitions

* `Complexity.IterateFind.step` — the length-guarded step on the state word (definitionally
  `Complexity.guardedStep`).

## Main results

* `Complexity.IterateFind.computesFunInTime_find` — the finite machine with arbitrary
  numerical fuel supplied in binary, a chosen initial state, and an explicit polynomial
  per-round budget.
* `Complexity.IterateFind.polyTimeComputable_find` — the loop-level form of the repetition
  lemma: the first accepted orbit point's payload along the guarded orbit of `⟨x, x⟩` is
  polynomial-time computable.
* `Complexity.IterateFind.find?_congr_of_mem` — `List.find?` depends only on the predicate's
  values on the list (used to identify the guarded orbit with `g^[i] x`).
* `Complexity.IterateFind.find?_range_and_lt` — a search over `[0, L)` whose test also demands
  `i < N` is the search over `[0, N)`, for `N ≤ L`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Theorem 87.3; Algorithms 123.4 and 128.7.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### The guarded step on the state word and its FP pieces -/

/-- The length-guarded step on the state word `w = ⟨x, s⟩`: advance to `⟨x, g s⟩` if the new
orbit point fits the bound `P|x|`, else stay (DESIGN.md §2.6, step 1). This is definitionally
`Complexity.guardedStep g P x w`; it is restated here because this file is imported by the
file defining `guardedStep`. -/
def step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) : List Bool :=
  if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w

/-- The guarded step: `step g P x w = ⟨x, g (snd w)⟩` if `|g (snd w)| ≤ P|x|`, and `w`
otherwise. -/
theorem step_eq (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) :
    step g P x w =
      if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w :=
  rfl

/-- The loop invariant used by the machine: the state word *is* a pair `⟨x, s⟩` with
`|s| ≤ P|x|` (stronger than the pure `Complexity.LoopInv`, which also admits malformed
words; the machine needs the well-formedness to bound the word's length). -/
private def Inv (P : PolyExpr) (x w : List Bool) : Prop :=
  ∃ s, w = pairEncode x s ∧ s.length ≤ P.eval x.length

/-- The initial word `⟨x, x⟩` is admissible when `|x| ≤ P|x|`. -/
private theorem inv_init (P : PolyExpr) (x : List Bool) (h0 : x.length ≤ P.eval x.length) :
    Inv P x (pairEncode x x) :=
  ⟨x, rfl, h0⟩

/-- The invariant is closed under the guarded step (the guard keeps the word unchanged when
the new point would be too long). -/
private theorem inv_step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool)
    (h : Inv P x w) : Inv P x (step g P x w) := by
  obtain ⟨s, rfl, hs⟩ := h
  unfold step
  rw [pairSndD_pairEncode]
  split_ifs with hg
  · exact ⟨g s, rfl, hg⟩
  · exact ⟨s, rfl, hs⟩

/-- The length of an admissible state word is at most `2|x| + 2 + P|x|`. -/
private theorem inv_length (P : PolyExpr) (x w : List Bool) (h : Inv P x w) :
    w.length ≤ 2 * x.length + 2 + P.eval x.length := by
  obtain ⟨s, rfl, hs⟩ := h
  rw [length_pairEncode]
  omega

/-- The verdict word: `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell, since
`pairEncode [b] w = [b, b, false, true] ++ w`). -/
private def verdictWord (acc : List Bool → Bool) (w : List Bool) : List Bool :=
  pairEncode [acc (pairSndD w)] w

/-- The step on a verdict word: strip the verdict, then take the guarded step on the pair
`⟨x, s⟩` carried by the word, with `x` recovered from the word itself. -/
private def stepWord (g : List Bool → List Bool) (P : PolyExpr) (w' : List Bool) : List Bool :=
  if (g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length then
    pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w')))
  else pairSndD w'

/-- The payload of a verdict word: `out` of the orbit point `snd (snd w')`. -/
private def outWord (out : List Bool → List Bool) (w' : List Bool) : List Bool :=
  out (pairSndD (pairSndD w'))

/-- The first cell of a verdict word is the verdict. -/
private theorem verdictWord_head (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w)[0]? = some (acc (pairSndD w)) := by
  simp [verdictWord, pairEncode_eq]

/-- The length of a verdict word. -/
private theorem verdictWord_length (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w).length = w.length + 4 := by
  simp [verdictWord, length_pairEncode]
  omega

/-- On the verdict word of a pair `⟨x, s⟩`, `stepWord` is the guarded step. -/
private theorem stepWord_verdictWord (g : List Bool → List Bool) (P : PolyExpr)
    (acc : List Bool → Bool) (x s : List Bool) :
    stepWord g P (verdictWord acc (pairEncode x s)) = step g P x (pairEncode x s) := by
  simp [stepWord, verdictWord, step]

/-- On the verdict word of a pair, `outWord` is `out` of the orbit point. -/
private theorem outWord_verdictWord (out : List Bool → List Bool) (acc : List Bool → Bool)
    (x s : List Bool) : outWord out (verdictWord acc (pairEncode x s)) = out s := by
  simp [outWord, verdictWord]

/-- The verdict word is polynomial-time computable (`PolyTimeComputable.pairEncode` of the
test composed with the projection and the identity). -/
private theorem verdictWord_poly {acc : List Bool → Bool}
    (hacc : PolyTimeComputable fun s => [acc s]) : PolyTimeComputable (verdictWord acc) := by
  have h := (hacc.comp polyTimeComputable_pairSndD).pairEncode polyTimeComputable_id
  exact h

/-- The step on verdict words is polynomial-time computable.

**Proof sketch.** `Complexity.polyTimeComputable_ite`: the test
`|g (snd (snd w'))| ≤ P|fst (snd w')|` is `Complexity.polyTimeComputable_lenLe` on the pair
`⟨1^{P|fst (snd w')|}, g (snd (snd w'))⟩`, built with the unary evaluator
`Complexity.polyTimeComputable_unaryPoly P` and `PolyTimeComputable.pairEncode`; the `then`
branch is the pairing of the two projections (with `g`), the `else` branch the projection
`snd`; the Boolean test is identified with the propositional `if` by `decide_eq_true_eq`. -/
private theorem stepWord_poly {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (P : PolyExpr) : PolyTimeComputable (stepWord g P) := by
  have hs2 : PolyTimeComputable fun w' => pairSndD (pairSndD w') :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hf1 : PolyTimeComputable fun w' => pairFstD (pairSndD w') :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hgg : PolyTimeComputable fun w' => g (pairSndD (pairSndD w')) := hg.comp hs2
  have hun : PolyTimeComputable fun w' =>
      List.replicate (P.eval (pairFstD (pairSndD w')).length) true :=
    (polyTimeComputable_unaryPoly P).comp hf1
  have htest : PolyTimeComputable fun w' =>
      [decide ((g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length)] := by
    have h := polyTimeComputable_lenLe.comp (hun.pairEncode hgg)
    convert h using 1
    funext w'
    simp
  have hthen : PolyTimeComputable fun w' =>
      pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w'))) := hf1.pairEncode hgg
  have h := polyTimeComputable_ite htest hthen polyTimeComputable_pairSndD
  convert h using 1
  funext w'
  simp [stepWord]

/-- The payload map on verdict words is polynomial-time computable. -/
private theorem outWord_poly {out : List Bool → List Bool} (hout : PolyTimeComputable out) :
    PolyTimeComputable (outWord out) :=
  hout.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The duplication `x ↦ ⟨x, x⟩` is polynomial-time computable. -/
private theorem dupWord_poly : PolyTimeComputable fun x => pairEncode x x :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup

/-! ### Assembly -/

/-- `List.find?` depends only on the values of the predicate on the list's elements. -/
theorem find?_congr_of_mem {α : Type*} {p q : α → Bool} :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = q a := h a (List.mem_cons_self ..)
    by_cases hq : q a = true
    · rw [List.find?_cons_of_pos (by rw [ha]; exact hq), List.find?_cons_of_pos hq]
    · rw [List.find?_cons_of_neg (by rw [ha]; exact hq), List.find?_cons_of_neg hq]
      exact find?_congr_of_mem l (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- **A bounded search is a search over a shorter range**: for `N ≤ L`, searching `[0, L)` for
the first `i` with `i < N` and `p i` is searching `[0, N)` for the first `i` with `p i`:
`(List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p`.

**Proof sketch.** Write `L = N + d` (`List.range_add`, `List.find?_append`). On `[0, N)` the guard
`i < N` holds, so the two predicates agree (`find?_congr_of_mem`). On the shifted tail `N + [0, d)`
it fails, so that search is `none` (`List.find?_eq_none`), and `o <|> none = o`. -/
theorem find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
  rw [List.range_add, List.find?_append,
    find?_congr_of_mem _ (fun i hi => by rw [decide_eq_true (List.mem_range.1 hi), Bool.true_and])]
  have hnone : (List.map (fun x => N + x) (List.range d)).find?
      (fun i => decide (i < N) && p i) = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    rw [decide_eq_false (by omega), Bool.false_and]
    exact Bool.false_ne_true
  rw [hnone, Option.or_none]

/-- The final budget arithmetic: the loop combinator's bound `c (T n + 1)(R n + 2)` with
`T n = A (2n + 2 + P n + 5)^D` is in the normal form `C (n + 1)^e` once `P` and `R` are
majorised by `CP (n+1)^cP` and `CR (n+1)^cR`.

**Proof sketch.** `2n + 7 + P n ≤ (CP + 7)(n+1)^{cP+1}` (both `7(n+1)` and `CP (n+1)^{cP}`
are at most the corresponding multiples of `(n+1)^{cP+1}`); raise to the `D`-th power
(`Nat.pow_le_pow_left`, `Nat.mul_pow`, `Nat.pow_mul`), absorb the `+ 1` with
`1 ≤ (n+1)^{(cP+1)D}`, bound `R n + 2 ≤ (CR + 2)(n+1)^{cR}` likewise, and multiply
(`Nat.mul_le_mul`, `Nat.pow_add`). -/
private lemma final_bound (c A D CP cP CR cR n Pn Rn : ℕ)
    (hP : Pn ≤ CP * (n + 1) ^ cP) (hR : Rn ≤ CR * (n + 1) ^ cR) :
    c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2) ≤
      c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have h1 : 2 * n + 2 + Pn + 5 ≤ (CP + 7) * (n + 1) ^ (cP + 1) := by
    have ha : n + 1 ≤ (n + 1) ^ (cP + 1) := by
      simpa using Nat.pow_le_pow_right hpos (show 1 ≤ cP + 1 by omega)
    have hb : (n + 1) ^ cP ≤ (n + 1) ^ (cP + 1) := Nat.pow_le_pow_right hpos (by omega)
    have hc := Nat.mul_le_mul_left CP hb
    calc 2 * n + 2 + Pn + 5 ≤ 7 * (n + 1) + CP * (n + 1) ^ cP := by omega
      _ ≤ 7 * (n + 1) ^ (cP + 1) + CP * (n + 1) ^ (cP + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 7 ha) hc
      _ = (CP + 7) * (n + 1) ^ (cP + 1) := by ring
  have h2 : (2 * n + 2 + Pn + 5) ^ D ≤ (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by
    calc (2 * n + 2 + Pn + 5) ^ D ≤ ((CP + 7) * (n + 1) ^ (cP + 1)) ^ D :=
          Nat.pow_le_pow_left h1 D
      _ = (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  have hone : 1 ≤ (n + 1) ^ ((cP + 1) * D) := Nat.one_le_pow _ _ hpos
  have h3 : A * (2 * n + 2 + Pn + 5) ^ D + 1 ≤
      (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by
    calc A * (2 * n + 2 + Pn + 5) ^ D + 1
        ≤ A * ((CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D)) + (n + 1) ^ ((cP + 1) * D) :=
          Nat.add_le_add (Nat.mul_le_mul_left A h2) hone
      _ = (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by ring
  have h4 : Rn + 2 ≤ (CR + 2) * (n + 1) ^ cR := by
    have hone' : 1 ≤ (n + 1) ^ cR := Nat.one_le_pow _ _ hpos
    calc Rn + 2 ≤ CR * (n + 1) ^ cR + 2 * (n + 1) ^ cR := by omega
      _ = (CR + 2) * (n + 1) ^ cR := by ring
  calc c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2)
      ≤ c * ((A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D)) * ((CR + 2) * (n + 1) ^ cR) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c h3) h4
    _ = c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
        rw [Nat.pow_add]; ring

/-- **The loop-level repetition lemma.** Let `g` be a polynomial-time step, `acc` a
polynomial-time test, `out` a polynomial-time payload map, and `R, P` syntactic polynomials
with `|g^[i] x| ≤ P|x|` for `i ≤ R|x|`. Then the function returning `out` of the orbit point
of the first index `i ≤ R|x|` at which `acc` accepts the second component of the `i`-fold
guarded step `Complexity.IterateFind.step g P x` from `⟨x, x⟩` (`[]` if none) is
polynomial-time computable. This is the machine behind
`Complexity.polyTimeComputable_iterateFind` [PS10, Algorithm 38.5, Theorem 35.1]; the pure
identification of the guarded orbit with `g^[i] x` is done there.

**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` for the host `hostTM` (the
clean-module host `Turing.ModuleHost.hostTM` with the control table `hostCtrl`) over the five
clean modules (the copier, and `Turing.ModuleHost.clean_install`/`clean_emit` of
`x ↦ ⟨x, x⟩`, `verdictWord acc`, `stepWord g P`, `outWord out`), with anchor `inl 0`,
invariant `Inv P`,
step `step g P`, acceptance `acc ∘ snd`, payload `out ∘ snd`, start word `⟨x, x⟩`. The fuel
machine computes `Nat.bits (R|x|)` (`polyTimeComputable_unaryPoly R` composed with
`computesFunInTime_lengthBits`). `hstart`: the copier (`copy_clean`, `ModuleHost.host_call`)
then the startup install (`ModuleHost.host_clean`) reach the anchor seam with `⟨x, x⟩` in
`2|x| + 2 + t_S` steps
with no earlier anchor visit. `hround`: from the anchor seam with an admissible word `⟨x, s⟩`,
the dispatch step, the verdict call, the branch step (`host_branch`), then either the payload
call and the halt step (`host_halt`) — state `none`, output `out s` — or the step call
returning to the anchor seam with `step g P x ⟨x, s⟩` (`stepWord_verdictWord`); the anchor
guard is `ModuleHost.guard_add` over the segments. All requests have length at most
`2|x| + 2 + P|x| + 4`, so every call fits the common budget `T n = A (2n + 2 + P n + 5)^D`
(`ModuleHost.request_budget`), and
`final_bound` puts the combinator's bound `c (T n + 1)(R n + 2)` in normal form. -/
theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find?
          (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x x)))) with
      | some i => out (pairSndD ((step g P x)^[i] (pairEncode x x)))
      | none => [] := by
  obtain ⟨S, aS, dS, hS⟩ := ModuleHost.clean_install dupWord_poly
  obtain ⟨V, aV, dV, hV⟩ := ModuleHost.clean_install (verdictWord_poly hacc)
  obtain ⟨I, aI, dI, hI⟩ := ModuleHost.clean_install (stepWord_poly hg P)
  obtain ⟨E, aE, dE, hE⟩ := ModuleHost.clean_emit (outWord_poly hout)
  have hbits : PolyTimeComputable fun x => Nat.bits (R.eval x.length) := by
    have h := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
      (polyTimeComputable_unaryPoly R)
    convert h using 1
    funext x
    simp
  obtain ⟨F, aF, dF, hF⟩ := (polyTimeComputable_iff _).1 hbits
  let M : Fin 5 → FinTM Bool := fun i => match i.val with
    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
  let K := S.k + V.k + I.k + E.k
  have hk : ∀ i, (M i).k ≤ K + 1 := by
    intro i; fin_cases i <;> simp [M, K, copyTM_k] <;> omega
  let H := hostTM M K hk
  let anchor : H.State := .inl 0
  have hclean := ModuleHost.host_clean M (K + 1) hk (hostCtrl M K) (hostRet M)
    (ModuleHost.entry M 0)
  let D := dS + dV + dI + dE + dF + 1
  let A := aS + aV + aI + aE + aF + 5
  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
      (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t = Cfg.ofWords anchor (stateWord H.k (pairEncode x x)) := by
    intro x
    obtain ⟨hcg, hce⟩ := copy_clean x
    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call M (K + 1) hk (hostCtrl M K) (hostRet M)
      (ModuleHost.entry M 0) 0 (by simp [M, copyTM_k]) x [] x [] [] (0 : Fin 2)
      (2 * x.length + 2) hcg (by simpa using hce)
    have hi : H.tm.initCfg x = Cfg.ofWords (ModuleHost.entry M 0) (stateWord (K + 1) []) := by
      refine Cfg.ext ?_ rfl ?_ rfl rfl
      · exact congrArg some (ModuleHost.hostTM_tm_q₀ M (K + 1) hk (hostCtrl M K) (hostRet M)
          (ModuleHost.entry M 0))
      funext i z
      simp [MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes,
          Cfg.init_workTapePos, Cfg.init_output, Cfg.ofWords_def, stateWord_eq]
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 0) (stateWord (K + 1) []))
      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
    rw [hostRet_zero] at hcEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := hclean 1
      (fun x => pairEncode x x) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
      (by simpa [M] using hS) x x []
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 1) (stateWord (K + 1) x))
      ts = Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x x)) at hsEnd
    rw [hostRet_one] at hsEnd
    have hsB := ModuleHost.request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact ModuleHost.guard_add H.tm anchor _ _ _ ts (fun v hv => hcGuard v hv 0) hcEnd
        (fun v hv => hsGuard v hv 0)
    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
      rfl
  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ t', 0 < t' → t' < t →
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
          ≠ some anchor) ∧
      if acc (pairSndD w) then
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
          out (pairSndD w)
      else
        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
    intro x w hw
    obtain ⟨s, rfl, hs⟩ := hw
    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
      rw [length_pairEncode]; omega
    have hw'len : (verdictWord acc (pairEncode x s)).length =
        (pairEncode x s).length + 4 := verdictWord_length acc _
    have hpow' := hpow x.length
    -- the dispatch, the verdict call, the branch
    have hdisp := host_dispatch M K hk x (pairEncode x s)
    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := hclean 2 (verdictWord acc)
      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2) (stateWord (K + 1)
      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s))) at hvEnd
    rw [hostRet_two] at hvEnd
    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
      (by rw [verdictWord_head, pairSndD_pairEncode])
    have hvB := ModuleHost.request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
        Cfg.ofWords (ModuleHost.entry M (if acc s then 4 else 3))
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
      refine ModuleHost.guard_add H.tm anchor _ _ tv 1 (fun v hv => hvGuard v hv 0) hvEnd ?_
      intro v hv
      have hv0 : v = 0 := by omega
      subst hv0
      simp [Cfg.ofWords_def, anchor]
    by_cases hb : acc s = true
    · -- accepting round: the payload call, then the halt
      rw [if_pos hb] at hseg
      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := hclean 4 id (outWord out)
        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 4) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
          (verdictWord acc (pairEncode x s))) with
            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
      rw [hostRet_four, List.nil_append, outWord_verdictWord] at heEnd
      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
      have heB := ModuleHost.request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
          {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1)
            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
        refine ModuleHost.guard_add H.tm anchor _ {Cfg.ofWords (input := x)
          (.inl 2 : ModuleHost.State (Fin 3) M)
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
          (tv + 1 + te) 1 ?_ ?_ ?_
        · exact ModuleHost.guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg
            (fun v hv => heGuard v hv 0)
        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
        · intro v hv
          have hv0 : v = 0 := by omega
          subst hv0
          simp [Cfg.ofWords_def, anchor]
      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_pos hb]
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
        exact ⟨rfl, rfl⟩
    · -- advancing round: the step call returns to the anchor
      rw [if_neg hb] at hseg
      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := hclean 3 (stepWord g P)
        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 3) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
      rw [hostRet_three, stepWord_verdictWord] at hiEnd
      have hiB := ModuleHost.request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
        ModuleHost.guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg
          (fun v hv => hiGuard v hv 0)
      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_neg hb]
        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + ti + 1) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R.eval x.length)) T := by
    intro x
    apply (hF x).mono
    have h := ModuleHost.request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    dsimp only [T, A, pow]
    simp only [Nat.add_mul]
    dsimp only [pow] at hp
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x x)
    (fun n => R.eval n) T hFuel
    (fun x => inv_init P x (by simpa using horbit x 0 (Nat.zero_le _)))
    (fun x w h => inv_step g P x w h) hstart hround
  obtain ⟨CP, cP, hCP⟩ := P.eval_le
  obtain ⟨CR, cR, hCR⟩ := R.eval_le
  refine ⟨L, c * (A * (CP + 7) ^ D + 1) * (CR + 2), (cP + 1) * D + cR, fun x => (hL x).mono ?_⟩
  exact final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length)
    (hCP _) (hCR _)

/-- A guarded search with arbitrary numerical fuel `R` and initial state `init` has a
finite machine computing the first accepted payload (or `[]` on exhaustion) within
`c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)` steps, for constants
`c, A, D`. The step `g`, acceptance word `[acc s]`, payload `out s`, and initial state are
polynomial-time computable; `|init x| ≤ P.eval |x|`. A fuel machine computes
`Nat.bits (R |x|)` within `aF * (|x| + 1) ^ dF`. The displayed common per-round budget
`T n = A * (2 * n + 2 + P.eval n + 5) ^ D` is polynomial; no polynomial bound on `R`
is assumed. [AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4]

**Proof sketch.** Reuse the invariant and guarded-step modules of
`polyTimeComputable_find`, installing `⟨x, init x⟩` at startup. The size guard preserves
the invariant under every step, including steps after the search terminates. Install the
verdict and step modules, emit the payload, and compose their clean calls through the
same five-module host. A common polynomial budget pays for startup, each round, and the
given binary fuel machine. The result-bearing loop combinator then supplies the stated
bound directly, without using the polynomial-fuel normal form `final_bound`. -/
theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    {init : List Bool → List Bool} (hinit : PolyTimeComputable init)
    (R : ℕ → ℕ) (P : PolyExpr)
    (hbound : ∀ x : List Bool, (init x).length ≤ P.eval x.length)
    (F : FinTM Bool) (aF dF : ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length))
      (fun n => aF * (n + 1) ^ dF)) :
    ∃ (M : FinTM Bool) (c A D : ℕ),
      M.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) with
          | some i => out (pairSndD ((step g P x)^[i] (pairEncode x (init x))))
          | none => [])
        (fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)) := by
  -- Build the four clean calls and their shared host.
  obtain ⟨S, aS, dS, hS⟩ := ModuleHost.clean_install (polyTimeComputable_id.pairEncode hinit)
  obtain ⟨V, aV, dV, hV⟩ := ModuleHost.clean_install (verdictWord_poly hacc)
  obtain ⟨I, aI, dI, hI⟩ := ModuleHost.clean_install (stepWord_poly hg P)
  obtain ⟨E, aE, dE, hE⟩ := ModuleHost.clean_emit (outWord_poly hout)
  let M : Fin 5 → FinTM Bool := fun i => match i.val with
    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
  let K := S.k + V.k + I.k + E.k
  have hk : ∀ i, (M i).k ≤ K + 1 := by
    intro i; fin_cases i <;> simp [M, K, copyTM_k] <;> omega
  let H := hostTM M K hk
  let anchor : H.State := .inl 0
  have hclean := ModuleHost.host_clean M (K + 1) hk (hostCtrl M K) (hostRet M)
    (ModuleHost.entry M 0)
  let D := dS + dV + dI + dE + dF + 1
  let A := aS + aV + aI + aE + aF + 5
  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
      (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
  -- Startup copies the input and installs the chosen initial state.
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord H.k (pairEncode x (init x))) := by
    intro x
    obtain ⟨hcg, hce⟩ := copy_clean x
    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call M (K + 1) hk (hostCtrl M K) (hostRet M)
      (ModuleHost.entry M 0) 0 (by simp [M, copyTM_k]) x [] x [] [] (0 : Fin 2)
      (2 * x.length + 2) hcg (by simpa using hce)
    have hi : H.tm.initCfg x = Cfg.ofWords (ModuleHost.entry M 0) (stateWord (K + 1) []) := by
      refine Cfg.ext ?_ rfl ?_ rfl rfl
      · exact congrArg some (ModuleHost.hostTM_tm_q₀ M (K + 1) hk (hostCtrl M K) (hostRet M)
          (ModuleHost.entry M 0))
      funext i z
      simp [MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes,
          Cfg.init_workTapePos, Cfg.init_output, Cfg.ofWords_def, stateWord_eq]
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 0) (stateWord (K + 1) []))
      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
    rw [hostRet_zero] at hcEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := hclean 1
      (fun x => pairEncode x (init x)) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
      (by simpa [M] using hS) x x []
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 1) (stateWord (K + 1) x))
      ts = Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x (init x))) at hsEnd
    rw [hostRet_one] at hsEnd
    have hsB := ModuleHost.request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact ModuleHost.guard_add H.tm anchor _ _ _ ts (fun v hv => hcGuard v hv 0) hcEnd
        (fun v hv => hsGuard v hv 0)
    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
      rfl
  -- A positive round either emits its payload or advances the guarded state.
  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ t', 0 < t' → t' < t →
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
          ≠ some anchor) ∧
      if acc (pairSndD w) then
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
          out (pairSndD w)
      else
        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
    intro x w hw
    obtain ⟨s, rfl, hs⟩ := hw
    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
      rw [length_pairEncode]; omega
    have hw'len : (verdictWord acc (pairEncode x s)).length =
        (pairEncode x s).length + 4 := verdictWord_length acc _
    have hpow' := hpow x.length
    -- the dispatch, the verdict call, the branch
    have hdisp := host_dispatch M K hk x (pairEncode x s)
    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := hclean 2 (verdictWord acc)
      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2) (stateWord (K + 1)
      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s))) at hvEnd
    rw [hostRet_two] at hvEnd
    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
      (by rw [verdictWord_head, pairSndD_pairEncode])
    have hvB := ModuleHost.request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
        Cfg.ofWords (ModuleHost.entry M (if acc s then 4 else 3))
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
      refine ModuleHost.guard_add H.tm anchor _ _ tv 1 (fun v hv => hvGuard v hv 0) hvEnd ?_
      intro v hv
      have hv0 : v = 0 := by omega
      subst hv0
      simp [Cfg.ofWords_def, anchor]
    by_cases hb : acc s = true
    · -- accepting round: the payload call, then the halt
      rw [if_pos hb] at hseg
      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := hclean 4 id (outWord out)
        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 4) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
          (verdictWord acc (pairEncode x s))) with
            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
      rw [hostRet_four, List.nil_append, outWord_verdictWord] at heEnd
      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
      have heB := ModuleHost.request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
          {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1)
            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
        refine ModuleHost.guard_add H.tm anchor _ {Cfg.ofWords (input := x)
          (.inl 2 : ModuleHost.State (Fin 3) M)
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
          (tv + 1 + te) 1 ?_ ?_ ?_
        · exact ModuleHost.guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg
            (fun v hv => heGuard v hv 0)
        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
        · intro v hv
          have hv0 : v = 0 := by omega
          subst hv0
          simp [Cfg.ofWords_def, anchor]
      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_pos hb]
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
        exact ⟨rfl, rfl⟩
    · -- advancing round: the step call returns to the anchor
      rw [if_neg hb] at hseg
      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := hclean 3 (stepWord g P)
        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 3) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
      rw [hostRet_three, stepWord_verdictWord] at hiEnd
      have hiB := ModuleHost.request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
        ModuleHost.guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg
          (fun v hv => hiGuard v hv 0)
      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_neg hb]
        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + ti + 1) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
  -- Pay for binary fuel in the same polynomial budget, then apply the host.
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T := by
    apply (FinTM.computesFunInTime_iff _ _ _).2
    intro x
    apply ((FinTM.computesFunInTime_iff _ _ _).1 hF x).mono
    have h := ModuleHost.request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    dsimp only [T, A, pow]
    simp only [Nat.add_mul]
    dsimp only [pow] at hp
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x (init x))
    R T hFuel (fun x => ⟨init x, rfl, hbound x⟩)
    (fun x w h => inv_step g P x w h) hstart hround
  refine ⟨L, c, A, D, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
  have hx := (FinTM.computesFunInTime_iff _ _ _).mp hL x
  simpa only [T, pow] using hx

end Complexity.IterateFind

## ===== TCSlib/Complexity/Randomized/Classes.lean =====

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The randomized complexity classes BPP, RP, coRP, ZPP

Verifier-style definitions of Arora–Barak's randomized complexity classes,
following the certificate view of [AB09, Def 7.3]: a language is in a
randomized class when some efficient two-input predicate `M(x, r)`, run on the
input `x` and a uniformly random string `r` of polynomially-bounded length,
decides membership with the class's acceptance-probability profile.

## Main definitions

* `Randomized.randProb` — the probability of an event over a uniform random
  string of a given length, as a rational counting ratio.
* `Randomized.polyLen` — the canonical polynomial length schedule
  `n ↦ a·(n+1)^k` for random strings.
* `Randomized.VerifierModel` — an abstract *efficiency notion* standing in for
  "polynomial-time Turing machine" (see **Deviations** below).
* `Randomized.InBPP` — [AB09, Def 7.3] (equivalently Def 7.2 via the
  certificate view).
* `Randomized.InRP`, `Randomized.InCoRP` — [AB09, Def 7.6] and the remark
  following it.
* `Randomized.InZPP` — [AB09, Def 7.7], in the zero-error "abort"
  formulation (see **Deviations**).
* `Randomized.raceVerifier`, `Randomized.majorityVerifier` — the two verifier
  constructions used by Theorems 7.8 and 7.10.

## Main results

* `Randomized.inZPP_iff_inRP_and_inCoRP` — `ZPP = RP ∩ coRP` [AB09, Thm 7.8].
* `Randomized.InBPP.compl` — `BPP = coBPP` (used by [AB09, Thm 7.15]).
* `Randomized.bpp_error_reduction` — error reduction [AB09, Thm 7.10].
* `Randomized.inBPPWeak_iff_inBPP` — `BPP_{n^{-c}} = BPP` [AB09, Lem 7.9].

## Deviations from the source

* **Machine model.** [AB09] defines these classes with polynomial-time Turing
  machines.  Per the repository's agreed scope, we use the certificate view of
  [AB09, Def 7.3] — predicates over inputs and random strings — and replace
  "`M` is a polynomial-time TM" by membership in an abstract
  `VerifierModel` `E`, a predicate on verifiers.  Every class and theorem is
  parametrized by `E`.  The closure properties that [AB09]'s proofs use
  (building the race, majority, complement, and projection verifiers out of
  given ones) are stated as explicit named hypotheses (`ClosedUnder…`), all of
  which hold for the intended instantiation "computable in polynomial time".
  That instantiation is `Randomized.polyTimeModel` (`Randomized/PolyTimeModel.lean`),
  which discharges the closure hypotheses; `Randomized/BPPAmplify.lean` instantiates
  Lemma 7.9 and Theorem 7.10 there and transfers them to polynomial-time PTMs.
* **Length schedules.** [AB09, Def 7.3] draws `r ∈ {0,1}^{p(|x|)}` for a
  polynomial `p`.  We fix the canonical schedule `polyLen a k : n ↦ a·(n+1)^k`
  (existentially quantified over `a, k : ℕ`) rather than an arbitrary
  `p : ℕ → ℕ` with a polynomial bound: an arbitrary bounded `p` need not be
  computable and could smuggle undecidable information through the schedule
  itself.  Every polynomial is dominated by some `polyLen a k`, and a verifier
  can ignore padding bits, so the class is unchanged.
* **Probability.** `Pr_{r ∈ {0,1}^m}` is the counting ratio
  `#{r : accepted}/2^m` valued in `ℚ`; random strings of length `m` are
  `Fin m → Bool`, passed to verifiers as lists via `List.ofFn`.
* **ZPP.** [AB09, Def 7.7] defines `ZPP` by expected running time of a
  zero-error machine.  Expected time is not expressible for abstract
  predicates, so we use the standard equivalent "Las Vegas" formulation: a
  verifier with values in `Option Bool` that is never wrong and outputs `none`
  ("don't know") with probability at most `1/2`.  [AB09, §7.4.2] sketches the
  equivalence of expected-time and worst-case formulations (truncation via
  Markov's inequality).
* **The weak threshold of Lemma 7.9.** The book's success threshold
  `1/2 + |x|^{-c}` exceeds `1` for `|x| ≤ 1`, making the literal class
  `BPP_{n^{-c}}` empty; we require advantage `min (1/6) ((|x|+1)^{-c})`
  instead, which for `c ≥ 1` agrees with the book's (up to the `n+1` shift) for
  `|x| ≥ 5` and makes `BPP ⊆ BPP_{n^{-c}}` hold as the book intends.
* The constant `2/3` follows [AB09, Defs 7.2/7.6]; `1/2` in `InZPP` is the
  conventional choice (any constant in `(0,1)` gives the same class, by the
  same repetition argument as [AB09, §7.4.1]).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

/-- The probability, over a uniformly random string `r ∈ {0,1}^m`, that the
event `A` holds of `r` (as a list): the counting ratio `#{r : A r}/2^m`.
[AB09, Def 7.3: "`Pr_{r ∈_R {0,1}^{p(|x|)}}`"] -/
def randProb (m : ℕ) (A : List Bool → Prop) [DecidablePred A] : ℚ :=
  ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) / 2 ^ m

/-- The probability of an event is the cardinality of its accepted bit tuples divided
by the number `2 ^ m` of all length-`m` bit tuples. -/
theorem randProb_eq (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    randProb m A =
      ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) / 2 ^ m := rfl

/-- Two events that agree on every random string have the same
probability. -/
theorem randProb_congr {m : ℕ} {A B : List Bool → Prop} [DecidablePred A]
    [DecidablePred B]
    (h : ∀ r : Fin m → Bool, A (List.ofFn r) ↔ B (List.ofFn r)) :
    randProb m A = randProb m B := by
  unfold randProb
  rw [Finset.filter_congr fun r _ => h r]

/-- Probabilities are nonnegative. -/
theorem randProb_nonneg {m : ℕ} {A : List Bool → Prop} [DecidablePred A] :
    0 ≤ randProb m A := by
  unfold randProb
  positivity

/-- There are `2^m` random strings of length `m`. -/
theorem card_univ_bitstrings (m : ℕ) :
    (univ : Finset (Fin m → Bool)).card = 2 ^ m := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Probabilities are at most one. -/
theorem randProb_le_one {m : ℕ} {A : List Bool → Prop} [DecidablePred A] :
    randProb m A ≤ 1 := by
  unfold randProb
  rw [div_le_one (by positivity)]
  calc ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ)
      ≤ ((univ : Finset (Fin m → Bool)).card : ℚ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = 2 ^ m := by rw [card_univ_bitstrings]; push_cast; rfl

/-- Probability is monotone in the event. -/
theorem randProb_mono {m : ℕ} {A B : List Bool → Prop} [DecidablePred A]
    [DecidablePred B]
    (h : ∀ r : Fin m → Bool, A (List.ofFn r) → B (List.ofFn r)) :
    randProb m A ≤ randProb m B := by
  unfold randProb
  gcongr
  exact h _

/-- Complement rule: `Pr[¬A] = 1 − Pr[A]`. -/
theorem randProb_not {m : ℕ} (A : List Bool → Prop) [DecidablePred A] :
    randProb m (fun l => ¬ A l) = 1 - randProb m A := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin m → Bool))) (p := fun r => A (List.ofFn r))
  rw [card_univ_bitstrings] at hsplit
  have h2 : ((2 : ℚ) ^ m) ≠ 0 := by positivity
  have hcast : ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ)
      = 2 ^ m - ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) := by
    have h3 : ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ)
        + ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ)
        = 2 ^ m := by
      exact_mod_cast hsplit
    linarith
  show ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ) / 2 ^ m
      = 1 - randProb m A
  unfold randProb
  rw [hcast, sub_div, div_self h2]

/-- The certain event has probability one. -/
theorem randProb_true {m : ℕ} : randProb m (fun _ => True) = 1 := by
  unfold randProb
  rw [Finset.filter_true_of_mem fun _ _ => trivial, card_univ_bitstrings]
  push_cast
  exact div_self (by positivity)

/-- Every list of length `m` arises from a tuple of `m` bits. -/
theorem exists_ofFn_eq {l : List Bool} {m : ℕ} (h : l.length = m) :
    ∃ r : Fin m → Bool, l = List.ofFn r := by
  refine ⟨fun i => l[(i : ℕ)]'(by omega), ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp

/-- **Independence of disjoint segments**: if the event is a conjunction of a
condition on the first `m₁` bits and a condition on the remaining `m₂` bits,
the probability factors.

**Proof sketch.** Combine the denominators by `2^{m₁+m₂} = 2^{m₁}·2^{m₂}`;
the numerators then agree via `Finset.card_bij` with the bijection
`(u, v) ↦ Fin.append u v` from pairs of accepted strings to accepted
concatenations.  `List.ofFn_fin_append` together with `List.take_left'` /
`List.drop_left'` matches the events on each side, injectivity is that of
`Fin.appendEquiv`, and surjectivity splits an arbitrary `r` by
`Fin.append_castAdd_natAdd`. -/
theorem randProb_split (m₁ m₂ : ℕ) (A B : List Bool → Prop)
    [DecidablePred A] [DecidablePred B] :
    randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ B (r.drop m₁)) =
      randProb m₁ A * randProb m₂ B := by
  unfold randProb
  rw [div_mul_div_comm, ← pow_add, ← Nat.cast_mul]
  congr 2
  rw [← Finset.card_product]
  refine (Finset.card_bij (fun uv _ => Fin.append uv.1 uv.2) ?_ ?_ ?_).symm
  · rintro ⟨u, v⟩ huv
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at huv
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [List.ofFn_fin_append, List.take_left' (by simp)]
      exact huv.1.2
    · rw [List.ofFn_fin_append, List.drop_left' (by simp)]
      exact huv.2.2
  · intro uv huv uv' huv' h
    exact (Fin.appendEquiv m₁ m₂).injective (by exact h)
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hA, hB⟩ := hr
    have hdec : Fin.append (fun i => r (Fin.castAdd m₂ i))
        (fun i => r (Fin.natAdd m₁ i)) = r := Fin.append_castAdd_natAdd
    refine ⟨(fun i => r (Fin.castAdd m₂ i), fun i => r (Fin.natAdd m₁ i)),
      ?_, hdec⟩
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    rw [← hdec, List.ofFn_fin_append] at hA hB
    rw [List.take_left' (by simp)] at hA
    rw [List.drop_left' (by simp)] at hB
    exact ⟨⟨Finset.mem_univ _, hA⟩, Finset.mem_univ _, hB⟩

/-- A condition on only the first `m₁ ≤ m` bits has the same probability over
`m`-bit strings as over `m₁`-bit strings: padding bits are ignored. -/
theorem randProb_take {m₁ m : ℕ} (h : m₁ ≤ m) (A : List Bool → Prop)
    [DecidablePred A] :
    randProb m (fun r => A (r.take m₁)) = randProb m₁ A := by
  obtain ⟨m₂, rfl⟩ := Nat.exists_eq_add_of_le h
  calc randProb (m₁ + m₂) (fun r => A (r.take m₁))
      = randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ (fun _ => True) (r.drop m₁)) :=
        randProb_congr fun r => by simp
    _ = randProb m₁ A * randProb m₂ (fun _ => True) :=
        randProb_split m₁ m₂ A (fun _ => True)
    _ = randProb m₁ A := by rw [randProb_true, mul_one]

/-- The canonical polynomial length schedule `n ↦ a·(n+1)^k` for random
strings — a concrete, computable stand-in for [AB09, Def 7.3]'s "polynomial
`p`" (see the module docstring's **Deviations**: an arbitrary polynomially
*bounded* `ℕ → ℕ` need not be computable and would let the schedule itself
decide undecidable languages). -/
def polyLen (a k : ℕ) : ℕ → ℕ := fun n => a * (n + 1) ^ k

/-- The canonical polynomial length schedule at `n` is `a * (n + 1) ^ k`. -/
theorem polyLen_eq (a k n : ℕ) : polyLen a k n = a * (n + 1) ^ k := rfl

/-- An abstract *efficiency notion* for verifiers, standing in for
"polynomial-time Turing machine" in [AB09, Def 7.3] (see the module
docstring's **Deviations**).  `Eff M` reads "`M` is an efficient verifier";
verifiers are `Option Bool`-valued so that zero-error ("don't know") verifiers
and ordinary Boolean verifiers share one notion.  `EffTwoWitness N` is the
corresponding notion for predicates of an input and two witness strings, the
verifier format of `Σ₂`-statements (used by [AB09, Thm 7.15]).  The
polynomial-time instance is `Randomized.polyTimeModel`. -/
structure VerifierModel where
  /-- "`M` is an efficient (poly-time) verifier." -/
  Eff : (List Bool → List Bool → Option Bool) → Prop
  /-- "`N` is an efficient (poly-time) two-witness predicate." -/
  EffTwoWitness : (List Bool → List Bool → List Bool → Bool) → Prop

/-- A Boolean verifier, viewed as an `Option Bool`-valued one. -/
def boolVerifier (M : List Bool → List Bool → Bool) :
    List Bool → List Bool → Option Bool :=
  fun x r => some (M x r)

/-- The Boolean verifier viewed as an optional verifier returns `some (M x r)`. -/
theorem boolVerifier_apply (M : List Bool → List Bool → Bool) (x r : List Bool) :
    boolVerifier M x r = some (M x r) := rfl

variable (E : VerifierModel)

/-- `L ∈ BPP`: some efficient verifier `M` with polynomially-long randomness
decides `L` with two-sided error at most `1/3` — for every input `x`,
`Pr_{r ∈ {0,1}^{p(|x|)}}[M(x,r) = L(x)] ≥ 2/3`, where `p = polyLen a k`.
[AB09, Def 7.3] (the certificate form of [AB09, Def 7.2]). -/
def InBPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)

/-- Membership of `L` in `BPP` for the verifier model `E`, unfolded [AB09, Definition 7.3]:
`InBPP E L ↔ ∃ (M : List Bool → List Bool → Bool) (a k : ℕ), E.Eff (boolVerifier M) ∧
∀ x : List Bool, (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
(x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)`. -/
theorem inBPP_iff (L : Language Bool) :
    InBPP E L ↔ ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
      E.Eff (boolVerifier M) ∧
      ∀ x : List Bool,
        (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
        (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false) :=
  Iff.rfl

/-- `L ∈ RP`: one-sided error — inputs in `L` are accepted with probability
at least `2/3`, inputs outside `L` are *never* accepted.  [AB09, Def 7.6] -/
def InRP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) = false)

/-- `L ∈ coRP` iff its complement is in `RP`: one-sided error in the other
direction.  [AB09, §7.3: "`coRP = {L | L̄ ∈ RP}`"] -/
def InCoRP (L : Language Bool) : Prop :=
  InRP E Lᶜ

/-- `L ∈ ZPP`: some efficient zero-error verifier decides `L` — it may output
`none` ("don't know") with probability at most `1/2`, but whenever it outputs
an answer, the answer is correct.  [AB09, Def 7.7], in the equivalent
Las Vegas formulation (see the module docstring's **Deviations**). -/
def InZPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Option Bool) (a k : ℕ),
    E.Eff M ∧
    ∀ x : List Bool,
      (x ∈ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some false) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some true) ∧
      randProb (polyLen a k x.length) (fun r => M x r = none) ≤ 1/2

section Constructions

/-- The *race* of an `RP` verifier for `L` and an `RP` verifier for `Lᶜ` on
split randomness: on `r = r₁ ++ r₂`, answer `some true` if `M₁` accepts `r₁`,
else `some false` if `M₂` accepts `r₂`, else `none`.  The construction behind
`RP ∩ coRP ⊆ ZPP` in [AB09, Thm 7.8]. -/
def raceVerifier (M₁ M₂ : List Bool → List Bool → Bool) (p₁ : ℕ → ℕ) :
    List Bool → List Bool → Option Bool := fun x r =>
  if M₁ x (r.take (p₁ x.length)) then some true
  else if M₂ x (r.drop (p₁ x.length)) then some false
  else none

/-- The defining equation of `raceVerifier`: `raceVerifier M₁ M₂ p₁ = fun x r => if M₁ x
(r.take (p₁ x.length)) then some true else if M₂ x (r.drop (p₁ x.length)) then some false else
none`. -/
theorem raceVerifier_def (M₁ M₂ : List Bool → List Bool → Bool) (p₁ : ℕ → ℕ) :
    raceVerifier M₁ M₂ p₁ =
      (fun x r =>
        if M₁ x (r.take (p₁ x.length)) then some true
        else if M₂ x (r.drop (p₁ x.length)) then some false
        else none :
        List Bool → List Bool → Option Bool) := rfl

/-- The `k`-fold repetition of a verifier with majority vote, on randomness
split into `k` blocks of length `p(|x|)`: the construction behind error
reduction [AB09, Thm 7.10]. -/
def majorityVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  let n := x.length
  let votes := (List.range (k n)).countP fun i =>
    M x ((r.drop (i * p n)).take (p n))
  k n < 2 * votes

/-- The defining equation of `majorityVerifier`: with `n = |x|`, `majorityVerifier M p k x r`
holds when `k n < 2 · votes`, `votes` the number of the `k n` blocks
`(r.drop (i * p n)).take (p n)` that `M x` accepts. -/
theorem majorityVerifier_def (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    majorityVerifier M p k =
      (fun x r =>
        let n := x.length
        let votes := (List.range (k n)).countP fun i =>
          M x ((r.drop (i * p n)).take (p n))
        k n < 2 * votes :
        List Bool → List Bool → Bool) := rfl

/-- `E` can race two of its Boolean verifiers on a polynomial split point
(closure of polynomial time under running two machines on split
randomness). -/
def ClosedUnderRace : Prop :=
  ∀ M₁ M₂ a k, E.Eff (boolVerifier M₁) → E.Eff (boolVerifier M₂) →
    E.Eff (raceVerifier M₁ M₂ (polyLen a k))

/-- The defining property of `ClosedUnderRace`: `E` races any two of its Boolean verifiers on a
polynomial split point. -/
theorem closedUnderRace_iff : ClosedUnderRace E ↔ ∀ M₁ M₂ a k, E.Eff (boolVerifier M₁) →
    E.Eff (boolVerifier M₂) → E.Eff (raceVerifier M₁ M₂ (polyLen a k)) :=
  Iff.rfl

/-- `E` can turn a zero-error verifier into the Boolean verifier answering
"did it output `some b`?" (closure of polynomial time under postprocessing
the output). -/
def ClosedUnderAnswerIs : Prop :=
  ∀ M b, E.Eff M →
    E.Eff (boolVerifier fun x r => M x r = some b)

/-- The defining property of `ClosedUnderAnswerIs`: every efficient verifier `M` gives the
efficient Boolean verifier `fun x r => M x r = some b`. -/
theorem closedUnderAnswerIs_iff : ClosedUnderAnswerIs E ↔
    ∀ M b, E.Eff M → E.Eff (boolVerifier fun x r => M x r = some b) :=
  Iff.rfl

/-- The `k`-fold repetition of a verifier accepting if *any* repetition
accepts, on randomness split into `k` blocks of length `p(|x|)`: the
one-sided amplifier (an `OR`, not a majority — a strict majority cannot
amplify success probability exactly `1/2`, whereas for one-sided error the
`OR` drives the failure probability to `(1/2)^k` without hurting
soundness).  Used by [AB09, Thm 7.8]'s `ZPP ⊆ RP` direction. -/
def anyVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  (List.range (k x.length)).any fun i =>
    M x ((r.drop (i * p x.length)).take (p x.length))

/-- The defining equation of `anyVerifier`: `anyVerifier M p k = fun x r =>
(List.range (k x.length)).any fun i => M x ((r.drop (i * p x.length)).take (p x.length))`. -/
theorem anyVerifier_def (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    anyVerifier M p k =
      (fun x r =>
        (List.range (k x.length)).any fun i =>
          M x ((r.drop (i * p x.length)).take (p x.length)) :
        List Bool → List Bool → Bool) := rfl

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and take the majority (closure of polynomial time under
polynomial repetition). -/
def ClosedUnderMajority : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (majorityVerifier M (polyLen a k) (polyLen a' k')))

/-- The defining property of `ClosedUnderMajority`: the polynomial majority repetition of an
efficient Boolean verifier is efficient. -/
theorem closedUnderMajority_iff : ClosedUnderMajority E ↔ ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (majorityVerifier M (polyLen a k) (polyLen a' k'))) :=
  Iff.rfl

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and accept if any repetition accepts (closure of
polynomial time under polynomial repetition with an `OR`). -/
def ClosedUnderAny : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (anyVerifier M (polyLen a k) (polyLen a' k')))

/-- The defining property of `ClosedUnderAny`: the polynomial `OR`-repetition of an efficient
Boolean verifier is efficient. -/
theorem closedUnderAny_iff : ClosedUnderAny E ↔ ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (anyVerifier M (polyLen a k) (polyLen a' k'))) :=
  Iff.rfl

/-- `E` can negate a Boolean verifier's answer (closure of polynomial time
under complementation of the output). -/
def ClosedUnderNot : Prop :=
  ∀ M, E.Eff (boolVerifier M) →
    E.Eff (boolVerifier fun x r => !(M x r))

/-- The defining property of `ClosedUnderNot`: the negation of an efficient Boolean verifier is
efficient. -/
theorem closedUnderNot_iff : ClosedUnderNot E ↔
    ∀ M, E.Eff (boolVerifier M) → E.Eff (boolVerifier fun x r => !(M x r)) :=
  Iff.rfl

end Constructions

section Counting

/-- `Pr[∅] = 0`. -/
theorem randProb_false {m : ℕ} : randProb m (fun _ => False) = 0 := by
  unfold randProb
  rw [Finset.filter_false]
  simp

/-- Additivity over disjoint events. -/
theorem randProb_or_disjoint {m : ℕ} (A B : List Bool → Prop)
    [DecidablePred A] [DecidablePred B]
    (h : ∀ r : Fin m → Bool, ¬ (A (List.ofFn r) ∧ B (List.ofFn r))) :
    randProb m (fun l => A l ∨ B l) = randProb m A + randProb m B := by
  unfold randProb
  rw [← add_div, ← Nat.cast_add]
  congr 2
  rw [Finset.filter_or]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro r hrA hrB
  rw [Finset.mem_filter] at hrA hrB
  exact h r ⟨hrA.2, hrB.2⟩

/-- Partitioning by the value of a natural-number statistic. -/
theorem randProb_mem_eq_sum {m : ℕ} (g : List Bool → ℕ) (T : Finset ℕ) :
    randProb m (fun l => g l ∈ T) = ∑ j ∈ T, randProb m (fun l => g l = j) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,
      randProb_congr (B := fun _ => False) fun r => by simp]
    exact randProb_false
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih,
      randProb_congr (B := fun l => g l = a ∨ g l ∈ T) fun r => by
        simp [Finset.mem_insert]]
    exact randProb_or_disjoint _ _ fun r ⟨h1, h2⟩ => ha (h1 ▸ h2)

/-- `Pr[B = false] = 1 − Pr[B = true]` for a Boolean test. -/
theorem randProb_bool_false {m : ℕ} (B : List Bool → Bool) :
    randProb m (fun l => B l = false) =
      1 - randProb m (fun l => B l = true) := by
  rw [randProb_congr (B := fun l => ¬ (B l = true)) fun r => by simp]
  exact randProb_not _

/-- The number of the `K` successive length-`q` blocks of `l` on which the
Boolean test `B` succeeds: the vote count of `majorityVerifier` and
`anyVerifier`, abstracted over the test. -/
def blockCount (q K : ℕ) (B : List Bool → Bool) (l : List Bool) : ℕ :=
  (List.range K).countP fun i => B ((l.drop (i * q)).take q)

/-- The vote count over `K` blocks is at most `K`: it counts a subset of the
`K` block indices. -/
theorem blockCount_le (q K : ℕ) (B : List Bool → Bool) (l : List Bool) :
    blockCount q K B l ≤ K := by
  calc blockCount q K B l ≤ (List.range K).length := List.countP_le_length ..
    _ = K := List.length_range ..

/-- Peeling off the first block. -/
theorem blockCount_succ (q K : ℕ) (B : List Bool → Bool) (l : List Bool) :
    blockCount q (K + 1) B l =
      (if B (l.take q) then 1 else 0) + blockCount q K B (l.drop q) := by
  unfold blockCount
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
  have hfun : ((fun i => B ((l.drop (i * q)).take q)) ∘ Nat.succ)
      = fun i => B (((l.drop q).drop (i * q)).take q) := by
    funext i
    simp only [Function.comp_apply]
    rw [Nat.succ_mul, Nat.add_comm (i * q) q, ← List.drop_drop]
  rw [hfun, zero_mul, List.drop_zero]
  exact Nat.add_comm _ _

/-- **The vote count is binomially distributed**: over a uniform string of
`K` blocks of `q` bits each, `Pr[blockCount = j] = C(K,j)·s^j·(1−s)^{K−j}`,
where `s` is the single-block success probability.

**Proof sketch.** Recursion on the number of blocks.  `blockCount_succ`
peels off the first block, and splitting the event by that block's outcome
gives a disjoint union (`randProb_or_disjoint`) whose branches factor into
first-block times remaining-blocks probabilities by `randProb_split`; the
recursive values recombine through Pascal's rule `Nat.choose_succ_succ`.
In the boundary case `j = K`, the branch asking for `K + 1` successes among
`K` blocks has probability zero by `blockCount_le`. -/
theorem randProb_blockCount (q : ℕ) (B : List Bool → Bool) :
    ∀ K j : ℕ, j ≤ K →
      randProb (K * q) (fun l => blockCount q K B l = j) =
        (K.choose j : ℚ) * (randProb q (fun l => B l = true)) ^ j *
          (1 - randProb q (fun l => B l = true)) ^ (K - j)
  | 0, 0, _ => by
    rw [randProb_congr (B := fun _ => True) fun r => by simp [blockCount],
      randProb_true]
    simp
  | 0, j + 1, h => absurd h (by omega)
  | K + 1, 0, _ => by
    have hmul : (K + 1) * q = q + K * q := by ring
    rw [hmul]
    have hev : randProb (q + K * q) (fun l => blockCount q (K + 1) B l = 0)
        = randProb (q + K * q) (fun l =>
            (fun l' => B l' = false) (l.take q) ∧
            (fun w => blockCount q K B w = 0) (l.drop q)) :=
      randProb_congr fun r => by
        rw [blockCount_succ]
        rcases hb : B ((List.ofFn r).take q) <;> simp [hb]
    rw [hev, randProb_split q (K * q) (fun l' => B l' = false)
        (fun w => blockCount q K B w = 0),
      randProb_bool_false, randProb_blockCount q B K 0 (by omega)]
    simp [pow_succ]
    ring
  | K + 1, j + 1, h => by
    have hmul : (K + 1) * q = q + K * q := by ring
    rw [hmul]
    have hev : randProb (q + K * q)
        (fun l => blockCount q (K + 1) B l = j + 1)
        = randProb (q + K * q) (fun l =>
            ((fun l' => B l' = true) (l.take q) ∧
              (fun w => blockCount q K B w = j) (l.drop q)) ∨
            ((fun l' => B l' = false) (l.take q) ∧
              (fun w => blockCount q K B w = j + 1) (l.drop q))) :=
      randProb_congr fun r => by
        rw [blockCount_succ]
        rcases hb : B ((List.ofFn r).take q) <;> simp [hb] <;> omega
    rw [hev, randProb_or_disjoint _ _ (fun r => by
      rintro ⟨⟨h1, -⟩, h2, -⟩
      rw [h1] at h2
      exact absurd h2 (by simp)),
      randProb_split q (K * q) (fun l' => B l' = true)
        (fun w => blockCount q K B w = j),
      randProb_split q (K * q) (fun l' => B l' = false)
        (fun w => blockCount q K B w = j + 1),
      randProb_bool_false]
    rcases Nat.lt_or_ge j K with hjK | hjK
    · rw [randProb_blockCount q B K j (by omega),
        randProb_blockCount q B K (j + 1) (by omega)]
      have hpascal : (((K + 1).choose (j + 1) : ℕ) : ℚ)
          = (K.choose j : ℚ) + (K.choose (j + 1) : ℚ) := by
        exact_mod_cast Nat.choose_succ_succ K j
      have he1 : K + 1 - (j + 1) = K - j := by omega
      have he2 : K - j = (K - (j + 1)) + 1 := by omega
      rw [he1, hpascal, he2, pow_succ]
      ring
    · have hjeq : j = K := by omega
      rw [hjeq, randProb_blockCount q B K K (le_refl _)]
      have hzero : randProb (K * q)
          (fun w => blockCount q K B w = K + 1) = 0 := by
        rw [randProb_congr (B := fun _ => False) fun r => by
          have := blockCount_le q K B (List.ofFn r)
          simp
          omega]
        exact randProb_false
      rw [hzero, mul_zero, add_zero]
      simp [Nat.choose_self, pow_succ]
      ring

/-- **Elementary Chernoff-type tail bound** for the vote count: if each
block succeeds with probability at most `1/2 − ε`, then at least half of
the `K` blocks succeed with probability at most `2·(1 − 4ε²)^⌊K/2⌋`.
(The elementary `2^K·(s(1−s))^{⌊K/2⌋}` estimate; no exponential function
is needed, which keeps the whole development inside `ℚ`.)

**Proof sketch.** Partition the tail event by the exact vote count `j`
ranging over `{j ≤ K : K ≤ 2j}` (`randProb_mem_eq_sum`) and expand each
term with the binomial formula `randProb_blockCount`.  Since `s ≤ 1 − s`,
shifting exponents toward the balanced point bounds each
`s^j·(1−s)^{K−j}` by `(s(1−s))^{⌊K/2⌋}`, and summing *all* binomial
coefficients (`Nat.sum_range_choose`) leaves `2^K·(s(1−s))^{⌊K/2⌋}`.
Finally `s(1−s) ≤ 1/4 − ε²` and `2^K ≤ 2·4^{⌊K/2⌋}` reshape this into
`2·(1 − 4ε²)^{⌊K/2⌋}`. -/
theorem randProb_tail_le (q K : ℕ) (B : List Bool → Bool) {ε : ℚ}
    (hε0 : 0 ≤ ε) (hs : randProb q (fun l => B l = true) ≤ 1/2 - ε) :
    randProb (K * q) (fun l => K ≤ 2 * blockCount q K B l) ≤
      2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
  have hs0 : (0:ℚ) ≤ randProb q (fun l => B l = true) := randProb_nonneg
  have hs1 : randProb q (fun l => B l = true) ≤ 1 := randProb_le_one
  set s : ℚ := randProb q (fun l => B l = true) with hs_def
  have hf0 : (0:ℚ) ≤ 1 - s := by linarith
  have hεhalf : ε ≤ 1/2 := by linarith
  set T : Finset ℕ := (Finset.range (K + 1)).filter (fun j => K ≤ 2 * j)
    with hT
  have hev : randProb (K * q) (fun l => K ≤ 2 * blockCount q K B l)
      = ∑ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j) := by
    rw [← randProb_mem_eq_sum (fun l => blockCount q K B l) T]
    refine randProb_congr fun r => ?_
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨Nat.lt_succ_of_le (blockCount_le q K B _), h⟩
    · exact fun h => h.2
  rw [hev]
  have hterm : ∀ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j)
      ≤ (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) := by
    intro j hj
    rw [hT, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjK, hKj⟩ := hj
    have hjK' : j ≤ K := by omega
    rw [randProb_blockCount q B K j hjK', ← hs_def]
    have hj₀ : K - K / 2 ≤ j := by omega
    have hsf : s ≤ 1 - s := by linarith
    -- shift the exponent towards the balanced point
    have hstep1 : s ^ j * (1 - s) ^ (K - j)
        ≤ s ^ (K - K / 2) * (1 - s) ^ (K / 2) := by
      have e1 : s ^ j = s ^ (K - K / 2) * s ^ (j - (K - K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      have e2 : (1 - s) ^ (K / 2)
          = (1 - s) ^ (K - j) * (1 - s) ^ (j - (K - K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e1, e2]
      have hpow : s ^ (j - (K - K / 2)) ≤ (1 - s) ^ (j - (K - K / 2)) :=
        pow_le_pow_left₀ hs0 hsf _
      calc s ^ (K - K / 2) * s ^ (j - (K - K / 2)) * (1 - s) ^ (K - j)
          ≤ s ^ (K - K / 2) * (1 - s) ^ (j - (K - K / 2)) *
              (1 - s) ^ (K - j) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
        _ = s ^ (K - K / 2) * ((1 - s) ^ (K - j) *
              (1 - s) ^ (j - (K - K / 2))) := by ring
    have hstep2 : s ^ (K - K / 2) * (1 - s) ^ (K / 2)
        ≤ (s * (1 - s)) ^ (K / 2) := by
      have e3 : s ^ (K - K / 2) = s ^ (K / 2) * s ^ (K - 2 * (K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e3, mul_pow]
      have hle1 : s ^ (K - 2 * (K / 2)) ≤ 1 := pow_le_one₀ hs0 hs1
      calc s ^ (K / 2) * s ^ (K - 2 * (K / 2)) * (1 - s) ^ (K / 2)
          ≤ s ^ (K / 2) * 1 * (1 - s) ^ (K / 2) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hle1 (by positivity)) (by positivity)
        _ = s ^ (K / 2) * (1 - s) ^ (K / 2) := by ring
    have hmono := hstep1.trans hstep2
    calc (K.choose j : ℚ) * s ^ j * (1 - s) ^ (K - j)
        = (K.choose j : ℚ) * (s ^ j * (1 - s) ^ (K - j)) := by ring
      _ ≤ (K.choose j : ℚ) * ((s * (1 - s)) ^ (K / 2)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  have hTsub : T ⊆ Finset.range (K + 1) := by
    rw [hT]
    exact Finset.filter_subset _ _
  have hsum2 : ∑ j ∈ T, (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2)
      ≤ ∑ j ∈ Finset.range (K + 1),
          (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hTsub fun j _ _ => by positivity
  have hsum3 : ∑ j ∈ Finset.range (K + 1),
      (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2)
      = (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  have hprod : s * (1 - s) ≤ 1/4 - ε ^ 2 := by nlinarith
  have hprod0 : (0:ℚ) ≤ s * (1 - s) := by positivity
  have hfinal : (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2)
      ≤ 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
    have h2K : (2 : ℚ) ^ K ≤ 2 * 4 ^ (K / 2) := by
      have e4 : K = 2 * (K / 2) + K % 2 := by omega
      calc (2 : ℚ) ^ K = 2 ^ (2 * (K / 2)) * 2 ^ (K % 2) := by
            rw [← pow_add, ← e4]
        _ ≤ 2 ^ (2 * (K / 2)) * 2 ^ 1 := by
            refine mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
        _ = 2 * 4 ^ (K / 2) := by
            rw [pow_mul]
            norm_num
            ring
    have hpow : (s * (1 - s)) ^ (K / 2) ≤ (1/4 - ε ^ 2) ^ (K / 2) :=
      pow_le_pow_left₀ hprod0 hprod _
    calc (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2)
        ≤ (2 * 4 ^ (K / 2)) * (1/4 - ε ^ 2) ^ (K / 2) := by
          refine mul_le_mul h2K hpow (by positivity) (by positivity)
      _ = 2 * (4 * (1/4 - ε ^ 2)) ^ (K / 2) := by
          rw [mul_pow]
          ring
      _ = 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
          congr 2
          ring
  calc ∑ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j)
      ≤ ∑ j ∈ T, (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ Finset.range (K + 1),
          (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) := hsum2
    _ = (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2) := hsum3
    _ ≤ 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := hfinal

/-- The rational Bernoulli estimate `(1−x)^m ≤ 1/2` once `m·x ≥ 1`:
`(1−x)^m·(1+mx) ≤ 1` by induction, and `1+mx ≥ 2`.

**Proof sketch.** The key inequality `(1−x)^{m'}·(1 + m'·x) ≤ 1` holds for
every `m'` by induction: the step rewrites
`(1−x)·(1 + (m'+1)·x) = 1 + m'·x − (m'+1)·x²` and drops the nonnegative
correction term.  At `m' = m` the hypothesis gives `1 + m·x ≥ 2`, and
nonlinear arithmetic turns `(1−x)^m·(1 + m·x) ≤ 1` into
`(1−x)^m ≤ 1/2`. -/
theorem one_sub_pow_le_half {x : ℚ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ}
    (hm : 1 ≤ (m : ℚ) * x) : (1 - x) ^ m ≤ 1/2 := by
  have key : ∀ m' : ℕ, (1 - x) ^ m' * (1 + (m' : ℚ) * x) ≤ 1 := by
    intro m'
    induction m' with
    | zero => simp
    | succ m' ih =>
      have h1 : (0:ℚ) ≤ (1 - x) ^ m' := pow_nonneg (by linarith) m'
      have hstep : (1 - x) * (1 + ((m' : ℚ) + 1) * x) ≤ 1 + (m' : ℚ) * x := by
        have hnn : 0 ≤ ((m' : ℚ) + 1) * x ^ 2 := by positivity
        have hexp : (1 - x) * (1 + ((m' : ℚ) + 1) * x)
            = 1 + (m' : ℚ) * x - ((m' : ℚ) + 1) * x ^ 2 := by ring
        rw [hexp]
        linarith
      calc (1 - x) ^ (m' + 1) * (1 + ((m' + 1 : ℕ) : ℚ) * x)
          = (1 - x) ^ m' * ((1 - x) * (1 + ((m' : ℚ) + 1) * x)) := by
            push_cast
            ring
        _ ≤ (1 - x) ^ m' * (1 + (m' : ℚ) * x) :=
            mul_le_mul_of_nonneg_left hstep h1
        _ ≤ 1 := ih
  have h3 := key m
  nlinarith [pow_nonneg (by linarith : (0:ℚ) ≤ 1 - x) m]

/-- Iterating `one_sub_pow_le_half`: `(1−x)^e ≤ (1/2)^T` once `e ≥ m·T`
with `m·x ≥ 1`. -/
theorem one_sub_pow_le_half_pow {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {m T e : ℕ} (hm : 1 ≤ (m : ℚ) * x) (he : m * T ≤ e) :
    (1 - x) ^ e ≤ (1/2 : ℚ) ^ T := by
  calc (1 - x) ^ e ≤ (1 - x) ^ (m * T) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) he
    _ = ((1 - x) ^ m) ^ T := by rw [pow_mul]
    _ ≤ (1/2 : ℚ) ^ T :=
      pow_le_pow_left₀ (pow_nonneg (by linarith) m)
        (one_sub_pow_le_half hx0 hx1 hm) T

end Counting

/-- `BPP` is closed under complementation (`BPP = coBPP`): swap the two
acceptance clauses and negate the verifier's answer.  Used by
[AB09, Thm 7.15]'s proof ("it is enough to prove `BPP ⊆ Σ₂ᵖ` because `BPP`
is closed under complementation").

**Proof sketch.** If `M` decides `L` with two-sided error `1/3`, then
`¬M` decides `Lᶜ` with the same error: the `x ∈ Lᶜ` clause for `¬M` is the
`x ∉ L` clause for `M` and vice versa, since
`¬M x r = true ↔ M x r = false`. -/
theorem InBPP.compl (hNot : ClosedUnderNot E) {L : Language Bool}
    (hL : InBPP E L) : InBPP E Lᶜ := by
  obtain ⟨M, a, k, hM, hacc⟩ := hL
  refine ⟨fun x r => !(M x r), a, k, hNot M hM, fun x => ?_⟩
  constructor
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = false :=
          (hacc x).2 hx
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = true :=
          randProb_congr fun r => by simp
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = true :=
          (hacc x).1 (Set.not_notMem.mp hx)
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = false :=
          randProb_congr fun r => by simp

/-- From a zero-error verifier whose definite answers are never wrong, a
one-sided witness: on members it answers `some b` with probability at least
`1/2` (it never answers `some (!b)` and aborts with probability at most
`1/2`), and on non-members it never answers `some b`; a 2-fold `OR`
(`anyVerifier`) amplifies `1/2` to `3/4 ≥ 2/3`.  The common core of the
inclusions `ZPP ⊆ RP` and `ZPP ⊆ coRP` in [AB09, Thm 7.8].

**Proof sketch.** The `RP` witness is `anyVerifier` over the test
`M x r = some b`, run on two independent randomness blocks.  For `x ∈ L'`,
one run answers `some b` with probability at least `1/2`: a non-aborting
answer is never `some (!b)`, so `randProb_mono` lifts `Pr[¬abort] ≥ 1/2`
(from `randProb_not` and the abort bound) to `Pr[some b] ≥ 1/2`; the OR
fails only when both halves fail, a product `≤ (1/2)² = 1/4` by
`randProb_split` and `randProb_take`, so acceptance is `≥ 3/4 ≥ 2/3`.
For `x ∉ L'`, each half of the random string is a genuine length-`q`
string (`exists_ofFn_eq`) on which `hout` forbids the answer `some b`, so
the OR never accepts. -/
theorem inRP_of_zeroError (hAns : ClosedUnderAnswerIs E)
    (hAny : ClosedUnderAny E) {M : List Bool → List Bool → Option Bool}
    {a k : ℕ} (hM : E.Eff M) (L' : Language Bool) (b : Bool)
    (hin : ∀ x ∈ L', (∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some (!b)) ∧
        randProb (polyLen a k x.length) (fun r => M x r = none) ≤ 1/2)
    (hout : ∀ x ∉ L', ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some b) :
    InRP E L' := by
  classical
  refine ⟨anyVerifier (fun x r => decide (M x r = some b)) (polyLen a k)
    (polyLen 2 0), 2 * a, k, hAny _ a k 2 0 (hAns M b hM), fun x => ?_⟩
  have hlen : polyLen (2 * a) k x.length
      = polyLen a k x.length + polyLen a k x.length := by
    unfold polyLen
    ring
  -- Unfold the 2-fold `OR` on an arbitrary random string.
  have hN_iff : ∀ l : List Bool,
      anyVerifier (fun x r => decide (M x r = some b)) (polyLen a k)
          (polyLen 2 0) x l = true ↔
        (M x (l.take (polyLen a k x.length)) = some b ∨
          M x ((l.drop (polyLen a k x.length)).take
            (polyLen a k x.length)) = some b) := by
    intro l
    unfold anyVerifier
    rw [show polyLen 2 0 x.length = 2 from by unfold polyLen; ring,
      show List.range 2 = [0, 1] from rfl]
    simp
  constructor
  · -- members are accepted with probability at least `3/4`
    intro hx
    obtain ⟨hnever, habort⟩ := hin x hx
    -- one run answers `some b` with probability at least `1/2`
    have hone : 1/2 ≤ randProb (polyLen a k x.length)
        (fun l => M x l = some b) := by
      have hmono : randProb (polyLen a k x.length)
          (fun l => ¬ (M x l = none)) ≤
          randProb (polyLen a k x.length) (fun l => M x l = some b) := by
        refine randProb_mono fun r hr => ?_
        rcases hcase : M x (List.ofFn r) with _ | b'
        · exact absurd hcase hr
        · have hb' : b' ≠ !b := fun h => hnever r (h ▸ hcase)
          have hbb : b' = b := by cases b <;> cases b' <;> simp_all
          rw [hbb]
      have hnot := randProb_not (m := polyLen a k x.length)
        (fun l => M x l = none)
      linarith
    rw [hlen]
    have hstep1 : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) =
        randProb (polyLen a k x.length + polyLen a k x.length)
          (fun l => (fun l' => ¬ (M x l' = some b))
              (l.take (polyLen a k x.length)) ∧
            (fun w => ¬ (M x (w.take (polyLen a k x.length)) = some b))
              (l.drop (polyLen a k x.length))) :=
      randProb_congr fun rr => by
        rw [hN_iff (List.ofFn rr)]
        exact not_or
    have hstep2 := randProb_split (polyLen a k x.length) (polyLen a k x.length)
      (fun l' => ¬ (M x l' = some b))
      (fun w => ¬ (M x (w.take (polyLen a k x.length)) = some b))
    have hstep3 := randProb_take (le_refl (polyLen a k x.length))
      (fun l' => ¬ (M x l' = some b))
    have hfail : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) =
        randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) *
          randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) := by
      rw [hstep1, hstep2, hstep3]
    have hs_le : randProb (polyLen a k x.length)
        (fun l => ¬ (M x l = some b)) ≤ 1/2 := by
      rw [randProb_not]
      linarith
    have hs_nonneg : (0 : ℚ) ≤ randProb (polyLen a k x.length)
        (fun l => ¬ (M x l = some b)) := randProb_nonneg
    have hfail_le : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) ≤ 1/4 := by
      rw [hfail]
      calc randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) *
            randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b))
          ≤ (1/2) * (1/2) := mul_le_mul hs_le hs_le hs_nonneg (by norm_num)
        _ = 1/4 := by norm_num
    have hnotN := randProb_not
      (m := polyLen a k x.length + polyLen a k x.length)
      (fun l => anyVerifier (fun x r => decide (M x r = some b))
        (polyLen a k) (polyLen 2 0) x l = true)
    linarith
  · -- non-members are never accepted
    intro hx rr
    rw [Bool.eq_false_iff]
    intro hacc
    rw [hN_iff (List.ofFn rr)] at hacc
    have hlen' : (List.ofFn rr).length
        = polyLen a k x.length + polyLen a k x.length := by
      rw [List.length_ofFn, hlen]
    rcases hacc with h | h
    · have hb1 : ((List.ofFn rr).take (polyLen a k x.length)).length
          = polyLen a k x.length := by
        rw [List.length_take, hlen']
        omega
      obtain ⟨r', hr'⟩ := exists_ofFn_eq hb1
      rw [hr'] at h
      exact hout x hx r' h
    · have hb2 : (((List.ofFn rr).drop (polyLen a k x.length)).take
          (polyLen a k x.length)).length = polyLen a k x.length := by
        rw [List.length_take, List.length_drop, hlen']
        omega
      obtain ⟨r', hr'⟩ := exists_ofFn_eq hb2
      rw [hr'] at h
      exact hout x hx r' h

/-- **`ZPP = RP ∩ coRP`** ([AB09, Thm 7.8]).  Stated relative to the
efficiency notion `E`, under the closure properties the two directions use.

This is the identity for the **Las Vegas / abort-form** `ZPP` (`InZPP`: a
zero-error verifier that outputs `some b` or aborts with `none`, abort
probability `≤ 1/2`), **not** the book's expected-polynomial-time formulation
([AB09, Def 7.7]).  The two are equivalent by the standard truncate-and-repeat
bridge, formalized for polynomial time as `Randomized.ZPP_PTM_eq_setOf_inZPP`
(`Randomized/ZPPHostsClasses.lean`); the book's Theorem 7.8 for Def 7.7's `ZPP`
is `Randomized.ZPP_PTM_eq_RP_PTM_inter_coRP_PTM` there.

**Proof sketch.** (⊆) A zero-error verifier yields an `RP` verifier by
answering `true` exactly on output `some true` (`hAns`): inputs outside `L`
are never accepted (zero error), and inputs in `L` are accepted whenever the
verifier does not abort, hence with probability at least `1/2`.  Amplify
`1/2` to `2/3` with a 2-fold `OR` (`anyVerifier`, `hAny`): soundness is
preserved (an `OR` of never-accepting runs never accepts) and the failure
probability drops to `(1/2)² = 1/4`, so success is `≥ 3/4 ≥ 2/3`.  (A strict
*majority* cannot amplify success probability exactly `1/2`, which is why
the one-sided `OR` closure is the right tool here.)  Symmetrically with
`some false` for `Lᶜ`, giving `coRP`.  (⊇) Race an `RP` verifier `M₁` for
`L` against an `RP` verifier `M₂` for `Lᶜ` on split randomness
(`raceVerifier`): a definite answer is never wrong, since `M₁` accepting
certifies `x ∈ L` and `M₂` accepting certifies `x ∉ L`; and whichever of the
two is the "live" verifier for `x` accepts with probability ≥ `2/3`, so the
race aborts with probability at most `1/3 ≤ 1/2`. -/
theorem inZPP_iff_inRP_and_inCoRP (hRace : ClosedUnderRace E)
    (hAns : ClosedUnderAnswerIs E) (hAny : ClosedUnderAny E)
    (L : Language Bool) :
    InZPP E L ↔ InRP E L ∧ InCoRP E L := by
  classical
  constructor
  · rintro ⟨M, a, k, hM, hprop⟩
    constructor
    · refine inRP_of_zeroError E hAns hAny hM L true
        (fun x hx => ⟨?_, (hprop x).2.2⟩) (fun x hx => (hprop x).2.1 hx)
      simpa using (hprop x).1 hx
    · refine inRP_of_zeroError E hAns hAny hM Lᶜ false
        (fun x hx => ⟨?_, (hprop x).2.2⟩)
        (fun x hx => (hprop x).1 (Set.not_notMem.mp hx))
      simpa using (hprop x).2.1 hx
  · rintro ⟨⟨M₁, a₁, k₁, hM₁, h₁⟩, M₂, a₂, k₂, hM₂, h₂⟩
    -- Trim `M₂` to its first `polyLen a₂ k₂` bits, then race.
    set M₂' : List Bool → List Bool → Bool :=
      anyVerifier M₂ (polyLen a₂ k₂) (polyLen 1 0) with hM₂'def
    have hM₂'eff : E.Eff (boolVerifier M₂') := hAny M₂ a₂ k₂ 1 0 hM₂
    have hM₂'eq : ∀ (x : List Bool) (w : List Bool),
        M₂' x w = M₂ x (w.take (polyLen a₂ k₂ x.length)) := by
      intro x w
      show (List.range (polyLen 1 0 x.length)).any _ = _
      rw [show polyLen 1 0 x.length = 1 by simp [polyLen]]
      show (List.range 1).any _ = _
      rw [show List.range 1 = [0] from rfl]
      simp [List.any_cons]
    refine ⟨raceVerifier M₁ M₂' (polyLen a₁ k₁), a₁ + a₂, k₁ + k₂,
      hRace M₁ M₂' a₁ k₁ hM₁ hM₂'eff, fun x => ?_⟩
    set n := x.length
    set q₁ := polyLen a₁ k₁ n with hq₁
    set q₂ := polyLen a₂ k₂ n with hq₂
    set Q := polyLen (a₁ + a₂) (k₁ + k₂) n with hQ
    have hone : 1 ≤ n + 1 := Nat.le_add_left 1 n
    have hQ₁ : q₁ ≤ Q := by
      rw [hq₁, hQ]
      unfold polyLen
      calc a₁ * (n + 1) ^ k₁ ≤ a₁ * (n + 1) ^ (k₁ + k₂) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
        _ ≤ (a₁ + a₂) * (n + 1) ^ (k₁ + k₂) :=
            Nat.mul_le_mul_right _ (by omega)
    have hQ₂ : q₁ + q₂ ≤ Q := by
      rw [hq₁, hq₂, hQ]
      unfold polyLen
      have e₁ : a₁ * (n + 1) ^ k₁ ≤ a₁ * (n + 1) ^ (k₁ + k₂) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
      have e₂ : a₂ * (n + 1) ^ k₂ ≤ a₂ * (n + 1) ^ (k₁ + k₂) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
      calc a₁ * (n + 1) ^ k₁ + a₂ * (n + 1) ^ k₂
          ≤ a₁ * (n + 1) ^ (k₁ + k₂) + a₂ * (n + 1) ^ (k₁ + k₂) := by omega
        _ = (a₁ + a₂) * (n + 1) ^ (k₁ + k₂) := by ring
    -- Lengths of the two segments fed to the verifiers.
    have hlen₁ : ∀ rr : Fin Q → Bool, ((List.ofFn rr).take q₁).length = q₁ := by
      intro rr
      simp [List.length_take, List.length_ofFn]
      omega
    have hlen₂ : ∀ rr : Fin Q → Bool,
        (((List.ofFn rr).drop q₁).take q₂).length = q₂ := by
      intro rr
      simp [List.length_take, List.length_drop, List.length_ofFn]
      omega
    -- The three branches of the race on a concrete random string.
    have hrace_val : ∀ rr : Fin Q → Bool,
        raceVerifier M₁ M₂' (polyLen a₁ k₁) x (List.ofFn rr) =
          if M₁ x ((List.ofFn rr).take q₁) then some true
          else if M₂ x (((List.ofFn rr).drop q₁).take q₂) then some false
          else none := by
      intro rr
      show (if M₁ x ((List.ofFn rr).take q₁) then some true
        else if M₂' x ((List.ofFn rr).drop q₁) then some false else none) = _
      rw [hM₂'eq]
    refine ⟨fun hx rr => ?_, fun hx rr => ?_, ?_⟩
    · -- `x ∈ L`: never answers `some false`
      rw [hrace_val rr]
      have hx' : x ∉ Lᶜ := Set.not_notMem.mpr hx
      obtain ⟨r₂, hr₂⟩ := exists_ofFn_eq (hlen₂ rr)
      have hM₂false : M₂ x (((List.ofFn rr).drop q₁).take q₂) = false := by
        rw [hr₂]
        exact (h₂ x).2 hx' r₂
      rw [hM₂false]
      split
      · simp
      · simp
    · -- `x ∉ L`: never answers `some true`
      rw [hrace_val rr]
      obtain ⟨r₁, hr₁⟩ := exists_ofFn_eq (hlen₁ rr)
      have hM₁false : M₁ x ((List.ofFn rr).take q₁) = false := by
        rw [hr₁]
        exact (h₁ x).2 hx r₁
      rw [hM₁false]
      split
      · simp_all
      · split <;> simp
    · -- aborts with probability at most `1/2`
      obtain ⟨m₂, hm₂⟩ : ∃ m₂, Q = q₁ + m₂ := ⟨Q - q₁, by omega⟩
      have hq₂m₂ : q₂ ≤ m₂ := by omega
      have hs1 : randProb Q
          (fun l => raceVerifier M₁ M₂' (polyLen a₁ k₁) x l = none) =
          randProb Q (fun l => (fun l' => ¬ (M₁ x l' = true)) (l.take q₁) ∧
            (fun w => ¬ (M₂ x (w.take q₂) = true)) (l.drop q₁)) :=
        randProb_congr fun rr => by
          rw [hrace_val rr]
          rcases hb₁ : M₁ x ((List.ofFn rr).take q₁) <;>
            rcases hb₂ : M₂ x (((List.ofFn rr).drop q₁).take q₂) <;> simp_all
      have hs3 := randProb_split q₁ m₂ (fun l' => ¬ (M₁ x l' = true))
        (fun w => ¬ (M₂ x (w.take q₂) = true))
      have hs4 := randProb_take hq₂m₂ (fun l' => ¬ (M₂ x l' = true))
      have hnone_eq : randProb Q
          (fun l => raceVerifier M₁ M₂' (polyLen a₁ k₁) x l = none) =
          randProb q₁ (fun l => ¬ (M₁ x l = true)) *
            randProb q₂ (fun l => ¬ (M₂ x l = true)) := by
        rw [hs1, hm₂, hs3, hs4]
      rw [hnone_eq]
      by_cases hx : x ∈ L
      · have hacc := (h₁ x).1 hx
        have h1 : randProb q₁ (fun l => ¬ (M₁ x l = true)) ≤ 1/3 := by
          rw [randProb_not]
          linarith
        calc randProb q₁ (fun l => ¬ (M₁ x l = true)) *
              randProb q₂ (fun l => ¬ (M₂ x l = true))
            ≤ (1/3) * 1 := by
              refine mul_le_mul h1 randProb_le_one randProb_nonneg (by norm_num)
          _ ≤ 1/2 := by norm_num
      · have hacc := (h₂ x).1 hx
        have h2 : randProb q₂ (fun l => ¬ (M₂ x l = true)) ≤ 1/3 := by
          rw [randProb_not]
          linarith
        calc randProb q₁ (fun l => ¬ (M₁ x l = true)) *
              randProb q₂ (fun l => ¬ (M₂ x l = true))
            ≤ 1 * (1/3) := by
              refine mul_le_mul randProb_le_one h2 randProb_nonneg (by norm_num)
          _ ≤ 1/2 := by norm_num

/-- The advantage demanded of a weak `BPP` verifier on inputs of length `n`:
`min (1/6) ((n+1)^{-c})`.  For `c ≥ 1` and `n ≥ 5` this is the book's
`n^{-c}` up to the `n+1` shift (for `c = 0` both the book's `n^{-c}` and
`(n+1)^{-c}` are the constant `1`, and the cap takes over); the cap `1/6`
keeps the threshold `1/2 + weakAdv c n ≤ 2/3` attainable at small lengths,
where the book's literal `1/2 + n^{-c}` exceeds `1` (see the module
docstring's **Deviations**). -/
def weakAdv (c n : ℕ) : ℚ :=
  min (1/6) (((n : ℚ) + 1)⁻¹ ^ c)

/-- The weak advantage is positive: both the cap `1/6` and the
inverse-polynomial `(n+1)^{-c}` are positive. -/
theorem weakAdv_pos (c n : ℕ) : 0 < weakAdv c n := by
  unfold weakAdv
  refine lt_min (by norm_num) ?_
  positivity

/-- The weak advantage never exceeds its cap `1/6`, keeping the weak success
threshold `1/2 + weakAdv c n` at most `2/3` at every length. -/
theorem weakAdv_le_sixth (c n : ℕ) : weakAdv c n ≤ 1/6 :=
  min_le_left _ _

/-- The weak advantage is inverse-polynomially large: `weakAdv c n` is at
least `(n+1)^{-c}/6`, since `(n+1)^{-c} ≤ 1` puts a sixth of it below both
branches of the `min`. -/
theorem weakAdv_ge (c n : ℕ) :
    (((n : ℚ) + 1)⁻¹) ^ c / 6 ≤ weakAdv c n := by
  have hy0 : (0:ℚ) ≤ (((n : ℚ) + 1)⁻¹) ^ c := by positivity
  have hy1 : (((n : ℚ) + 1)⁻¹) ^ c ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    rw [inv_le_one₀ (by positivity)]
    have := Nat.cast_nonneg (α := ℚ) n
    linarith
  unfold weakAdv
  exact le_min (by linarith) (by linarith)

/-- The arithmetic core of the amplification: with
`k(n) = 56·(n+1)^{2c+d}` repetitions, the elementary tail bound beats
`2^{-((n+1)^d + 1)}`.

**Proof sketch.** Write `ε = weakAdv c n`; by `weakAdv_ge`,
`6ε ≥ (n+1)^{-c}`, whence `9·(n+1)^{2c}·(4ε²) ≥ 1` — the hypothesis
`m·x ≥ 1` of the Bernoulli bound, with `m = 9(n+1)^{2c}` and `x = 4ε²`.
The exponent `⌊56(n+1)^{2c+d}/2⌋ = 28(n+1)^{2c+d}` dominates
`9(n+1)^{2c}·((n+1)^d + 2)`, so `one_sub_pow_le_half_pow` yields
`(1 − 4ε²)^{⌊k/2⌋} ≤ (1/2)^{(n+1)^d + 2}`, and the leading factor `2`
absorbs one halving. -/
theorem weakAdv_tail_bound (c d n : ℕ) :
    2 * (1 - 4 * weakAdv c n ^ 2) ^ (polyLen 56 (2 * c + d) n / 2) ≤
      (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := by
  have hε0 : 0 < weakAdv c n := weakAdv_pos c n
  have hε6 : weakAdv c n ≤ 1/6 := weakAdv_le_sixth c n
  set ε := weakAdv c n with hε
  have hx1 : 4 * ε ^ 2 ≤ 1 := by nlinarith
  have hx0 : (0:ℚ) ≤ 4 * ε ^ 2 := by positivity
  have hy0 : (0:ℚ) ≤ (((n : ℚ) + 1)⁻¹) ^ c := by positivity
  have hc0 : (0:ℚ) ≤ ((n : ℚ) + 1) ^ c := by positivity
  have hcancel : ((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
  have hεge : (((n : ℚ) + 1)⁻¹) ^ c / 6 ≤ ε := weakAdv_ge c n
  have hm : 1 ≤ ((9 * (n + 1) ^ (2 * c) : ℕ) : ℚ) * (4 * ε ^ 2) := by
    have hcast : ((9 * (n + 1) ^ (2 * c) : ℕ) : ℚ)
        = 9 * ((n : ℚ) + 1) ^ (2 * c) := by
      push_cast
      ring
    rw [hcast]
    have h1 : (((n : ℚ) + 1)⁻¹) ^ c ≤ 6 * ε := by linarith
    have h2 : (((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c
        ≤ (6 * ε) * (6 * ε) := mul_self_le_mul_self hy0 h1
    have h3 : ((n : ℚ) + 1) ^ (2 * c) *
        ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) = 1 := by
      rw [two_mul, pow_add]
      calc ((n : ℚ) + 1) ^ c * ((n : ℚ) + 1) ^ c *
            ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c)
          = (((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) *
            (((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) := by ring
        _ = 1 := by rw [hcancel, one_mul]
    have h4 : ((n : ℚ) + 1) ^ (2 * c) *
        ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c)
        ≤ ((n : ℚ) + 1) ^ (2 * c) * ((6 * ε) * (6 * ε)) := by
      refine mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [h3, h4]
  have hexp : (9 * (n + 1) ^ (2 * c)) * ((n + 1) ^ d + 2) ≤
      polyLen 56 (2 * c + d) n / 2 := by
    have h562 : polyLen 56 (2 * c + d) n / 2 = 28 * (n + 1) ^ (2 * c + d) := by
      unfold polyLen
      omega
    rw [h562, pow_add]
    have hge1 : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have hge2 : 1 ≤ (n + 1) ^ (2 * c) := Nat.one_le_pow _ _ (by omega)
    nlinarith [hge1, hge2]
  have hhalf := one_sub_pow_le_half_pow hx0 hx1 hm hexp
  calc 2 * (1 - 4 * ε ^ 2) ^ (polyLen 56 (2 * c + d) n / 2)
      ≤ 2 * (1/2 : ℚ) ^ ((n + 1) ^ d + 2) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := by
        rw [show (n + 1) ^ d + 2 = ((n + 1) ^ d + 1) + 1 from rfl, pow_succ]
        ring

/-- `L ∈ BPP_{n^{-c}}`: like `InBPP`, but with success probability only
`1/2 + weakAdv c |x|`, i.e. an inverse-polynomial advantage over guessing.
[AB09, Lem 7.9], with the small-length repair described in the module
docstring. -/
def InBPPWeak (c : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- `L ∈ BPP` with error at most `2^{-((|x|+1)^d + 1)}` — the amplified form
produced by error reduction.  The exponent `(|x|+1)^d + 1 ≥ |x|^d`
strengthens [AB09, Thm 7.10]'s `2^{-|x|^d}` uniformly in `|x|`, and the
`+ 1` keeps the success threshold at least `3/4 > 2/3` at *every* length
and every `d` (including `d = 0` and the empty input), so
`InBPPStrong E d L → InBPP E L` follows directly using the same witnesses
(via the arithmetic inequality `2/3 ≤ 1 − (1/2)^{(n+1)^d + 1}`), with no closure
assumption on `E`.  (With the bare exponent `(|x|+1)^d`, a fair coin would
satisfy the definition at `d = 0` for every language, and at `|x| = 0` for
every `d` — a finite exception that cannot be patched for an abstract
model.) -/
def InBPPStrong (d : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- **Error reduction** ([AB09, Thm 7.10]).  A language decidable with an
inverse-polynomial advantage is decidable with success probability
`1 − 2^{-((|x|+1)^d + 1)}`, for every constant `d` — relative to `E`,
assuming `E` is closed under polynomial majority repetition.

**Proof sketch.** Run the weak verifier `k(n) = 56·(n+1)^{2c+d}` times on
independent blocks of randomness and take the majority
(`majorityVerifier`).  In each of the two symmetric cases the failure
event is a vote-count tail — for `x ∈ L` the *false* votes reach `k/2`
(rephrased through the complementary vote-count identity), for `x ∉ L`
the *true* votes do — where each single block errs with probability
`≤ 1/2 − ε` with `ε = weakAdv c n ≥ (n+1)^{-c}/6`, so the elementary tail
estimate `randProb_tail_le` (built on the binomial distribution
`randProb_blockCount`) bounds it by `2·(1 − 4ε²)^{⌊k/2⌋}`; the arithmetic
crunch `weakAdv_tail_bound` (via the rational Bernoulli bound
`one_sub_pow_le_half_pow`) then gives `≤ 2^{-((n+1)^d + 1)}`.  (The book
computes with `e^{−2ε²k}`; the elementary `(4p(1−p))^{k/2}` bound proves
the same statement while keeping every quantity rational.) -/
theorem bpp_error_reduction (hMaj : ClosedUnderMajority E) {c : ℕ}
    {L : Language Bool} (hL : InBPPWeak E c L) (d : ℕ) :
    InBPPStrong E d L := by
  classical
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨majorityVerifier M (polyLen a k) (polyLen 56 (2 * c + d)),
    56 * a, 2 * c + d + k, hMaj M a k 56 (2 * c + d) hM, fun x => ?_⟩
  have hqK : polyLen (56 * a) (2 * c + d + k) x.length
      = polyLen 56 (2 * c + d) x.length * polyLen a k x.length := by
    unfold polyLen
    ring
  set n := x.length with hn
  set q := polyLen a k n with hq
  set K := polyLen 56 (2 * c + d) n with hK
  have hε0 : 0 < weakAdv c n := weakAdv_pos c n
  -- The majority verifier accepts iff more than half the blocks accept.
  have hmaj_iff : ∀ l : List Bool,
      majorityVerifier M (polyLen a k) (polyLen 56 (2 * c + d)) x l = true ↔
        K < 2 * blockCount q K (M x) l := by
    intro l
    show decide (K < 2 * blockCount q K (M x) l) = true ↔ _
    rw [decide_eq_true_iff]
  -- Complementary vote counts.
  have hcount : ∀ l : List Bool,
      blockCount q K (M x) l +
        blockCount q K (fun l' => !(M x l')) l = K := by
    intro l
    unfold blockCount
    have haux : ∀ (p : ℕ → Bool) (li : List ℕ),
        li.countP p + li.countP (fun i => !(p i)) = li.length := by
      intro p li
      induction li with
      | nil => simp
      | cons hd tl ih =>
        rw [List.countP_cons, List.countP_cons, List.length_cons]
        rcases hp : p hd <;> simp [hp] <;> omega
    rw [haux (fun i => M x ((l.drop (i * q)).take q)) (List.range K)]
    exact List.length_range
  -- Single-run probabilities.
  have hs_false : randProb q (fun l => M x l = false)
      = 1 - randProb q (fun l => M x l = true) := randProb_bool_false (M x)
  have hs_not : randProb q (fun l => (!(M x l)) = true)
      = randProb q (fun l => M x l = false) :=
    randProb_congr fun r => by simp
  rw [hqK]
  constructor
  · -- `x ∈ L`: the failure event is `K ≤ 2·(false votes)`
    intro hx
    have hW := (hprop x).1 hx
    have hsf : randProb q (fun l => (!(M x l)) = true) ≤ 1/2 - weakAdv c n := by
      rw [hs_not, hs_false]
      linarith
    have htail := randProb_tail_le q K (fun l' => !(M x l')) hε0.le hsf
    have hev : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x l = true))
        = randProb (K * q) (fun l =>
            K ≤ 2 * blockCount q K (fun l' => !(M x l')) l) :=
      randProb_congr fun r => by
        rw [hmaj_iff]
        have := hcount (List.ofFn r)
        constructor
        · intro h
          omega
        · intro h
          omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k)
        (polyLen 56 (2 * c + d)) x l = true)
    have hbound := weakAdv_tail_bound c d n
    rw [hev] at hnot
    have : randProb (K * q) (fun l =>
        K ≤ 2 * blockCount q K (fun l' => !(M x l')) l)
        ≤ (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := le_trans htail (by
      rw [hK]
      exact hbound)
    linarith
  · -- `x ∉ L`: the failure event is `K < 2·(true votes)`
    intro hx
    have hW := (hprop x).2 hx
    have hst : randProb q (fun l => M x l = true) ≤ 1/2 - weakAdv c n := by
      have := hs_false
      linarith
    have htail := randProb_tail_le q K (M x) hε0.le hst
    have hmono : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x l = false))
        ≤ randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M x) l) := by
      refine randProb_mono fun r hr => ?_
      have h1 : majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x (List.ofFn r) = true := by
        rcases hb : majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x (List.ofFn r)
        · exact absurd hb hr
        · rfl
      have h2 := (hmaj_iff (List.ofFn r)).mp h1
      omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k)
        (polyLen 56 (2 * c + d)) x l = false)
    have hbound := weakAdv_tail_bound c d n
    have : randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M x) l)
        ≤ (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := le_trans htail (by
      rw [hK]
      exact hbound)
    linarith

/-- The amplified form implies plain `BPP` membership: the success
threshold `1 − 2^{-((|x|+1)^d+1)}` is at least `3/4 ≥ 2/3` at every length,
using the same witnesses. -/
theorem InBPPStrong.toInBPP {d : ℕ} {L : Language Bool}
    (hL : InBPPStrong E d L) : InBPP E L := by
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨M, a, k, hM, fun x => ?_⟩
  have he : 2 ≤ (x.length + 1) ^ d + 1 := by
    have := Nat.one_le_pow d (x.length + 1) (by omega)
    omega
  have hth : (2/3 : ℚ) ≤ 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) := by
    have h2 : (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤ (1/2 : ℚ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he
    norm_num at h2
    linarith
  exact ⟨fun hx => hth.trans ((hprop x).1 hx),
    fun hx => hth.trans ((hprop x).2 hx)⟩

/-- **`BPP_{n^{-c}} = BPP`** ([AB09, Lem 7.9]): the success threshold `2/3`
in the definition of `BPP` can be weakened to an inverse-polynomial advantage
over `1/2` without changing the class.

**Proof.** `BPP ⊆ BPP_{n^{-c}}` since `weakAdv c n ≤ 1/6` makes the
weak threshold at most `2/3` at every length.  Conversely, error reduction
at `d = 0` (`bpp_error_reduction`) amplifies the weak advantage to success
probability `1 − (1/2)^{(n+1)^0+1} ≥ 3/4 ≥ 2/3`
(`InBPPStrong.toInBPP`). -/
theorem inBPPWeak_iff_inBPP (hMaj : ClosedUnderMajority E) (c : ℕ)
    (L : Language Bool) :
    InBPPWeak E c L ↔ InBPP E L := by
  constructor
  · intro hL
    exact (bpp_error_reduction E hMaj hL 0).toInBPP
  · rintro ⟨M, a, k, hM, hprop⟩
    refine ⟨M, a, k, hM, fun x => ?_⟩
    have hadv : 1/2 + weakAdv c x.length ≤ 2/3 := by
      have := weakAdv_le_sixth c x.length
      linarith
    exact ⟨fun hx => hadv.trans ((hprop x).1 hx),
      fun hx => hadv.trans ((hprop x).2 hx)⟩

end Randomized

## ===== TCSlib/Complexity/Randomized/SeedMajority.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.SeedMajority.Words
import TCSlib.Complexity.Randomized.SeedMajority.State
import TCSlib.Complexity.Randomized.SeedMajority.Enumeration
import TCSlib.Complexity.Randomized.SeedMajority.Envelope

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic majority over all seeds

The counting enumeration host: a deterministic machine that, on input `x`, runs a
polynomial-time test on `⟨x, u⟩` for **every** seed `u ∈ {0,1}^{w(|x|)}`, counts the accepting
seeds, and accepts iff more than half of them accept, in time `2^{w(n)} · poly(n)`. It is the
enumeration behind `BPP ⊆ EXP` [AB09, §7.1, p. 126] (run the machine on every random string
and count the accepting ones) and step 4 of the proof of [PS10, §8.2, Theorem 180.1] (run the
derandomized verifier on every seed of the generator and take the majority). It is a *host* in
the sense of `policy.md` §1 (*Hosts come first*): an odometer over all seeds, generic in the
leaf test `V` and in the width `w`. Its contract is stated here, ahead of its consumers, by
Seyoon's rulings of 2026-11-14 (the host) and 2026-11-15 (the machine-level contract with a
head envelope, Gate 28, G28-02). **Proof owner:** the `derand` fill proves the host contract
`Complexity.exists_seedMajorityTM`, its corollary `Complexity.seedMajority_mem_DTIME`, and
Theorem 180.1 (`TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp`).

**The formal reading.**
- **The test** is a language `V ∈ P` read on `Turing.pairEncode x u`, the library's two-argument
  convention (`Randomized.polyTimeModel`'s verifiers are read the same way), so that the test may
  depend on the input `x` as well as on the seed `u`.
- **The width** `w : ℕ → ℕ` depends on the input length only, and its unary word
  `x ↦ 1^{w(|x|)}` is polynomial-time computable. This makes `w` computable by the machine and
  bounds it polynomially (`Complexity.PolyTimeComputable.output_length_le`); it is otherwise
  arbitrary, so a consumer may use a non-polynomial schedule such as an integer root, or a
  piecewise one.
- **The count** is `#{u : Fin (w |x|) → Bool | ⟨x, u⟩ ∈ V}`, the numerator of
  `Randomized.randProb` (`Randomized.half_lt_randProb_iff` converts), and **majority** is the
  strict `2^{w(|x|)} < 2 · count`, so ties reject.
- **The machine contract** (`Complexity.exists_seedMajorityTM`) ties correctness, time and a
  head envelope to the **same machine**: some finite machine `M` and constants `c, e`, with the
  budget `B(n) = c · (2^{w(n)} · (n+1)^e)`, satisfy
  - *correctness and time:* `M` decides the majority language within `B`
    (`Turing.FinTM.DecidesInTime`, the library's machine-level decision contract);
  - *head envelope:* at every time `v` of the run of `M` from its initial configuration on `x`,
    every work head is within `B |x|` cells of the origin. This is the coarse envelope derived
    from the time bound, in the form of the clean-module host's `Turing.ModuleHost.Clean.envelope`
    (`machine-library-design.md` §14, rows H14 and H16).
- **The class** `DTIME (n ↦ 2^{w(n)} · (n+1)^e)` is a corollary (`seedMajority_mem_DTIME`),
  which follows from the contract through the reader `Complexity.mem_DTIME_iff`. The `derand`
  fill adds that reader beside `DTIME` (`ClassP/DTIME.lean`) under its pre-approval (Seyoon,
  2026-11-15). Until then the corollary is admitted: without the reader its proof would read
  `Turing.FinTM.DecidesInTime`, `Turing.FinTM.DecidesInTimeVia` and `DTIME` by their
  definitions (Rule 10).

## Contents

* `Complexity.Randomized.SeedMajority.Words`: binary seed words and prefix counts.
* `Complexity.Randomized.SeedMajority.State`: the FP counting round and terminal tests.
* `Complexity.Randomized.SeedMajority.Enumeration`: the finite binary-fuel machine.
* `Complexity.Randomized.SeedMajority.Envelope`: the all-times work-head bound.

## Main results

* `Complexity.exists_seedMajorityTM` — the host's machine-level contract: correctness, time and
  head envelope of one machine, proved through the generic binary-fuel harvest.
  [AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4 of the proof]
* `Complexity.seedMajority_mem_DTIME` — the decision-class corollary
  `∃ e, {x | 2^{w(|x|)} < 2 · count} ∈ DTIME (n ↦ 2^{w(n)} · (n+1)^e)`, proved from
  the host contract through `mem_DTIME_iff`.
* `Randomized.half_lt_randProb_iff` — majority as a probability:
  `1/2 < randProb m A ↔ 2^m < 2 · #{r | A r}` (proved).

## Consumers

* `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` ([PS10, Theorem 180.1]), through
  `seedMajority_mem_DTIME`, with the test **and** the width of the paper proof, both piecewise in
  a threshold length `n₀`. Let `V₁` be the accepting paired language of the `BPP` verifier `M`,
  `m(n)` its coin width, `F'` the evaluator of the expanded generator, and `ℓ(n)` the least `t`
  with `n ≤ t^d`. Below `n₀`, the test is `V₁` itself on the true coins,
  `⟨x, u⟩ ↦ M(x; u)`, with the width `w(n) = m(n)`. From `n₀` on, the test is
  `⟨x, u⟩ ↦ M(x; F'(u)↾m(|x|))` with the width `w(n) = ℓ(n)`. Changing the width alone would not
  remove the generator: `PRG` security says nothing about finitely many seed lengths, so the test
  changes with it.
* Prospectively, `BPP ⊆ EXP` by coin enumeration [AB09, p. 126] (`w = polyLen a k`), which
  `Randomized.mem_EXP_of_inBPP_polyTimeModel` currently obtains through Sipser–Gács.

## Design

* The nearest relative is the existential projection decider `Complexity.exists_proj_decider`
  (`ClassNP/EXP.lean`): the same odometer with an *any* verdict, a fixed width `C(n+1)^c` and
  the test on `x ++ u`. Its engine `enumMachine_contracts` and the `enumCont_*` body are
  private, it does not count, and its width is not a parameter, so it is not reused.
* The polynomial block-majority tests (`Complexity.polyTimeComputable_blockMajorityTest`) count
  over polynomially many blocks; this host counts over exponentially many seeds.
* The test is polynomial-time (`V ∈ P`), not a decider of arbitrary time `Tv` as in
  `exists_proj_decider`: both consumers have polynomial tests, and the clean-module host below
  installs polynomial-time word functions only (`Turing.ModuleHost.clean_install`).
* **Head envelope** (`policy.md` §1, *Hosts come first*; Seyoon's ruling of 2026-11-15, Gate 28,
  G28-02). The contract is machine-level, and its envelope is the coarse one from its own time
  bound `B`, on the same machine, as H14 states `Clean.envelope` and H16 composes with it. A
  sharper envelope does hold (every state word has length `O(n + w(n))`), but no consumer needs
  it and it is not stated. The admitted `loopHostTM_*` and `timedCondTM_*` space specifications
  are not used for it.

## Route for the proof (the `derand` fill)

1. *State loop.* The state word is `⟨x, ⟨i, a⟩⟩`: the binary rank `i` of the current seed and
   the binary acceptance count `a`, from `⟨x, ⟨0, 0⟩⟩`. A step tests `⟨x, word_w(i)⟩ ∈ V`,
   where `word_w(i)` is the width-`w(|x|)` binary word of `i`, adds the verdict to `a` and
   increments `i`. The loop stops when `i = 2^{w(|x|)}` and outputs `[decide (2^w < 2a)]`.
   Every piece is a polynomial-time word function of the state (`Complexity.BinArith`'s
   `add`, `lt` and `beq`, zero padding, the unary width, and `V`'s decider through
   `Complexity.mem_P_iff_polyTimeComputable`).
2. *Machine.* The result-bearing loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host (`Turing.ModuleHost`, with `Complexity.IterateFind.hostTM`, `hostCtrl`,
   `hostRet`, `copyTM` and their run lemmas), exactly as in
   `Complexity.IterateFind.polyTimeComputable_find`, but with the exponential fuel
   `R(n) = 2^{w(n)}`, written as `Nat.bits (2^{w(|x|)})`
   (`w(|x|)` zeros, then a one) from the unary width. The combinator's bound is
   `c (T(n) + 1)(R(n) + 2)`, with `T` polynomial because every state word has length
   `O(n + w(n))` and `w(n) ≤ C(n+1)^c`. The admitted `loopHostTM_*` and `timedCondTM_*` specs
   are not used: `exists_loopFindTM` is proved from the private `loopHost_contracts`.
3. *Count.* The first stopping round is `2^{w(|x|)}`; there `a` counts the ranks `i < 2^w`
   whose word is accepted, which is the `Finset` count above through the bijection
   `i ↦ word_w(i)` between `[0, 2^w)` and `{0,1}^w`.
4. *Normal form.* `c (T(n) + 1)(2^{w(n)} + 2) ≤ b · (2^{w(n)} · (n+1)^e)`: the budget `B`.
5. *Envelope.* Every work head starts at the origin (`Turing.Cfg.init_workTapePos`) and moves by
   at most one cell per step (`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`); the run halts
   by time `B |x|` and is constant afterwards (`Turing.MultiTapeTM.runFrom_of_halt`). This is the
   argument of `Turing.ModuleHost.Clean.envelope`, applied to the machine of steps 2–4.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, §7.1, p. 126 (`BPP ⊆ EXP` by enumerating the random strings) and Claim 2.4 (the
  enumeration argument of `NP ⊆ EXP`).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
-/

namespace Randomized

open Finset

/-- **Majority as a probability.** For an event `A` on `m`-bit strings, the uniform probability
of `A` exceeds `1/2` exactly when more than half of the `2^m` strings satisfy it:
`1/2 < randProb m A ↔ 2^m < 2 · #{r : Fin m → Bool | A (List.ofFn r)}`. This converts the
counting form of `Complexity.seedMajority_mem_DTIME` into the probabilistic form of
[AB09, Def 7.3] and [PS10, Theorem 180.1]. -/
theorem half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card := by
  rw [randProb_eq, lt_div_iff₀ (by positivity), ← Nat.cast_lt (α := ℚ)]
  push_cast
  constructor <;> intro h <;> linarith

end Randomized

namespace Complexity

open Turing

open Classical in
/-- **Deterministic majority over all seeds: the machine contract** [AB09, §7.1, p. 126];
[PS10, §8.2, Theorem 180.1, step 4 of the proof]. For a test `V ∈ P` on paired words and a width
`w : ℕ → ℕ` whose unary word `x ↦ 1^{w(|x|)}` is polynomial-time computable, one finite machine
`M`, with constants `c, e` and the budget `B(n) = c · (2^{w(n)} · (n+1)^e)`,
- decides the strict-majority language
  `S = {x | 2^{w(|x|)} < 2 · #{u : Fin (w |x|) → Bool | pairEncode x (List.ofFn u) ∈ V}}`
  within `B` (`M.DecidesInTime S B`): on every input `x` it halts within `B |x|` steps with
  output `[true]` if `x ∈ S` and `[false]` otherwise; ties (`2 · count = 2^w`) reject; and
- keeps every work head within `B |x|` cells of the origin at every time `v` of its run on `x`:
  `|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ B |x|` (the head envelope, the coarse one
  from the time bound, as `Turing.ModuleHost.Clean.envelope`).

**Deviation.** The source's machine runs the test on every seed and counts; here the test is a
`P`-language on `Turing.pairEncode x u` and the count is a `Finset` count over
`Fin (w |x|) → Bool`, the numerator of `Randomized.randProb` (`Randomized.half_lt_randProb_iff`).
The head envelope is not in the source; it is the host clause of `policy.md` §1.

**Status.** Proved through `SeedMajority.exists_countingTM` and
`SeedMajority.envelope_of_computesInTime`, using only the published decision and
computation readers.

**Proof sketch** (the route of the module docstring; implemented in the helpers).
1. Run the state loop `⟨x, ⟨i, a⟩⟩ ↦ ⟨x, ⟨i + 1, a + [⟨x, word_w(i)⟩ ∈ V]⟩⟩` from
   `⟨x, ⟨0, 0⟩⟩`, stopping at `i = 2^{w(|x|)}` with the payload `[2^w < 2a]`; each piece is a
   polynomial-time word function of the state.
2. Build the machine with the loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host, as in `Complexity.IterateFind.polyTimeComputable_find`, with the fuel
   `Nat.bits (2^{w(|x|)})`; it halts within `c₀ (T(n) + 1)(2^{w(n)} + 2)` with `T` polynomial,
   since `w(n) ≤ C (n+1)^c` (`PolyTimeComputable.output_length_le`).
3. At the stopping round, `a` is the number of accepted ranks `i < 2^w`, which equals the
   `Finset` count through the bijection `i ↦ word_w(i)` onto `{0,1}^w`.
4. Bound `c₀ (T(n) + 1)(2^{w(n)} + 2)` by `c · (2^{w(n)} · (n+1)^e)`.
5. The envelope: the heads start at the origin (`Cfg.init_workTapePos`), move by at most one
   cell per step (`MultiTapeTM.workTapePos_runFrom_mem_Icc`), and the run is constant after its
   halt at a time `≤ B |x|` (`MultiTapeTM.runFrom_of_halt`). -/
theorem exists_seedMajorityTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ (M : FinTM Bool) (c e : ℕ),
      M.DecidesInTime
          {x : List Bool | 2 ^ w x.length <
            2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
              pairEncode x (List.ofFn u) ∈ V).card}
          (fun n => c * (2 ^ w n * (n + 1) ^ e)) ∧
        ∀ (x : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤
            ((c * (2 ^ w x.length * (x.length + 1) ^ e) : ℕ) : ℤ) := by
  obtain ⟨M, c, e, hM⟩ := SeedMajority.exists_countingTM hV w hw
  refine ⟨M, c, e, ?_, ?_⟩
  · apply (FinTM.decidesInTime_iff _ _ _).mpr
    intro x
    have hx := (FinTM.computesFunInTime_iff _ _ _).mp hM x
    rw [MultiTapeTM.indicator_def]
    by_cases h : 2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card
    · simpa only [Set.mem_setOf_eq, if_pos h, decide_eq_true h] using hx
    · simpa only [Set.mem_setOf_eq, if_neg h, decide_eq_false h] using hx
  · intro x v j
    exact SeedMajority.envelope_of_computesInTime
      ((FinTM.computesFunInTime_iff _ _ _).mp hM x) v j

open Classical in
/-- **Deterministic majority over all seeds: the decision class** [AB09, §7.1, p. 126];
[PS10, §8.2, Theorem 180.1, step 4 of the proof]: for a test `V ∈ P` on paired words and a width
`w : ℕ → ℕ` whose unary word `x ↦ 1^{w(|x|)}` is polynomial-time computable, some degree `e`
puts the strict-majority language in `DTIME (n ↦ 2^{w(n)} · (n+1)^e)`:
`∃ e, {x | 2^{w(|x|)} < 2 · #{u : Fin (w |x|) → Bool | pairEncode x (List.ofFn u) ∈ V}}
∈ DTIME (fun n => 2^{w(n)} · (n+1)^e)`. Ties (`2 · count = 2^w`) reject. It is the corollary
of the machine contract `exists_seedMajorityTM` that the consumers of the class read.

**Status.** Proved from `exists_seedMajorityTM`. The proof reads the machine contract
through `Complexity.mem_DTIME_iff`, added beside `DTIME` under the pre-approval of
2026-11-15. It uses no definitional reading of either `DTIME` or `DecidesInTime`.

**Proof sketch.** Take the machine `M` and constants `c, e` of `exists_seedMajorityTM` (the
envelope is not needed here). `M` decides the language within
`n ↦ c · (2^{w(n)} · (n+1)^e)`, which is `c · T n` for `T n = 2^{w(n)} · (n+1)^e`. By
`mem_DTIME_iff` (membership in `DTIME T` is a constant `c` together with a machine deciding
within `c · T`), the language is in `DTIME T`, with the witness `e`. -/
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  obtain ⟨M, c, e, hM, _⟩ := exists_seedMajorityTM hV w hw
  exact ⟨e, mem_DTIME_iff.mpr ⟨c, M, hM⟩⟩

end Complexity

## ===== TCSlib/Cryptography/Randomness/Derandomization.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
import TCSlib.Cryptography.Randomness.Derandomization.Expanded
import TCSlib.Cryptography.Randomness.Derandomization.CoinGap
import TCSlib.Cryptography.Randomness.Derandomization.Majority
import TCSlib.Cryptography.Randomness.Derandomization.TimeBound
import TCSlib.Complexity.Randomized.QuasiPolyHierarchy

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Derandomization from pseudorandom generators

[PS10, Theorem 180.1]: if pseudorandom generators exist, then `BPP ⊆ DTIME(2^{n^ε})` for every
constant `ε > 0`.

**The formal reading.**
- **`BPP`** is `main`'s `Randomized.InBPP Randomized.polyTimeModel` ([AB09, Def 7.3]): an
  efficient verifier with randomness `polyLen a k |x|` and two-sided error `1/3` (decision D-6).
  It is inhabited: `P ⊆ BPP` is `Randomized.inBPP_polyTimeModel_of_mem_P`.
- **`DTIME(t)`** is `main`'s `Complexity.DTIME`, deterministic multi-tape time `O(t(n))`, the
  source's reading ("bounded by `O(t(n))`").
- **The bound** `2^{n^ε}` is taken with a real exponent and rounded up (`subexpBound`), so that
  every real `ε > 0` is covered, as in the source. It is at least `1` at every length
  (`subexpBound_pos`), so `DTIME (subexpBound ε)` is not empty for a trivial reason (`DTIME` of a
  bound that vanishes somewhere is).
- **"PRGs exist"** is `∃ G : PRG, G.Secure`, the ch. 2–4 layer's [PS10, Definition 77.1], secure
  against non-uniform distinguishers. A PRG of any stretch `ℓ(n) > n` gives one with any polynomial
  stretch by the ch. 2–4 expansion theorems (`PRG.Secure.truncate`, `prg_expand`), which the proof
  needs with a computable integer-root seed schedule and a syntactic polynomial output
  envelope, as specified in the proof sketch below.

## Main definitions

* `Randomness.subexpBound`: `n ↦ ⌈2^{n^ε}⌉`.

## Contents

* `Randomness.Derandomization.RootSchedule`: the integer-root seed schedule.
* `Randomness.Derandomization.AdviceGap`: the non-uniform advice gap bound.
* `Randomness.Derandomization.Expanded`: the secure polynomial output envelope.
* `Randomness.Derandomization.CoinGap`: the uniform prefix probability identification.
* `Randomness.Derandomization.Majority`: the piecewise verifier and strict majority.
* `Randomness.Derandomization.TimeBound`: the asymptotic estimate and finite exceptions.

## Main results

* `Randomness.subexpBound_pos`: the bound is positive.
* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1), proved through the shared
  seed-majority machine contract and its DTIME corollary.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, Definitions 1.12 and 7.3 (`main`'s `DTIME` and `BPP`).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity TCSlib.Cryptography

/-- The subexponential time bound `n ↦ ⌈2^{n^ε}⌉` (real exponent, rounded up). -/
noncomputable def subexpBound (ε : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊

/-- The subexponential bound is the natural ceiling of `2^{n^ε}` with real exponents:
`subexpBound ε n = ⌈2^{n^ε}⌉₊`. -/
theorem subexpBound_eq (ε : ℝ) (n : ℕ) :
    subexpBound ε n = ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := rfl

/-- The subexponential bound is positive at every length. -/
theorem subexpBound_pos (ε : ℝ) (n : ℕ) : 0 < subexpBound ε n :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)

/-- **Theorem 180.1: pseudorandom generators derandomize `BPP` in subexponential time**
[PS10, Theorem 180.1]: if a secure PRG exists, then every language of `main`'s `BPP` is in
`DTIME(2^{n^ε})` for every `ε > 0`.

**Status.** Proved through `Complexity.exists_seedMajorityTM` and
`Complexity.seedMajority_mem_DTIME`; the helpers introduce no admissions.

**Proof sketch** ([PS10, Theorem 180.1], with an explicit piecewise test).
1. Choose an integer `d ≥ 2` with `1/d < min(ε,1)`. The least natural root
   `ℓ(n) = min{t | n ≤ t^d}` has an FP unary word and satisfies
   `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^(1/d)+1`, including at zero.
2. Expand a secure generator to `a(s^d+1)^k+s+1` and extract its FP evaluator.
   Apply the verifier bridge to one bad input at each bad seed length, with
   advice bound `s^d`. The published probability bridge and prefix projection
   identify its PRG advantage with the verifier gap. Negligibility's inverse-linear
   bound rules out every gap above `1/12` beyond a seed threshold, hence beyond
   some input threshold `n₀`.
3. Below `n₀`, use the original verifier with its true polynomial coin width;
   from `n₀` on, use the generated prefix and width `ℓ(n)`. Both this paired
   test and its unary width are polynomial-time. Acceptance is above `1/2`
   exactly on members, with margins at least `7/12` and at most `5/12` in the
   generated case. `half_lt_randProb_iff` identifies `L` with the strict seed
   majority, including ties and zero widths. No exceptional-input table is used.
4. Apply `seedMajority_mem_DTIME`. The logarithm of `2^w(n)(n+1)^e`, divided
   by `n^ε`, tends to zero because `1/d < ε`; thus the time is eventually at
   most `2^(n^ε)`. A natural constant absorbs all earlier lengths, since the
   rounded bound is positive. Finish through `DTIME.mono` and
   `Randomized.DTIME_const_mul_subset`. -/
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  intro L hL
  obtain ⟨d, hd, hdε, _⟩ := Derand.exists_root_degree hε
  have hdpos : 0 < d := by omega
  obtain ⟨V, w, n₀, hV, hw, hevent, hmajority⟩ :=
    Derand.exists_seed_majority hPRG hL d hdpos
  obtain ⟨e, htime⟩ := seedMajority_mem_DTIME hV w hw
  rw [← hmajority] at htime
  obtain ⟨C, hbound⟩ := Derand.seed_time_le_subexp hdpos hε hdε w n₀ hevent e
  apply Randomized.DTIME_const_mul_subset C (subexpBound ε)
  apply DTIME.mono (fun n => ?_) htime
  simpa only [subexpBound_eq] using hbound n

end TCSlib.Cryptography.Randomness
