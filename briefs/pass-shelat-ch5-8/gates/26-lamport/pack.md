# Gate 26 · Lamport signatures are one-time secure (`lamport`, Theorem 137.2)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #309](https://github.com/Shilun-Allan-Li/tcslib/pull/309) at
  `987efb5156b3ae20cff4576b379eb1c607f33cb0` (branch `land/pass-shelat-lamport`, tree
  `dc1fb8fb5ba7fb427c6c94a03a6d64accf04e695`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `dee0de32ee33d7188afe97bdc3089fac68412057` (the merge base).
  - The fill was issued on `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, the merge of #299.
  - Between the issue base and the PR base, two merged PRs change non-record files: #303 (merge
    `d82e9a50414c6be160bcb3bd63ffdeb95e41e21c`, the four ext-nosrc files under `Randomness/`) and #305 (merge
    `8d0db40144102b847921b51ee2d1ebfd2994836d`, `scripts/campaign_style_lint.py` only). Neither touches a file of this PR.
    Every other commit in that range, and each of the 7 commits from the PR base to the records tip
    `09d0b6efbf795b94cb02c707b6dfd422b812441e`, touches records only (`PassShelatChapter5-8Plan.md` and `briefs/`). The
    PR diff equals the unit's diff from the issue base, byte for byte.
- **Commits:** 10.
  - The Codex worker's 6 patches (job `lamport`), applied with `git am` and rebased without conflict, author kept as
    delivered: `f95f2c9703cc2fc91c08ecc173abcd8e1368e5f0` (planted coupling and algorithm readers),
    `228f9d852828f386e5198ef0c9266c557522ad06` (helper imports in the facade),
    `98aef759419ffd9ae66c35ffa308d361949140dc` (the averaging bound for the actual forgery game),
    `188e4f315de417e937422a787c844de72f4c889e` (idempotent local opacity installation),
    `ea3d76b0ea4cbcbcc76afe0146504a4d0aee64c2` (one-time security via the planted-machine reduction) and
    `846103fae130d86eb7bb3cb9deff33804b0bd999` (reuse of the public `takeLen_poly`/`dropLen_poly`). At
    `846103fa` the 18 files are byte-identical to the worker's `src/`.
  - Landing edit **LE-facade** `99d7d775935c62f09b699923dfa3e2030e6b869a`: order only, sorting the 16 helper imports of
    `Authentication.lean` alphabetically after `Signatures.Lamport`.
  - Landing edit **LE-width** `1023834eb030197ef2fc94c7270cc0d5ac85ab12`: whitespace only, re-wrapping 11 new
    over-width lines in `Experiment`, `Machine`, `MachineSpec` and `Realization`.
  - Landing edit **LE-rule10** `32b1730838292add4c844ca1cf34b747412831d3`: proof only, in
    `LamportFill.exists_realization_machine` (`Realization.lean`).
  - Landing edit **LE-doc** `987efb5156b3ae20cff4576b379eb1c607f33cb0` (the head): 188 formula docstrings and 7 proof
    sketches; docstrings only.
- **Scope:** a **proof audit**. The job proves the admitted `Authentication.lamport_oneTimeSecure` [PS10, Theorem
  137.2]: Lamport's scheme is one-time secure when `f` is a strong one-way function. Its statement passed Gate 06
  (prong A) and is frozen.
- **Brief:** `fills/lamport/issued-r1/brief.md` on the records branch (SHA-256 `fe4c7706…`; exchange pack
  `b436d19a`): three checkpoints following the docstring sketch (planted experiment; averaging and best position;
  machine, advice and negligibility), the owned file plus the helper directory `Lamport/` only, `Games/Efficiency.lean`
  and every other file frozen, the duplication rule with "overlap" disclosures, Rule 10 with seals reported with
  `PolyExpr.eval` both excluded and sealed, and the evidence-completeness rule.

## What changed

All paths are under `TCSlib/Cryptography/Authentication/`; `L/` is `Signatures/Lamport/`. The PR touches 18 Lean
files: 2 modified and 16 new (3256 insertions, 7 deletions). Line counts are base → worker head `846103fa` → PR head.

| File | Status | Lines |
|---|---|---:|
| `Signatures/Lamport.lean` | owned, modified | 567 → 973 → 999 |
| `L/Advice.lean` | helper, new | 134 → 148 |
| `L/Averaging.lean` | helper, new | 135 → 140 |
| `L/AveragingExtra.lean` | helper, new | 89 → 91 |
| `L/Blocks.lean` | helper, new | 78 → 78 |
| `L/Closing.lean` | helper, new | 94 → 95 |
| `L/Encoding.lean` | helper, new | 84 → 85 |
| `L/Experiment.lean` | helper, new | 226 → 270 |
| `L/InversionProbability.lean` | helper, new | 87 → 89 |
| `L/Machine.lean` | helper, new | 340 → 407 |
| `L/MachineSpec.lean` | helper, new | 234 → 268 |
| `L/Nonabort.lean` | helper, new | 64 → 65 |
| `L/Planted.lean` | helper, new | 452 → 513 |
| `L/Realization.lean` | helper, new | 193 → 230 |
| `L/Seed.lean` | helper, new | 73 → 77 |
| `L/Statistics.lean` | helper, new | 149 → 153 |
| `L/TableCoins.lean` | helper, new | 88 → 92 |
| `../Authentication.lean` | frozen facade, approved imports | 52 → 68 → 68 |

The proof follows [PS10, Theorem 137.2] and the frozen sketch (REPORT § Proof route, review § Content):
1. **Planted experiment** (`Planted`, `TableCoins`, `Seed`, `Encoding`, `Blocks`): at a fixed position `(i, c)`, plant
   the challenge `y` in one public-key cell; answer a signing query `m` only when `m_i ≠ c` and abort otherwise;
   extract `σ'_i` from an accepted forgery with `m'_i = c`. Safe runs are coupled with the honest table.
2. **Favourable fraction** (`Averaging`, `AveragingExtra`, `Statistics`, `Experiment`): a successful honest run with
   query `m` and fresh `m'` has favourable fraction `#{i : m_i ≠ m'_i}/(2n) ≥ 1/(2n)`, exactly `1/2` with no query;
   coordinate resampling makes the planted preimage independent while keeping the average. No independence after
   conditioning on non-abort is assumed.
3. **Best position** (`lamport_exists_best_position`): averaging gives, for each `n ≥ 1`, a position `i` with
   `ε(n)/(2n) ≤` the fair-bit average of the planted success probability.
4. **Machine** (`Machine`, `MachineSpec`, `Nonabort`, `Realization`, `Advice`, `InversionProbability`): T1
   (`Games.exists_handlerMachine`) realizes the planted simulation as one machine; the best position is supplied as
   `Nat.size n`-bit advice through `NUPPT.exists_withAdvice` and decoded to unary; only non-aborting successes are
   transported to actual inversion witnesses (`fairBit_redProbability_le_invProbAt`).
5. **Conclusion** (`Closing`, `LamportReduction.oneTimeSecure_of_inversion_lower`): `ε(n) ≤ 2n·inv_C(n)` for `n ≥ 1`;
   strong one-wayness and `Negligible.mul_pow`, `const_mul` and `mono` make `ε` negligible, with `n = 0` a finite
   exception.

The edge cases are `n = 0` (finite exception; machines and advice stay total), no query (empty log, fraction `1/2`),
freshness (`m' = m` excluded; distinct messages differ in a bit), malformed or wrong-length forger words (the fixed-width
codec and guarded verifier, through their readers) and abort branches (a false final abort flag gives safe-query
agreement; no successful abort is assumed). No `take_poly` or `drop_poly` copy remains: `Machine` uses the published
`ReductionSupport.takeLen_poly` and `dropLen_poly`.

**Statements:** decls2 from the issue base to the worker head gives 220 ADDED, 0 CHANGED, 0 REMOVED, and the LE-doc
evidence reproduces the same 220 names and statements at the PR head. All 47 pre-existing declaration headers of
`Lamport.lean` are byte-identical, the target's included; only the target's body and step 5 of its sketch changed,
plus the module docstring's title, the target's Main-results line and the new `## Contents`.

## Rulings and records in force

1. **The sixteen facade imports are an approved scope extension (Seyoon).** The brief froze every file outside the owned
   file and helper directory. The decision log (2026-11-14, "Rulings confirmed (Seyoon)") records that the `lamport`
   worker's chat authorization stands for **exactly sixteen** helper imports in `Authentication.lean`. The same row
   records, as the maintainer's plan (not a ruling), that the `hash-sign` and `lamport` facade imports are merged into
   one consistently ordered facade at landing.
   - The worker's own record (`worker/requests/facade-authorization.md`) quotes the reply "Allow the required facade
     imports", which it reads as import-only registrations as helpers are completed; its
     `authentication-facade-imports.patch` is the checkpoint-1 request (three imports). The number sixteen comes from
     the decision log, not from the worker's record.
   - Against the base, the facade diff is exactly 16 added `Signatures.Lamport.*` import lines (the 16 helper
     modules), 0 removed, every non-import line identical.
   - **LE-facade** (the maintainer's) only reorders those 16 lines, alphabetically after `Signatures.Lamport`, the same
     form as the dl-crh and hash-sign LE-facades. The file's lines are the same multiset before and after.
   - **Not a finding.** What you can raise: any facade change beyond those sixteen lines, a cycle, or a change to what
     the facade's other imports export.
2. **Seal B: the 5 new helper-statement failures are accepted as inherited (Seyoon, 2026-11-14).** Seal B also seals
   `PolyExpr.eval`. At the base, seal B fails 11 declarations of `Lamport.lean` (`lamport`, `lamportOWF`,
   `lamportOWF_f`, `lamportOWF_inLen`, `lamportOWF_outLen`, `lamport_gen`, `lamport_msgLen`, `lamport_sigLen`,
   `lamport_sign`, `lamport_ver` and the target `lamport_oneTimeSecure`). At the head it fails those 11 plus 5 new
   helper statements: `lamport_signImpl_expect`, `lamport_loggedSignImpl_expect`, `lamport_forgerCodec`,
   `lamport_forgeGame_accept_eq_honestProbability` and `lamport_exists_best_position`. Seyoon's ruling accepts the 5
   as inherited from the frozen design `f : ∀ n, (Fin n → Bool) → …`, which is used where `Fin (var.eval n)` is
   expected and so typechecks only by unfolding `PolyExpr.eval`; the 11 base failures are the same class. The
   follow-up, restating the frozen hypothesis over `Fin (var.eval n)` with a published reader, is recorded in DL-43
   (it would clear all 16 and needs its own gate).
   - **Not a finding.** What you can raise: a seal-B failure among the 16 whose cause is not that frozen `f`, or any
     other seal-B failure at the head.
3. **`PolyExpr.eval` is notation (Q1, the user, 2026-11-07).** Seal A, which exempts it, is the canonical Rule-10
   seal; seal B is run and reported because the brief asks for both.
4. **Rule 10: a `CoeFun`/`Coe` instance whose body is a structure projection is notation (Seyoon, 2026-11-14).** This
   is `FinDist`'s `⟨FinDist.prob⟩`. The coe-variant seals are canonical, and the strict variant is still run with its
   differences attributed. **For this unit the two variants agree in every row** (review seal table, and LE-rule10's
   re-seal of `Realization.lean`).
5. **LE-rule10 (the maintainer's landing edit): proof only.** Under seal B, the worker's proof of
   `LamportFill.exists_realization_machine` read T1's oracle domain `(bitSpecAt var (var·var) n).dom j`, its answer
   type and its output width as `Fin n → Bool`, `Fin (n * n) → Bool` and `Fin (n + n * n) → Bool`, which holds only by
   unfolding `PolyExpr.eval` (6 errors in that one declaration). LE-rule10 reads T1's widths through
   `PolyExpr.eval_var`, `eval_mul`, `eval_add` and `eval_const`, moves the query and the table signature by
   `Fin.cast`, proves the planted simulation for arbitrary widths with equations to `n`, `n * n`, `n + n * n` and `1`,
   and substitutes them (`landing-le/0001-*.patch`). It changes `Realization.lean` only, inside that proof: 1 CHANGED
   and 267 UNCHANGED in `touched`, 268 headers byte-identical, decls2 empty. Seals A and B for `Realization.lean` now
   pass in both variants; paired controls 8 probes and 30 sealed negatives, ALL_OK. The build at `32b17308` gives 9/9
   rc 0 through root `TCSlib`.
6. **LE-doc (the maintainer's landing edit): docstrings only.** Its 188 hunks all lie inside doc comments; with doc
   comments blanked all 16 changed files are byte-identical (the `run_cmd` blocks included); `Authentication.lean` is
   untouched; 268 headers byte-identical; decls2 against `32b17308` is empty.
   - The 188 formulas are the 189 NO-FORMULA public declarations of the review minus the target, whose first line is
     the book statement (prose) and whose tag, sketch, header and body LE-doc leaves untouched. Docaudit after: 220 OK
     plus the target.
   - Sketches: 7 added. Every proof of 15 or more lines has one; of the six 10–14-line proofs without one, five were
     sketched. `runAt_lamportSign_table` (10 lines, `Lamport.lean`) has none, because a sketch would take the file to
     1000 lines.
   - **`Lamport.lean` is now at 999 lines.** A split must happen before it grows any further; this is recorded as a
     follow-up and is not a finding of this gate.
7. **The opacity blocks (worker patch 4) are a performance guard.** `Lamport.lean`, `Experiment.lean` and
   `Statistics.lean` each run a `run_cmd` (head lines 797, 41 and 37; the review cites 777, 40 and 36 at `1023834e`) that
   sets `attribute [local irreducible]` on `ProbComp.expect`, `ProbComp.sample` and `OracleComp.bind` unless the name
   is already irreducible, the seal harness's own install pattern. The review records that the blocks are file-local,
   only add opacity, and are no-ops under a seal (the seal has already installed the three names); the attributes do not
   leak to a downstream importer. Without the block `Statistics` did not finish in about 8.5 minutes (5.2 GB) against 2
   seconds with it. In-file controls and paired-control rows for the three names show that the seals stay meaningful.
   Evidence: `landing/opacity-*` (see the note on `opacity-runner.out` below) and `opacity-runs/`, `controls-infile/`
   in `review-evidence.zip`.
8. **The facade-completeness lint fix, #305 (Seyoon's ruling to fix the bug by a PR on our branch; merged by
   Seyoon).** The Cryptography baseline is now **92 FAIL / 102 WARN**. At the head the lint gives 92 FAIL / 101 WARN:
   the only difference from the records tip is that `Lamport.lean`'s check-8 WARN (`lamportGen`, `lamportSign` without
   lemmas) is resolved. No FAIL or WARN is new, and the 16 helpers raise no facade FAIL. Under the old lint the count
   was 216 / 102 at the base and 216 / 101 at the worker head.
9. **The landing edits are the maintainer's** (the ext-nosrc, cca2-ett, dl-crh and hash-sign precedents; decision log
   rows of 2026-11-14): LE-facade order only, LE-width whitespace only, LE-rule10 proof only, LE-doc docstrings only.
   Re-checked for this pack from git objects: LE-facade has the same line multiset and changes import lines only;
   LE-width is identical with all whitespace removed; LE-doc is identical with doc comments blanked; LE-rule10's seven
   hunks all fall after the `:= by` that ends the statement of `exists_realization_machine` (old lines 116–186; the
   statement ends at line 105).

## What is frozen

- **The target's statement** (quoted in the brief), the 46 other pre-existing declarations of `Lamport.lean`, the
  statement prose and the global simp attributes.
- **Every file outside** `Signatures/Lamport.lean` and `Signatures/Lamport/`, except the sixteen approved facade
  imports. That includes `Signatures/Defs.lean`, `Signatures/HashAndSign.lean`, `Asymptotic/Collections.lean`,
  `Asymptotic/OneWay.lean` and `Games/Efficiency.lean`.
- **The landing edits:** LE-facade changes import order only, LE-width whitespace only, LE-rule10 one proof only, and
  LE-doc docstrings only.

## Questions for the audit

**1. Correctness against [PS10, Theorem 137.2]**
- Does the proof establish the frozen statement for every one-query forger under `hf`, including `n = 0`, no query,
  `m′ = m`, wrong-length or malformed words and signatures, and abort branches reached by a successful forger?
- Is the planted experiment coupled correctly with the honest run, so that on jointly favourable pairs the experiments
  agree and extraction inverts `y`?
- Is the favourable fraction `≥ 1/(2n)` (exactly `1/2` with no query) proved for the actual forge game, without
  assuming independence after conditioning on non-abort?
- Is the inverter `C` a legitimate NUPPT inverter: T1's handler bounds, `Nat.size n`-bit advice through
  `NUPPT.exists_withAdvice` with an unchanged coin polynomial, and the transport of only non-aborting successes?
- Does `ε(n) ≤ 2n·inv_C(n)` for `n ≥ 1` with the negligible closure give `OneTimeSecure`?
- Does the edited step 5 of the target sketch describe the delivered proof?

**2. Frozen-statement integrity**
- Are the target's header and the other 46 pre-existing declarations byte-identical (`landing/header-bytes.txt`,
  `landing/decls2.tsv`, `landing/touched.tsv`), and are only the target's body, step 5 of its sketch and the module
  docstring changed?

**3. The facade imports (ruling 1)**
- Is the `Authentication.lean` change exactly the sixteen helper imports, in LE-facade's order, and does it match the
  approval as the decision log records it?

**4. The seal-B disposition (ruling 2)**
- Do all 16 seal-B failures in `Lamport.lean` come from the frozen `f : ∀ n, (Fin n → Bool) → …` being used at
  `Fin (var.eval n)`, and nothing else (`landing/seal-table.txt`, the seal-B records and logs in
  `review-evidence.zip`)? In particular, does the target fail seal B only through that inherited class?
- Do the seals, collected from the elaborated terms plus matchers, cover every touched declaration of the 18 files over
  the full closure, at the base and at the head, in both variants? Do the paired controls (16 probes, 37 sealed
  negatives, ALL_OK; `landing/ctlcheck.log`) show that the seals bite? Explicit-unfold scan: 797 items, 0 foreign.
- Seals were run at `1023834e` for all 18 files and re-run at `32b17308` for `Realization.lean`; LE-doc is code-identical
  with doc comments blanked. Is carrying the seals forward to the head sound?

**5. LE-rule10 (ruling 5)**
- Is it proof only, and is the new width transport correct (casts, `List.ofFn_congr`, the `subst` of the width
  equations)? Does seal B now pass for `exists_realization_machine` in both variants, with controls that bite
  (`le-evidence.zip`: `rule10/`)?

**6. LE-doc (ruling 6)**
- Does each of the 188 new formulas state what its declaration proves or defines, and does each of the 7 new sketches
  describe its proof (`landing-le/0002-*.patch`; `statements/docaudit-after.tsv`, `statements/sketchaudit-*-after.tsv`
  in `le-evidence.zip`)? A formula or sketch that misstates its declaration is a minor. The maintainer's open points:
  the formulas are hand transcriptions checked by reading; `LamportFill.` prefixes are omitted in `Lamport.lean`'s
  formulas; the `Statistics` formula defines its `𝔼`/`[A]` shorthand inline.
- Is LE-doc docstrings only?

**7. The opacity blocks (ruling 7)**
- Are the three `run_cmd` blocks safe: file-local, only adding opacity, no-ops under a seal, not leaking to importers,
  and unable to hide a Rule-10 read or change a statement? Do the seals stay meaningful with the blocks present?

**8. Duplication**
- Does any new declaration duplicate a public TCSlib or Mathlib lemma beyond DL-42 and DL-43 (below)?
- Is any private lemma of another file copied rather than re-derived from published readers, beyond the worker's
  disclosed overlaps (`OneWay.lean` `ofFn_blocks_two_symm`; `Lamport.lean` `lamportVerFun_sign.hflat`; the removed
  prefix wrappers' relatives `TMSAT.tmsat_pt_take`, `Hardness.clA5Drop_native`, `DiscreteLogHardcore.dlb_take_poly`
  and `dlb_drop_poly`)?

## Known dispositions (not findings)

- **DL-43** (duplication ledger, open, deferred): the **undisclosed** `LamportFill.signatureBlock σ i` =
  `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class; review finding 4), and the near relatives
  `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`) and `Averaging.expect_favourable_of_success` (the
  `ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Fix: re-point `signatureBlock`, promote the averaging
  lemma. DL-43 also holds the frozen-statement restatement (ruling 2).
- **DL-42** (open, deferred), the overlap with `hash-sign`: `lamport_codec_ext` ≈ `MachineCodec.ext_of_fields`,
  `lamport_forgerCodec` is an instance of `forgerCodec_eq_bitCodec`, and `exists_pure_of_cost_zero` ≈
  `eq_pure_of_cost_zero` (`landing/hash-sign-overlaps.txt`). The fold happens once both units have landed. The
  hash-sign code is not part of this audit (it is Gate 25, draft PR #308).
  What you can raise: a copy outside DL-42 and DL-43, or a disagreement with them.
- **The interaction with #308 on the `Authentication.lean` facade.** #308 (hash-sign, head
  `4f0280c85fae8730ca0dfad980b41749452980fa`) adds its eight approved helper imports to the same facade. The two PRs
  are disjoint otherwise and are built each on its own base. A trial merge has no conflict: the review's
  `git merge-tree` of `1023834e` with `4f0280c8` (`review-evidence.zip`: `landing/facade-combine-check.txt`, with the
  combined import block), and, re-run for this pack on the current heads, `git merge-tree --write-tree 4f0280c8 987efb51`
  gives tree `f779472f460c7ff08e55b8c9cb159f788862120c` with no conflict (LE-rule10 and LE-doc do not touch the
  facade). The combined tree has not been built. At this base `HashAndSign.lean` still has its issued `sorry`, which is
  why its row in `landing/root-checks.jsonl` shows 1 sorry.
- **7 linter warnings** (review finding 7): unused hypotheses, an unused `simp` argument and a dead `exact le_rfl`
  (`Blocks` 2, `InversionProbability` 2, `MachineSpec` 2, `Realization` 1). An optional follow-up.
- **The two lines over 100 characters** (`Lamport.lean:90`, `Authentication.lean:60`, 101 characters each) are the
  base's (lines 54 and 44 there), both in module docstrings.
- **The worker's commit hashes** (`47ced271` final, `252ec646` the earlier candidate) cannot be reproduced, because the
  delivery records no committer metadata. The content is verified: `git am` at the issue base gives tree `a84df5e9`,
  and the 18 files are byte-identical to `src/`.
- **Review slips, disclosed here; the review record is not edited.**
  - Finding 3 says "189 of the 221 new public declarations". The 221 docaudit rows are the 220 new declarations plus
    the pre-existing target, and the 189 NO-FORMULA rows include the target; LE-doc therefore adds 188 formulas.
    Its "8 long proofs" are the 8 proofs of 10 or more lines without a sketch; LE-doc adds 7.
  - The decision-log row of the review (2026-11-14) says "LE-doc (189 formulas, 8 sketches)", the plan at that time;
    the landing row and the review's last section record the result, 188 and 7.
  - The review's "Sizes" line (`Lamport.lean` has 973) and its opacity line numbers (777, 40, 36) are at `1023834e`,
    before LE-doc; at the head they are 999 lines and 797, 41, 37.
- **Evidence notes.**
  - `landing/opacity-runner.out` is empty (0 bytes); so is its original `logs/opacity-runner.out` in
    `review-evidence.zip`. The opacity runs' results are `opacity-runs/results.jsonl` and `opacity-runs/mods/*.log`
    in that ZIP.
  - The two `landing-le/` patches are `git format-patch 1023834e..987efb51` of the two commits (reproduced byte for
    byte from git objects for this pack). `le-evidence.zip`'s `landing/0009-*.patch` and `landing/0010-*.patch` are the
    same commits from the series `dee0de32..987efb51`; the two forms differ only in the Subject line (`[PATCH 1/2]` vs
    `[PATCH 09/10]`, re-wrapped). Every other extract is a byte copy of a ZIP entry.
  - `landing/lint-new-diff-workerhead.txt` and `landing/lint-new-diff-landinghead.txt` have the same bytes (the worker
    head and the landing head have the same lint lines).

## Also check

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]` at the head, and so does
  `LamportFill.exists_realization_machine` (`landing/axioms-head.txt`). At the base the target also had `sorryAx`.
- Census at `1023834e` (`review-evidence.zip`: `logs/census-head-summary.txt`): 321 stored constants in the 18 files,
  all with subsets of those three axioms; base 67 → head 321, 254 added, none removed, type-changed or moved; the only
  axioms change is the target. LE-rule10 changes one proof and LE-doc no code.
- Nothing new is `@[simp]` or an instance. One new public abbreviation, `LamportFill.Table`, with its reader
  `Table_eq`; the other abbreviations the census lists are generated matchers.

**Admissions:** 22 → 21 in the 12 issued modules; only the target is removed (`landing/sorry-census.txt`).

**Sizes and widths:** every file is under 1000 lines (`Lamport.lean` 999); every line is at most 100 characters except
the two pre-existing lines above (`source-head.json`).

**Build:** at `987efb51`, the 24 changed and downstream modules (the 16 helpers, `Lamport`, `HashAndSign`,
`Authentication`, #303's 4 base-delta modules and root `TCSlib`) have rc 0 and 0 errors
(`landing/root-checks.jsonl`; each changed file's `source_sha256` matches `source-head.json`), and the whole-tree check
passes for 1217 modules at the head's source and olean hashes (`landing/final-tree-check.txt`). No `audits/*/Checks`
module imports the unit. The olean tree was restored to the base snapshot afterwards.

## Evidence

- **`review.md`:** the maintainer's delivery review, verdict ACCEPT WITH LANDING EDITS, with its last section on
  LE-rule10 and LE-doc.
- **`verification.zip`** (48 entries): every file the review cites, as byte-identical originals. Its `SHA256SUMS`
  lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence.zip` (`fills/lamport/final-r1/`, SHA-256 `99b03cab…`) and `review-evidence-SHA256SUMS`, its
    manifest. The ZIP has 626 entries: 52 directory entries and 574 file entries. Under `lamport-r1/`, the file entries
    are exactly the 573 manifest paths plus that folder's `SHA256SUMS`, which is byte-identical to the manifest; all
    573 hashes verify. It covers integrity, the build and the full-tree check with the restore, decls2, header bytes,
    `touched`, the docstring and sketch audits, the census and axioms, the strict and coe-variant seals at the base and
    the head, the paired and in-file controls, the opacity runs, the scan, the old and new lint, sizes and the
    duplication grep;
  - `le-evidence.zip` (SHA-256 `329b830f…`, 217 entries, all files, exactly the manifest's paths) and
    `le-evidence-SHA256SUMS`: LE-rule10 with its seals and controls, the LE-doc patch and its docstring-only checks,
    the build at the head, the axioms, the #305 lint and the restore;
  - `landing/` and `landing-le/`: the review's extracts (see the evidence notes above);
  - `records/`: the issue package `fills/lamport/issued-r1/`, the duplication ledger, the decision log and the #305
    record `maintainer/lint-facade-fix-2026-11-14/` (README and patch), at records
    `09d0b6efbf795b94cb02c707b6dfd422b812441e`;
  - `worker/requests/`: the worker's `evidence/requests/` (`facade-authorization.md`,
    `authentication-facade-imports.patch`, `host-serialization-override.md`, `worker-coordination-note-authorized.json`),
    byte copies from exchange `5a50cdc0b738d955c346d2a0f81944ff1f11c94c`. The last two record the worker's host
    process limit and a coordination note to its peer workers, as the worker reports them; they bear on the
    environment, not on the Lean code.
- **The worker's own evidence:** on the exchange at `5a50cdc0b738d955c346d2a0f81944ff1f11c94c`, under
  `inbox/fills/lamport/`. Its top `SHA256SUMS` lists 3064 files and `evidence/SHA256SUMS` 3038, all delivered.
- **`landing/`:** at the final head, byte copies of `le-evidence.zip` entries.
  - `root-checks.jsonl` (= `build/results.jsonl`): the 24 modules at `987efb51`, rc 0.
  - `final-tree-check.txt` (= `build/tree-check-head.txt`): 1217/1217 modules at `987efb51`'s source and olean hashes.
  - `axioms-head.txt` (= `axioms/mods/LpProbe_AxiomsHead.log`): the axioms of the target and of
    `exists_realization_machine` at the head.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `5a50cdc0`.
- **`pr.diff.txt`:** `git diff` from the base to the head (18 paths, 3256 insertions, 7 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 18 changed files.
- **`sources.zip`:** the source closure at the head of every changed module, 177 files.

## Findings delivery

Return `gate26-lamport-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation beyond the approved facade imports.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
