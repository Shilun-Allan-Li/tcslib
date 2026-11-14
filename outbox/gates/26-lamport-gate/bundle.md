## ===== briefs/pass-shelat-ch5-8/gates/26-lamport/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/26-lamport/review.md =====

# lamport · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** LE-facade, LE-width, LE-rule10 and LE-doc are all done and built; see the last
section (head `987efb51`, PR #309).

## Delivery and landing branch

**Delivery**
- **Source:** Codex worker, exchange `5a50cdc0b738d955c346d2a0f81944ff1f11c94c` (`inbox/fills/lamport/`), 6 patches on the
  issue base `eff2dcd0`.
- **Target:** `lamport_oneTimeSecure`, [PS10, Theorem 137.2]: Lamport signatures are one-time secure under a one-way
  function. The brief is `../issued-r1/brief.md`, SHA-256 `fe4c7706…`.
- **Files:** the owned `Authentication/Signatures/Lamport.lean`; 16 new helpers under `Lamport/` (`Advice`,
  `Averaging`, `AveragingExtra`, `Blocks`, `Closing`, `Encoding`, `Experiment`, `InversionProbability`, `Machine`,
  `MachineSpec`, `Nonabort`, `Planted`, `Realization`, `Seed`, `Statistics`, `TableCoins`); and the facade
  `Authentication.lean`.
- **Approved exception** (Seyoon, 2026-11-14): exactly sixteen helper imports in `Authentication.lean`. The facade's
  import set is exactly those 16.

**Landing branch** `land/pass-shelat-lamport`
- The worker commits keep their author (Seyoon's git identity) and are rebased onto records tip
  `dee0de32ee33d7188afe97bdc3089fac68412057`, which comes after #305. The rebase had no conflict.
- **Worker commits:** `f95f2c97`, `228f9d85`, `98aef759`, `188e4f31`, `ea3d76b0`, `846103fa`.
- **LE-facade** `99d7d775`: sorts the 16 imports alphabetically after `Signatures.Lamport`, the same form as in dl-crh
  and hash-sign. Order only. A trial merge with `land/pass-shelat-hash-sign` has no conflict.
- **LE-width** `1023834eb030197ef2fc94c7270cc0d5ac85ab12` (tree `94aff1a580494d50002c6dde390c0112ea3212b6`): re-wraps 11
  new over-width lines. Whitespace only.
- The worker's commit ids (`47ced271`, `252ec646`) cannot be reproduced, because no committer metadata was delivered.
  The content is verified.

**Evidence:** `review-evidence.zip`.
- SHA-256 `99b03cabb109e59240525b91b1c20d473468258a94284f521b14ab83617cc7c0`.
- Its file entries are the 573 manifest paths plus `SHA256SUMS`, together with directory entries. The manifest is
  `evidence-SHA256SUMS`.
- Extracts are in `landing/`.

## Checks

**Integrity**
- The manifests verify 3064/3064 and 3038/3038, with exact path sets.
- The issue package verifies 7/7 and `SOURCE-SHA256SUMS` 150/150.
- `git am` gives tree `a84df5e9`, and the 18 files are byte-identical to `src/`.

**Build** on `$SP/dl-oleans-2`
- 24 modules give rc 0: the 18 changed modules, `HashAndSign`, `Authentication`, the #303 base-delta modules and root
  `TCSlib`.
- The whole-tree check passes: 1217 modules plus PFR.
- No `audits/*/Checks` module imports the unit.
- The tree was restored to the base snapshot.

**Statements**
- decls2: 220 ADDED, 0 CHANGED, 0 REMOVED.
- All 47 pre-existing headers are byte-identical, including the target's. Only the target's body and step 5 of its
  sketch change.

**Axioms**
- All 321 stored constants use only the standard three axioms, and so does the target.
- No new `@[simp]` lemma and no new instance.
- One new abbreviation, `Table`, with its reader `Table_eq`.

**Admissions:** 22 → 21.

**Rule 10**
- **Seal A** (the canonical seal, `PolyExpr.eval` exempt): 18/18 at the head and 2/2 at the base.
- **Seal B** (`PolyExpr.eval` sealed): 16/18 at the head, with the strict and coe variants agreeing. The failing
  declarations are:
  - **The 11 base failures, plus 5 new helper statements.** The new five are `lamport_signImpl_expect`,
    `lamport_loggedSignImpl_expect`, `lamport_forgerCodec`, `lamport_forgeGame_accept_eq_honestProbability` and
    `lamport_exists_best_position`. All 16 fail for the same reason: the frozen hypothesis
    `f : ∀ n, (Fin n → Bool) → …` is used where `Fin (var.eval n)` is expected, and that typechecks only by unfolding
    `PolyExpr.eval`. **Ruling (Seyoon, 2026-11-14): accepted as inherited from the frozen statement's design.** A
    follow-up will restate the frozen hypothesis over `Fin (var.eval n)` with a published reader, which would clear
    all 16.
  - **`LamportFill.exists_realization_machine`** in `Realization.lean`, inside its proof. It treats T1's
    `(bitSpecAt var (var·var) n).dom j` as `Fin n → Bool`. **Fixed by LE-rule10** `32b17308` (proof only); seal B now passes for it.
- **Paired controls:** 16 probes with 37 sealed negatives, ALL_OK.
- **Explicit-unfold scan:** 797 items, 0 foreign.
- **Opacity blocks (patch 4).** `Lamport.lean:777`, `Experiment.lean:40` and `Statistics.lean:36` each run a
  `run_cmd` that makes `ProbComp.expect`, `ProbComp.sample` and `OracleComp.bind` locally irreducible, unless they
  already are. This is the seal harness's own install logic.
  - It only makes those three definitions more opaque, it is file-local, and it is a no-op under a seal.
  - It is a performance guard. Without it, `Statistics` ran for more than 8.5 minutes and reached 5.2 GB, against 2
    seconds with it.
  - In-file controls, plus paired-control rows for the three names, show that the seals stay meaningful.
  - Recorded in `landing/opacity-*`.

**Lint**
- New lint: 92 FAIL / 102 WARN at the records tip, and 92 / 101 at the head. One warning was resolved and there is no
  new FAIL.
- Old lint, for continuity: 216 / 102 at the tip and 216 / 101 at the head.
- Sizes: every file is under 1000 lines (`Lamport.lean` has 973).

**Content.** The proof follows the book's reduction.
1. Plant the inversion challenge at `(i, c)`.
2. The favourable fraction is at least `1/(2n)`, and exactly `1/2` when there is no query.
3. Averaging gives a best position, supplied as `Nat.size n`-bit advice through T1.
4. Conclude `ε ≤ 2n·inv`.

The edge cases are handled: `n = 0` as a finite exception, no query, freshness, malformed words (through the codec),
and success only on non-aborting runs. No `take_poly` or `drop_poly` remains.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | Seal B fails on 5 new helper statements, for the same reason as the 11 base failures (frozen `f` over `Fin n`). | **Accepted as inherited** (Seyoon, 2026-11-14). The follow-up restating the frozen hypothesis is recorded. |
| 2 | minor | Seal B fails inside the proof of `exists_realization_machine`. | **Fixed** by LE-rule10 `32b17308`. |
| 3 | minor | 189 of the 221 new public declarations have no formula in their docstrings, and 8 long proofs have no sketch. | **Fixed** by LE-doc `987efb51`. |
| 4 | minor | Undisclosed duplicate: `LamportFill.signatureBlock σ i` is `FunFamily.blocks n n σ i` (via `blocks_apply`). | Ledger **DL-43**. |
| 5 | ledger | Overlaps with the parallel `hash-sign` delivery: `lamport_codec_ext` is `MachineCodec.ext_of_fields`; `lamport_forgerCodec` is an instance of `forgerCodec_eq_bitCodec`; `exists_pure_of_cost_zero` is `eq_pure_of_cost_zero` (`landing/hash-sign-overlaps.txt`). | Ledger **DL-42**, already recorded from the hash-sign side. Fold once both units have landed. |
| 6 | ledger | Near relatives: `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`) and `Averaging.expect_favourable_of_success` (the `ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). | Ledger **DL-43**. |
| 7 | nit | 7 linter warnings: unused hypotheses, an unused `simp` argument, and a dead `exact le_rfl`. | Optional follow-up. |

## Landing edits LE-rule10 and LE-doc (built)

- **Head:** `987efb5156b3ae20cff4576b379eb1c607f33cb0`, tree `dc1fb8fb5ba7fb427c6c94a03a6d64accf04e695`.
  - No rebase was needed: since `dee0de32` the records tip has only records commits.
- **LE-rule10** `32b1730838292add4c844ca1cf34b747412831d3` changes the proof of `exists_realization_machine` and nothing
  else. All 268 headers are byte-identical, and decls2 is empty.
  - T1's widths are now read through `PolyExpr.eval_var`, `eval_mul`, `eval_add` and `eval_const`, with `Fin.cast`
    and `List.ofFn_congr`.
  - Seals for `Realization.lean`: A and B pass in both the strict and the coe variant. Before the edit, B failed
    with 6 errors in this one declaration.
  - Paired controls: 8 probes with 30 sealed negatives, ALL_OK.
- **LE-doc** `987efb51` changes docstrings only: 188 formulas in 16 files and 7 sketches.
  - All hunks are inside doc comments. With doc comments blanked the code is identical, `run_cmd` blocks included.
  - Docaudit: 220 OK. The one exception is the target, whose first line is prose.
  - Every proof of 15 or more lines has a sketch.
  - One 10-line proof, `runAt_lamportSign_table`, has no sketch, because adding one would push `Lamport.lean` to
    1000 lines.
  - **`Lamport.lean` now has 999 lines.** It must be split before it grows any further. This is recorded as a
    follow-up.
- **Build:** 24/24 modules give rc 0 through root `TCSlib`. The whole-tree check at the head (1217 modules) gives OK.
  - Both `lamport_oneTimeSecure` and `exists_realization_machine` print only the standard axioms.
  - The tree was restored to the base snapshot.
- **Lint (#305):** 92 FAIL / 101 WARN at the head and 92 / 102 at the tip. No FAIL or WARN is new.
- **Evidence:** `le-evidence.zip`, SHA-256 `329b830f6398997d621ea5ad36a7515b79cae6edc564a8db449dee1e44a68fe3`, 217 entries.
  Its manifest is `le-evidence-SHA256SUMS`, and the patches are in `landing-le/`.
- **PR:** draft [PR #309](https://github.com/Shilun-Allan-Li/tcslib/pull/309).

## ===== briefs/pass-shelat-ch5-8/gates/26-lamport/worker-report.md =====

# Lamport fill — final

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
Final local proof head: `47ced271090f45918645c842cd358c5079092754` on `fill/lamport`.
The proof branch is kept local and is not pushed.

**Proved:** `TCSlib.Cryptography.Authentication.lamport_oneTimeSecure`, with its original
statement unchanged. Lean 4.25.0 and pinned Mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` are retained.
The final 177-module sweep passes with zero errors. Admissions are exactly 22→21,
removing only this target. Its direct axiom probe prints exactly
`[propext, Classical.choice, Quot.sound]`.

All eighteen ordinary-definition seals A pass. Strict B additionally seals
`PolyExpr.eval` and reports 32 diagnostics across seventeen declarations in two files;
those results and their type-width causes are reported below, not called passes.
All 102 paired controls pass, all 321 stored constants have only standard axioms,
and all 50 explicit-unfold candidates were reviewed without a forbidden foreign unfold.

## Proof route and checkpoints

For each one-query forger `A`, write `ε_A(n)` for acceptance in the actual
`SignatureScheme.forgeGame`. The proof follows the issued planted-experiment route:

1. At fixed `(i,c)`, plant the challenge image in one public-key cell. Couple safe signing
   queries with the honest table, and extract the corresponding preimage block from an
   accepted forgery whose message bit is `c`.
2. A successful honest run with query `m` and fresh forgery message `m'` has favorable
   fraction `#{i : m_i ≠ m'_i}/(2n) ≥ 1/(2n)`. Without a query the fraction is exactly `1/2`.
   Coordinate resampling makes the challenge preimage independent while preserving the
   average. No independence after conditioning on nonabort is assumed.
3. The actual-game equality and averaging theorem choose a best fixed position for every
   positive length. T1 realizes the planted simulation as one machine before this sequence
   of positions is supplied as advice. Only nonaborting reduction successes are transported
   to actual inversion witnesses.
4. The chosen index is encoded in exactly `Nat.size n` binary bits. The existing bounded
   binary-to-unary decoder, parameter-aware preprocessing and `NUPPT.exists_withAdvice`
   recover its unary form internally. The constructor's polynomial bound is
   `Nat.size n ≤ n`; no uniform best-index search or exact uniform `Fin n` sampler is needed.
5. The result is one inverter `C` satisfying
   `ε_A(n)/(2n) ≤ (lamportOWF L f).invProbAt C n` for `n ≥ 1`.
   Strong one-wayness and the published `Negligible.mul_pow`, `const_mul` and `mono`
   lemmas make `ε_A` negligible. The eventual comparison begins at one, so `n=0` is a
   finite exception without changing any probability or theorem statement.


Checkpoint 1 (planted coupling and algorithm readers) was pushed as
`70023e3c331fcf7861ff230dd9ff5ef525d0f08d`. Checkpoint 2 (actual-game averaging and best
position), proof head `77ec7bb1255852eb6288c6c38577a540a5e1a266`, was pushed as
`12e086f037ba0b6bc5d78d83790252387c0de60f`. Its exact transport verification is
[evidence/logs/checkpoint2-delivery-verification.json](evidence/logs/checkpoint2-delivery-verification.json).
Both intermediate checkpoints retained the target admission; this final source removes it.

The first proved candidate `252ec646b9a5605c11aa245629a4ce8f404f74e8` was corrected for
public-API reuse before finalization. Its complete successful sweep and earlier source
preparations remain historical evidence; final verification uses `47ced271…`.

## Files, declarations and scope

The payload changes eighteen library source files: the owned
`TCSlib/Cryptography/Authentication/Signatures/Lamport.lean`, sixteen helpers in its
`Lamport/` directory, and authorized import-only registrations in `Authentication.lean`.

| Helpers | Purpose |
| --- | --- |
| Encoding | Tuple-encoding injectivity and equality readers. |
| Planted | Tables, planting, one-query coupling, nonabort and extraction. |
| TableCoins, Seed | Tape/table and fair-bit/table equivalences. |
| Averaging, AveragingExtra | Favorable-pair counts and fixed-position averaging. |
| Statistics, Experiment | Independent resampling and typed probability bounds. |
| Blocks | Fixed-width tuple replacement under serialization. |
| Machine, MachineSpec | Polynomial-time handler and its functional contracts. |
| Nonabort, Realization | Nonabort-to-safety and T1 machine realization. |
| Advice | Binary index advice and bounded unary expansion. |
| InversionProbability | Transport to the actual machine inversion probability. |
| Closing | Linear-loss negligibility and one-time-security closure. |

The title drops “(statement phase)”, Main results marks the theorem proved, Contents lists
all sixteen helpers, and sketch step 5 describes the actual machine, advice and closure.
The explicit source inventory is
[evidence/new-declarations-final-r2.json](evidence/new-declarations-final-r2.json):
268 declarations across the eighteen files, consisting of all 47 original names and
220 new public plus one new private declaration. No original name is removed. Its lexical
parser limits are explicit; generated/private stored constants are covered by the separate
321-constant native census. Every new public definition has its readers and docstring.

The immutable final source commit `47ced271090f45918645c842cd358c5079092754` changes exactly the owned Lamport module, its sixteen new helper modules, and the authorized import-only `Authentication.lean` facade. All six intermediate source commits stay within that path scope, and every intermediate facade retains all non-import bytes and original imports. All eighteen files are plain Lean source files and contain fewer than 1,000 lines; the main module has 973 and `Machine.lean` has 340.

The target theorem header is byte-for-byte equal to the issued base. The source audit finds all forty-six other original declaration bodies and directly attached docstrings unchanged, with no removed line outside the allowed module title, target Main-results status, and target doc/proof regions. The added Contents section lists the sixteen delivered helpers. Manual review confirms that all four added `include ... in` occurrences affect only new lemmas and that the idempotent command after all original non-target declarations installs only local irreducibility for `ProbComp.expect`, `ProbComp.sample`, and `OracleComp.bind`. That command intentionally tightens the later target proof's transparency context while preserving its statement. No new `sorry`, `admit`, axiom, unsafe declaration, global simp directive, or bare `Mathlib` import was detected. This is an exact-text and lexical audit, not a claim to have parsed Lean semantically; compiled target types, axioms, effective imported environments, and Rule-10 results are reported separately.

Compared with the historical `252ec646…` candidate, only `Machine.lean` changes: it removes the duplicate `LamportMachine.take_poly` and `LamportMachine.drop_poly` wrappers, imports `Asymptotic.ReductionSupport`, and uses the already-published `TCSlib.Cryptography.takeLen_poly` and `dropLen_poly` at every former use site. The provider source is unchanged from the pinned base; the public API reuse resolves this duplication and requires no promotion request. The main module, facade and other fifteen helper files are byte-identical to the preceding candidate.

The frozen-commit campaign lint has the same 216 findings as the pinned baseline, with zero added or removed findings. Its exit status remains 1 because the inherited findings remain. Fresh raw Git diff, source blobs/hashes, removed-line records, manual review, mode records, provider source and candidate delta are under `evidence/logs/final-source-integrity-r2/`; lint comparison and raw output are `evidence/logs/lint-final-source-integrity-r2-comparison.json` and `evidence/logs/style-final-source-integrity-r2-delivered-tree.log`. The historical candidate's r1 audit is retained.


The facade exception was explicitly authorized by the user (“Allow the required facade
imports”); see [the authorization](evidence/requests/facade-authorization.md).

## Reuse, promotion and overlap

Final Machine imports `Asymptotic.ReductionSupport` and consumes its public
`TCSlib.Cryptography.takeLen_poly` and `dropLen_poly`. The two duplicate local wrappers
were removed. The provider is unchanged from the issue base and was already in the issued
order; this adds no module or Mathlib root and creates no promotion request for those facts.
The exact disposition is in
[evidence/preparation/final18-r2/public-prefix-reuse-resolution.json](evidence/preparation/final18-r2/public-prefix-reuse-resolution.json).

- **overlap: TCSlib/Cryptography/Asymptotic/OneWay.lean ofFn_blocks_two_symm**.
  The general serialization proof rederives the private two-block identity through public
  `FunFamily.ofFn_blocks_symm` and `OneWay.flatten_ofFn_two`; no private proof is copied.
- **overlap: TCSlib/Cryptography/Authentication/Signatures/Lamport.lean lamportVerFun_sign.hflat**.
  `MachineSpec.publicWord_flatten` rederives the serialization identity through the public
  encoding/list equations. The additional owned verifier now consumes this public helper.
- **overlap: TCSlib/Complexity/ClassNP/TMSAT.lean tmsat_pt_take**.
  Historical local prefix wrapper removed; public `takeLen_poly` is used instead.
- **overlap: TCSlib/Complexity/CookLevin/Hardness.lean clA5Drop_native**.
  Historical local suffix wrapper removed; public `dropLen_poly` is used instead.
- **overlap: TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean dlb_take_poly** and
  **overlap: TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean dlb_drop_poly**.
  These additional exact private overlaps were found in the final search; removal of the
  local wrappers resolves them too. Their private proofs were not copied.

Promotion requests: shared encoding injectivity/equality; the cost-zero OracleComp return
characterization; codec extensionality; list-window and fixed-width tuple-update readers;
favorable-pair/optional-query averaging; coordinate-invariant reduction; bounded binary
index/advice support; polynomial-loss negligibility and signature-reduction closure.
The current nonabort reader may be generalized for another consumer. Table/seed layouts,
realization and inversion comparison retain Lamport contracts. Existing probability
product, coordinate-resampling and simulation laws are imported, not reimplemented.
Search commands, raw matches and dispositions are retained in the preparation and checkpoint
search evidence. No missing frozen foreign reader or mathematical route failure was found.

## Edge cases

- At zero, the machines/advice remain total; the eventual negligible comparison starts at
  one and permits that finite exception without changing any probability.
- With no query, the log is empty, query safety holds, and the favorable fraction is 1/2.
- Freshness excludes reusing the signed message; distinct messages provide a differing bit.
- Malformed/wrong-length forger words use the existing fixed-width codec/defaults and guarded
  verifier through their readers in both actual and typed games.
- The lower bound counts only nonaborting reduction runs. A false final abort flag yields
  safe-query agreement and the actual extracted inverse; no successful abort is assumed.

## Environment and bootstrap

The seven issued pack hashes and all issue source hashes verified before editing.
Only the 82 issued Mathlib roots were fetched; the final 177-module root census is exactly
that same set. The preexisting host cache held 32,667 files / 1,595,387,830 bytes of unknown
earlier origin. The narrowed fetch downloaded zero files and unpacked 2,339 existing
archives. All present packages match the manifest; doc-gen4, UnicodeBasic, BibtexQuery and
MD4Lean are ABSENT documentation packages. The Mathlib import probe passed; no empty olean
was found.

The native macOS preflight records 12 CPUs, 19,327,352,832 physical-memory bytes,
available-memory estimate 8,697,308,774 bytes (45%), and APFS free space initially
276,725,379,072 bytes, then 273,175,490,560 bytes. These exceed the initial 4 GiB memory and
12 GiB disk floors. Linux-only commands were unavailable; raw failures and native
measurements are in [preflight.log](evidence/logs/preflight.log). Native timing permissions
were corrected after the initial sysctl instrumentation failure; it was not cache corruption.

The supplied 150-module baseline, nine extra T1 prerequisites, `Games.Bridges.Experiments`
and `Games.Hopping` were checked one module at a time in this worker's own olean tree.
The final order has all 150 issued modules in the same order plus sixteen helpers and
eleven prerequisites. No project `lake build`, unfiltered cache fetch, copied dependency
tree, joined `LEAN_PATH` or memory-backed scratch was used. Python is `python3 -I`.
The separate exchange checkout is transport-only.

The user's shared-Mac limit of three actual Lean processes supersedes the initial single
process rule. Lamport still checks one module at a time. The temporary dl-crh bootstrap
reservation, its release after that bootstrap completed, and the explicitly authorized
coordination message are retained under `evidence/requests/`. Only our own native child was
interrupted when needed. Resource waits/interrupted attempts remain distinct from proof
failures and successful checks. Retirement of the stopped Python coordinator was intentional;
no Lean was killed by that retirement and it is not a Lean resource-shortage exit.

## Final checks

The final canonical source checks and direct target axiom probe pass on the exact frozen
source bytes. The required final 177-module sweep passes with every module checked once,
zero errors, and exactly 21 admission warnings. The baseline set of 22 loses only
`lamport_oneTimeSecure`; no new admission appears. Exact order/source hashes, raw module
logs and the independent comparison are at
[evidence/logs/final-sweep-comparison-r2/report.json](evidence/logs/final-sweep-comparison-r2/report.json).
The direct axiom output is
[evidence/logs/helper-checks/FinalTargetAxioms-Reuse01.log](evidence/logs/helper-checks/FinalTargetAxioms-Reuse01.log).
Lint remains 216 inherited findings with zero new findings. The six cumulative patches
reproduce all eighteen final source files byte for byte from the issue base; see
[evidence/logs/source-payload-final-r2.json](evidence/logs/source-payload-final-r2.json).

## Whole-file seals, axioms and explicit unfolding

A excludes `PolyExpr.eval` as notation; B also seals it. The base Lamport A passed;
base B reported 15 diagnostics in eleven declarations:
`lamport`, `lamportOWF`, `lamportOWF_f`, `lamportOWF_inLen`, `lamportOWF_outLen`,
`lamport_gen`, `lamport_msgLen`, `lamport_oneTimeSecure`, `lamport_sigLen`, `lamport_sign`,
`lamport_ver` (all in `TCSlib.Cryptography.Authentication`). Its first obstruction is
`PolyExpr.var.eval n` versus `n` in the unchanged family/scheme definitions. All six base
controls pass. Base Auth has zero own constants and exact closure149; both A/B and six
controls pass. Its base Lamport/HashSign products and all147 other provider hashes were
checked, and original final sources restored/rechecked. The interrupted B-reader retries
and exact provenance remain at
[evidence/logs/base-auth/base-auth-cp2-completion.json](evidence/logs/base-auth/base-auth-cp2-completion.json).
All sixteen new helper paths are ABSENT at base, with raw Git errors/exits retained;
no empty base compilation is substituted.

All eighteen final whole-file Rule 10 reviews are complete for `47ced271090f45918645c842cd358c5079092754`.

| File | Own constants | Closure | A/B definitions | A/B errors | Controls | Scan readings/candidates |
|---|---:|---:|---:|---:|---:|---:|
| Planted | 67 | 100 | 1438/1439 | 0/0 | 6 | 150/3 |
| Encoding | 3 | 53 | 813/814 | 0/0 | 6 | 6/0 |
| TableCoins | 6 | 101 | 1455/1456 | 0/0 | 6 | 8/0 |
| Averaging | 7 | 3 | 38/38 | 0/0 | 6 | 30/0 |
| AveragingExtra | 3 | 9 | 50/50 | 0/0 | 6 | 7/0 |
| Statistics | 2 | 102 | 1455/1456 | 0/0 | 6 | 18/0 |
| Experiment | 23 | 107 | 1462/1463 | 0/0 | 6 | 38/2 |
| Advice | 12 | 67 | 911/912 | 0/0 | 6 | 34/0 |
| Blocks | 2 | 0 | 0/0 | 0/0 | 0 | 31/0 |
| Closing | 4 | 78 | 1057/1058 | 0/0 | 6 | 12/0 |
| InversionProbability | 2 | 108 | 1468/1469 | 0/0 | 6 | 17/0 |
| Machine | 73 | 138 | 1930/1931 | 0/0 | 6 | 46/0 |
| Seed | 6 | 102 | 1456/1457 | 0/0 | 6 | 6/0 |
| MachineSpec | 13 | 148 | 2003/2004 | 0/0 | 6 | 175/5 |
| Nonabort | 1 | 101 | 1455/1456 | 0/0 | 6 | 11/0 |
| Realization | 6 | 156 | 2014/2015 | 0/6 | 6 | 77/8 |
| Lamport | 91 | 163 | 2025/2026 | 0/26 | 6 | 386/32 |
| Auth | 0 | 176 | 2149/2150 | 0/0 | 6 | 0/0 |

All eighteen A seals pass. All 102 controls pass, including 34 sealed negatives with exactly one error each. The 321 stored constants have only subsets of `{propext, Classical.choice, Quot.sound}` as axioms. All 50 scanner candidates were reviewed in their source contexts; none is a forbidden explicit foreign unfold. Blocks has no TCSlib import closure and therefore zero requested definitions and no closure-local control; the other seventeen phases supply the paired controls.

B failures (with `PolyExpr.eval` sealed):

- `TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization`: 6 errors in 1 declarations: `TCSlib.Cryptography.Authentication.LamportFill.exists_realization_machine`.
- `TCSlib.Cryptography.Authentication.Signatures.Lamport`: 26 errors in 16 declarations: `TCSlib.Cryptography.Authentication.lamport`, `TCSlib.Cryptography.Authentication.lamportOWF`, `TCSlib.Cryptography.Authentication.lamportOWF_f`, `TCSlib.Cryptography.Authentication.lamportOWF_inLen`, `TCSlib.Cryptography.Authentication.lamportOWF_outLen`, `TCSlib.Cryptography.Authentication.lamport_exists_best_position`, `TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability`, `TCSlib.Cryptography.Authentication.lamport_forgerCodec`, `TCSlib.Cryptography.Authentication.lamport_gen`, `TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect`, `TCSlib.Cryptography.Authentication.lamport_msgLen`, `TCSlib.Cryptography.Authentication.lamport_oneTimeSecure`, `TCSlib.Cryptography.Authentication.lamport_sigLen`, `TCSlib.Cryptography.Authentication.lamport_sign`, `TCSlib.Cryptography.Authentication.lamport_signImpl_expect`, `TCSlib.Cryptography.Authentication.lamport_ver`.

Per-name INSTALL and EOF multisets, actual Name/home identity, original-source maps and hashes, full eligible-set selection (including private definitions and generated matchers), exact runtime import closure, every own axiom row, and control locations were checked against the retained raw evidence. The versioned module-name cache changes only pure reads of a captured immutable environment. Earlier Core-loop/sparse proposals were not adopted; historical attempts and the actual generator bindings are preserved.


Strict B adds PolyExpr.eval to the same sealed request sets. In Realization, the first type conversion failures occur at source146 in the new exists_realization_machine proof: Fin n / Fin(n*n) arguments do not convert to bitSpecAt(var,var.mul var)n domain/range when eval is opaque. The other failures concern the same oracle specification or output-vector widths. These new helper diagnostics are not classified as inherited baseline failures.

In the main file, the first failure is at source499 in lamportOWF: its f accepts Fin n, while the declared FunFamily input expects Fin(PolyExpr.var.eval n). A second width conversion appears at598 in lamport correctness. Later declarations report type/notation/context cascades from the failed declarations, including the target theorem. This strict-B result is not a passing proof of those declarations under opaque eval. The standard A source seal and ordinary native proof remain passing.

Every strict-B failing declaration and all its mapped source error lines:

| File | Declaration | Original source lines |
| --- | --- | --- |
| TCSlib/Cryptography/Authentication/Signatures/Lamport/Realization.lean | TCSlib.Cryptography.Authentication.LamportFill.exists_realization_machine | 146, 153, 174, 177, 179 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport | 598 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF | 499 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_f | 508 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_inLen | 502 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_outLen | 505 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_exists_best_position | 876, 881 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability | 826 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_forgerCodec | 766 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_gen | 607 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect | 807, 810 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_msgLen | 601 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_oneTimeSecure | 917, 918, 921 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_sigLen | 604 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_sign | 610 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_signImpl_expect | 791 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_ver | 613 |


Full 32 mapped diagnostics with raw result/log links are
[evidence/logs/final18-native-r3/strict-b-failures.json](evidence/logs/final18-native-r3/strict-b-failures.json).
The independent aggregate and scan dispositions are
[evidence/audits/final18-peer-completion-r1/summary.json](evidence/audits/final18-peer-completion-r1/summary.json)
and [explicit-unfold-review-summary.json](evidence/audits/final18-peer-completion-r1/explicit-unfold-review-summary.json).
There are 1,052 scan token readings, 50 reviewed candidates, and zero forbidden explicit
foreign unfolds. Full selection covers private definitions, generated matchers/projections,
actual names/homes and exact runtime import closure. All 138 source/control probe byte
strings were independently regenerated; 703 referenced raw artifacts were checked present
and hashed.

The first four final phases retain their original successful probes/tool bindings. The
remaining fourteen use a versioned, qualified pure cache of the imported module-name array
from the same captured immutable environment. Attribute commands, local scope, validations,
request sets, controls and EOF checks are unchanged. Qualification reran full Planted A/B
and all six controls; cached census output was byte-identical for all9,103 catalog rows,
67 axiom rows and closure/END markers. Queue version maps and actual-generator provenance
separate adopted and cached attempts. The Core-loop and sparse alternatives were not adopted.

Historical failed native attempts, the checkpoint-2 local-attribute idempotency failure,
its repair and all strict-B diagnostics remain preserved. The original checkpoint-2 A
had three attribute-command errors, not a codec proof failure; B had25 then22 diagnostics
across the same sixteen main declarations listed above. Earlier 252ec inventory preparations
were never run and are labeled historical. No failed sealed check is replaced by an
unsealed pass and no raw evidence is omitted for size.

## Payload and delivery

This payload contains `REPORT.md`, all six issue-base-to-final format patches, all eighteen
changed/new source files, and complete raw evidence with `evidence/SHA256SUMS`. The root
`SHA256SUMS` covers the complete payload. The freezing tool checks exact path-set equality
and every hash, verifies an identical frozen snapshot and ZIP, and verifies every ZIP entry.
The fallback ZIP has `lamport/` at its root.

Delivery is only under `inbox/fills/lamport/` on `exchange/pass-shelat-ch5-8`, with pull/rebase
before pushing and no force push. The final exchange commit and verified fallback ZIP are
returned in chat. The proof branch remains local. Campaign integration is for maintainer
review and a PR Seyoon approves; this worker does not merge the campaign branch.

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

## ===== briefs/pass-shelat-ch5-8/fills/lamport/issued-r1/brief.md =====

# Codex fill · Lamport is one-time secure (`lamport_oneTimeSecure`, Theorem 137.2)

**Issue base** `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4` (the merge of #299).
**Unit** `lamport`. **Worker** Codex (Seyoon, 2026-11-14). **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `lamport_oneTimeSecure` of [PS10, Theorem 137.2] in `TCSlib/Cryptography/Authentication/Signatures/Lamport.lean`. The
statement passed Gate 06 (prong A) and is frozen. Its docstring holds the maintainer's proof sketch.

## Checkout and delivery

- Work in a local checkout of the repository. Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/lamport` at the exact issue base. Record the base in `REPORT.md`. Keep the proof branch local: never push it.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Deliver** every checkpoint and the final payload under `inbox/fills/lamport/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the changed and new files;
  - `evidence/`, with a `SHA256SUMS` manifest (see *Evidence completeness*).
- Commit as `fill lamport: checkpoint N` and `fill lamport: final`. Pull with rebase before pushing, push only your
  delivery path, and never force-push.
- **At the end, also return the final payload in the chat** as a ZIP with `lamport/` at its root, holding the same
  `REPORT.md`, `patches/`, `src/` and `evidence/`. This is a fallback in case the push fails.
- Campaign changes land by a maintainer PR for Seyoon's approval.

## Target (frozen; quoted from the issue base)

```lean
theorem lamport_oneTimeSecure (hf : (lamportOWF L f).StrongOneWay) :
    (lamport L f E hE hfE).OneTimeSecure := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. The section variables are `L : PolyExpr`, `f : ∀ n, (Fin n → Bool) → (Fin (L.eval n) → Bool)`, `E`, `hE : PolyTimeComputable E` and `hfE` (`E` evaluates `f` on `advInput`). `lamportOWF L f` is `f` as a one-way collection; `StrongOneWay` is in `Asymptotic/Collections.lean`. `HashAndSign.lean` imports this file; the parallel `hash-sign` fill does not depend on this proof.

The target's docstring sketch is the route. You may edit it to describe the delivered proof.

## Published interfaces

| Interface | Provider |
|---|---|
| `lamportGen`, `lamportSign`, `lamportVerFun`, `lamportOWF`, the `lamport_*` field readers and the machine readers | owned file |
| `SignatureScheme`, `OneTimeSecure` and its experiment readers | `Authentication/Signatures/Defs.lean` |
| `StrongOneWay` and readers | `Asymptotic/Collections.lean`, `Asymptotic/OneWay.lean` |
| T1 `Games.exists_handlerMachine` and the `PolyHandler` readers | `Games/Efficiency.lean` |
| `NUPPT.exists_withAdvice` (bounded advice for the best position), `exists_comp`; run/coin readers; `Negligible` closure incl. polynomial factors (`mul_pow`, `const_mul`, `mono`) | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |
| `coinBlock`, `FunFamily.blocks`, `ofFn_blocks`, `Foundations/BitLists` | `Asymptotic/Adversary.lean`, `Foundations/BitLists.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq`, `prob_eq_until_bad` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the planted experiment (sketch steps 1–3).** Define the reduction experiment for a fixed position `(i, c)`: plant `y` at `(i, c)`, answer the query when `m_i ≠ c` and abort otherwise, and extract `σ'_i` from a forgery with `m'_i = c`. Prove the coupling with the honest run: on the jointly favourable pairs the experiments agree and extraction inverts `y`. Send this checkpoint.
2. **Checkpoint 2 · the averaging bound (sketch steps 3–4).** Count the favourable pairs (`≥ 1/(2n)`, exactly `1/2` with no query) and average over successful honest runs to get inversion probability `≥ ε(n)/(2n)` for the uniform position; then a best position per length is at least as good. Send this checkpoint.
3. **Final · the machine and negligibility (sketch step 5).** Apply T1 to the extended input `⟨y, i(n)⟩`, supply the best position with `NUPPT.exists_withAdvice`, and conclude that `ε` is negligible by one-wayness and polynomial-factor closure.

Check the edge cases: `n = 0` (finite exception); no query; a query or forgery of the wrong length; `m' = m`; malformed signatures; an abort branch reached by a successful forger.

If the sketch is wrong, or the target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken the statement.

## Scope and proof discipline

- **Owned file.** You own `Authentication/Signatures/Lamport.lean`. Replace the target's proof body and edit its sketch. Update the module title (drop
  "(statement phase)") and the `## Main results` status.
- **Helper modules.** They are permitted under `TCSlib/Cryptography/Authentication/Signatures/Lamport/`. The owned file imports them precisely and
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

- **Bootstrap.** Bootstrap from `order.txt` (150 modules) and the narrow `roots.txt` (82), following the
  addendum. Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Never run
  `lake build` or an unfiltered cache get. Run Python as `python3 -I`. Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (22 declarations in 12 modules). The only change
    must be the removal of `lamport_oneTimeSecure`.
- **Axioms.**
  - Print the axioms of `lamport_oneTimeSecure`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
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
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies. |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | Re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |

## ===== briefs/pass-shelat-ch5-8/gates/26-lamport/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Authentication.lean b/TCSlib/Cryptography/Authentication.lean
index e33d4b40f..e3128031a 100644
--- a/TCSlib/Cryptography/Authentication.lean
+++ b/TCSlib/Cryptography/Authentication.lean
@@ -12,6 +12,22 @@ import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
 import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
 import TCSlib.Cryptography.Authentication.MAC.FromPRF
 import TCSlib.Cryptography.Authentication.Signatures.Lamport
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Advice
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Closing
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Encoding
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.InversionProbability
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
 import TCSlib.Cryptography.Hashing.FromDiscreteLog
 import TCSlib.Cryptography.Authentication.Signatures.HashAndSign
 
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean
index 2f4b0795f..422197181 100644
--- a/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport.lean
@@ -3,6 +3,23 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Authentication.Signatures.Defs
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Encoding
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Advice
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Closing
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.InversionProbability
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization
+import TCSlib.Cryptography.Games.Hopping
 import TCSlib.Cryptography.Authentication.Encoding
 import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
 import TCSlib.Cryptography.Asymptotic.BlockEncryptor
@@ -14,7 +31,7 @@ set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
 /-!
-# Lamport's one-time signatures (statement phase)
+# Lamport's one-time signatures
 
 [PS10, Protocol 137.1]: for a one-way function `f`,
 - `Gen(1^n)` samples `x_i^b ← U_n` for `i ∈ [n]` and `b ∈ {0, 1}`, and outputs
@@ -43,6 +60,25 @@ Theorem 137.2: if `f` is one-way, the scheme is one-time secure.
 - **The one-way function is strong** ([PS10, Definition 27.3], `FunFamily.StrongOneWay`), the
   notes' "one-way function"; by §2.4 a weak one suffices.
 
+## Contents
+
+* `Signatures.Lamport.Encoding`: injectivity of the cryptographic tuple encoding.
+* `Signatures.Lamport.Planted`: the typed planted experiment and safe-run coupling.
+* `Signatures.Lamport.TableCoins`: the equivalence between key tapes and typed tables.
+* `Signatures.Lamport.Averaging`: finite favourable-pair counting.
+* `Signatures.Lamport.AveragingExtra`: optional-query counting and fixed-position selection.
+* `Signatures.Lamport.Statistics`: independent-coordinate averaging.
+* `Signatures.Lamport.Experiment`: the typed honest and planted probability bounds.
+* `Signatures.Lamport.Advice`: binary advice and bounded decoding for the best position.
+* `Signatures.Lamport.Blocks`: updating a fixed-width serialized tuple block.
+* `Signatures.Lamport.Closing`: negligibility under the linear reduction loss.
+* `Signatures.Lamport.InversionProbability`: transport to the actual machine inversion probability.
+* `Signatures.Lamport.Machine`: the polynomial-time planting handler.
+* `Signatures.Lamport.Seed`: the fair-bit and random-table seed equivalence.
+* `Signatures.Lamport.MachineSpec`: functional contracts for planting, signing and extraction.
+* `Signatures.Lamport.Nonabort`: nonaborting one-query runs have a safe query.
+* `Signatures.Lamport.Realization`: T1 realization with an explicit coin equivalence.
+
 ## Main definitions
 
 * `Authentication.lamportOWF`: `f` as a `FunFamily`.
@@ -55,7 +91,7 @@ Theorem 137.2: if `f` is one-way, the scheme is one-time secure.
 * `Authentication.lamport_msgLen`, `lamport_sigLen`, `lamport_gen`, `lamport_sign`, `lamport_ver`:
   the signature-scheme data fields.
 * `Authentication.lamportVerFun_sign`: correctness, `Ver` accepts honest signatures.
-* `Authentication.lamport_oneTimeSecure` (Thm 137.2, stated; a `sorry` under the source's sketch).
+* `Authentication.lamport_oneTimeSecure` (Thm 137.2): one-time security from strong one-wayness.
 
 ## References
 
@@ -366,6 +402,57 @@ noncomputable def lamportGen : NUPPT :=
 noncomputable def lamportSign : NUPPT :=
   NUPPT.ofPolyTimeUniform polyTimeComputable_lamportSignFun (.const 0)
 
+/-- Lamport's generator uses the coin polynomial `2n²`: `(lamportGen hE).coins = .mul (.mul
+(.const 2) .var) .var`. -/
+theorem lamportGen_coins : (lamportGen hE).coins = .mul (.mul (.const 2) .var) .var := by
+  unfold lamportGen
+  exact NUPPT.coins_ofPolyTimeUniform _ _
+
+/-- The generator's coin tape has `2n²` bits at parameter `n`: `(lamportGen hE).coinLen n = 2 * n *
+n`. -/
+theorem lamportGen_coinLen (n : ℕ) : (lamportGen hE).coinLen n = 2 * n * n := by
+  rw [NUPPT.coinLen_eq, lamportGen_coins]
+  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+
+/-- Lamport's generator coin tapes are equivalent to its row-major preimage tables:
+`lamportCoinTables hE n : (lamportGen hE).Coins n ≃ Table n`. -/
+noncomputable def lamportCoinTables (n : ℕ) : (lamportGen hE).Coins n ≃ LamportFill.Table n :=
+  (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl Bool)).trans
+    (LamportFill.tableCoins n)
+
+/-- The coin-table equivalence first casts the tape width to `2n²`, then groups its blocks:
+`lamportCoinTables hE n = (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl
+Bool)).trans (tableCoins n)`. -/
+theorem lamportCoinTables_eq (n : ℕ) :
+    lamportCoinTables hE n =
+      (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl Bool)).trans
+        (LamportFill.tableCoins n) := rfl
+
+/-- The inverse coin-table equivalence serializes the table and casts back to the generator's
+declared coin length: `(lamportCoinTables hE n).symm T = (Equiv.arrowCongr (finCongr
+(lamportGen_coinLen hE n).symm) (Equiv.refl Bool)) ((tableCoins n).symm T)`. -/
+theorem lamportCoinTables_symm (n : ℕ) (T : LamportFill.Table n) :
+    (lamportCoinTables hE n).symm T =
+      (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n).symm) (Equiv.refl Bool))
+        ((LamportFill.tableCoins n).symm T) := rfl
+
+/-- The coin tape for table `T` is exactly its row-major secret word: `List.ofFn ((lamportCoinTables
+hE n).symm T) = secretWord T`. -/
+theorem ofFn_lamportCoinTables_symm (n : ℕ) (T : LamportFill.Table n) :
+    List.ofFn ((lamportCoinTables hE n).symm T) = LamportFill.secretWord T := by
+  rw [lamportCoinTables_symm, ofFn_arrowCongr_finCongr, LamportFill.ofFn_tableCoins_symm]
+
+/-- Serializing the table of a generator coin tape recovers that tape's word: `secretWord
+(lamportCoinTables hE n ρ) = List.ofFn ρ`. -/
+theorem secretWord_lamportCoinTables (n : ℕ) (ρ : (lamportGen hE).Coins n) :
+    LamportFill.secretWord (lamportCoinTables hE n ρ) = List.ofFn ρ := by
+  rw [← ofFn_lamportCoinTables_symm, Equiv.symm_apply_apply]
+
+/-- Lamport's deterministic signer uses the zero coin polynomial: `lamportSign.coins = .const 0`. -/
+theorem lamportSign_coins : lamportSign.coins = .const 0 := by
+  unfold lamportSign
+  exact NUPPT.coins_ofPolyTimeUniform _ _
+
 /-- `Gen` on coins `ρ`: `⟨pk, ρ⟩`, `pk` the tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the
 `2n`-bit segments `x_i^0 ‖ x_i^1` of `ρ`. -/
 theorem runAt_lamportGen (n : ℕ) (ρ : (lamportGen hE).Coins n) :
@@ -533,6 +620,296 @@ theorem lamport_sign : (lamport L f E hE hfE).sign = lamportSign := rfl
 /-- Lamport uses its length-guarded block verifier. -/
 theorem lamport_ver : (lamport L f E hE hfE).ver = lamportVerFun L E := rfl
 
+include hfE in
+/-- On a serialized preimage table, key generation returns its public images and the table itself
+[PS10, Protocol 137.1]: if `List.ofFn ρ = secretWord T`, then `(lamportGen hE).runAt n [] ρ =
+pairEncode (publicWord (tablePublic (f n) T)) (secretWord T)`.
+
+**Proof sketch.** Block `i` of `secretWord T` is `T (i, false) ‖ T (i, true)`
+(`coinBlock_flatten_ofFn`); `lamportHalf` reads its halves, and `hfE` maps them to their images. -/
+theorem runAt_lamportGen_table (n : ℕ) (T : LamportFill.Table n)
+    (ρ : (lamportGen hE).Coins n) (hρ : List.ofFn ρ = LamportFill.secretWord T) :
+    (lamportGen hE).runAt n [] ρ =
+      pairEncode (LamportFill.publicWord (LamportFill.tablePublic (f n) T))
+        (LamportFill.secretWord T) := by
+  have hrow (i : Fin n) :
+      (List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).length = 2 * n := by
+    simp only [List.length_append, List.length_ofFn]
+    omega
+  have hhalf (i : Fin n) (b : Bool) :
+      lamportHalf n b (coinBlock (2 * n) i (LamportFill.secretWord T)) =
+        List.ofFn (T (i, b)) := by
+    rw [LamportFill.secretWord_eq, coinBlock_flatten_ofFn _ hrow i]
+    cases b <;> simp [lamportHalf_eq]
+  have hE' (x : Fin n → Bool) :
+      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
+    simpa only [NUPPT.advInput_eq] using hfE n x
+  rw [runAt_lamportGen, hρ, LamportFill.publicWord_eq]
+  congr 1
+  apply congrArg encodeList
+  apply congrArg List.ofFn
+  funext i
+  rw [hhalf i false, hhalf i true, hE', hE',
+    LamportFill.tablePublic_eq, LamportFill.tablePublic_eq]
+
+/-- On a serialized preimage table, signing returns the typed signature selected from that table,
+independently of its signing coins [PS10, Protocol 137.1]: `lamportSign.runAt n (pairEncode
+(secretWord T) (List.ofFn m)) r = List.ofFn (tableSignature T m)`. -/
+theorem runAt_lamportSign_table (n : ℕ) (T : LamportFill.Table n) (m : Fin n → Bool)
+    (r : lamportSign.Coins n) :
+    lamportSign.runAt n (pairEncode (LamportFill.secretWord T) (List.ofFn m)) r =
+      List.ofFn (LamportFill.tableSignature T m) := by
+  rw [runAt_lamportSign, LamportFill.ofFn_tableSignature]
+  have hrow (i : Fin n) :
+      (List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).length = 2 * n := by
+    simp only [List.length_append, List.length_ofFn]
+    omega
+  apply congrArg List.flatten
+  apply congrArg List.ofFn
+  funext i
+  rw [LamportFill.secretWord_eq, coinBlock_flatten_ofFn _ hrow i]
+  cases m i <;> simp [lamportHalf_eq]
+
+include hE hfE in
+/-- On the canonical layout of a table, the generator string function returns its public images
+paired with its secret serialization [PS10, Protocol 137.1]: `lamportGenFun E (NUPPT.layout
+(List.replicate n true) [] [] (secretWord T)) = pairEncode (publicWord (tablePublic (f n) T))
+(secretWord T)`. -/
+theorem lamportGenFun_table (n : ℕ) (T : LamportFill.Table n) :
+    lamportGenFun E (NUPPT.layout (List.replicate n true) [] [] (LamportFill.secretWord T)) =
+      pairEncode (LamportFill.publicWord (LamportFill.tablePublic (f n) T))
+        (LamportFill.secretWord T) := by
+  have h := runAt_lamportGen_table L f E hE hfE n T
+    ((lamportCoinTables hE n).symm T) (ofFn_lamportCoinTables_symm hE n T)
+  rw [NUPPT.runAt_eq] at h
+  rw [ofFn_lamportCoinTables_symm (E := E) hE n T] at h
+  unfold lamportGen at h
+  rw [NUPPT.runAtL_ofPolyTimeUniform] at h
+  simpa only [NUPPT.layout_eq, NUPPT.advInput_eq] using h
+
+/-- On the canonical signing layout, the signing string function returns the selected preimage
+vector [PS10, Protocol 137.1]: `lamportSignFun (NUPPT.layout (List.replicate n true) (pairEncode
+(secretWord T) (List.ofFn m)) [] []) = List.ofFn (tableSignature T m)`. -/
+theorem lamportSignFun_table (n : ℕ) (T : LamportFill.Table n) (m : Fin n → Bool) :
+    lamportSignFun (NUPPT.layout (List.replicate n true)
+      (pairEncode (LamportFill.secretWord T) (List.ofFn m)) [] []) =
+        List.ofFn (LamportFill.tableSignature T m) := by
+  let r : lamportSign.Coins n := fun _ => false
+  have hr : List.ofFn r = [] := by
+    apply List.eq_nil_of_length_eq_zero
+    rw [List.length_ofFn, NUPPT.coinLen_eq, lamportSign_coins, PolyExpr.eval_const]
+  have h := runAt_lamportSign_table n T m r
+  rw [NUPPT.runAt_eq] at h
+  unfold lamportSign at h
+  rw [NUPPT.runAtL_ofPolyTimeUniform, hr] at h
+  simpa only [NUPPT.layout_eq, NUPPT.advInput_eq] using h
+
+include hfE in
+/-- Verification of a typed public table accepts exactly when each signature block maps to the image
+selected by the corresponding message bit [PS10, Protocol 137.1]: `lamportVerFun L E (atParam n
+(pairEncode (publicWord Y) (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] ↔ ∀ i, f n
+(signatureBlock σ i) = Y (i, m i)`.
+
+**Proof sketch.** Both length guards pass. The two block loops are tuple encodings of
+the signature-block images and selected public images. Injectivity of the tuple encoding
+and of bit-vector serialization turns their equality into coordinatewise equality. -/
+theorem lamportVerFun_publicWord_iff (n : ℕ)
+    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (m : Fin n → Bool)
+    (σ : Fin (n * n) → Bool) :
+    lamportVerFun L E (atParam n (pairEncode (LamportFill.publicWord Y)
+      (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] ↔
+      ∀ i, f n (LamportFill.signatureBlock σ i) = Y (i, m i) := by
+  have hb : FunFamily.blocks n n σ = fun i => LamportFill.signatureBlock σ i := by
+    funext i k
+    rw [FunFamily.blocks_apply, LamportFill.signatureBlock_eq]
+  have hσ := FunFamily.ofFn_blocks_symm n n (FunFamily.blocks n n σ)
+  rw [Equiv.symm_apply_apply, hb] at hσ
+  have hsig (i : Fin n) : (List.ofFn (LamportFill.signatureBlock σ i)).length = n :=
+    List.length_ofFn
+  have hpk (i : Fin n) :
+      (pairEncode (pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) []).length =
+        (lamportPkBlock L).eval n := by
+    simp only [length_pairEncode, List.length_ofFn, List.length_nil, lamportPkBlock_eq,
+      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
+    ring
+  have hE' (x : Fin n → Bool) :
+      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
+    simpa only [NUPPT.advInput_eq] using hfE n x
+  simp only [lamportVerFun_eq, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
+    List.length_replicate, List.length_ofFn, decide_true, Bool.true_and,
+    List.cons.injEq, and_true, decide_eq_true_eq]
+  rw [LamportFill.publicWord_flatten, hσ, blockEncFun_ofFn, blockEncFun_ofFn]
+  have hleft : (fun i : Fin n =>
+      lamportEvalEmit E (NUPPT.layout (List.replicate n true) (pairEncode [] [m i]) []
+        (coinBlock n i (List.ofFn fun j => List.ofFn (LamportFill.signatureBlock σ j)).flatten))) =
+        fun i => List.ofFn (f n (LamportFill.signatureBlock σ i)) := by
+    funext i
+    simp only [lamportEvalEmit_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout]
+    rw [coinBlock_flatten_ofFn _ hsig i, hE']
+  have hright : (fun i : Fin n =>
+      lamportPkEmit (NUPPT.layout (List.replicate n true) (pairEncode [] [m i]) []
+        (coinBlock ((lamportPkBlock L).eval n) i
+          (List.ofFn fun j => pairEncode
+            (pairEncode (List.ofFn (Y (j, false))) (List.ofFn (Y (j, true)))) []).flatten))) =
+        fun i => List.ofFn (Y (i, m i)) := by
+    funext i
+    rw [coinBlock_flatten_ofFn _ hpk i]
+    simp only [lamportPkEmit_eq, NUPPT.inArg_layout, NUPPT.inCoins_layout,
+      pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons]
+    cases m i <;> rfl
+  simp only [PolyExpr.eval_var, List.length_replicate]
+  rw [hleft, hright, LamportReduction.encodeList_ofFn_eq_iff]
+  constructor
+  · intro h i
+    exact List.ofFn_injective (congrFun h i)
+  · intro h
+    funext i
+    exact congrArg List.ofFn (h i)
+
+
+/-- Machine codecs with equal move decoders, entry encoders and timeout values are equal. -/
+private theorem lamport_codec_ext {ι α : Type} {spec : OracleSpec ι}
+    (a b : MachineCodec spec α) (hd : a.decodeMove = b.decodeMove)
+    (he : a.encodeEntry = b.encodeEntry) (ht : a.timeout = b.timeout) : a = b := by
+  cases a
+  cases b
+  cases hd
+  cases he
+  cases ht
+  rfl
+
+/-- Lamport's forger codec is the canonical bit codec with query width `n`, answer width `n²` and
+final width `n+n²`: `(lamport L f E hE hfE).forgerCodec n = bitCodec (fun _ : Fin 1 => n) (fun _ =>
+n * n) (n + n * n)`. -/
+theorem lamport_forgerCodec (n : ℕ) :
+    (lamport L f E hE hfE).forgerCodec n =
+      bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n) := by
+  apply lamport_codec_ext
+  · funext w
+    rw [SignatureScheme.forgerCodec_decodeMove, bitCodec_decodeMove]
+    simp only [lamport_msgLen, lamport_sigLen, PolyExpr.eval_var, PolyExpr.eval_mul]
+  · funext e
+    rw [SignatureScheme.forgerCodec_encodeEntry, bitCodec_encodeEntry]
+  · rw [SignatureScheme.forgerCodec_timeout, bitCodec_timeout]
+    simp only [lamport_msgLen, lamport_sigLen, PolyExpr.eval_var, PolyExpr.eval_mul]
+
+-- Probability proofs read their laws rather than reducing the sample interpreter.
+run_cmd do
+  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
+    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
+    unless status == .irreducible do
+      let id := Lean.mkIdent n
+      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
+
+/-- Against a serialized key table, every Lamport signing call has exactly the deterministic
+selected-preimage law. The equality holds for every function of the answer and state:
+`ProbComp.expect ((lamport L f E hE hfE).signImpl n (secretWord T) i m s) G = ProbComp.expect
+(tableSigner T i m s) G`. -/
+theorem lamport_signImpl_expect (n : ℕ) (T : LamportFill.Table n)
+    (i : Fin 1) (m : Fin n → Bool) (s : Unit)
+    (G : (Fin (n * n) → Bool) × Unit → ℝ) :
+    ProbComp.expect
+        ((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T) i m s) G =
+      ProbComp.expect (LamportFill.tableSigner T i m s) G := by
+  rw [SignatureScheme.signImpl_eq, LamportFill.tableSigner_eq]
+  simp only [QueryImpl.ofComp_apply, ProbComp.expect_bind, ProbComp.expect_pure,
+    lamport_sign, lamport_sigLen, PolyExpr.eval_mul, PolyExpr.eval_var,
+    runAt_lamportSign_table, padFin_ofFn]
+  exact ProbComp.expect_const _ _
+
+/-- Logging preserves the equality between actual Lamport signing and typed table signing, including
+the full appended query and answer log: `ProbComp.expect (((lamport L f E hE hfE).signImpl n
+(secretWord T)).withLog i m s) G = ProbComp.expect ((tableSigner T).withLog i m s) G`. -/
+theorem lamport_loggedSignImpl_expect (n : ℕ) (T : LamportFill.Table n)
+    (i : Fin 1) (m : Fin n → Bool)
+    (s : Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)))
+    (G : (Fin (n * n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))) → ℝ) :
+    ProbComp.expect
+        (((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T)).withLog i m s) G =
+      ProbComp.expect ((LamportFill.tableSigner T).withLog i m s) G := by
+  simp only [QueryImpl.withLog_apply, ProbComp.expect_bind]
+  exact lamport_signImpl_expect (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE)
+    n T i m s.1 (fun ys =>
+      ProbComp.expect (.pure (ys.1, (ys.2, s.2 ++ [⟨i, m, ys.1⟩]))) G)
+
+include hfE in
+/-- The actual one-query Lamport forgery game has exactly the typed honest-table success probability
+[PS10, Definition 136.2 and proof of Theorem 137.2]: `accept ((lamport L f E hE hfE).forgeGame A 1
+n) = honestProbability (f n) adv`, where `adv Y r = A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _
+=> n * n) (n + n * n)) n 1 (publicWord Y) r`.
+
+**Proof sketch.** Reindex key-generation coins by the table equivalence and use the generator
+reader to identify public and secret keys. The signing machine ignores its signing coins, so
+its call expectation is the deterministic table signer's expectation; the simulation
+congruence theorem lifts this equality to the logged forger execution. The one-query
+transcript reader identifies its output and first-query log. Finally the verifier reader
+identifies acceptance with coordinatewise verification, and the freshness reader identifies
+absence from the log with inequality to the optional query. -/
+theorem lamport_forgeGame_accept_eq_honestProbability (A : NUPPT) (n : ℕ) :
+    accept ((lamport L f E hE hfE).forgeGame A 1 n) =
+      LamportFill.honestProbability (f n)
+        (fun Y r => A.toCompOn
+          (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
+          n 1 (LamportFill.publicWord Y) r) := by
+  classical
+  rw [accept_eq, SignatureScheme.forgeGame_eq]
+  simp only [ProbComp.prob_bind, ProbComp.prob_pure, decide_eq_true_eq,
+    lamport_gen, lamport_forgerCodec]
+  rw [← ProbComp.expect_sample_equiv (lamportCoinTables hE n).symm,
+    LamportFill.honestProbability_eq]
+  apply congrArg (ProbComp.expect (ProbComp.sample (LamportFill.Table n)))
+  funext T
+  have hgen := runAt_lamportGen_table
+    (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE) n T
+    ((lamportCoinTables hE n).symm T) (ofFn_lamportCoinTables_symm hE n T)
+  rw [hgen, pairFstD_pairEncode, pairSndD_pairEncode]
+  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
+  funext r
+  let codec := bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n)
+  let tree := A.toCompOn codec n 1
+    (LamportFill.publicWord (LamportFill.tablePublic (f n) T)) r
+  have hcost : tree.CostBoundedBy (fun _ => 1) 1 :=
+    A.toCompOn_costBoundedBy codec n 1 _ r
+  have hsim (G : (Fin (n + n * n) → Bool) ×
+      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))) → ℝ) :=
+    ProbComp.expect_simulate_congr
+      (((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T)).withLog)
+      ((LamportFill.tableSigner T).withLog)
+      (fun i m s H => lamport_loggedSignImpl_expect
+        (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE) n T i m s H)
+      tree ((), []) G
+  rw [hsim, LamportFill.honest_transcript T tree hcost, ProbComp.expect_pure]
+  simp only [SignatureScheme.accepts_iff, lamport_ver,
+    lamportVerFun_publicWord_iff (L := L) (f := f) (E := E) (hfE := hfE),
+    LamportFill.tablePublic_eq,
+    LamportFill.honestSuccess_iff, LamportFill.honestOutput_eq]
+  apply if_congr ?_ rfl rfl
+  apply and_congr_right
+  intro _
+  exact LamportFill.fresh_firstLog_iff T tree _
+
+
+/-- For every positive parameter, some fixed position with a fair planted bit gives reduction
+success at least the actual one-query forgery probability divided by `2n` [PS10, averaging step in
+the proof of Theorem 137.2]: if `0 < n`, then `∃ i : Fin n, accept ((lamport L f E hE hfE).forgeGame
+A 1 n) / (2 * (n : ℝ)) ≤ ProbComp.expect (ProbComp.sample Bool) (fun c => redProbability (f n) adv
+(i, c))`, with `adv` as in `lamport_forgeGame_accept_eq_honestProbability`.
+
+**Proof sketch.** Read the actual forgery game as the typed honest probability, then apply
+the counted favorable-pair bound and select a position at least as good as its average. -/
+theorem lamport_exists_best_position (A : NUPPT) (n : ℕ) (hn : 0 < n) :
+    ∃ i : Fin n, accept ((lamport L f E hE hfE).forgeGame A 1 n) / (2 * (n : ℝ)) ≤
+      ProbComp.expect (ProbComp.sample Bool) (fun c =>
+        LamportFill.redProbability (f n)
+          (fun Y r => A.toCompOn
+            (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
+            n 1 (LamportFill.publicWord Y) r) (i, c)) := by
+  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
+  rw [lamport_forgeGame_accept_eq_honestProbability]
+  exact LamportFill.exists_best_position (f n) _
+    (fun Y r => A.toCompOn_costBoundedBy _ n 1 (LamportFill.publicWord Y) r)
+
 /-- **Theorem 137.2: Lamport's scheme is one-time secure** [PS10, Theorem 137.2] when `f` is a
 (strong) one-way function.
 
@@ -554,14 +931,69 @@ theorem lamport_ver : (lamport L f E hE hfE).ver = lamportVerFun L E := rfl
    A best position at each length is at least as good as the uniform-position average; supply
    it as `O(log n)` bits of non-uniform advice and sample only the fair bit `c`. Thus the
    machine need not sample an exactly uniform element of `[n]` from a fixed finite coin tape.
-5. `f` is one-way, so this lower bound is negligible, and polynomial-factor closure makes `ε`
-   negligible. Apply T1 (`Games.exists_handlerMachine`) to the extended input `⟨y,i(n)⟩`, then
-   `NUPPT.exists_withAdvice` supplies the bounded advised position. `advIn` builds the public
-   key from that input and the seed, the handler answers or aborts, and `out` extracts `σ′_i`.
+5. T1 (`Games.exists_handlerMachine`) realizes the handler on `⟨y,1^i⟩`, using a fair
+   bit, a complete sampled table, and the forger's coins. A successful nonaborting typed run
+   has a safe query, so the handler's real output is the extracted preimage. Bounded decoding
+   expands the `Nat.size n`-bit best-position advice to unary; `NUPPT.exists_withAdvice`
+   supplies it without changing the coin polynomial. One-wayness makes this fixed machine's
+   inversion probability negligible. Since `ε(n) ≤ 2n·inv_B(n)` for `n ≥ 1`, polynomial-factor
+   closure proves one-time security, with zero handled by the finite exception.
 
 For zero-query successful runs the extraction fraction is `1/2`, rather than just `1/(2n)`. -/
 theorem lamport_oneTimeSecure (hf : (lamportOWF L f).StrongOneWay) :
     (lamport L f E hE hfE).OneTimeSecure := by
-  sorry
+  classical
+  apply LamportReduction.oneTimeSecure_of_inversion_lower
+    (lamport L f E hE hfE) (lamportOWF L f) hf
+  intro A
+  have hW (n : ℕ) : (lamportPkBlock L).eval n = 6 * L.eval n + 6 := by
+    rw [lamportPkBlock_eq]
+    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
+  have hEval (n : ℕ) (x : Fin n → Bool) :
+      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
+    simpa only [NUPPT.advInput_eq] using hfE n x
+  obtain ⟨B, hB⟩ := LamportFill.exists_realization_machine L (lamportPkBlock L) f
+    E (lamportGenFun E) lamportSignFun hE
+    (polyTimeComputable_lamportGenFun hE) polyTimeComputable_lamportSignFun
+    hW hEval (lamportGenFun_table L f E hE hfE) lamportSignFun_table
+    coinBlock_flatten_ofFn A
+  have hbest (n : ℕ) (hn : 0 < n) : ∃ i : Fin n,
+      accept ((lamport L f E hE hfE).forgeGame A 1 n) / (2 * (n : ℝ)) ≤
+        ProbComp.expect (ProbComp.sample Bool)
+          (fun c => LamportFill.redProbability (f n)
+            (LamportFill.machineForger L A n) (i, c)) := by
+    simpa only [LamportFill.machineForger_eq_fun] using
+      lamport_exists_best_position L f E hE hfE A n hn
+  let idx : ℕ → ℕ := fun n => if hn : 0 < n then (Classical.choose (hbest n hn)).val else 0
+  have hidx_le (n : ℕ) : idx n ≤ n := by
+    dsimp only [idx]
+    split_ifs with hn
+    · exact (Classical.choose (hbest n hn)).isLt.le
+    · exact Nat.zero_le n
+  obtain ⟨C, hCcoins, hC⟩ := LamportFill.exists_withIndexAdvice B idx hidx_le
+  refine ⟨C, fun n hn => ?_⟩
+  have hnpos : 0 < n := hn
+  let i : Fin n := Classical.choose (hbest n hnpos)
+  have hi := Classical.choose_spec (hbest n hnpos)
+  have hidx : idx n = i.val := by
+    dsimp only [idx]
+    rw [dif_pos hnpos]
+  obtain ⟨φ, hφ⟩ := hB n
+  let e : ((Bool × LamportFill.Table n) × A.Coins n) ≃ C.Coins n :=
+    φ.trans (NUPPT.coinsCongr hCcoins.symm n)
+  have hreal (y : Fin (L.eval n) → Bool) (T : LamportFill.Table n) (c : Bool)
+      (r : A.Coins n)
+      (hs : LamportFill.RedSuccess (f n) (LamportFill.machineForger L A n) y T r (i, c)) :
+      ∃ x' : Fin n → Bool,
+        C.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ f n x' = y := by
+    obtain ⟨x', hout, hfx⟩ := hφ i y T c r hs
+    refine ⟨x', ?_, hfx⟩
+    change C.runAt n (List.ofFn y)
+      (NUPPT.coinsCongr hCcoins.symm n (φ ((c, T), r))) = List.ofFn x'
+    rw [LamportFill.runAt_indexAdvice hCcoins idx hC, hidx]
+    exact hout
+  have hInv := LamportFill.fairBit_redProbability_le_invProbAt (lamportOWF L f)
+    n A C i (LamportFill.machineForger L A n) e hreal
+  exact hi.trans (by simpa only [lamportOWF_f] using hInv)
 
 end TCSlib.Cryptography.Authentication
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Advice.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Advice.lean
new file mode 100644
index 000000000..d08d63ca6
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Advice.lean
@@ -0,0 +1,148 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Asymptotic.OneWayLemmas
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Binary advice for a best Lamport position
+
+## Main definitions
+
+* `indexBits n i`: an index bounded by `n` encoded using exactly `Nat.size n` bits.
+* `expandIndex U`: expand binary index advice to unary using a parameter-bounded decoder.
+
+## Main results
+
+* `indexBits_value`: the encoded index reads back as `i`.
+* `exists_withIndexAdvice`: a machine expecting unary index data can receive that index
+  through binary non-uniform advice of exactly `Nat.size n` bits.
+
+`Nat.size n` is the binary digit count, hence the added advice has logarithmic length.
+The polynomial bound supplied to the machine constructor is the weaker `Nat.size n ≤ n`.
+The zero parameter uses an empty binary word encoding zero.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, proof of Theorem 137.2, choosing the best position as non-uniform advice.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open Complexity Turing TCSlib.Cryptography
+
+/-- An index `i ≤ n` is encoded as the inverse of the published binary-number equivalence
+at width `Nat.size n`. Its width is logarithmic, including an empty encoding at `n=0`. -/
+noncomputable def indexBits (n i : ℕ) (hi : i ≤ n) : List Bool :=
+  List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)
+
+/-- The index word is the serialized inverse image of `i` under `bitsEquiv`: `indexBits n i hi =
+List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)`. -/
+theorem indexBits_eq (n i : ℕ) (hi : i ≤ n) : indexBits n i hi =
+    List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩) := rfl
+
+/-- The binary index word has exactly `Nat.size n` bits: `(indexBits n i hi).length = Nat.size n`.
+-/
+theorem length_indexBits (n i : ℕ) (hi : i ≤ n) :
+    (indexBits n i hi).length = Nat.size n := by
+  rw [indexBits_eq, List.length_ofFn]
+
+/-- Its logarithmic width is bounded by the polynomial width `n`: `(indexBits n i hi).length ≤ n`.
+-/
+theorem length_indexBits_le (n i : ℕ) (hi : i ≤ n) : (indexBits n i hi).length ≤ n := by
+  rw [length_indexBits]
+  exact Nat.size_le.2 n.lt_two_pow_self
+
+/-- Reading the binary index word gives the original natural number `i`: `OneWay.bitListToNat
+(indexBits n i hi) = i`.
+
+**Proof sketch.** Apply `bitsEquiv` to its inverse image, read the natural-number value
+using `bitsEquiv_val`, then use the published equivalence between typed and list numerals. -/
+theorem indexBits_value (n i : ℕ) (hi : i ≤ n) :
+    OneWay.bitListToNat (indexBits n i hi) = i := by
+  have h := congrArg Fin.val ((bitsEquiv (Nat.size n)).apply_symm_apply
+    ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)
+  rw [bitsEquiv_val, OneWay.bitsToNat_eq_bitListToNat] at h
+  rw [indexBits_eq]
+  exact h
+
+/-- On a parameter-aware input `⟨1^n,⟨y,b⟩⟩`, decode the bounded binary index `b` to unary
+and return `⟨y,U(⟨1^n,b⟩)⟩`: `expandIndex U w = pairEncode (pairFstD (pairSndD w)) (U (pairEncode
+(pairFstD w) (pairSndD (pairSndD w))))`. -/
+def expandIndex (U : List Bool → List Bool) (w : List Bool) : List Bool :=
+  pairEncode (pairFstD (pairSndD w))
+    (U (pairEncode (pairFstD w) (pairSndD (pairSndD w))))
+
+/-- The expansion pairs the challenge with `U` applied to the parameter and binary index:
+`expandIndex U w = pairEncode (pairFstD (pairSndD w)) (U (pairEncode (pairFstD w) (pairSndD
+(pairSndD w))))`. -/
+theorem expandIndex_eq (U : List Bool → List Bool) (w : List Bool) : expandIndex U w =
+    pairEncode (pairFstD (pairSndD w))
+      (U (pairEncode (pairFstD w) (pairSndD (pairSndD w)))) := rfl
+
+/-- Expanding binary index advice is polynomial-time whenever the bounded decoder is:
+`PolyTimeComputable U → PolyTimeComputable (expandIndex U)`. -/
+theorem expandIndex_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
+    PolyTimeComputable (expandIndex U) :=
+  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
+    (hU.comp (polyTimeComputable_pairFstD.pairEncode
+      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
+
+/-- On canonical parameter-aware input, the bounded decoder expands `b` to its unary
+numeric value: if `OneWay.bitListToNat b ≤ n` and `U (pairEncode p b) = List.replicate
+(OneWay.bitListToNat b) true` whenever `OneWay.bitListToNat b ≤ p.length`, then `expandIndex U
+(NUPPT.advInput n (pairEncode y b)) = pairEncode y (List.replicate (OneWay.bitListToNat b) true)`.
+This reads `advInput` and pairing only through their public equations. -/
+theorem expandIndex_advInput (U : List Bool → List Bool)
+    (hU : ∀ p b : List Bool, OneWay.bitListToNat b ≤ p.length →
+      U (pairEncode p b) = List.replicate (OneWay.bitListToNat b) true)
+    (n : ℕ) (y b : List Bool) (hb : OneWay.bitListToNat b ≤ n) :
+    expandIndex U (NUPPT.advInput n (pairEncode y b)) =
+      pairEncode y (List.replicate (OneWay.bitListToNat b) true) := by
+  simp only [expandIndex_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+  rw [hU _ b (by simpa only [List.length_replicate] using hb)]
+
+/-- A machine expecting `⟨y,1^(i n)⟩` can instead receive `i n ≤ n` as non-uniform binary
+advice of exactly `Nat.size n` bits, keeping its coin polynomial. This is the best-position
+advice step in [PS10, proof of Theorem 137.2].
+
+**Proof sketch.** The public bounded binary-to-unary decoder expands an index using `1^n`
+as its output cap. Parameter-aware preprocessing composes that decoder with the original
+machine. Hard-wire the binary word using `exists_withAdvice`, bounded by `Nat.size n ≤ n`.
+The preprocessor recovers the chosen unary index at every parameter, including zero. -/
+theorem exists_withIndexAdvice (A : NUPPT) (i : ℕ → ℕ) (hi : ∀ n, i n ≤ n) :
+    ∃ B : NUPPT, B.coins = A.coins ∧
+      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r := by
+  obtain ⟨U, hU, hUread⟩ := OneWay.exists_unaryOf
+  obtain ⟨D, hDcoins, _, _, hD⟩ := NUPPT.exists_compParam A
+    (expandIndex_poly hU) polyTimeComputable_pairSndD
+  let β : ℕ → List Bool := fun n => indexBits n (i n) (hi n)
+  have hβ : ∀ n, (β n).length ≤ PolyExpr.var.eval n := by
+    intro n
+    rw [PolyExpr.eval_var]
+    exact length_indexBits_le n (i n) (hi n)
+  obtain ⟨B, hBcoins, hB⟩ := NUPPT.exists_withAdvice D β .var hβ
+  refine ⟨B, hBcoins.trans hDcoins, fun n y r => ?_⟩
+  have hvalue : OneWay.bitListToNat (β n) = i n := indexBits_value n (i n) (hi n)
+  have hcap : OneWay.bitListToNat (β n) ≤ n := by rw [hvalue]; exact hi n
+  rw [hB, hD, pairSndD_pairEncode, expandIndex_advInput U hUread n y (β n) hcap, hvalue]
+
+/-- A same-coins machine with the indexed untyped activation equation has the corresponding
+typed activation equation through the published `coinsCongr` equivalence: if `hcoins : B.coins =
+A.coins` and `B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r` for all `n`,
+`y`, `r`, then `B.runAt n y (NUPPT.coinsCongr hcoins.symm n r) = A.runAt n (pairEncode y
+(List.replicate (i n) true)) r`. -/
+theorem runAt_indexAdvice {A B : NUPPT} (hcoins : B.coins = A.coins)
+    (i : ℕ → ℕ)
+    (hB : ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r)
+    (n : ℕ) (y : List Bool) (r : A.Coins n) :
+    B.runAt n y (NUPPT.coinsCongr hcoins.symm n r) =
+      A.runAt n (pairEncode y (List.replicate (i n) true)) r := by
+  rw [NUPPT.runAt_coinsCongr hcoins.symm, hB, ← NUPPT.runAt_eq]
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Averaging.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Averaging.lean
new file mode 100644
index 000000000..608ff0beb
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Averaging.lean
@@ -0,0 +1,140 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Probability
+import Mathlib.Data.Finset.Max
+import Mathlib.Data.Fintype.Prod
+import Mathlib.Tactic.FieldSimp
+import Mathlib.Tactic.Linarith
+import Mathlib.Tactic.Positivity
+import Mathlib.Tactic.Ring
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Finite position averaging for Lamport's reduction
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `sum_favourable_bits`: a differing pair of message bits has one favourable plant bit.
+* `one_le_favourable_sum`: distinct messages have at least one favourable position and bit.
+* `favourable_expect_ge`: the favourable fraction is at least `1 / (2 |I|)`.
+* `noQuery_expect_eq_half`: without a query the favourable fraction is exactly `1 / 2`.
+* `exists_expect_sample_le`: a finite uniform average is bounded by a value it averages.
+* `expect_favourable_of_success`: pointwise favourable mass bounds its average on successes.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, Theorem 137.2. The finite arithmetic is generic glue for its reduction.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportReduction
+
+open Finset TCSlib.Cryptography.Games
+
+/-- For two bits `a` and `b`, the number of bits `c` satisfying `a ≠ c = b` is one
+when `a ≠ b`, and zero otherwise. -/
+theorem sum_favourable_bits (a b : Bool) :
+    (∑ c : Bool, if a ≠ c ∧ b = c then (1 : ℝ) else 0) = if a ≠ b then 1 else 0 := by
+  cases a <;> cases b <;> simp
+
+/-- The number of position-bit pairs with `m i ≠ c = m' i` is the number of positions at
+which the messages differ. [PS10, proof of Theorem 137.2]. -/
+theorem sum_favourable_pairs {ι : Type} [Fintype ι] (m m' : ι → Bool) :
+    (∑ p : ι × Bool, if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0) =
+      ∑ i : ι, if m i ≠ m' i then (1 : ℝ) else 0 := by
+  rw [Fintype.sum_prod_type]
+  exact Finset.sum_congr rfl fun i _ => sum_favourable_bits (m i) (m' i)
+
+/-- Distinct messages have at least one jointly favourable position and bit:
+`1 ≤ ∑_(i,c) 1[m_i ≠ c = m'_i]`. [PS10, proof of Theorem 137.2].
+
+**Proof sketch.** Extensional inequality supplies a differing coordinate. Its indicator is
+one, and all other indicators in the sum are nonnegative. -/
+theorem one_le_favourable_sum {ι : Type} [Fintype ι] {m m' : ι → Bool} (h : m ≠ m') :
+    1 ≤ ∑ p : ι × Bool, if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0 := by
+  classical
+  have hex : ∃ i, m i ≠ m' i := by
+    by_contra hh
+    push_neg at hh
+    exact h (funext hh)
+  obtain ⟨i, hi⟩ := hex
+  rw [sum_favourable_pairs]
+  have hle := Finset.single_le_sum
+    (s := Finset.univ) (a := i)
+    (f := fun j => if m j ≠ m' j then (1 : ℝ) else 0)
+    (fun j _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ i)
+  calc
+    1 = (if m i ≠ m' i then (1 : ℝ) else 0) := (if_pos hi).symm
+    _ ≤ ∑ j : ι, if m j ≠ m' j then (1 : ℝ) else 0 := hle
+
+/-- For distinct messages on a nonempty finite position type, uniform `(i,c)` is jointly
+favourable with probability at least `1 / (2 |I|)`: if `m ≠ m'`, then `1 / (2 * (Fintype.card ι :
+ℝ)) ≤ ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 :
+ℝ) else 0)`. [PS10, proof of Theorem 137.2]. -/
+theorem favourable_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
+    {m m' : ι → Bool} (h : m ≠ m') :
+    1 / (2 * (Fintype.card ι : ℝ)) ≤
+      ProbComp.expect (ProbComp.sample (ι × Bool))
+        (fun p => if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0) := by
+  rw [ProbComp.expect_sample]
+  simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
+  have hcount := one_le_favourable_sum h
+  have hden : 0 ≤ ((Fintype.card ι : ℝ) * 2)⁻¹ := by positivity
+  have hmul := mul_le_mul_of_nonneg_left hcount hden
+  simpa only [mul_one, one_div, mul_comm 2 (Fintype.card ι : ℝ)] using hmul
+
+/-- When there was no signing query, a uniform position and bit agrees with the forged
+message bit with probability exactly `1 / 2`: `ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p
+=> if m' p.1 = p.2 then (1 : ℝ) else 0) = 1 / 2`. [PS10, proof of Theorem 137.2]. -/
+theorem noQuery_expect_eq_half {ι : Type} [Fintype ι] [Nonempty ι] (m' : ι → Bool) :
+    ProbComp.expect (ProbComp.sample (ι × Bool))
+        (fun p => if m' p.1 = p.2 then (1 : ℝ) else 0) = 1 / 2 := by
+  have hbit (b : Bool) : (∑ c : Bool, if b = c then (1 : ℝ) else 0) = 1 := by
+    cases b <;> simp
+  rw [ProbComp.expect_sample, Fintype.sum_prod_type]
+  simp only [hbit, sum_const, card_univ, nsmul_eq_mul, mul_one,
+    Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
+  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by positivity
+  field_simp
+
+/-- A uniform finite average has a position whose value is at least the average: `∃ i,
+ProbComp.expect (ProbComp.sample ι) g ≤ g i`.
+
+**Proof sketch.** A maximum exists on the nonempty finite type. Every term of the sum is at
+most that maximum, so the uniform average is at most it. -/
+theorem exists_expect_sample_le {ι : Type} [Fintype ι] [Nonempty ι] (g : ι → ℝ) :
+    ∃ i, ProbComp.expect (ProbComp.sample ι) g ≤ g i := by
+  classical
+  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
+  refine ⟨i, ?_⟩
+  calc
+    ProbComp.expect (ProbComp.sample ι) g ≤
+        ProbComp.expect (ProbComp.sample ι) (fun _ => g i) :=
+      ProbComp.expect_mono _ (fun j => hi j (Finset.mem_univ j))
+    _ = g i := ProbComp.expect_const _ _
+
+/-- If nonnegative favourable mass is at least `b` on every successful output, its average
+is at least `b` times the success probability: if `∀ a, 0 ≤ q a` and `∀ a, P a → b ≤ q a`, then `b *
+ProbComp.prob c P ≤ ProbComp.expect c q`. This is the finite averaging step in [PS10, proof of
+Theorem 137.2]. -/
+theorem expect_favourable_of_success {α : Type} (c : ProbComp α) (P : α → Prop)
+    (q : α → ℝ) (b : ℝ) (hq : ∀ a, 0 ≤ q a) (hP : ∀ a, P a → b ≤ q a) :
+    b * ProbComp.prob c P ≤ ProbComp.expect c q := by
+  classical
+  rw [ProbComp.prob_eq_expect, ← ProbComp.expect_const_mul]
+  apply ProbComp.expect_mono
+  intro a
+  by_cases ha : P a
+  · simpa only [ha, if_true, mul_one] using hP a ha
+  · simpa only [ha, if_false, mul_zero] using hq a
+
+end TCSlib.Cryptography.Authentication.LamportReduction
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/AveragingExtra.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/AveragingExtra.lean
new file mode 100644
index 000000000..0029e6dd5
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/AveragingExtra.lean
@@ -0,0 +1,91 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
+import TCSlib.Cryptography.Games.Bridges.Experiments
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Optional-query and fair-bit position averaging
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `optionQuery_favourable_expect_ge`: fresh forged messages have favourable fraction
+  at least `1 / (2 |I|)`, with or without a query.
+* `exists_position_fairBit_expect_ge`: some fixed position with a fresh fair bit performs
+  at least as well as a uniform position and bit.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, Theorem 137.2. These are the counting and best-position steps of its reduction.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportReduction
+
+open TCSlib.Cryptography.Games
+
+/-- If an optional queried message differs from the forged message, a uniform position and
+bit avoids revealing the planted preimage and selects the forged preimage with probability
+at least `1 / (2 |I|)`: if `q ≠ some m'`, then `1 / (2 * (Fintype.card ι : ℝ)) ≤ ProbComp.expect
+(ProbComp.sample (ι × Bool)) (fun p => if (∀ m, q = some m → m p.1 ≠ p.2) ∧ m' p.1 = p.2 then (1 :
+ℝ) else 0)`. An absent query imposes no avoidance constraint. [PS10, proof of Theorem 137.2].
+
+**Proof sketch.** With a query, freshness gives distinct messages and the differing-coordinate
+bound applies. Without a query, half of the position-bit pairs select the forged preimage;
+this is at least `1 / (2 |I|)` because the position type is nonempty. -/
+theorem optionQuery_favourable_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
+    (q : Option (ι → Bool)) (m' : ι → Bool) (hfresh : q ≠ some m') :
+    1 / (2 * (Fintype.card ι : ℝ)) ≤
+      ProbComp.expect (ProbComp.sample (ι × Bool))
+        (fun p => if (∀ m, q = some m → m p.1 ≠ p.2) ∧ m' p.1 = p.2
+          then (1 : ℝ) else 0) := by
+  classical
+  cases q with
+  | none =>
+    simp only [reduceCtorEq, false_implies, forall_const, true_and]
+    rw [noQuery_expect_eq_half]
+    have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
+      exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card ι))
+    exact one_div_le_one_div_of_le (by positivity) (by linarith)
+  | some m =>
+    have hne : m ≠ m' := by
+      intro h
+      exact hfresh (congrArg some h)
+    simpa using (favourable_expect_ge hne)
+
+/-- For every payoff `v(i,c)` on a nonempty finite position type and a bit, there is a
+position whose average over a fair bit is at least the average over a uniform position and
+fair bit: `∃ i, ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) ≤ ProbComp.expect
+(ProbComp.sample Bool) (v i)`. [PS10, proof of Theorem 137.2].
+
+**Proof sketch.** Apply finite maximum averaging to the payoff already averaged over the bit.
+The published product-sampling equation identifies its average over positions with the
+uniform-pair expectation. -/
+theorem exists_position_fairBit_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
+    (v : ι → Bool → ℝ) :
+    ∃ i, ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) ≤
+      ProbComp.expect (ProbComp.sample Bool) (v i) := by
+  obtain ⟨i, hi⟩ := exists_expect_sample_le
+    (fun j : ι => ProbComp.expect (ProbComp.sample Bool) (v j))
+  refine ⟨i, ?_⟩
+  calc
+    ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) =
+        ProbComp.expect
+          ((ProbComp.sample ι).bind fun j =>
+            (ProbComp.sample Bool).bind fun c => .pure (j, c)) (fun p => v p.1 p.2) :=
+      (Bridge.expect_sample_pair (fun p : ι × Bool => v p.1 p.2)).symm
+    _ = ProbComp.expect (ProbComp.sample ι)
+        (fun j => ProbComp.expect (ProbComp.sample Bool) (v j)) := by
+      simp only [ProbComp.expect_bind, ProbComp.expect_pure]
+    _ ≤ ProbComp.expect (ProbComp.sample Bool) (v i) := hi
+
+end TCSlib.Cryptography.Authentication.LamportReduction
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Blocks.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Blocks.lean
new file mode 100644
index 000000000..e9f9796aa
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Blocks.lean
@@ -0,0 +1,78 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import Mathlib.Data.List.OfFn
+import Mathlib.Data.List.Basic
+import Mathlib.Tactic.Ring
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Replacing a fixed-width block in a concatenated tuple
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `flatten_ofFn_update`: replacing a block by prefix, replacement and suffix agrees with a
+  function update before serialization.
+
+## References
+
+Generic list and finite-tuple glue; no textbook counterpart.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+/-- Replacing block `i` of a concatenation of `B`-bit blocks by the `B`-bit word `h` is
+serialization of the updated tuple:
+`take(iB, flatten(g)) ++ h ++ drop((i+1)B, flatten(g)) = flatten(update(g,i,h))`.
+
+**Proof sketch.** Induct on the number of blocks and split the updated index into zero or a
+successor. At zero, dropping the first block leaves the unchanged tail. At a successor,
+taking and dropping pass the initial block, so the induction hypothesis applies to the tail;
+the untouched initial block is then prepended. All length calculations use the given uniform
+block-width equations. -/
+theorem flatten_ofFn_update {B : ℕ} :
+    ∀ {q : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
+      (i : Fin q) (h : List Bool) (hh : h.length = B),
+      (List.ofFn g).flatten.take (i.val * B) ++ h ++
+          (List.ofFn g).flatten.drop ((i.val + 1) * B) =
+        (List.ofFn (Function.update g i h)).flatten
+  | 0, _, _, i, _, _ => i.elim0
+  | q + 1, g, hg, i, h, hh => by
+    have hflat : (List.ofFn g).flatten =
+        g 0 ++ (List.ofFn (Fin.tail g)).flatten := by
+      rw [List.ofFn_succ, List.flatten_cons, Fin.tail_def]
+    cases i using Fin.cases with
+    | zero =>
+      have hupdate : Function.update g 0 h = Fin.cons h (Fin.tail g) := by
+        have hu := Fin.update_cons_zero (x := g 0) (p := Fin.tail g) (z := h)
+        simpa only [Fin.cons_self_tail] using hu
+      rw [hflat, hupdate, List.ofFn_cons, List.flatten_cons]
+      simp only [Fin.val_zero, Nat.zero_mul, List.take_zero, List.nil_append,
+        Nat.zero_add, Nat.one_mul]
+      rw [List.drop_left' (hg 0)]
+    | succ j =>
+      have hstart : (j.succ : Fin (q + 1)).val * B = (g 0).length + j.val * B := by
+        simp only [Fin.val_succ, hg 0]
+        ring
+      have hend : ((j.succ : Fin (q + 1)).val + 1) * B =
+          (g 0).length + (j.val + 1) * B := by
+        simp only [Fin.val_succ, hg 0]
+        ring
+      have hupdate : Function.update g j.succ h =
+          Fin.cons (g 0) (Function.update (Fin.tail g) j h) := by
+        rw [Fin.cons_update, Fin.cons_self_tail]
+      rw [hflat, hstart, hend, List.take_length_add_append,
+        List.drop_length_add_append, hupdate, List.ofFn_cons, List.flatten_cons]
+      have ht : ∀ k : Fin q, ((Fin.tail g) k).length = B := fun k => hg k.succ
+      simpa only [List.append_assoc] using congrArg (List.append (g 0))
+        (flatten_ofFn_update (Fin.tail g) ht j h hh)
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Closing.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Closing.lean
new file mode 100644
index 000000000..2315e2f31
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Closing.lean
@@ -0,0 +1,95 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Defs
+import TCSlib.Cryptography.Asymptotic.OneWay
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Closing Lamport's linear-loss reduction
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `negligible_of_linear_bound`: a nonnegative function bounded by `2n` times a negligible
+  nonnegative function for `n ≥ 1` is negligible.
+* `oneTimeSecure_of_inversion_bound`: the same bound for each forger proves one-time security.
+
+The zero parameter is excluded only from the eventual comparison supplied to
+`Negligible.mono`; no value at zero is changed or assumed.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, proof of Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportReduction
+
+open Complexity TCSlib.Cryptography.Games
+
+/-- If `e` and `p` are nonnegative, `p` is negligible, and `e(n) ≤ 2n·p(n)` for `n ≥ 1`,
+then `e` is negligible. [PS10, final step of the proof of Theorem 137.2].
+
+**Proof sketch.** Multiplication by `n` and then by two preserves negligibility. The eventual
+comparison starts at one, so the zero parameter is a finite exception. -/
+theorem negligible_of_linear_bound {e p : ℕ → ℝ} (hp : Negligible p)
+    (hp0 : ∀ n, 0 ≤ p n) (he0 : ∀ n, 0 ≤ e n)
+    (hbound : ∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * p n) : Negligible e := by
+  have hmajorant : Negligible (fun n => (2 : ℝ) * ((n : ℝ) ^ 1 * p n)) :=
+    (hp.mul_pow 1).const_mul 2
+  apply hmajorant.mono
+  refine ⟨1, fun n hn => ?_⟩
+  have hnonneg : 0 ≤ (2 : ℝ) * ((n : ℝ) ^ 1 * p n) :=
+    mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 1) (hp0 n))
+  rw [abs_of_nonneg (he0 n), abs_of_nonneg hnonneg]
+  simpa only [pow_one, mul_assoc] using hbound n hn
+
+/-- A nonnegative advantage bounded by `2n` times the inversion probability of a fixed
+machine against a strong one-way family is negligible for all parameters, with no condition
+needed at zero: if `F.StrongOneWay`, `∀ n, 0 ≤ e n` and `∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * F.invProbAt B
+n`, then `Negligible e`. [PS10, final step of the proof of Theorem 137.2]. -/
+theorem negligible_of_inversion_bound (F : FunFamily) (hf : F.StrongOneWay) (B : NUPPT)
+    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n)
+    (hbound : ∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * F.invProbAt B n) : Negligible e :=
+  negligible_of_linear_bound (hf.hard B) (F.invProbAt_nonneg B) he0 hbound
+
+/-- A signature scheme is one-time secure if each forger yields a fixed machine whose
+inversion probability against a strong one-way family bounds its forgery probability with
+loss `2n` for `n ≥ 1`. [PS10, reduction conclusion in Theorem 137.2].
+
+**Proof sketch.** Use each forger's own acceptance probability as its security majorant.
+Polynomial-factor closure proves that majorant negligible; its pointwise bound is equality. -/
+theorem oneTimeSecure_of_inversion_bound (S : SignatureScheme) (F : FunFamily)
+    (hf : F.StrongOneWay)
+    (hred : ∀ A : NUPPT, ∃ B : NUPPT, ∀ n ≥ 1,
+      accept (S.forgeGame A 1 n) ≤ 2 * (n : ℝ) * F.invProbAt B n) : S.OneTimeSecure := by
+  apply (S.oneTimeSecure_iff).2
+  intro A
+  obtain ⟨B, hB⟩ := hred A
+  refine ⟨fun n => accept (S.forgeGame A 1 n), ?_, fun _ => le_rfl⟩
+  exact negligible_of_inversion_bound F hf B _ (fun n => accept_nonneg _) hB
+
+/-- The probability-form reduction `ε(n)/(2n) ≤ inv_B(n)` also implies one-time security.
+[PS10, averaging bound and conclusion in Theorem 137.2]. -/
+theorem oneTimeSecure_of_inversion_lower (S : SignatureScheme) (F : FunFamily)
+    (hf : F.StrongOneWay)
+    (hred : ∀ A : NUPPT, ∃ B : NUPPT, ∀ n ≥ 1,
+      accept (S.forgeGame A 1 n) / (2 * (n : ℝ)) ≤ F.invProbAt B n) : S.OneTimeSecure := by
+  apply oneTimeSecure_of_inversion_bound S F hf
+  intro A
+  obtain ⟨B, hB⟩ := hred A
+  refine ⟨B, fun n hn => ?_⟩
+  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
+  have hden : 0 < (2 : ℝ) * (n : ℝ) := mul_pos (by norm_num) hn0
+  have h := (div_le_iff₀ hden).1 (hB n hn)
+  simpa only [mul_comm (F.invProbAt B n) (2 * (n : ℝ))] using h
+
+end TCSlib.Cryptography.Authentication.LamportReduction
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Encoding.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Encoding.lean
new file mode 100644
index 000000000..f5e776f43
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Encoding.lean
@@ -0,0 +1,85 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
+import TCSlib.Complexity.TuringMachine.Encoding
+import Mathlib.Data.List.OfFn
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Injectivity of the cryptographic tuple encoding
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `encodeList_injective`: equality of encoded lists implies equality of their blocks.
+* `encodeList_eq_iff`: list encodings agree exactly when the lists agree.
+* `encodeList_ofFn_eq_iff`: encodings of finite tuples agree exactly when the tuples agree.
+
+## References
+
+Generic encoding lemmas; no textbook counterpart. These use the list encoding of
+[PS10, Definition 93.1] through its published equations only.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportReduction
+
+open Turing
+open TCSlib.Cryptography.PrivateKeyScheme (encodeList encodeList_nil encodeList_cons)
+
+/-- The nested-pair list encoding is injective: `encodeList xs = encodeList ys` implies
+`xs = ys`.
+
+**Proof sketch.** Induct on the first list. An empty encoding cannot equal a cons encoding,
+since a pair encoding is nonempty. For two cons encodings, injectivity of pairing identifies
+the heads and the encoded tails, and induction identifies the tails. -/
+theorem encodeList_injective : Function.Injective encodeList := by
+  have haux : ∀ xs ys : List (List Bool), encodeList xs = encodeList ys → xs = ys := by
+    intro xs
+    induction xs with
+    | nil =>
+      intro ys h
+      cases ys with
+      | nil => rfl
+      | cons y ys =>
+        rw [encodeList_nil, encodeList_cons] at h
+        exact False.elim (pairEncode_ne_nil y (encodeList ys) h.symm)
+    | cons x xs ih =>
+      intro ys h
+      cases ys with
+      | nil =>
+        rw [encodeList_cons, encodeList_nil] at h
+        exact False.elim (pairEncode_ne_nil x (encodeList xs) h)
+      | cons y ys =>
+        rw [encodeList_cons, encodeList_cons] at h
+        have hp : (x, encodeList xs) = (y, encodeList ys) := pairEncode_injective h
+        have hx : x = y := congrArg Prod.fst hp
+        have hxs : xs = ys := ih ys (congrArg Prod.snd hp)
+        exact congrArg₂ List.cons hx hxs
+  intro xs ys h
+  exact haux xs ys h
+
+/-- Two nested-pair list encodings agree exactly when their lists of blocks agree: `encodeList xs =
+encodeList ys ↔ xs = ys`. -/
+theorem encodeList_eq_iff (xs ys : List (List Bool)) :
+    encodeList xs = encodeList ys ↔ xs = ys :=
+  ⟨fun h => encodeList_injective h, congrArg encodeList⟩
+
+/-- Encodings of two tuples with the same finite index length agree exactly when the tuples
+agree: `encodeList (List.ofFn g) = encodeList (List.ofFn h) ↔ g = h`. -/
+theorem encodeList_ofFn_eq_iff {q : ℕ} (g h : Fin q → List Bool) :
+    encodeList (List.ofFn g) = encodeList (List.ofFn h) ↔ g = h := by
+  constructor
+  · intro heq
+    exact List.ofFn_injective (encodeList_injective heq)
+  · intro heq
+    exact congrArg (fun k : Fin q → List Bool => encodeList (List.ofFn k)) heq
+
+end TCSlib.Cryptography.Authentication.LamportReduction
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Experiment.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Experiment.lean
new file mode 100644
index 000000000..67580f411
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Experiment.lean
@@ -0,0 +1,270 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
+import TCSlib.Cryptography.Authentication.Encoding
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The typed Lamport reduction and its average success
+
+## Main definitions
+
+* `honestOutput` and `HonestSuccess`: the honest typed forgery and its acceptance/freshness test.
+* `Favourable`: the sole query avoids the planted preimage and the forgery uses it.
+* `RedSuccess`: a nonaborting planted simulation whose extracted block inverts its challenge.
+* `honestProbability` and `redProbability`: the honest and independently challenged averages.
+
+## Main results
+
+* `favourable_mass_of_success`: favorable position mass is at least `1/(2n)` on successes.
+* `diagonal_red_of_success_favourable`: favorable honest successes invert their table entry.
+* `averaged_redProbability_ge`: uniform planted reduction success is at least `H/(2n)`.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, Protocol 137.1 and Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open TCSlib.Cryptography.Games
+open scoped Classical
+
+-- Keep elaboration on the published probability readers.
+run_cmd do
+  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
+    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
+    unless status == .irreducible do
+      let id := Lean.mkIdent n
+      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
+
+section TypedExperiment
+
+variable {n ℓ : ℕ} {ρ : Type}
+  (g : (Fin n → Bool) → Fin ℓ → Bool)
+  (adv : ((Fin n × Bool) → Fin ℓ → Bool) → ρ →
+    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) (Fin (n + n * n) → Bool))
+
+/-- Evaluate the forger on the honest public table with deterministic table signing: `honestOutput g
+adv T r = (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m)`. -/
+def honestOutput (T : Table n) (r : ρ) : Fin (n + n * n) → Bool :=
+  (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m)
+
+/-- The honest output is functional evaluation against the selected-preimage signing function:
+`honestOutput g adv T r = (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m)`. -/
+theorem honestOutput_eq (T : Table n) (r : ρ) :
+    honestOutput g adv T r =
+      (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m) := rfl
+
+/-- An honest output succeeds when all its signature blocks verify and its message was
+not the optional signing query [PS10, Definition 136.2]: `HonestSuccess g adv T r ↔ (∀ j, g
+(signatureBlock σ j) = g (T (j, m j))) ∧ firstQuery (adv (tablePublic g T) r) ≠ some m`, where `(m,
+σ) = splitBits (honestOutput g adv T r)`. -/
+def HonestSuccess (T : Table n) (r : ρ) : Prop :=
+  (∀ j, g (signatureBlock (splitBits (honestOutput g adv T r)).2 j) =
+    g (T (j, (splitBits (honestOutput g adv T r)).1 j))) ∧
+    firstQuery (adv (tablePublic g T) r) ≠ some (splitBits (honestOutput g adv T r)).1
+
+/-- Honest success is coordinate verification together with inequality to the optional query:
+`HonestSuccess g adv T r ↔ (∀ j, g (signatureBlock σ j) = g (T (j, m j))) ∧ firstQuery (adv
+(tablePublic g T) r) ≠ some m`, where `(m, σ) = splitBits (honestOutput g adv T r)`. -/
+theorem honestSuccess_iff (T : Table n) (r : ρ) :
+    HonestSuccess g adv T r ↔
+      (∀ j, g (signatureBlock (splitBits (honestOutput g adv T r)).2 j) =
+        g (T (j, (splitBits (honestOutput g adv T r)).1 j))) ∧
+      firstQuery (adv (tablePublic g T) r) ≠ some (splitBits (honestOutput g adv T r)).1 :=
+  Iff.rfl
+
+/-- A position-bit pair is favorable when its signing query is safe and its forged message
+uses the planted bit [PS10, proof of Theorem 137.2]: `Favourable g adv T r p ↔ Safe (adv
+(tablePublic g T) r) p.1 p.2 ∧ (splitBits (honestOutput g adv T r)).1 p.1 = p.2`. -/
+def Favourable (T : Table n) (r : ρ) (p : Fin n × Bool) : Prop :=
+  Safe (adv (tablePublic g T) r) p.1 p.2 ∧
+    (splitBits (honestOutput g adv T r)).1 p.1 = p.2
+
+/-- Favorability is signing-query safety conjoined with the forged message's planted bit:
+`Favourable g adv T r p ↔ Safe (adv (tablePublic g T) r) p.1 p.2 ∧ (splitBits (honestOutput g adv T
+r)).1 p.1 = p.2`. -/
+theorem favourable_iff (T : Table n) (r : ρ) (p : Fin n × Bool) :
+    Favourable g adv T r p ↔ Safe (adv (tablePublic g T) r) p.1 p.2 ∧
+      (splitBits (honestOutput g adv T r)).1 p.1 = p.2 := Iff.rfl
+
+/-- The planted reduction succeeds if it ends without abort and its extracted signature
+block is a preimage of the challenge [PS10, proof of Theorem 137.2]: `RedSuccess g adv y T r p ↔ ∃
+a, simulate (abortingImpl T p.1 p.2) (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false)
+∧ g (signatureBlock (splitBits a).2 p.1) = y`. -/
+def RedSuccess (y : Fin ℓ → Bool) (T : Table n) (r : ρ) (p : Fin n × Bool) : Prop :=
+  ∃ a, simulate (abortingImpl T p.1 p.2)
+      (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧
+    g (signatureBlock (splitBits a).2 p.1) = y
+
+/-- Reduction success means a pure nonaborting simulation output whose selected block
+maps to the challenge: `RedSuccess g adv y T r p ↔ ∃ a, simulate (abortingImpl T p.1 p.2) (adv
+(plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧ g (signatureBlock (splitBits a).2 p.1) =
+y`. -/
+theorem redSuccess_iff (y : Fin ℓ → Bool) (T : Table n) (r : ρ) (p : Fin n × Bool) :
+    RedSuccess g adv y T r p ↔
+      ∃ a, simulate (abortingImpl T p.1 p.2)
+          (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧
+        g (signatureBlock (splitBits a).2 p.1) = y := Iff.rfl
+
+/-- Replacing a table coordinate by its present value leaves the table unchanged: `plantTable T i c
+(T (i, c)) = T`. -/
+theorem plantTable_self (T : Table n) (i : Fin n) (c : Bool) :
+    plantTable T i c (T (i, c)) = T := by
+  funext p
+  rw [plantTable_eq]
+  by_cases hp : p = (i, c)
+  · rw [if_pos hp, hp]
+  · rw [if_neg hp]
+
+/-- Reduction success ignores the original table preimage at the planted position: `RedSuccess g adv
+y (plantTable T p.1 p.2 x) r p ↔ RedSuccess g adv y T r p`. -/
+theorem redSuccess_plant_iff (y : Fin ℓ → Bool) (T : Table n) (r : ρ)
+    (p : Fin n × Bool) (x : Fin n → Bool) :
+    RedSuccess g adv y (plantTable T p.1 p.2 x) r p ↔ RedSuccess g adv y T r p := by
+  rw [redSuccess_iff, redSuccess_iff, plantedPublic_plant, abortingImpl_plant]
+
+/-- A favorable successful honest run is a successful planted reduction when challenged
+with the image of its own selected table entry [PS10, proof of Theorem 137.2]: if every `adv Y r`
+has `(adv Y r).CostBoundedBy (fun _ => 1) 1`, `HonestSuccess g adv T r` and `Favourable g adv T r
+p`, then `RedSuccess g adv (g (T p)) T r p`.
+
+**Proof sketch.** Planting the present entry `T p` leaves the planted public table equal to the
+honest one and the key unchanged (`plantedPublic_image`, `plantTable_self`). Safety then gives, by
+`planted_coupling`, the nonaborting output `honestOutput g adv T r`. Acceptance at position `p.1`,
+whose forged bit is `p.2`, says that its block maps to `g (T p)`. -/
+theorem diagonal_red_of_success_favourable
+    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1)
+    (T : Table n) (r : ρ) (p : Fin n × Bool)
+    (hs : HonestSuccess g adv T r) (hq : Favourable g adv T r p) :
+    RedSuccess g adv (g (T p)) T r p := by
+  obtain ⟨hacc, hfresh⟩ := (honestSuccess_iff g adv T r).1 hs
+  obtain ⟨hsafe, hbit⟩ := (favourable_iff g adv T r p).1 hq
+  apply (redSuccess_iff g adv (g (T p)) T r p).2
+  refine ⟨honestOutput g adv T r, ?_, ?_⟩
+  · rw [plantedPublic_image, plantTable_self]
+    have h := planted_coupling T p.1 p.2 (T p) (adv (tablePublic g T) r)
+      (hcost _ r) hsafe
+    rw [plantTable_self, ← honestOutput_eq g adv T r] at h
+    exact h
+  · have h := hacc p.1
+    rw [hbit] at h
+    exact h
+
+/-- On every successful honest run, favorable position-bit mass is at least `1/(2n)`;
+the no-query case has mass exactly `1/2` [PS10, proof of Theorem 137.2]: if `HonestSuccess g adv T
+r`, then `1 / (2 * (n : ℝ)) ≤ ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p => if
+Favourable g adv T r p then (1 : ℝ) else 0)`.
+
+**Proof sketch.** Freshness says that the optional first query differs from the forged message, so
+`optionQuery_favourable_expect_ge` bounds the mass of the pairs that avoid the query and select the
+forged bit. Each such pair is favourable (`favourable_iff`, `safe_iff`), and expectation is
+monotone. -/
+theorem favourable_mass_of_success [Nonempty (Fin n)] (T : Table n) (r : ρ)
+    (hs : HonestSuccess g adv T r) :
+    1 / (2 * (n : ℝ)) ≤ ProbComp.expect (ProbComp.sample (Fin n × Bool))
+      (fun p => if Favourable g adv T r p then (1 : ℝ) else 0) := by
+  have h := LamportReduction.optionQuery_favourable_expect_ge
+    (firstQuery (adv (tablePublic g T) r)) (splitBits (honestOutput g adv T r)).1
+    ((honestSuccess_iff g adv T r).1 hs).2
+  simp only [Fintype.card_fin] at h
+  apply h.trans
+  apply ProbComp.expect_mono
+  intro p
+  by_cases hp : Favourable g adv T r p
+  · obtain ⟨hsafe, hbit⟩ := (favourable_iff g adv T r p).1 hp
+    have hr : (∀ m, firstQuery (adv (tablePublic g T) r) = some m → m p.1 ≠ p.2) ∧
+        (splitBits (honestOutput g adv T r)).1 p.1 = p.2 :=
+      ⟨(safe_iff _ p.1 p.2).1 hsafe, hbit⟩
+    simp only [if_pos hr, if_pos hp, le_refl]
+  · have hr : ¬ ((∀ m, firstQuery (adv (tablePublic g T) r) = some m → m p.1 ≠ p.2) ∧
+        (splitBits (honestOutput g adv T r)).1 p.1 = p.2) := by
+      intro hh
+      exact hp ((favourable_iff g adv T r p).2 ⟨(safe_iff _ p.1 p.2).2 hh.1, hh.2⟩)
+    simp only [if_neg hr, if_neg hp, le_refl]
+
+variable [Fintype ρ] [Nonempty ρ]
+
+/-- Honest success probability averages over the complete key table and forger coins:
+`honestProbability g adv = ProbComp.expect (ProbComp.sample (Table n)) (fun T => ProbComp.expect
+(ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0)`. -/
+noncomputable def honestProbability : ℝ :=
+  ProbComp.expect (ProbComp.sample (Table n)) fun T =>
+    ProbComp.expect (ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0
+
+/-- Honest probability is the nested uniform expectation of the honest-success indicator:
+`honestProbability g adv = ProbComp.expect (ProbComp.sample (Table n)) (fun T => ProbComp.expect
+(ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0)`. -/
+theorem honestProbability_eq : honestProbability g adv =
+    ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
+      ProbComp.expect (ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0) := rfl
+
+/-- The fixed-position reduction's success probability uses an independent challenge
+preimage, a complete random table, and forger coins: `redProbability g adv p = ProbComp.expect
+(ProbComp.sample (Fin n → Bool)) (fun x => ProbComp.expect (ProbComp.sample (Table n)) fun T =>
+ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1 else 0)`. -/
+noncomputable def redProbability (p : Fin n × Bool) : ℝ :=
+  ProbComp.expect (ProbComp.sample (Fin n → Bool)) fun x =>
+    ProbComp.expect (ProbComp.sample (Table n)) fun T =>
+      ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1 else 0
+
+/-- Fixed-position reduction probability is the nested average of its nonaborting inversion
+indicator over independent challenge, key-table and forger samples: `redProbability g adv p =
+ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x => ProbComp.expect (ProbComp.sample (Table
+n)) fun T => ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1
+else 0)`. -/
+theorem redProbability_eq (p : Fin n × Bool) : redProbability g adv p =
+    ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
+      ProbComp.expect (ProbComp.sample (Table n)) fun T =>
+        ProbComp.expect (ProbComp.sample ρ) fun r =>
+          if RedSuccess g adv (g x) T r p then 1 else 0) :=
+  rfl
+
+/-- A uniform position-bit planted reduction succeeds with probability at least the honest
+forgery probability divided by `2n` [PS10, proof of Theorem 137.2]: if every `adv Y r` has `(adv Y
+r).CostBoundedBy (fun _ => 1) 1`, then `honestProbability g adv / (2 * (n : ℝ)) ≤ ProbComp.expect
+(ProbComp.sample (Fin n × Bool)) (redProbability g adv)`.
+
+**Proof sketch.** Favorable pairs occupy at least `1/(2n)` of every successful honest run.
+On those pairs the planted simulation is safe and its extracted signature block inverts
+the image of the corresponding honest preimage. The reduction ignores that preimage,
+so coordinate resampling makes the challenge independent while preserving the average. -/
+theorem averaged_redProbability_ge [Nonempty (Fin n)]
+    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1) :
+    honestProbability g adv / (2 * (n : ℝ)) ≤
+      ProbComp.expect (ProbComp.sample (Fin n × Bool)) (redProbability g adv) := by
+  classical
+  have h := coordinate_reduction_bound
+    (HonestSuccess g adv) (Favourable g adv)
+    (fun x T r p => RedSuccess g adv (g x) T r p) (1 / (2 * (n : ℝ)))
+    (favourable_mass_of_success g adv)
+    (diagonal_red_of_success_favourable g adv hcost)
+    (fun x x' T r p => by
+      rw [← plantTable_update T p.1 p.2 x']
+      exact redSuccess_plant_iff g adv (g x) T r p x')
+  simpa only [honestProbability_eq, redProbability_eq, one_div_mul_eq_div] using h
+
+/-- Some fixed position, while its planted bit remains fair, has reduction probability at
+least `H/(2n)` [PS10, proof of Theorem 137.2]: if every `adv Y r` has `(adv Y r).CostBoundedBy (fun
+_ => 1) 1`, then `∃ i : Fin n, honestProbability g adv / (2 * (n : ℝ)) ≤ ProbComp.expect
+(ProbComp.sample Bool) (fun c => redProbability g adv (i, c))`. This is the position supplied as
+advice. -/
+theorem exists_best_position [Nonempty (Fin n)]
+    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1) :
+    ∃ i : Fin n, honestProbability g adv / (2 * (n : ℝ)) ≤
+      ProbComp.expect (ProbComp.sample Bool) (fun c => redProbability g adv (i, c)) := by
+  obtain ⟨i, hi⟩ := LamportReduction.exists_position_fairBit_expect_ge
+    (fun i : Fin n => fun c : Bool => redProbability g adv (i, c))
+  exact ⟨i, (averaged_redProbability_ge g adv hcost).trans hi⟩
+
+end TypedExperiment
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/InversionProbability.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/InversionProbability.lean
new file mode 100644
index 000000000..b86647d62
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/InversionProbability.lean
@@ -0,0 +1,89 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
+import TCSlib.Cryptography.Asymptotic.OneWay
+import TCSlib.Cryptography.Games.Bridges.Experiments
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The planted reduction probability is bounded by machine inversion
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `fairBit_redProbability_le_invProbAt`: a realization of successful typed reductions by a
+  machine transfers the typed fair-bit success probability to the family's inversion game.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, proof of Theorem 137.2. This is generic probability and machine transport glue.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open Complexity TCSlib.Cryptography.Games
+
+/-- Suppose a machine's coins are a fair planting bit, a complete key table and forger coins,
+and every successful typed planted run yields the machine's correctly encoded preimage.
+Then the typed reduction's success averaged over the fair bit is at most the machine's
+inversion probability against the function family: `ProbComp.expect (ProbComp.sample Bool) (fun c =>
+redProbability (F.f n) adv (i, c)) ≤ F.invProbAt B n`, provided `RedSuccess (F.f n) adv y T r (i, c)
+→ ∃ x', B.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ F.f n x' = y` for all `y`, `T`,
+`c`, `r`. The preimage width is the family's actual input width, so no dependent width casts are
+needed. [PS10, proof of Theorem 137.2].
+
+**Proof sketch.** Read the machine inversion probability as the uniform probability that its
+output encodes a preimage. Product sampling separates the challenge preimage and machine
+coins. Reindex the latter by the given coin equivalence, and split the resulting product
+sample into its bit, table and forger coins using the published product-sampling law.
+Commute the independent bit and challenge samples on the typed side. All remaining samples
+have the same order, and the realization hypothesis implies the pointwise event inclusion.
+No query-cost assumption is needed for this transport: it is already encapsulated in the
+realization hypothesis. -/
+theorem fairBit_redProbability_le_invProbAt (F : FunFamily) (n : ℕ) (A B : NUPPT)
+    (i : Fin (F.inLen.eval n))
+    (adv : ((Fin (F.inLen.eval n) × Bool) → Fin (F.outLen.eval n) → Bool) →
+      A.Coins n → OracleComp
+        (bitSpec (fun _ : Fin 1 => F.inLen.eval n)
+          (fun _ => F.inLen.eval n * F.inLen.eval n))
+        (Fin (F.inLen.eval n + F.inLen.eval n * F.inLen.eval n) → Bool))
+    (e : ((Bool × Table (F.inLen.eval n)) × A.Coins n) ≃ B.Coins n)
+    (hreal : ∀ (y : Fin (F.outLen.eval n) → Bool) (T : Table (F.inLen.eval n))
+        (c : Bool) (r : A.Coins n),
+      RedSuccess (F.f n) adv y T r (i, c) →
+        ∃ x' : Fin (F.inLen.eval n) → Bool,
+          B.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ F.f n x' = y) :
+    ProbComp.expect (ProbComp.sample Bool)
+        (fun c => redProbability (F.f n) adv (i, c)) ≤ F.invProbAt B n := by
+  classical
+  rw [FunFamily.invProbAt_eq_uprob, ← Bridge.prob_sample_eq_uprob,
+    ProbComp.prob_eq_expect, ← Bridge.expect_sample_pair]
+  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
+  simp_rw [← ProbComp.expect_sample_equiv e]
+  simp only [redProbability_eq]
+  rw [ProbComp.expect_sample_comm]
+  simp only [← Bridge.expect_sample_pair, ProbComp.expect_bind, ProbComp.expect_pure]
+  apply ProbComp.expect_mono
+  intro x
+  apply ProbComp.expect_mono
+  intro c
+  apply ProbComp.expect_mono
+  intro T
+  apply ProbComp.expect_mono
+  intro r
+  by_cases hs : RedSuccess (F.f n) adv (F.f n x) T r (i, c)
+  · have hwin := hreal (F.f n x) T c r hs
+    rw [if_pos hs, if_pos hwin] <;> exact le_rfl
+  · rw [if_neg hs]
+    split_ifs <;> positivity
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Machine.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Machine.lean
new file mode 100644
index 000000000..6004d801f
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Machine.lean
@@ -0,0 +1,407 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.Efficiency
+import TCSlib.Cryptography.Asymptotic.OneWayLemmas
+import TCSlib.Cryptography.Asymptotic.ReductionSupport
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# String machine for Lamport's planted experiment
+
+## Main definitions
+
+* `advIn` replaces one fixed-width public-key block with a planted image.
+* `run` signs from the sampled tape and records whether the planted half was requested.
+* `out` extracts one signature block unless the run aborted.
+* `handler` packages these string functions for T1.
+
+The generator and signer are parameters, so this module does not import its consumer.
+The generator is expected to return `⟨pk, tape⟩`; the signer is expected to implement the
+deterministic Lamport string function. Their mathematical contracts belong to the consumer.
+
+## Main results
+
+All string functions are polynomial-time; every public definition has an equation reader.
+The functional contracts and machine realization are proved in `MachineSpec` and
+`Realization`; the owned Lamport module closes the security reduction.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, Protocol 137.1 and proof of Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportMachine
+
+open Complexity Turing TCSlib.Cryptography.Games
+
+/-- The context's unary parameter is its first component: `u v = pairFstD v`. -/
+def u (v : List Bool) : List Bool := pairFstD v
+/-- `u v = pairFstD v`. -/
+theorem u_eq (v : List Bool) : u v = pairFstD v := rfl
+/-- The unary parameter projection is polynomial-time: `PolyTimeComputable u`, for `u : List Bool →
+List Bool`. -/
+theorem u_poly : PolyTimeComputable u := polyTimeComputable_pairFstD
+
+/-- The context's challenge is the first component of its reduction input: `y v = pairFstD (pairFstD
+(pairSndD v))`. -/
+def y (v : List Bool) : List Bool := pairFstD (pairFstD (pairSndD v))
+/-- `y v = fst (fst (snd v))`. -/
+theorem y_eq (v : List Bool) : y v = pairFstD (pairFstD (pairSndD v)) := rfl
+/-- The challenge projection is polynomial-time: `PolyTimeComputable y`, for `y : List Bool → List
+Bool`. -/
+theorem y_poly : PolyTimeComputable y :=
+  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
+
+/-- The planted position is the second component of the reduction input, encoded in unary: `pos v =
+pairSndD (pairFstD (pairSndD v))`. -/
+def pos (v : List Bool) : List Bool := pairSndD (pairFstD (pairSndD v))
+/-- `pos v = snd (fst (snd v))`. -/
+theorem pos_eq (v : List Bool) : pos v = pairSndD (pairFstD (pairSndD v)) := rfl
+/-- The position projection is polynomial-time: `PolyTimeComputable pos`, for `pos : List Bool →
+List Bool`. -/
+theorem pos_poly : PolyTimeComputable pos :=
+  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
+
+/-- The handler seed is the second component of the context's second component: `seed v = pairSndD
+(pairSndD v)`. -/
+def seed (v : List Bool) : List Bool := pairSndD (pairSndD v)
+/-- `seed v = snd (snd v)`. -/
+theorem seed_eq (v : List Bool) : seed v = pairSndD (pairSndD v) := rfl
+/-- The seed projection is polynomial-time: `PolyTimeComputable seed`, for `seed : List Bool → List
+Bool`. -/
+theorem seed_poly : PolyTimeComputable seed :=
+  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
+
+/-- The planted half is the first seed bit, defaulting to false: `bit v = (seed v).headD false`. -/
+def bit (v : List Bool) : Bool := (seed v).headD false
+/-- `bit v = (seed v).headD false`. -/
+theorem bit_eq (v : List Bool) : bit v = (seed v).headD false := rfl
+/-- The planted bit is polynomial-time as a one-bit output: `PolyTimeComputable (fun v => [bit v])`,
+for `bit : List Bool → Bool`. -/
+theorem bit_poly : PolyTimeComputable (fun v => [bit v]) :=
+  polyTimeComputable_headD.comp seed_poly
+
+/-- The sampled preimage tape is the seed after its planted bit: `tape v = (seed v).drop 1`. -/
+def tape (v : List Bool) : List Bool := (seed v).drop 1
+/-- `tape v = (seed v).drop 1`. -/
+theorem tape_eq (v : List Bool) : tape v = (seed v).drop 1 := rfl
+/-- Removing the planted bit is polynomial-time: `PolyTimeComputable tape`, for `tape : List Bool →
+List Bool`. -/
+theorem tape_poly : PolyTimeComputable tape := polyTimeComputable_tail.comp seed_poly
+
+/-- A canonical context exposes its unary parameter: `u (seedIn n z ω) = List.replicate n true`. -/
+theorem u_seedIn (n : ℕ) (z ω : List Bool) :
+    u (seedIn n z ω) = List.replicate n true := by
+  rw [u_eq, seedIn_eq, pairFstD_pairEncode]
+
+/-- A canonical context with input `⟨challenge,index⟩` exposes its challenge: `y (seedIn n
+(pairEncode challenge index) ω) = challenge`. -/
+theorem y_seedIn (n : ℕ) (challenge index ω : List Bool) :
+    y (seedIn n (pairEncode challenge index) ω) = challenge := by
+  simp only [y_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- A canonical context with input `⟨challenge,index⟩` exposes its unary position: `pos (seedIn n
+(pairEncode challenge index) ω) = index`. -/
+theorem pos_seedIn (n : ℕ) (challenge index ω : List Bool) :
+    pos (seedIn n (pairEncode challenge index) ω) = index := by
+  simp only [pos_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]
+
+/-- A canonical context exposes its seed: `seed (seedIn n z ω) = ω`. -/
+theorem seed_seedIn (n : ℕ) (z ω : List Bool) : seed (seedIn n z ω) = ω := by
+  simp only [seed_eq, seedIn_eq, pairSndD_pairEncode]
+
+/-- A seed beginning with `c` supplies the planted half `c`: `bit (seedIn n z (c :: ρ)) = c`. -/
+theorem bit_seedIn (n : ℕ) (z ρ : List Bool) (c : Bool) :
+    bit (seedIn n z (c :: ρ)) = c := by
+  rw [bit_eq, seed_seedIn, List.headD_cons]
+
+/-- A seed beginning with `c` leaves exactly the sampled preimage tape after it: `tape (seedIn n z
+(c :: ρ)) = ρ`. -/
+theorem tape_seedIn (n : ℕ) (z ρ : List Bool) (c : Bool) :
+    tape (seedIn n z (c :: ρ)) = ρ := by
+  rw [tape_eq, seed_seedIn]
+  rfl
+
+/-- A fixed polynomial width, encoded as a unary word of length `W(|u|)`: `width W v =
+List.replicate (W.eval (u v).length) true`. -/
+def width (W : PolyExpr) (v : List Bool) : List Bool := List.replicate (W.eval (u v).length) true
+/-- `width W v = 1^(W(|u v|))`. -/
+theorem width_eq (W : PolyExpr) (v : List Bool) :
+    width W v = List.replicate (W.eval (u v).length) true := rfl
+/-- A polynomial width is polynomial-time in the context: `PolyTimeComputable (width W)`, for `width
+W : List Bool → List Bool`. -/
+theorem width_poly (W : PolyExpr) : PolyTimeComputable (width W) :=
+  (polyTimeComputable_unaryPoly W).comp u_poly
+
+/-- The unary offset to block `i` at width `W(n)` has `i · W(n)` symbols: `offset W v =
+List.replicate ((pos v).length * W.eval (u v).length) true`. -/
+def offset (W : PolyExpr) (v : List Bool) : List Bool :=
+  List.replicate ((pos v).length * W.eval (u v).length) true
+/-- `offset W v = 1^(|pos v| · W(|u v|))`. -/
+theorem offset_eq (W : PolyExpr) (v : List Bool) :
+    offset W v = List.replicate ((pos v).length * W.eval (u v).length) true := rfl
+/-- Block offsets are polynomial-time by the existing unary multiplication machine:
+`PolyTimeComputable (offset W)`, for `offset W : List Bool → List Bool`. -/
+theorem offset_poly (W : PolyExpr) : PolyTimeComputable (offset W) := by
+  refine (OneWay.polyTimeComputable_unaryMulPair.comp (pos_poly.pairEncode (width_poly W))).congr ?_
+  intro v
+  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
+    width_eq, offset_eq, List.length_replicate]
+
+/-- The first preimage at the selected position consists of `n` bits after offset `2ni`: `first v =
+((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length`. -/
+def first (v : List Bool) : List Bool :=
+  ((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length
+/-- `first` is the first `n`-bit half of the selected preimage pair: `first v = ((tape v).drop
+(offset (.mul (.const 2) .var) v).length).take (u v).length`. -/
+theorem first_eq (v : List Bool) : first v =
+    ((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length := rfl
+/-- Selecting the first preimage is polynomial-time: `PolyTimeComputable first`, for `first : List
+Bool → List Bool`. -/
+theorem first_poly : PolyTimeComputable first :=
+  TCSlib.Cryptography.takeLen_poly u_poly
+    (TCSlib.Cryptography.dropLen_poly (offset_poly _) tape_poly)
+
+/-- The second preimage is the next `n` bits after offset `2ni+n`: `second v = ((tape v).drop
+((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length`. -/
+def second (v : List Bool) : List Bool :=
+  ((tape v).drop ((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length
+/-- `second` is the second `n`-bit half of the selected preimage pair: `second v = ((tape v).drop
+((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length`. -/
+theorem second_eq (v : List Bool) : second v =
+    ((tape v).drop ((offset (.mul (.const 2) .var) v).length +
+      (u v).length)).take (u v).length := rfl
+/-- Selecting the second preimage is polynomial-time: `PolyTimeComputable second`, for `second :
+List Bool → List Bool`. -/
+theorem second_poly : PolyTimeComputable second := by
+  refine (TCSlib.Cryptography.takeLen_poly u_poly
+    (TCSlib.Cryptography.dropLen_poly ((offset_poly (.mul (.const 2) .var)).append u_poly)
+      tape_poly)).congr ?_
+  intro v
+  simp only [second_eq, List.length_append]
+
+/-- The ordinary generated public key on the sampled tape: `honestPk G v = pairFstD (G (NUPPT.layout
+(u v) [] [] (tape v)))`. -/
+def honestPk (G : List Bool → List Bool) (v : List Bool) : List Bool :=
+  pairFstD (G (NUPPT.layout (u v) [] [] (tape v)))
+/-- `honestPk G` runs `G` on the sampled preimage tape and reads its public-key component: `honestPk
+G v = pairFstD (G (NUPPT.layout (u v) [] [] (tape v)))`. -/
+theorem honestPk_eq (G : List Bool → List Bool) (v : List Bool) : honestPk G v =
+    pairFstD (G (NUPPT.layout (u v) [] [] (tape v))) := rfl
+/-- Generating the ordinary public key is polynomial-time when `G` is: `PolyTimeComputable G →
+PolyTimeComputable (honestPk G)`. -/
+theorem honestPk_poly {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
+    PolyTimeComputable (honestPk G) :=
+  polyTimeComputable_pairFstD.comp (hG.comp (NUPPT.polyTimeComputable_layout u_poly
+    (polyTimeComputable_const []) (polyTimeComputable_const []) tape_poly))
+
+/-- The replacement public-key block is `⟨⟨y,E(x¹)⟩,[]⟩` for bit false and
+`⟨⟨E(x⁰),y⟩,[]⟩` for bit true: `replacement E v = pairEncode (pairEncode (if bit v then E
+(pairEncode (u v) (first v)) else y v) (if bit v then y v else E (pairEncode (u v) (second v))))
+[]`. -/
+def replacement (E : List Bool → List Bool) (v : List Bool) : List Bool :=
+  pairEncode (pairEncode
+    (if bit v then E (pairEncode (u v) (first v)) else y v)
+    (if bit v then y v else E (pairEncode (u v) (second v)))) []
+/-- The replacement block plants the challenge in the selected half: `replacement E v = pairEncode
+(pairEncode (if bit v then E (pairEncode (u v) (first v)) else y v) (if bit v then y v else E
+(pairEncode (u v) (second v)))) []`. -/
+theorem replacement_eq (E : List Bool → List Bool) (v : List Bool) : replacement E v =
+    pairEncode (pairEncode
+      (if bit v then E (pairEncode (u v) (first v)) else y v)
+      (if bit v then y v else E (pairEncode (u v) (second v)))) [] := rfl
+/-- Building the replacement public-key block is polynomial-time when `E` is: `PolyTimeComputable E
+→ PolyTimeComputable (replacement E)`. -/
+theorem replacement_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
+    PolyTimeComputable (replacement E) :=
+  ((polyTimeComputable_ite bit_poly (hE.comp (u_poly.pairEncode first_poly)) y_poly).pairEncode
+    (polyTimeComputable_ite bit_poly y_poly (hE.comp (u_poly.pairEncode second_poly)))).pairEncode
+      (polyTimeComputable_const [])
+
+/-- The adversary's public key replaces one width-`W(n)` block of the ordinary generated key
+with the planted block: `advIn W E G v = (honestPk G v).take (offset W v).length ++ replacement E v
+++ (honestPk G v).drop ((offset W v).length + (width W v).length)`. [PS10, proof of Theorem 137.2].
+-/
+def advIn (W : PolyExpr) (E G : List Bool → List Bool) (v : List Bool) : List Bool :=
+  (honestPk G v).take (offset W v).length ++ replacement E v ++
+    (honestPk G v).drop ((offset W v).length + (width W v).length)
+/-- `advIn` keeps the prefix and suffix around the planted block: `advIn W E G v = (honestPk G
+v).take (offset W v).length ++ replacement E v ++ (honestPk G v).drop ((offset W v).length + (width
+W v).length)`. -/
+theorem advIn_eq (W : PolyExpr) (E G : List Bool → List Bool) (v : List Bool) :
+    advIn W E G v = (honestPk G v).take (offset W v).length ++ replacement E v ++
+      (honestPk G v).drop ((offset W v).length + (width W v).length) := rfl
+/-- Planting one public-key block is polynomial-time: `PolyTimeComputable E → PolyTimeComputable G →
+PolyTimeComputable (advIn W E G)`.
+
+**Proof sketch.** Compute both unary offsets by the existing multiplication primitive,
+take the prefix and drop the suffix, then concatenate the replacement block between them. -/
+theorem advIn_poly (W : PolyExpr) {E G : List Bool → List Bool}
+    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) :
+    PolyTimeComputable (advIn W E G) := by
+  refine (((TCSlib.Cryptography.takeLen_poly (offset_poly W) (honestPk_poly hG)).append
+      (replacement_poly hE)).append
+    (TCSlib.Cryptography.dropLen_poly ((offset_poly W).append (width_poly W))
+      (honestPk_poly hG))).congr ?_
+  intro v
+  simp only [advIn_eq, List.length_append]
+
+/-- The context of a query or finalization input is its first component: `context w = pairFstD w`.
+-/
+def context (w : List Bool) : List Bool := pairFstD w
+/-- `context w = fst w`. -/
+theorem context_eq (w : List Bool) : context w = pairFstD w := rfl
+/-- The context of an activation is polynomial-time: `PolyTimeComputable context`, for `context :
+List Bool → List Bool`. -/
+theorem context_poly : PolyTimeComputable context := polyTimeComputable_pairFstD
+
+/-- The current abort state is the first component of the second input component: `state w =
+pairFstD (pairSndD w)`. -/
+def state (w : List Bool) : List Bool := pairFstD (pairSndD w)
+/-- `state w = fst (snd w)`. -/
+theorem state_eq (w : List Bool) : state w = pairFstD (pairSndD w) := rfl
+/-- The current state projection is polynomial-time: `PolyTimeComputable state`, for `state : List
+Bool → List Bool`. -/
+theorem state_poly : PolyTimeComputable state :=
+  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
+
+/-- The query message is the second component after the state and oracle index: `message w =
+pairSndD (pairSndD (pairSndD w))`. -/
+def message (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
+/-- `message w = snd (snd (snd w))`. -/
+theorem message_eq (w : List Bool) : message w = pairSndD (pairSndD (pairSndD w)) := rfl
+/-- The query message projection is polynomial-time: `PolyTimeComputable message`, for `message :
+List Bool → List Bool`. -/
+theorem message_poly : PolyTimeComputable message :=
+  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
+
+/-- The context of a canonical handler query is its original seed context: `context
+(PolyHandler.input n z ω s i x) = seedIn n z ω`. -/
+theorem context_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
+    context (PolyHandler.input n z ω s i x) = seedIn n z ω := by
+  simp only [context_eq, PolyHandler.input_eq, seedIn_eq, pairFstD_pairEncode]
+
+/-- A canonical handler query exposes its state: `state (PolyHandler.input n z ω s i x) = s`. -/
+theorem state_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
+    state (PolyHandler.input n z ω s i x) = s := by
+  simp only [state_eq, PolyHandler.input_eq, pairSndD_pairEncode, pairFstD_pairEncode]
+
+/-- A canonical handler query exposes its message: `message (PolyHandler.input n z ω s i x) = x`. -/
+theorem message_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
+    message (PolyHandler.input n z ω s i x) = x := by
+  simp only [message_eq, PolyHandler.input_eq, pairSndD_pairEncode]
+
+/-- A query is blocked precisely when its selected message bit is the planted bit: `blocked w =
+decide (((message w).drop (pos (context w)).length).headD false = bit (context w))`. -/
+def blocked (w : List Bool) : Bool :=
+  decide (((message w).drop (pos (context w)).length).headD false = bit (context w))
+/-- `blocked` tests equality of the query bit at the planted position and the planted half: `blocked
+w = decide (((message w).drop (pos (context w)).length).headD false = bit (context w))`. -/
+theorem blocked_eq (w : List Bool) : blocked w =
+    decide (((message w).drop (pos (context w)).length).headD false = bit (context w)) := rfl
+/-- Testing whether a query requests the planted half is polynomial-time: `PolyTimeComputable (fun w
+=> [blocked w])`, for `blocked : List Bool → Bool`. -/
+theorem blocked_poly : PolyTimeComputable (fun w => [blocked w]) := by
+  have hq := polyTimeComputable_headD.comp
+    (TCSlib.Cryptography.dropLen_poly (pos_poly.comp context_poly) message_poly)
+  have hb := bit_poly.comp context_poly
+  refine (polyTimeComputable_pairEq.comp (hq.pairEncode hb)).congr ?_
+  intro w
+  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, blocked_eq,
+    List.cons.injEq, and_true]
+
+/-- A handler query returns the ordinary sampled-tape signature and sets the persistent
+abort bit if the planted half was requested: `run S w = pairEncode (S (NUPPT.layout (u (context w))
+(pairEncode (tape (context w)) (message w)) [] [])) [(state w).headD false || blocked w]`.
+Continuing after an abort is harmless because finalization returns no candidate. [PS10, proof of
+Theorem 137.2]. -/
+def run (S : List Bool → List Bool) (w : List Bool) : List Bool :=
+  pairEncode
+    (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
+    [(state w).headD false || blocked w]
+/-- The query answer uses the sampled tape and records the disjunction of old and new aborts: `run S
+w = pairEncode (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
+[(state w).headD false || blocked w]`. -/
+theorem run_eq (S : List Bool → List Bool) (w : List Bool) : run S w =
+    pairEncode
+      (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
+      [(state w).headD false || blocked w] := rfl
+/-- Query answering and the abort-state update are polynomial-time when `S` is: `PolyTimeComputable
+S → PolyTimeComputable (run S)`. -/
+theorem run_poly {S : List Bool → List Bool} (hS : PolyTimeComputable S) :
+    PolyTimeComputable (run S) :=
+  (hS.comp (NUPPT.polyTimeComputable_layout (u_poly.comp context_poly)
+    ((tape_poly.comp context_poly).pairEncode message_poly)
+    (polyTimeComputable_const []) (polyTimeComputable_const []))).pairEncode
+      (polyTimeComputable_or (polyTimeComputable_headD.comp state_poly) blocked_poly)
+
+/-- The final output is empty after an abort; otherwise it is block `i` of the forged signature
+(the adversary's word begins with the `n` message bits): `out w = if (state w).headD false then []
+else (((pairSndD (pairSndD w)).drop (u (context w)).length).drop (offset .var (context
+w)).length).take (u (context w)).length`. [PS10, proof of Theorem 137.2]. -/
+def out (w : List Bool) : List Bool :=
+  if (state w).headD false then [] else
+    (((pairSndD (pairSndD w)).drop (u (context w)).length).drop
+      (offset .var (context w)).length).take (u (context w)).length
+/-- Finalization suppresses aborted runs and extracts the selected signature block otherwise: `out
+w = if (state w).headD false then [] else (((pairSndD (pairSndD w)).drop (u (context
+w)).length).drop (offset .var (context w)).length).take (u (context w)).length`. -/
+theorem out_eq (w : List Bool) : out w =
+    if (state w).headD false then [] else
+      (((pairSndD (pairSndD w)).drop (u (context w)).length).drop
+        (offset .var (context w)).length).take (u (context w)).length := rfl
+/-- Finalization is polynomial-time by three variable-prefix operations and one branch:
+`PolyTimeComputable out`, for `out : List Bool → List Bool`. -/
+theorem out_poly : PolyTimeComputable out :=
+  polyTimeComputable_ite (polyTimeComputable_headD.comp state_poly) (polyTimeComputable_const [])
+    (TCSlib.Cryptography.takeLen_poly (u_poly.comp context_poly)
+      (TCSlib.Cryptography.dropLen_poly ((offset_poly .var).comp context_poly)
+        (TCSlib.Cryptography.dropLen_poly (u_poly.comp context_poly)
+          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))))
+
+/-- The planted Lamport handler has one abort bit and `1+2n²` seed bits, with the fair planted
+half first: its fields are `stateLen = .const 1`, `seedLen = .add (.const 1) (.mul (.mul (.const 2)
+.var) .var)`, `init = fun _ _ => false`, `run = run S`, `advIn = advIn W E G` and `out = out`. It
+signs at most one query and extracts one candidate preimage. -/
+def handler (W : PolyExpr) (E G S : List Bool → List Bool)
+    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S) :
+    PolyHandler 1 (fun _ => .var) (fun _ => .mul .var .var) where
+  stateLen := .const 1
+  seedLen := .add (.const 1) (.mul (.mul (.const 2) .var) .var)
+  init := fun _ _ => false
+  run := run S
+  poly := run_poly hS
+  advIn := advIn W E G
+  advIn_poly := advIn_poly W hE hG
+  out := out
+  out_poly := out_poly
+
+variable (W : PolyExpr) (E G S : List Bool → List Bool)
+  (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S)
+
+/-- The handler state-length polynomial is the constant one: `(handler W E G S hE hG hS).stateLen =
+.const 1`. -/
+theorem handler_stateLen : (handler W E G S hE hG hS).stateLen = .const 1 := rfl
+/-- The handler seed-length polynomial is `1+2n²`: `(handler W E G S hE hG hS).seedLen = .add
+(.const 1) (.mul (.mul (.const 2) .var) .var)`. -/
+theorem handler_seedLen : (handler W E G S hE hG hS).seedLen =
+    .add (.const 1) (.mul (.mul (.const 2) .var) .var) := rfl
+/-- Every bit of the initial abort state is false: `(handler W E G S hE hG hS).init n i = false`. -/
+theorem handler_init (n : ℕ) (i : Fin ((handler W E G S hE hG hS).stateLen.eval n)) :
+    (handler W E G S hE hG hS).init n i = false := rfl
+/-- The handler's query function is `run S`: `(handler W E G S hE hG hS).run = run S`. -/
+theorem handler_run : (handler W E G S hE hG hS).run = run S := rfl
+/-- The handler's adversary-input function is the planted public-key function: `(handler W E G S hE
+hG hS).advIn = advIn W E G`. -/
+theorem handler_advIn : (handler W E G S hE hG hS).advIn = advIn W E G := rfl
+/-- The handler's output function is the signature-block extractor: `(handler W E G S hE hG
+hS).out = out`. -/
+theorem handler_out : (handler W E G S hE hG hS).out = out := rfl
+
+end TCSlib.Cryptography.Authentication.LamportMachine
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean
new file mode 100644
index 000000000..60fb7d4ac
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean
@@ -0,0 +1,268 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
+import TCSlib.Cryptography.Authentication.Encoding
+import TCSlib.Cryptography.Foundations.BitLists
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Functional contracts of the planted Lamport machine
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `advIn_context` identifies the machine's public key with the typed planted public table.
+* `run_input` identifies its query answer and abort flag.
+* `out_nonabort` identifies its final signature-block extraction.
+
+The exact finite-tuple `coinBlock` reader is passed as a parameter, so this helper neither
+imports the owned consumer nor copies that consumer's public lemma.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, proof of Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open Complexity Turing TCSlib.Cryptography.Games
+open TCSlib.Cryptography
+
+/-- The serialized public table is the concatenation of its self-delimiting image-pair
+blocks: `publicWord Y = (List.ofFn fun i : Fin n => pairEncode (pairEncode (List.ofFn (Y (i,
+false))) (List.ofFn (Y (i, true)))) []).flatten`. This reads the public tuple encoding through
+`encodeList_eq_flatMap`. -/
+theorem publicWord_flatten {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) :
+    publicWord Y = (List.ofFn fun i : Fin n =>
+      pairEncode (pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) []).flatten := by
+  rw [publicWord_eq, encodeList_eq_flatMap, List.flatMap_def, List.map_ofFn]
+  rw [Function.comp_def]
+
+section KeyWindows
+
+variable (hcoin : ∀ {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
+  (i : Fin q), coinBlock B i (List.ofFn g).flatten = g i)
+
+include hcoin in
+/-- Reading the first `n`-bit half of the selected sampled row returns `T(i,false)`:
+`LamportMachine.first (seedIn n (pairEncode challenge (List.replicate i.val true)) (c :: secretWord
+T)) = List.ofFn (T (i, false))`.
+
+**Proof sketch.** On this context `first` takes `n` bits of `secretWord T` after the offset `2n·i`
+(`first_eq`, `tape_seedIn`, `offset_eq`, `pos_seedIn`, `u_seedIn`). By `hcoin`, the `2n` bits there
+are row `i`, that is `T (i, false) ‖ T (i, true)`, and the first `n` of them are `T (i, false)`. -/
+theorem first_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
+    LamportMachine.first (seedIn n (pairEncode challenge (List.replicate i.val true))
+      (c :: secretWord T)) = List.ofFn (T (i, false)) := by
+  rw [LamportMachine.first_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
+    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
+  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+  have hrow := hcoin (B := 2 * n)
+    (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
+    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
+  rw [coinBlock_eq, ← secretWord_eq] at hrow
+  have h := congrArg (fun w : List Bool => w.take n) hrow
+  dsimp only at h
+  rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' List.length_ofFn] at h
+  exact h
+
+include hcoin in
+/-- Reading the second `n`-bit half of the selected sampled row returns `T(i,true)`:
+`LamportMachine.second (seedIn n (pairEncode challenge (List.replicate i.val true)) (c :: secretWord
+T)) = List.ofFn (T (i, true))`.
+
+**Proof sketch.** On this context `second` takes `n` bits of `secretWord T` after the offset `2n·i +
+n` (`second_eq`, `tape_seedIn`, `offset_eq`, `pos_seedIn`, `u_seedIn`). By `hcoin`, the `2n` bits
+after offset `2n·i` are row `i`, that is `T (i, false) ‖ T (i, true)`, and dropping its first `n`
+bits leaves `T (i, true)`. -/
+theorem second_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
+    LamportMachine.second (seedIn n (pairEncode challenge (List.replicate i.val true))
+      (c :: secretWord T)) = List.ofFn (T (i, true)) := by
+  rw [LamportMachine.second_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
+    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
+  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
+  have hrow := hcoin (B := 2 * n)
+    (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
+    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
+  rw [coinBlock_eq, ← secretWord_eq] at hrow
+  have h := congrArg (fun w : List Bool => w.drop n) hrow
+  dsimp only at h
+  rw [List.drop_take, show 2 * n - n = n by omega, List.drop_drop,
+    List.drop_left' List.length_ofFn] at h
+  exact h
+
+include hcoin in
+/-- The machine's replacement block serializes the planted row, using the evaluator's
+published agreement on `n`-bit inputs: `LamportMachine.replacement E (seedIn n (pairEncode
+(List.ofFn challenge) (List.replicate i.val true)) (c :: secretWord T)) = pairEncode (pairEncode
+(List.ofFn (plantedPublic g T i c challenge (i, false))) (List.ofFn (plantedPublic g T i c challenge
+(i, true)))) []`. -/
+theorem replacement_context {n ℓ : ℕ} (g : (Fin n → Bool) → Fin ℓ → Bool)
+    (E : List Bool → List Bool)
+    (hE : ∀ x : Fin n → Bool,
+      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
+    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
+    LamportMachine.replacement E
+        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
+          (c :: secretWord T)) =
+      pairEncode (pairEncode
+        (List.ofFn (plantedPublic g T i c challenge (i, false)))
+        (List.ofFn (plantedPublic g T i c challenge (i, true)))) [] := by
+  rw [LamportMachine.replacement_eq, LamportMachine.bit_seedIn, LamportMachine.u_seedIn,
+    LamportMachine.y_seedIn, first_context hcoin, second_context hcoin, hE, hE]
+  cases c <;> simp [plantedPublic_eq]
+
+include hcoin in
+/-- On a canonical seed context, the machine's public-key input is exactly the serialized
+typed planted table: if `W.eval n = 6 * ℓ + 6`, then `LamportMachine.advIn W E G (seedIn n
+(pairEncode (List.ofFn challenge) (List.replicate i.val true)) (c :: secretWord T)) = publicWord
+(plantedPublic g T i c challenge)`. The only generator/evaluator facts required are their stated
+functional contracts; the owned Lamport module supplies them.
+
+**Proof sketch.** The ordinary generated key is a concatenation of width `6ℓ+6` blocks.
+The machine takes the blocks before `i`, inserts the planted block, and drops through block
+`i`. The general fixed-width replacement lemma identifies this with updating row `i` before
+serialization. Every other row retains both images. -/
+theorem advIn_context {n ℓ : ℕ} (W : PolyExpr)
+    (hW : W.eval n = 6 * ℓ + 6) (g : (Fin n → Bool) → Fin ℓ → Bool)
+    (E G : List Bool → List Bool)
+    (hE : ∀ x : Fin n → Bool,
+      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
+    (hG : ∀ T : Table n,
+      G (NUPPT.layout (List.replicate n true) [] [] (secretWord T)) =
+        pairEncode (publicWord (tablePublic g T)) (secretWord T))
+    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
+    LamportMachine.advIn W E G
+        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
+          (c :: secretWord T)) =
+      publicWord (plantedPublic g T i c challenge) := by
+  have hpk : LamportMachine.honestPk G
+      (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
+        (c :: secretWord T)) = publicWord (tablePublic g T) := by
+    rw [LamportMachine.honestPk_eq, LamportMachine.u_seedIn, LamportMachine.tape_seedIn,
+      hG, pairFstD_pairEncode]
+  let rows : Fin n → List Bool := fun j => pairEncode (pairEncode
+    (List.ofFn (g (T (j, false)))) (List.ofFn (g (T (j, true))))) []
+  let plantedRows : Fin n → List Bool := fun j => pairEncode (pairEncode
+    (List.ofFn (plantedPublic g T i c challenge (j, false)))
+    (List.ofFn (plantedPublic g T i c challenge (j, true)))) []
+  have hrows (j : Fin n) : (rows j).length = W.eval n := by
+    simp only [rows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
+    ring
+  have hnew : (plantedRows i).length = W.eval n := by
+    simp only [plantedRows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
+    ring
+  have hupdate : Function.update rows i (plantedRows i) = plantedRows := by
+    funext j
+    by_cases hj : j = i
+    · subst j
+      rw [Function.update_self]
+    · have hp0 : (j, false) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
+      have hp1 : (j, true) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
+      rw [Function.update_of_ne hj]
+      simp only [rows, plantedRows, plantedPublic_eq, if_neg hp0, if_neg hp1]
+  have hnormal : publicWord (tablePublic g T) = (List.ofFn rows).flatten := by
+    rw [publicWord_flatten]
+    simp only [tablePublic_eq, rows]
+  have hplant : publicWord (plantedPublic g T i c challenge) =
+      (List.ofFn plantedRows).flatten := by
+    rw [publicWord_flatten]
+  simp only [LamportMachine.advIn_eq, hpk, replacement_context hcoin g E hE,
+    LamportMachine.offset_eq, LamportMachine.width_eq, LamportMachine.pos_seedIn,
+    LamportMachine.u_seedIn, List.length_replicate]
+  simp only [hnormal, hplant]
+  change (List.ofFn rows).flatten.take (i.val * W.eval n) ++ plantedRows i ++
+    (List.ofFn rows).flatten.drop (i.val * W.eval n + W.eval n) =
+      (List.ofFn plantedRows).flatten
+  rw [show i.val * W.eval n + W.eval n = (i.val + 1) * W.eval n by ring,
+    flatten_ofFn_update rows hrows i (plantedRows i) hnew, hupdate]
+
+end KeyWindows
+
+/-- The selected bit of a serialized message is its typed bit at that position: `((List.ofFn m).drop
+i.val).headD false = m i`. -/
+theorem headD_drop_ofFn {n : ℕ} (m : Fin n → Bool) (i : Fin n) :
+    ((List.ofFn m).drop i.val).headD false = m i := by
+  simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
+    dif_pos i.isLt, Option.getD_some]
+
+/-- On canonical input, the machine returns the typed signature and records the old abort
+bit or equality `m_i=c`. This statement covers both safe and aborting calls. -/
+theorem run_input {n : ℕ} (S : List Bool → List Bool)
+    (hS : ∀ (T : Table n) (m : Fin n → Bool),
+      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
+        List.ofFn (tableSignature T m))
+    (T : Table n) (i : Fin n) (c bad : Bool) (challenge : List Bool)
+    (j : Fin 1) (m : Fin n → Bool) :
+    LamportMachine.run S (PolyHandler.input n
+        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
+        [bad] j (List.ofFn m)) =
+      pairEncode (List.ofFn (tableSignature T m)) [bad || decide (m i = c)] := by
+  have hb : LamportMachine.blocked (PolyHandler.input n
+      (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
+      [bad] j (List.ofFn m)) = decide (m i = c) := by
+    rw [LamportMachine.blocked_eq, LamportMachine.context_input, LamportMachine.message_input,
+      LamportMachine.pos_seedIn, LamportMachine.bit_seedIn, List.length_replicate,
+      headD_drop_ofFn]
+  simp only [LamportMachine.run_eq, LamportMachine.context_input, LamportMachine.state_input,
+    LamportMachine.message_input, LamportMachine.u_seedIn, LamportMachine.tape_seedIn, hS,
+    List.headD_cons, hb]
+
+/-- A safe query from non-abort state returns the typed signature and a false abort bit: if `m i ≠
+c`, then `LamportMachine.run S (PolyHandler.input n (pairEncode challenge (List.replicate i.val
+true)) (c :: secretWord T) [false] j (List.ofFn m)) = pairEncode (List.ofFn (tableSignature T m))
+[false]`. -/
+theorem run_safe {n : ℕ} (S : List Bool → List Bool)
+    (hS : ∀ (T : Table n) (m : Fin n → Bool),
+      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
+        List.ofFn (tableSignature T m))
+    (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool)
+    (j : Fin 1) (m : Fin n → Bool) (hm : m i ≠ c) :
+    LamportMachine.run S (PolyHandler.input n
+        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
+        [false] j (List.ofFn m)) =
+      pairEncode (List.ofFn (tableSignature T m)) [false] := by
+  rw [run_input S hS]
+  simp only [hm, decide_false, Bool.false_or]
+
+/-- Finalization in non-abort state returns exactly the selected block of the typed forged
+signature, after its first `n` message bits: if `LamportMachine.pos (seedIn n z ρ) = List.replicate
+i.val true`, then `LamportMachine.out (pairEncode (seedIn n z ρ) (pairEncode [false] (List.ofFn
+a))) = List.ofFn (signatureBlock (splitBits a).2 i)`.
+
+**Proof sketch.** With state `[false]`, `out` drops the `n` message bits, then `n·i` more bits, and
+takes `n` (`out_eq`, `u_seedIn`, `offset_eq`, `hz`). After the message the word is `List.ofFn
+(splitBits a).2` (`splitBits_snd`, `ofFn_natAdd_eq_drop`), and its block `i` is the signature block
+(`FunFamily.ofFn_blocks`, `signatureBlock_eq`). -/
+theorem out_nonabort {n : ℕ} (i : Fin n) (z ρ : List Bool)
+    (a : Fin (n + n * n) → Bool)
+    (hz : LamportMachine.pos (seedIn n z ρ) = List.replicate i.val true) :
+    LamportMachine.out (pairEncode (seedIn n z ρ) (pairEncode [false] (List.ofFn a))) =
+      List.ofFn (signatureBlock (splitBits a).2 i) := by
+  rw [LamportMachine.out_eq, LamportMachine.state_eq, LamportMachine.context_eq]
+  simp only [LamportMachine.context_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
+    Bool.false_eq_true,
+    if_false, LamportMachine.u_seedIn, LamportMachine.offset_eq, hz,
+    List.length_replicate, PolyExpr.eval_var]
+  have hs : List.ofFn (splitBits a).2 = (List.ofFn a).drop n := by
+    have hsplit : (splitBits a).2 = fun j => a (Fin.natAdd n j) := by
+      funext j
+      exact splitBits_snd a j
+    rw [hsplit, ofFn_natAdd_eq_drop]
+  rw [← hs, ← FunFamily.ofFn_blocks n n (splitBits a).2 i]
+  apply congrArg List.ofFn
+  funext k
+  rw [FunFamily.blocks_apply, signatureBlock_eq]
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Nonabort.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Nonabort.lean
new file mode 100644
index 000000000..10a107e12
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Nonabort.lean
@@ -0,0 +1,65 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Reading nonabort as query safety
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `safe_of_nonabort`: a nonaborting one-query planted transcript has a safe query.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
+  January 2010, proof of Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open TCSlib.Cryptography.Games
+
+/-- A planted run with at most one query ending with a false abort bit queried no message
+that reveals the planted cell [PS10, proof of Theorem 137.2]: if `tree.CostBoundedBy (fun _ => 1) 1`
+and `simulate (abortingImpl T i c) tree false = .pure (a', false)`, then `Safe tree i c`.
+
+**Proof sketch.** An immediate return has no query. A query leaves cost zero, so its
+continuation is a return; the final abort flag is exactly equality of its selected bit with
+the planted bit. A false flag therefore says that the query was safe. -/
+theorem safe_of_nonabort {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (a' : α)
+    (hsim : simulate (abortingImpl T i c) tree false = .pure (a', false)) :
+    Safe tree i c := by
+  cases tree with
+  | pure a =>
+    apply (safe_iff _ i c).2
+    intro m hm
+    rw [firstQuery_pure] at hm
+    cases hm
+  | query j m k =>
+    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
+    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (abortingAnswer T i c m))
+      (by simpa only [Nat.sub_self] using (hk.2 (abortingAnswer T i c m)))
+    rw [simulate_query, abortingImpl_apply, OracleComp.pure_bind, ha, simulate_pure] at hsim
+    have hp : (a, false || decide (m i = c)) = (a', false) := OracleComp.pure.inj hsim
+    have hb : decide (m i = c) = false := by
+      simpa only [Bool.false_or] using congrArg Prod.snd hp
+    have hm : m i ≠ c := of_decide_eq_false hb
+    apply (safe_iff _ i c).2
+    intro m' hm'
+    rw [firstQuery_query, Option.some.injEq] at hm'
+    rw [← hm']
+    exact hm
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Planted.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Planted.lean
new file mode 100644
index 000000000..a4af70e9d
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Planted.lean
@@ -0,0 +1,513 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Games.BitCodec
+import TCSlib.Cryptography.Games.Bridges.QueryTree
+import TCSlib.Cryptography.Asymptotic.BlockEncryptor
+import TCSlib.Cryptography.Asymptotic.OneWay
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The fixed-position Lamport planting coupling
+
+## Main definitions
+
+* `plantTable` replaces one preimage in a typed Lamport key table.
+* `tableSignature` selects one preimage per message bit.
+* `plantedPublic` replaces one image without reading its preimage.
+* `firstQuery` and `Safe` record whether the sole query avoids the planted cell.
+* `abortingImpl` answers safe queries and remembers an unsafe query.
+
+## Main results
+
+* `planted_coupling`: on the safe branch of a computation with at most one query,
+  the planted implementation returns the honest output and never aborts.
+* `extract_planted`: an accepting signature with the planted message bit inverts
+  the planted image.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
+  January 2010, Protocol 137.1 and Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open TCSlib.Cryptography TCSlib.Cryptography.Games
+open Complexity Turing
+
+/-- A table has an `n`-bit preimage at each coordinate `(i,c)`: `Table n = ((Fin n × Bool) → Fin n →
+Bool)`. -/
+abbrev Table (n : ℕ) := (Fin n × Bool) → Fin n → Bool
+
+/-- The type of tables is the function type `(Fin n × Bool) → Fin n → Bool`. -/
+theorem Table_eq (n : ℕ) : Table n = ((Fin n × Bool) → Fin n → Bool) := rfl
+
+/-- Serialize a public table as the tuple of its pairs of images: `publicWord Y =
+PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n => pairEncode (List.ofFn (Y (i, false)))
+(List.ofFn (Y (i, true))))`. -/
+def publicWord {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) : List Bool :=
+  PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
+    pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true))))
+
+/-- The public word is the tuple of the encoded pairs `⟨Y(i,0),Y(i,1)⟩`: `publicWord Y =
+PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n => pairEncode (List.ofFn (Y (i, false)))
+(List.ofFn (Y (i, true))))`. -/
+theorem publicWord_eq {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) :
+    publicWord Y = PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
+      pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) := rfl
+
+/-- Serialize a preimage table in row order, with its false and true cells adjacent: `secretWord T =
+(List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten`. -/
+def secretWord {n : ℕ} (T : Table n) : List Bool :=
+  (List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten
+
+/-- The secret word concatenates `T(i,0) ‖ T(i,1)` for consecutive rows `i`: `secretWord T =
+(List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten`. -/
+theorem secretWord_eq {n : ℕ} (T : Table n) :
+    secretWord T =
+      (List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten :=
+  rfl
+
+/-- A serialized table contains `n` rows of `2n` bits, hence `2n²` bits: `(secretWord T).length =
+2 * n * n`. -/
+theorem length_secretWord {n : ℕ} (T : Table n) : (secretWord T).length = 2 * n * n := by
+  have hrow : (List.length ∘ fun i : Fin n =>
+      List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))) = fun _ => n + n := by
+    funext i
+    simp only [Function.comp_apply, List.length_append, List.length_ofFn]
+  rw [secretWord_eq, List.length_flatten, List.map_ofFn, hrow, List.ofFn_const,
+    List.sum_replicate]
+  simp only [nsmul_eq_mul, Nat.cast_id]
+  ring
+
+/-- Replace preimage `(i,c)` by `x`, leaving every other cell unchanged: `plantTable T i c x p = if
+p = (i, c) then x else T p`. -/
+def plantTable {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
+    (p : Fin n × Bool) : Fin n → Bool :=
+  if p = (i, c) then x else T p
+
+/-- Planting returns `x` at the selected cell and `T p` elsewhere: `plantTable T i c x p = if p =
+(i, c) then x else T p`. -/
+theorem plantTable_eq {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
+    (p : Fin n × Bool) :
+    plantTable T i c x p = if p = (i, c) then x else T p := rfl
+
+/-- The planted cell contains `x`: `plantTable T i c x (i, c) = x`. -/
+theorem plantTable_at {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool) :
+    plantTable T i c x (i, c) = x := by
+  simp only [plantTable, if_true]
+
+/-- A cell different from `(i,c)` retains its original preimage: if `p ≠ (i, c)`, then `plantTable T
+i c x p = T p`. -/
+theorem plantTable_ne {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
+    {p : Fin n × Bool} (hp : p ≠ (i, c)) : plantTable T i c x p = T p := by
+  rw [plantTable_eq, if_neg hp]
+
+/-- Planting a table is the ordinary update of its selected coordinate: `plantTable T i c x =
+Function.update T (i, c) x`. -/
+theorem plantTable_update {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
+    (x : Fin n → Bool) : plantTable T i c x = Function.update T (i, c) x := by
+  funext p
+  rw [plantTable_eq, Function.update_apply]
+
+/-- The signature is the flattened table of preimages selected by the message bits: `tableSignature
+T m j = T (k.1, m k.1) k.2` with `k = finProdFinEquiv.symm j`. -/
+def tableSignature {n : ℕ} (T : Table n) (m : Fin n → Bool) : Fin (n * n) → Bool :=
+  fun j => T ((finProdFinEquiv.symm j).1, m (finProdFinEquiv.symm j).1)
+    (finProdFinEquiv.symm j).2
+
+/-- At the flattened index for `(i,k)`, the signature reads bit `k` of `T(i,m i)`: `tableSignature T
+m (finProdFinEquiv (i, k)) = T (i, m i) k`. -/
+theorem tableSignature_apply {n : ℕ} (T : Table n) (m : Fin n → Bool)
+    (i k : Fin n) : tableSignature T m (finProdFinEquiv (i, k)) = T (i, m i) k := by
+  simp only [tableSignature, Equiv.symm_apply_apply]
+
+/-- The word of a selected signature concatenates the selected preimage words: `List.ofFn
+(tableSignature T m) = (List.ofFn fun i : Fin n => List.ofFn (T (i, m i))).flatten`. -/
+theorem ofFn_tableSignature {n : ℕ} (T : Table n) (m : Fin n → Bool) :
+    List.ofFn (tableSignature T m) =
+      (List.ofFn fun i : Fin n => List.ofFn (T (i, m i))).flatten := by
+  have hblocks : FunFamily.blocks n n (tableSignature T m) = fun i => T (i, m i) := by
+    funext i k
+    rw [FunFamily.blocks_apply, tableSignature_apply]
+  have h := FunFamily.ofFn_blocks_symm n n (FunFamily.blocks n n (tableSignature T m))
+  rw [Equiv.symm_apply_apply, hblocks] at h
+  exact h
+
+/-- A message avoiding the planted cell has exactly its original signature: if `m i ≠ c`, then
+`tableSignature (plantTable T i c x) m = tableSignature T m`.
+
+**Proof sketch.** Entry `j` of either signature reads the cell `(k.1, m k.1)` with `k =
+finProdFinEquiv.symm j`. That cell is not `(i, c)`, since `k.1 = i` would give `m i = c`, so
+`plantTable_ne` returns its original preimage. -/
+theorem tableSignature_plant_of_safe {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
+    (x : Fin n → Bool) (m : Fin n → Bool) (hm : m i ≠ c) :
+    tableSignature (plantTable T i c x) m = tableSignature T m := by
+  funext j
+  simp only [tableSignature]
+  have hp : ((finProdFinEquiv.symm j).1, m (finProdFinEquiv.symm j).1) ≠ (i, c) := by
+    intro h
+    have hi := congrArg Prod.fst h
+    have hc := congrArg Prod.snd h
+    simp only at hi hc
+    rw [hi] at hc
+    exact hm hc
+  rw [plantTable_ne T i c x hp]
+
+/-- The public table applies the one-way map to every preimage: `tablePublic g T p = g (T p)`. -/
+def tablePublic {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (p : Fin n × Bool) : Y := g (T p)
+
+/-- The public image at cell `p` is `g (T p)`: `tablePublic g T p = g (T p)`. -/
+theorem tablePublic_eq {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (p : Fin n × Bool) : tablePublic g T p = g (T p) := rfl
+
+/-- Replace the public image at `(i,c)` by `y`, without knowing a preimage of `y`: `plantedPublic g
+T i c y p = if p = (i, c) then y else g (T p)`. -/
+def plantedPublic {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (i : Fin n) (c : Bool) (y : Y) (p : Fin n × Bool) : Y :=
+  if p = (i, c) then y else g (T p)
+
+/-- The planted public table reads `y` at `(i,c)` and the original images elsewhere: `plantedPublic
+g T i c y p = if p = (i, c) then y else g (T p)`. -/
+theorem plantedPublic_eq {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (i : Fin n) (c : Bool) (y : Y) (p : Fin n × Bool) :
+    plantedPublic g T i c y p = if p = (i, c) then y else g (T p) := rfl
+
+/-- When `y=g(x)`, the planted public table is the honest public table of the updated key. -/
+theorem plantedPublic_image {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (i : Fin n) (c : Bool) (x : Fin n → Bool) :
+    plantedPublic g T i c (g x) = tablePublic g (plantTable T i c x) := by
+  funext p
+  by_cases hp : p = (i, c)
+  · simp only [plantedPublic, tablePublic, plantTable, hp, if_true]
+  · simp only [plantedPublic, tablePublic, plantTable, hp, if_false]
+
+/-- The planted public table ignores the original preimage at its planted coordinate: `plantedPublic
+g (plantTable T i c x) i c y = plantedPublic g T i c y`. -/
+theorem plantedPublic_plant {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (i : Fin n) (c : Bool) (x : Fin n → Bool) (y : Y) :
+    plantedPublic g (plantTable T i c x) i c y = plantedPublic g T i c y := by
+  funext p
+  by_cases hp : p = (i, c)
+  · rw [plantedPublic_eq, plantedPublic_eq, if_pos hp, if_pos hp]
+  · rw [plantedPublic_eq, plantedPublic_eq, if_neg hp, if_neg hp,
+      plantTable_ne T i c x hp]
+
+/-- Extract the `i`-th preimage block from a flattened signature: `signatureBlock σ i = fun k => σ
+(finProdFinEquiv (i, k))`. -/
+def signatureBlock {n : ℕ} (σ : Fin (n * n) → Bool) (i : Fin n) : Fin n → Bool :=
+  fun k => σ (finProdFinEquiv (i, k))
+
+/-- Extracted block `i` reads the flattened signature at indices `(i,k)`: `signatureBlock σ i = fun
+k => σ (finProdFinEquiv (i, k))`. -/
+theorem signatureBlock_eq {n : ℕ} (σ : Fin (n * n) → Bool) (i : Fin n) :
+    signatureBlock σ i = fun k => σ (finProdFinEquiv (i, k)) := rfl
+
+/-- An accepting signature on a message with bit `c` at `i` supplies a preimage of `g(x)`
+under the planted public table [PS10, Theorem 137.2]: if `∀ j, g (signatureBlock σ j) =
+plantedPublic g T i c (g x) (j, m j)` and `m i = c`, then `g (signatureBlock σ i) = g x`. -/
+theorem extract_planted {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (i : Fin n) (c : Bool) (x : Fin n → Bool) (m : Fin n → Bool)
+    (σ : Fin (n * n) → Bool)
+    (hacc : ∀ j, g (signatureBlock σ j) = plantedPublic g T i c (g x) (j, m j))
+    (hm : m i = c) : g (signatureBlock σ i) = g x := by
+  have h := hacc i
+  rw [plantedPublic_eq, hm, if_pos rfl] at h
+  exact h
+
+/-- A computation of cost zero under unit query costs is a return: if `tree.CostBoundedBy (fun _
+=> 1) 0`, then `∃ a, tree = .pure a`. -/
+theorem exists_pure_of_cost_zero {ι α : Type} {spec : OracleSpec ι}
+    (tree : OracleComp spec α) (h : tree.CostBoundedBy (fun _ => 1) 0) :
+    ∃ a, tree = .pure a := by
+  cases tree with
+  | pure a => exact ⟨a, rfl⟩
+  | query j m k =>
+    have hcost := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 0).1 h
+    omega
+
+/-- The first query of a typed signature-forging computation, or `none` if it returns: `firstQuery
+(.pure a) = none` and `firstQuery (.query j m k) = some m`. -/
+def firstQuery {n : ℕ} {α : Type} :
+    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α → Option (Fin n → Bool)
+  | .pure _ => none
+  | .query _ m _ => some m
+
+/-- A return has no first query: `firstQuery (.pure a : OracleComp (bitSpec (fun _ : Fin 1 => n)
+(fun _ => n * n)) α) = none`. -/
+theorem firstQuery_pure {n : ℕ} {α : Type} (a : α) :
+    firstQuery (.pure a : OracleComp
+      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) = none := rfl
+
+/-- A query node's first query is its own message: `firstQuery (.query j m k) = some m`. -/
+theorem firstQuery_query {n : ℕ} {α : Type} (j : Fin 1) (m : Fin n → Bool)
+    (k : (Fin (n * n) → Bool) → OracleComp
+      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) :
+    firstQuery (.query j m k) = some m := rfl
+
+/-- The deterministic typed signing oracle returns the table's selected preimages: `tableSigner T =
+QueryImpl.ofComp fun _ m => .pure (tableSignature T m)`. -/
+def tableSigner {n : ℕ} (T : Table n) :
+    QueryImpl (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) Unit unifSpec :=
+  QueryImpl.ofComp fun _ m => .pure (tableSignature T m)
+
+/-- The table signer is the stateless implementation of `m ↦ pure (tableSignature T m)`:
+`tableSigner T = QueryImpl.ofComp (fun _ m => .pure (tableSignature T m))`. -/
+theorem tableSigner_eq {n : ℕ} (T : Table n) :
+    tableSigner T = QueryImpl.ofComp (fun _ m => .pure (tableSignature T m)) := rfl
+
+/-- The log of a computation with at most one query consists of its first query and answer,
+or is empty if it returns immediately: `firstLog T (.pure a) = []` and `firstLog T (.query j m k) =
+[⟨j, m, tableSignature T m⟩]`. -/
+def firstLog {n : ℕ} {α : Type} (T : Table n) :
+    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α →
+      QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))
+  | .pure _ => []
+  | .query j m _ => [⟨j, m, tableSignature T m⟩]
+
+/-- A return has an empty first-query log: `firstLog T (.pure a : OracleComp (bitSpec (fun _ : Fin 1
+=> n) (fun _ => n * n)) α) = []`. -/
+theorem firstLog_pure {n : ℕ} {α : Type} (T : Table n) (a : α) :
+    firstLog T (.pure a : OracleComp
+      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) = [] := rfl
+
+/-- A query node's first-query log contains exactly its message and deterministic answer: `firstLog
+T (.query j m k) = [⟨j, m, tableSignature T m⟩]`. -/
+theorem firstLog_query {n : ℕ} {α : Type} (T : Table n) (j : Fin 1) (m : Fin n → Bool)
+    (k : (Fin (n * n) → Bool) → OracleComp
+      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) :
+    firstLog T (.query j m k) = [⟨j, m, tableSignature T m⟩] := rfl
+
+/-- A computation with at most one query against the logged deterministic signer returns its
+functional evaluation and exactly its first-query log: if `tree.CostBoundedBy (fun _ => 1) 1`, then
+`simulate (tableSigner T).withLog tree ((), []) = .pure (tree.evalFn (fun _ m => tableSignature T
+m), ((), firstLog T tree))`.
+
+**Proof sketch.** An immediate return has no log. At a query, the signer returns its selected
+preimages and appends one entry. Unit query cost leaves cost zero for the continuation, so
+the continuation is a return and appends no further entry. -/
+theorem honest_transcript {n : ℕ} {α : Type} (T : Table n)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (hcost : tree.CostBoundedBy (fun _ => 1) 1) :
+    simulate (tableSigner T).withLog tree ((), []) =
+      .pure (tree.evalFn (fun _ m => tableSignature T m), ((), firstLog T tree)) := by
+  cases tree with
+  | pure a => rw [simulate_pure, OracleComp.evalFn_pure, firstLog_pure]
+  | query j m k =>
+    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
+    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (tableSignature T m))
+      (by simpa only [Nat.sub_self] using hk.2 (tableSignature T m))
+    simp only [simulate_query, QueryImpl.withLog_apply, tableSigner_eq, QueryImpl.ofComp_apply,
+      OracleComp.pure_bind, ha, simulate_pure, OracleComp.evalFn_query,
+      OracleComp.evalFn_pure, firstLog_query, List.nil_append]
+
+/-- Freshness against the first-query log is exactly inequality with the optional first
+message: no logged entry queried `m` if and only if `firstQuery tree ≠ some m`. -/
+theorem fresh_firstLog_iff {n : ℕ} {α : Type} (T : Table n)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (m : Fin n → Bool) :
+    (∀ e ∈ firstLog T tree, e.2.1 ≠ m) ↔ firstQuery tree ≠ some m := by
+  cases tree <;> simp [firstLog, firstQuery]
+
+/-- The logged one-query signing run has an output and log whose freshness condition is
+equivalent to avoiding the optional first query, for any projection of a forgery's message: if
+`tree.CostBoundedBy (fun _ => 1) 1`, then `∃ a log, simulate (tableSigner T).withLog tree ((), []) =
+.pure (a, ((), log)) ∧ a = tree.evalFn (fun _ m => tableSignature T m) ∧ ((∀ e ∈ log, e.2.1 ≠
+message a) ↔ firstQuery tree ≠ some (message a))`. -/
+theorem exists_honest_transcript {n : ℕ} {α : Type} (T : Table n)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (message : α → Fin n → Bool) :
+    ∃ a log, simulate (tableSigner T).withLog tree ((), []) = .pure (a, ((), log)) ∧
+      a = tree.evalFn (fun _ m => tableSignature T m) ∧
+      ((∀ e ∈ log, e.2.1 ≠ message a) ↔ firstQuery tree ≠ some (message a)) := by
+  exact ⟨_, _, honest_transcript T tree hcost, rfl, fresh_firstLog_iff T tree _⟩
+
+/-- The sole signing query, if present, avoids the planted cell: `Safe tree i c ↔ ∀ m, firstQuery
+tree = some m → m i ≠ c`. -/
+def Safe {n : ℕ} {α : Type}
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (i : Fin n) (c : Bool) : Prop :=
+  ∀ m, firstQuery tree = some m → m i ≠ c
+
+/-- Safety means that every message recorded as the first query has bit different from `c`: `Safe
+tree i c ↔ ∀ m, firstQuery tree = some m → m i ≠ c`. -/
+theorem safe_iff {n : ℕ} {α : Type}
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (i : Fin n) (c : Bool) :
+    Safe tree i c ↔ ∀ m, firstQuery tree = some m → m i ≠ c := Iff.rfl
+
+/-- The aborting oracle answers an unsafe query with zero and answers a safe one honestly:
+`abortingAnswer T i c m = if m i = c then zeroBits _ else tableSignature T m`. -/
+def abortingAnswer {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (m : Fin n → Bool) :
+    Fin (n * n) → Bool :=
+  if m i = c then zeroBits _ else tableSignature T m
+
+/-- An aborting answer is zero when `m i=c`, and otherwise is the original signature. -/
+theorem abortingAnswer_eq {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (m : Fin n → Bool) :
+    abortingAnswer T i c m = if m i = c then zeroBits _ else tableSignature T m := rfl
+
+/-- The aborting answer ignores the original preimage at the planted coordinate: `abortingAnswer
+(plantTable T i c x) i c m = abortingAnswer T i c m`. -/
+theorem abortingAnswer_plant {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
+    (x : Fin n → Bool) (m : Fin n → Bool) :
+    abortingAnswer (plantTable T i c x) i c m = abortingAnswer T i c m := by
+  rw [abortingAnswer_eq, abortingAnswer_eq]
+  by_cases hm : m i = c
+  · rw [if_pos hm, if_pos hm]
+  · rw [if_neg hm, if_neg hm, tableSignature_plant_of_safe T i c x m hm]
+
+/-- The planted implementation remembers whether an unsafe query has occurred: `abortingImpl T i c j
+m bad = .pure (abortingAnswer T i c m, bad || decide (m i = c))`. -/
+def abortingImpl {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) :
+    QueryImpl (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) Bool unifSpec :=
+  fun _ m bad => .pure (abortingAnswer T i c m, bad || decide (m i = c))
+
+/-- A call returns the aborting answer and sets its abort bit to `bad ∨ (m i=c)`. -/
+theorem abortingImpl_apply {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
+    (j : Fin 1) (m : Fin n → Bool) (bad : Bool) :
+    abortingImpl T i c j m bad =
+      .pure (abortingAnswer T i c m, bad || decide (m i = c)) := rfl
+
+/-- The aborting implementation ignores the original preimage at its planted coordinate:
+`abortingImpl (plantTable T i c x) i c = abortingImpl T i c`. -/
+theorem abortingImpl_plant {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
+    (x : Fin n → Bool) :
+    abortingImpl (plantTable T i c x) i c = abortingImpl T i c := by
+  funext j m bad
+  rw [abortingImpl_apply, abortingImpl_apply, abortingAnswer_plant]
+
+/-- A safe call agrees with the updated key and leaves the abort bit false: if `m i ≠ c`, then
+`abortingImpl T i c j m false = .pure (tableSignature (plantTable T i c x) m, false)`. -/
+theorem abortingImpl_safe {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
+    (x : Fin n → Bool) (j : Fin 1) (m : Fin n → Bool) (hm : m i ≠ c) :
+    abortingImpl T i c j m false = .pure (tableSignature (plantTable T i c x) m, false) := by
+  rw [abortingImpl_apply, abortingAnswer_eq, if_neg hm,
+    tableSignature_plant_of_safe T i c x m hm]
+  simp only [hm, decide_false, Bool.false_or]
+
+/-- A safe run with at most one signing query has exactly the honest output for the updated
+key and never aborts [PS10, Theorem 137.2]: if `tree.CostBoundedBy (fun _ => 1) 1` and `Safe tree i
+c`, then `simulate (abortingImpl T i c) tree false = .pure (tree.evalFn (fun _ m => tableSignature
+(plantTable T i c x) m), false)`.
+
+**Proof sketch.** A return needs no coupling. At a query, safety says that the queried message
+does not reveal the planted cell, so its answer is exactly the updated key's honest answer.
+The remaining computation has query cost zero and is a return; therefore the final outputs
+agree and the abort flag stays false. -/
+theorem planted_coupling {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
+    (x : Fin n → Bool)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (hsafe : Safe tree i c) :
+    simulate (abortingImpl T i c) tree false =
+      .pure (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m), false) := by
+  cases tree with
+  | pure a => rw [simulate_pure, OracleComp.evalFn_pure]
+  | query j m k =>
+    have hm : m i ≠ c := (safe_iff _ i c).1 hsafe m (firstQuery_query j m k)
+    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
+    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero
+      (k (tableSignature (plantTable T i c x) m))
+      (by simpa only [Nat.sub_self] using (hk.2 (tableSignature (plantTable T i c x) m)))
+    rw [simulate_query, abortingImpl_safe T i c x j m hm, OracleComp.pure_bind, ha,
+      simulate_pure, OracleComp.evalFn_query, ha, OracleComp.evalFn_pure]
+
+/-- Run a fixed-position planted forger and extract block `i`, returning zero after an abort:
+`extractionExperiment T i c tree signature = (simulate (abortingImpl T i c) tree false).bind (fun
+res => .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i))`. -/
+def extractionExperiment {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (signature : α → Fin (n * n) → Bool) : ProbComp (Fin n → Bool) :=
+  (simulate (abortingImpl T i c) tree false).bind fun res =>
+    .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i)
+
+/-- The extraction experiment simulates the aborting implementation and selects the `i`-th
+signature block when the final abort bit is false: `extractionExperiment T i c tree signature =
+(simulate (abortingImpl T i c) tree false).bind (fun res => .pure (if res.2 then zeroBits n else
+signatureBlock (signature res.1) i))`. -/
+theorem extractionExperiment_eq {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (signature : α → Fin (n * n) → Bool) :
+    extractionExperiment T i c tree signature =
+      (simulate (abortingImpl T i c) tree false).bind (fun res =>
+        .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i)) := rfl
+
+/-- The extraction experiment ignores the original preimage at the planted coordinate:
+`extractionExperiment (plantTable T i c x) i c tree signature = extractionExperiment T i c tree
+signature`. -/
+theorem extractionExperiment_plant {n : ℕ} {α : Type} (T : Table n) (i : Fin n)
+    (c : Bool) (x : Fin n → Bool)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (signature : α → Fin (n * n) → Bool) :
+    extractionExperiment (plantTable T i c x) i c tree signature =
+      extractionExperiment T i c tree signature := by
+  rw [extractionExperiment_eq, extractionExperiment_eq, abortingImpl_plant]
+
+/-- The fixed-position reduction builds the planted public table, runs the forger against
+the aborting signer, and extracts the `i`-th signature block: `plantedExperiment g T i c y adv
+signature = extractionExperiment T i c (adv (plantedPublic g T i c y)) signature`. -/
+def plantedExperiment {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (i : Fin n) (c : Bool) (y : Y)
+    (adv : ((Fin n × Bool) → Y) →
+      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (signature : α → Fin (n * n) → Bool) : ProbComp (Fin n → Bool) :=
+  extractionExperiment T i c (adv (plantedPublic g T i c y)) signature
+
+/-- The planted experiment is extraction after running the adversary on the planted public
+table: `plantedExperiment g T i c y adv signature = extractionExperiment T i c (adv (plantedPublic g
+T i c y)) signature`. -/
+theorem plantedExperiment_eq {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
+    (i : Fin n) (c : Bool) (y : Y)
+    (adv : ((Fin n × Bool) → Y) →
+      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (signature : α → Fin (n * n) → Bool) :
+    plantedExperiment g T i c y adv signature =
+      extractionExperiment T i c (adv (plantedPublic g T i c y)) signature := rfl
+
+/-- The entire planted experiment ignores the original preimage at `(i,c)`, `plantedExperiment g
+(plantTable T i c x) i c y adv signature = plantedExperiment g T i c y adv signature`; this is the
+coordinate-invariance hypothesis for sampling that preimage independently. -/
+theorem plantedExperiment_plant {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y)
+    (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool) (y : Y)
+    (adv : ((Fin n × Bool) → Y) →
+      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (signature : α → Fin (n * n) → Bool) :
+    plantedExperiment g (plantTable T i c x) i c y adv signature =
+      plantedExperiment g T i c y adv signature := by
+  rw [plantedExperiment_eq, plantedExperiment_eq, plantedPublic_plant,
+    extractionExperiment_plant]
+
+/-- A safe, accepting honest run whose forged message uses the planted bit produces an
+inverse of the planted image in the reduction experiment [PS10, Theorem 137.2]: if
+`tree.CostBoundedBy (fun _ => 1) 1`, `Safe tree i c`, and the updated-key honest output `a`
+satisfies `∀ j, g (signatureBlock (signature a) j) = plantedPublic g T i c (g x) (j, message a j)`
+and `message a i = c`, then `∃ z, extractionExperiment T i c tree signature = .pure z ∧ g z = g x`,
+where `a = tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)`.
+
+**Proof sketch.** The safe coupling identifies the reduction's output with the honest forged
+signature block and keeps its abort bit false. Acceptance at the planted position then says
+that applying the one-way map to that block gives the planted image. -/
+theorem favorable_extraction {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y)
+    (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
+    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
+    (signature : α → Fin (n * n) → Bool) (message : α → Fin n → Bool)
+    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (hsafe : Safe tree i c)
+    (hacc : ∀ j, g (signatureBlock
+        (signature (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m))) j) =
+      plantedPublic g T i c (g x)
+        (j, message (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)) j))
+    (hm : message (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)) i = c) :
+    ∃ z, extractionExperiment T i c tree signature = .pure z ∧ g z = g x := by
+  refine ⟨signatureBlock
+    (signature (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m))) i, ?_, ?_⟩
+  · rw [extractionExperiment_eq, planted_coupling T i c x tree hcost hsafe,
+      OracleComp.pure_bind]
+    rfl
+  · exact extract_planted g T i c x _ _ hacc hm
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Realization.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Realization.lean
new file mode 100644
index 000000000..6dc2f8df2
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Realization.lean
@@ -0,0 +1,230 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Realizing the planted Lamport experiment as a machine
+
+## Main definitions
+
+* `machineForger`: a machine forger on a typed public-key table, with budget one.
+
+## Main results
+
+* `exists_realization_machine`: T1 realizes every nonaborting successful planted transcript
+  by an actual machine output, with an explicit uniform coin equivalence.
+
+The generator, signer, evaluator, and fixed-width block reader are parameters. Their
+functional contracts are assumptions about algorithms, rather than additional hardness
+assumptions. The owned Lamport module discharges them from its published readers.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, proof of Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open Complexity Turing TCSlib.Cryptography.Games
+open TCSlib.Cryptography
+
+/-- Run a machine forger on the serialized typed public table, using the canonical
+message/signature codec and a budget of one signing query: `machineForger L A n Y r = A.toCompOn
+(bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n)) n 1 (publicWord Y) r`. -/
+def machineForger (L : PolyExpr) (A : NUPPT) (n : ℕ)
+    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
+    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))
+      (Fin (n + n * n) → Bool) :=
+  A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
+    n 1 (publicWord Y) r
+
+/-- The typed machine forger is `A.toCompOn` on the serialized public table: `machineForger L A n Y
+r = A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n)) n 1 (publicWord Y) r`.
+-/
+theorem machineForger_eq (L : PolyExpr) (A : NUPPT) (n : ℕ)
+    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
+    machineForger L A n Y r =
+      A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
+        n 1 (publicWord Y) r := rfl
+
+/-- As a function of the public table and coins, the machine forger is the canonical
+one-query `toCompOn` construction: `machineForger L A n = fun Y r => A.toCompOn (bitCodec (fun _ :
+Fin 1 => n) (fun _ => n * n) (n + n * n)) n 1 (publicWord Y) r`. This form also reads it beneath an
+opaque expectation. -/
+theorem machineForger_eq_fun (L : PolyExpr) (A : NUPPT) (n : ℕ) :
+    machineForger L A n = fun Y r =>
+      A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
+        n 1 (publicWord Y) r := rfl
+
+/-- Every typed machine-forger tree has unit-query cost at most one: `(machineForger L A n Y
+r).CostBoundedBy (fun _ => 1) 1`. -/
+theorem machineForger_cost (L : PolyExpr) (A : NUPPT) (n : ℕ)
+    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
+    (machineForger L A n Y r).CostBoundedBy (fun _ => 1) 1 := by
+  rw [machineForger_eq]
+  exact A.toCompOn_costBoundedBy _ _ _ _ _
+
+/-- The planted experiment's successful nonaborting outputs are actual inverter outputs: `∃ B :
+NUPPT, ∀ n, ∃ φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n, ∀ i y T c r, RedSuccess (f n)
+(machineForger L A n) y T r (i, c) → ∃ x', B.runAt n (pairEncode (List.ofFn y) (List.replicate i.val
+true)) (φ ((c, T), r)) = List.ofFn x' ∧ f n x' = y`, given the evaluator, generator, signer and
+block-reader contracts `hEval`, `hGen`, `hSign` and `hcoin`. The machine uses one fair seed bit, one
+random table, and the forger's own random tape. [PS10, machine-realization step in the proof of
+Theorem 137.2].
+
+**Proof sketch.** T1 gives a machine for the polynomial-time planting handler. Reindex its
+seed by the public seed/table equivalence. On a successful planted transcript the final
+abort flag is false, so its sole query was safe. A return needs no oracle call; a safe query
+has the ordinary sampled-table signature and leaves the false handler state unchanged.
+The remaining tree has cost zero and is a return. Thus the handler simulation and the
+typed planted simulation have the same output. T1's output equation and the public
+nonabort-extraction contract identify the actual machine output with that signature block. -/
+theorem exists_realization_machine
+    (L W : PolyExpr)
+    (f : ∀ n, (Fin n → Bool) → Fin (L.eval n) → Bool)
+    (E G S : List Bool → List Bool)
+    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S)
+    (hW : ∀ n, W.eval n = 6 * L.eval n + 6)
+    (hEval : ∀ n (x : Fin n → Bool),
+      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x))
+    (hGen : ∀ n (T : Table n),
+      G (NUPPT.layout (List.replicate n true) [] [] (secretWord T)) =
+        pairEncode (publicWord (tablePublic (f n) T)) (secretWord T))
+    (hSign : ∀ n (T : Table n) (m : Fin n → Bool),
+      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
+        List.ofFn (tableSignature T m))
+    (hcoin : ∀ {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
+      (i : Fin q), coinBlock B i (List.ofFn g).flatten = g i)
+    (A : NUPPT) :
+    ∃ B : NUPPT, ∀ n,
+      ∃ φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n,
+        ∀ (i : Fin n) (y : Fin (L.eval n) → Bool) (T : Table n) (c : Bool) (r : A.Coins n),
+          RedSuccess (f n) (machineForger L A n) y T r (i, c) →
+            ∃ x' : Fin n → Bool,
+              B.runAt n (pairEncode (List.ofFn y) (List.replicate i.val true))
+                  (φ ((c, T), r)) = List.ofFn x' ∧
+                f n x' = y := by
+  let H := LamportMachine.handler W E G S hE hG hS
+  obtain ⟨B, hB⟩ := exists_handlerMachine A (.const 1)
+    (fun _ : Fin 1 => PolyExpr.var) (fun _ => PolyExpr.mul .var .var)
+    (.add .var (.mul .var .var)) H
+  refine ⟨B, fun n => ?_⟩
+  obtain ⟨ψ, hψ⟩ := hB n
+  have hseed : H.seedLen.eval n = 1 + 2 * n * n := by
+    simp only [H, LamportMachine.handler_seedLen, PolyExpr.eval_add, PolyExpr.eval_const,
+      PolyExpr.eval_mul, PolyExpr.eval_var]
+  have hstate : H.stateLen.eval n = 1 := by
+    simp only [H, LamportMachine.handler_stateLen, PolyExpr.eval_const]
+  -- T1's query, answer and output widths, read through the `PolyExpr.eval` equations.
+  have hd : PolyExpr.var.eval n = n := PolyExpr.eval_var n
+  have he : (PolyExpr.mul .var .var).eval n = n * n := by
+    rw [PolyExpr.eval_mul, PolyExpr.eval_var]
+  have ho : (PolyExpr.add .var (.mul .var .var)).eval n = n + n * n := by
+    rw [PolyExpr.eval_add, he, PolyExpr.eval_var]
+  let toSeed : (Bool × Table n) ≃ (Fin (H.seedLen.eval n) → Bool) :=
+    (seedCoins n).symm.trans
+      (Equiv.arrowCongr (finCongr hseed.symm) (Equiv.refl Bool))
+  let φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n :=
+    (toSeed.prodCongr (Equiv.refl (A.Coins n))).trans ψ
+  refine ⟨φ, fun i y T c r hred => ?_⟩
+  let z := pairEncode (List.ofFn y) (List.replicate i.val true)
+  let ω := toSeed (c, T)
+  have hω : List.ofFn ω = c :: secretWord T := by
+    change List.ofFn ((Equiv.arrowCongr (finCongr hseed.symm) (Equiv.refl Bool))
+      ((seedCoins n).symm (c, T))) = c :: secretWord T
+    rw [ofFn_arrowCongr_finCongr, ofFn_seedCoins_symm]
+  have hinit : H.init n = fun _ => false := by
+    funext j
+    exact LamportMachine.handler_init W E G S hE hG hS n j
+  have hinitWord : List.ofFn (H.init n) = [false] := by
+    rw [hinit, List.ofFn_const, hstate]
+    rfl
+  have hadv : H.advInput n z ω = publicWord (plantedPublic (f n) T i c y) := by
+    simp only [PolyHandler.advInput_eq, H, LamportMachine.handler_advIn, hω, z]
+    exact advIn_context hcoin W (hW n) (f n) E G (hEval n) (hGen n) T i c y
+  let tree := machineForger L A n (plantedPublic (f n) T i c y) r
+  have hcost : tree.CostBoundedBy (fun _ => 1) 1 := machineForger_cost L A n _ r
+  obtain ⟨a₀, habort, hinverts⟩ := (redSuccess_iff (f n) (machineForger L A n) y T r (i, c)).1 hred
+  change simulate (abortingImpl T i c) tree false = .pure (a₀, false) at habort
+  have hsafe : Safe tree i c := safe_of_nonabort T i c tree hcost a₀ habort
+  have hrunread : H.run = LamportMachine.run S :=
+    LamportMachine.handler_run W E G S hE hG hS
+  -- A safe query at T1's widths is answered by its table signature, cast to the answer width.
+  have hcall : ∀ (j : Fin 1) (m : Fin (PolyExpr.var.eval n) → Bool), m (Fin.cast hd.symm i) ≠ c →
+      H.impl n z ω j m (H.init n) = .pure (fun k => tableSignature T
+        (fun l => m (Fin.cast hd.symm l)) (Fin.cast he k), H.init n) := by
+    intro j m hm
+    rw [PolyHandler.impl_apply]
+    apply congrArg OracleComp.pure
+    apply PolyHandler.answer_of_run_eq H
+    simp only [hrunread, hω, hinitWord]
+    rw [List.ofFn_congr hd m, List.ofFn_congr he]
+    simp only [Fin.cast_cast]
+    simp only [Fin.cast_refl, id_eq]
+    simpa only [z] using run_safe S (hSign n) T i c (List.ofFn y) j _ hm
+  -- The planted simulation at any widths equal to T1's: substitute the widths, then read the
+  -- typed tree. A return needs no query; a safe query keeps the false state.
+  have htransport : ∀ (d e o q : ℕ) (Y : List Bool) (hd : d = n) (he : e = n * n)
+      (ho : o = n + n * n), q = 1 → Y = publicWord (plantedPublic (f n) T i c y) →
+      ∀ impl : QueryImpl (bitSpec (fun _ : Fin 1 => d) (fun _ => e))
+        (Fin (H.stateLen.eval n) → Bool) unifSpec,
+      (∀ (j : Fin 1) (m : Fin d → Bool), m (Fin.cast hd.symm i) ≠ c →
+        impl j m (H.init n) = .pure (fun k => tableSignature T
+          (fun l => m (Fin.cast hd.symm l)) (Fin.cast he k), H.init n)) →
+      simulate impl (A.toCompOn (bitCodec (fun _ : Fin 1 => d) (fun _ => e) o) n q Y r)
+        (H.init n) = .pure (fun k => a₀ (Fin.cast ho k), H.init n) := by
+    intro d e o q Y hd he ho hq hY impl himpl
+    subst d e o q Y
+    simp only [Fin.cast_refl, id_eq] at himpl ⊢
+    rw [← machineForger_eq L A n]
+    change simulate impl tree (H.init n) = .pure (a₀, H.init n)
+    cases ht : tree with
+    | pure a =>
+      rw [ht] at habort
+      have hp : (a, false) = (a₀, false) :=
+        OracleComp.pure.inj (by simpa only [simulate_pure] using habort)
+      have haa : a = a₀ := congrArg Prod.fst hp
+      rw [simulate_pure, haa]
+    | query j m k =>
+      rw [ht] at habort hcost hsafe
+      have hm : m i ≠ c := (safe_iff _ i c).1 hsafe m (firstQuery_query j m k)
+      have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
+      obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (tableSignature T m))
+        (by simpa only [Nat.sub_self] using hk.2 (tableSignature T m))
+      have hp : (a, false) = (a₀, false) := OracleComp.pure.inj (by
+        simpa only [simulate_query, abortingImpl_apply, abortingAnswer_eq, if_neg hm,
+          hm, if_false, decide_false, Bool.false_or, OracleComp.pure_bind, ha, simulate_pure]
+          using habort)
+      have haa : a = a₀ := congrArg Prod.fst hp
+      rw [simulate_query, himpl j m hm, OracleComp.pure_bind, ha, simulate_pure,
+        haa]
+  obtain ⟨a, s, hsimulation, houtput⟩ := hψ z ω r
+  have hsim := htransport _ _ _ _ _ hd he ho (PolyExpr.eval_const 1 n) hadv (H.impl n z ω) hcall
+  have hp : (a, s) = (fun k => a₀ (Fin.cast ho k), H.init n) :=
+    OracleComp.pure.inj (hsimulation.symm.trans hsim)
+  have ha : a = fun k => a₀ (Fin.cast ho k) := congrArg Prod.fst hp
+  have hs : s = H.init n := congrArg Prod.snd hp
+  rw [ha, hs] at houtput
+  have hresult : H.result n z ω (H.init n) (fun k => a₀ (Fin.cast ho k)) =
+      List.ofFn (signatureBlock (splitBits a₀).2 i) := by
+    rw [PolyHandler.result_eq, show H.out = LamportMachine.out from
+      LamportMachine.handler_out W E G S hE hG hS, hω, hinitWord, List.ofFn_congr ho]
+    simp only [Fin.cast_cast]
+    simp only [Fin.cast_refl, id_eq]
+    apply out_nonabort i z (c :: secretWord T) a₀
+    simpa only [z] using LamportMachine.pos_seedIn n (List.ofFn y)
+      (List.replicate i.val true) (c :: secretWord T)
+  refine ⟨signatureBlock (splitBits a₀).2 i, ?_, hinverts⟩
+  change B.runAt n z (ψ (ω, r)) = List.ofFn (signatureBlock (splitBits a₀).2 i)
+  exact houtput.trans hresult
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Seed.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Seed.lean
new file mode 100644
index 000000000..323cdff8e
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Seed.lean
@@ -0,0 +1,77 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
+import Mathlib.Data.List.OfFn
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# A fair planting bit and a uniform Lamport table
+
+## Main definitions
+
+* `seedCoins`: a seed of `1 + 2n²` bits is a fair bit paired with a Lamport preimage table.
+
+## Main results
+
+* `seedCoins_apply` and `seedCoins_symm`: forward and inverse equations.
+* `ofFn_seedCoins_symm`: the inverse seed word is `c :: secretWord T`.
+* `ofFn_seedCoins`: the seed word decomposes into its planting bit and table serialization.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, Theorem 137.2. This is generic seed serialization glue for its reduction.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+/-- The seed width `1 + 2n²` is the successor width `2n² + 1`: `1 + 2 * n * n = 2 * n * n + 1`. -/
+theorem seedCoins_width (n : ℕ) : 1 + 2 * n * n = 2 * n * n + 1 :=
+  Nat.add_comm _ _
+
+/-- A seed of `1 + 2n²` bits is equivalent to a Boolean planting bit and a typed key table:
+`seedCoins n : (Fin (1 + 2 * n * n) → Bool) ≃ Bool × Table n`. The bit is the first seed entry and
+the table occupies the remaining entries in row order. -/
+def seedCoins (n : ℕ) : (Fin (1 + 2 * n * n) → Bool) ≃ Bool × Table n :=
+  ((Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)).trans
+    (Fin.consEquiv (fun _ : Fin (2 * n * n + 1) => Bool)).symm).trans
+      ((Equiv.refl Bool).prodCongr (tableCoins n))
+
+/-- `seedCoins n x` consists of the first entry of `x` and the table represented by its
+remaining entries, after the equality cast to successor width: `seedCoins n x = (x' 0, tableCoins n
+(Fin.tail x'))`, where `x' = (Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)) x`.
+-/
+theorem seedCoins_apply (n : ℕ) (x : Fin (1 + 2 * n * n) → Bool) :
+    seedCoins n x =
+      (((Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)) x) 0,
+        tableCoins n
+          (Fin.tail ((Equiv.arrowCongr (finCongr (seedCoins_width n))
+            (Equiv.refl Bool)) x))) := rfl
+
+/-- The inverse seed equivalence prepends `c` to the coin tape represented by `T`, and casts
+back from successor width to `1 + 2n²`: `(seedCoins n).symm (c, T) = (Equiv.arrowCongr (finCongr
+(seedCoins_width n).symm) (Equiv.refl Bool)) (Fin.cons c ((tableCoins n).symm T))`. -/
+theorem seedCoins_symm (n : ℕ) (c : Bool) (T : Table n) :
+    (seedCoins n).symm (c, T) =
+      (Equiv.arrowCongr (finCongr (seedCoins_width n).symm) (Equiv.refl Bool))
+        (Fin.cons c ((tableCoins n).symm T)) := rfl
+
+/-- The inverse seed word is the planting bit followed by the serialized key table:
+`List.ofFn ((seedCoins n).symm (c,T)) = c :: secretWord T`. -/
+theorem ofFn_seedCoins_symm {n : ℕ} (c : Bool) (T : Table n) :
+    List.ofFn ((seedCoins n).symm (c, T)) = c :: secretWord T := by
+  rw [seedCoins_symm, ofFn_arrowCongr_finCongr, List.ofFn_cons, ofFn_tableCoins_symm]
+
+/-- Every seed word is its extracted planting bit followed by its extracted key table's
+serialization: `List.ofFn x = (seedCoins n x).1 :: secretWord (seedCoins n x).2`. -/
+theorem ofFn_seedCoins {n : ℕ} (x : Fin (1 + 2 * n * n) → Bool) :
+    List.ofFn x = (seedCoins n x).1 :: secretWord (seedCoins n x).2 := by
+  have h := ofFn_seedCoins_symm (seedCoins n x).1 (seedCoins n x).2
+  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/Statistics.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Statistics.lean
new file mode 100644
index 000000000..7c1086c9f
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/Statistics.lean
@@ -0,0 +1,153 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Sampling a planted coordinate independently
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `coordinate_reduction_bound`: a pointwise favorable-position bound and a
+  coordinate-invariant reduction give the same bound with the challenge sampled
+  independently of the table.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
+  January 2010, proof of Theorem 137.2.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+open TCSlib.Cryptography.Games
+open scoped Classical
+
+-- Keep elaboration on the published probability readers.
+run_cmd do
+  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
+    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
+    unless status == .irreducible do
+      let id := Lean.mkIdent n
+      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
+
+/-- Suppose every successful honest run has favorable position mass at least `b`, and
+every successful favorable run makes a reduction succeed when challenged at its own
+table coordinate. If the reduction ignores that original coordinate, the average
+reduction success for an independent challenge is at least `b` times honest success: if `∀ T r, P T
+r → b ≤ 𝔼 p, [Q T r p]`, `∀ T r p, P T r → Q T r p → R (T p) T r p` and `∀ x x' T r p, R x
+(Function.update T p x') r p ↔ R x T r p`, then `b * 𝔼 T, 𝔼 r, [P T r] ≤ 𝔼 p, 𝔼 x, 𝔼 T, 𝔼 r, [R x T
+r p]`, writing `𝔼 v, h v` for `ProbComp.expect (ProbComp.sample V) (fun v => h v)` with `T : Table
+n`, `r : ρ`, `p : Fin n × Bool`, `x : Fin n → Bool`, and `[A]` for `if A then (1 : ℝ) else 0`.
+
+**Proof sketch.** Bound the reduction's position average pointwise by favorable mass
+on successful honest runs, and by zero on unsuccessful ones. Average over tables and
+forger coins. Exchange the position average with those samples. Finally use the
+coordinate-invariance hypothesis to sample the challenge preimage independently
+(`ProbComp.expect_sample_coord`). This is generic probability glue for the planting
+argument of [PS10, Theorem 137.2]. -/
+theorem coordinate_reduction_bound {n : ℕ} [Nonempty (Fin n)]
+    {ρ : Type} [Fintype ρ] [Nonempty ρ]
+    (P : Table n → ρ → Prop)
+    (Q : Table n → ρ → (Fin n × Bool) → Prop)
+    (R : (Fin n → Bool) → Table n → ρ → (Fin n × Bool) → Prop)
+    (b : ℝ)
+    (hgood : ∀ T r, P T r → b ≤
+      ProbComp.expect (ProbComp.sample (Fin n × Bool))
+        (fun p => if Q T r p then (1 : ℝ) else 0))
+    (himp : ∀ T r p, P T r → Q T r p → R (T p) T r p)
+    (hinv : ∀ x x' T r p,
+      R x (Function.update T p x') r p ↔ R x T r p) :
+    b * ProbComp.expect (ProbComp.sample (Table n))
+        (fun T => ProbComp.expect (ProbComp.sample ρ)
+          (fun r => if P T r then (1 : ℝ) else 0)) ≤
+      ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p =>
+        ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
+          ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
+            ProbComp.expect (ProbComp.sample ρ)
+              (fun r => if R x T r p then (1 : ℝ) else 0)))) := by
+  have hpoint (T : Table n) (r : ρ) :
+      b * (if P T r then (1 : ℝ) else 0) ≤
+        ProbComp.expect (ProbComp.sample (Fin n × Bool))
+          (fun p => if R (T p) T r p then (1 : ℝ) else 0) := by
+    by_cases hp : P T r
+    · simp only [hp, if_true, mul_one]
+      refine (hgood T r hp).trans (ProbComp.expect_mono _ fun p => ?_)
+      by_cases hq : Q T r p
+      · have hr := himp T r p hp hq
+        simp only [hq, hr, if_true, le_refl]
+      · simp only [hq, if_false]
+        split_ifs <;> positivity
+    · simp only [hp, if_false, mul_zero]
+      exact ProbComp.expect_nonneg _ (fun p => by split_ifs <;> positivity)
+  calc
+    b * ProbComp.expect (ProbComp.sample (Table n))
+        (fun T => ProbComp.expect (ProbComp.sample ρ)
+          (fun r => if P T r then (1 : ℝ) else 0)) =
+      ProbComp.expect (ProbComp.sample (Table n))
+        (fun T => ProbComp.expect (ProbComp.sample ρ)
+          (fun r => b * (if P T r then (1 : ℝ) else 0))) := by
+      symm
+      calc
+        ProbComp.expect (ProbComp.sample (Table n))
+            (fun T => ProbComp.expect (ProbComp.sample ρ)
+              (fun r => b * (if P T r then (1 : ℝ) else 0))) =
+          ProbComp.expect (ProbComp.sample (Table n))
+            (fun T => b * ProbComp.expect (ProbComp.sample ρ)
+              (fun r => if P T r then (1 : ℝ) else 0)) := by
+          apply congrArg (ProbComp.expect (ProbComp.sample (Table n)))
+          funext T
+          exact ProbComp.expect_const_mul (ProbComp.sample ρ) b
+            (fun r => if P T r then (1 : ℝ) else 0)
+        _ = b * ProbComp.expect (ProbComp.sample (Table n))
+            (fun T => ProbComp.expect (ProbComp.sample ρ)
+              (fun r => if P T r then (1 : ℝ) else 0)) :=
+          ProbComp.expect_const_mul (ProbComp.sample (Table n)) b
+            (fun T => ProbComp.expect (ProbComp.sample ρ)
+              (fun r => if P T r then (1 : ℝ) else 0))
+    _ ≤ ProbComp.expect (ProbComp.sample (Table n))
+        (fun T => ProbComp.expect (ProbComp.sample ρ)
+          (fun r => ProbComp.expect (ProbComp.sample (Fin n × Bool))
+            (fun p => if R (T p) T r p then (1 : ℝ) else 0))) :=
+      ProbComp.expect_mono _ (fun T => ProbComp.expect_mono _ (hpoint T))
+    _ = ProbComp.expect (ProbComp.sample (Table n))
+        (fun T => ProbComp.expect (ProbComp.sample (Fin n × Bool))
+          (fun p => ProbComp.expect (ProbComp.sample ρ)
+            (fun r => if R (T p) T r p then (1 : ℝ) else 0))) := by
+      apply congrArg (ProbComp.expect (ProbComp.sample (Table n)))
+      funext T
+      exact ProbComp.expect_sample_comm
+        (fun r p => if R (T p) T r p then (1 : ℝ) else 0)
+    _ = ProbComp.expect (ProbComp.sample (Fin n × Bool))
+        (fun p => ProbComp.expect (ProbComp.sample (Table n))
+          (fun T => ProbComp.expect (ProbComp.sample ρ)
+            (fun r => if R (T p) T r p then (1 : ℝ) else 0))) :=
+      ProbComp.expect_sample_comm
+        (fun T p => ProbComp.expect (ProbComp.sample ρ)
+          (fun r => if R (T p) T r p then (1 : ℝ) else 0))
+    _ = ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p =>
+        ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
+          ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
+            ProbComp.expect (ProbComp.sample ρ)
+              (fun r => if R x T r p then (1 : ℝ) else 0)))) := by
+      apply congrArg (ProbComp.expect (ProbComp.sample (Fin n × Bool)))
+      funext p
+      exact ProbComp.expect_sample_coord p
+        (fun x T => ProbComp.expect (ProbComp.sample ρ)
+          (fun r => if R x T r p then (1 : ℝ) else 0))
+        (fun x x' T => by
+          apply congrArg (ProbComp.expect (ProbComp.sample ρ))
+          funext r
+          rw [hinv x x' T r p])
+
+end TCSlib.Cryptography.Authentication.LamportFill
diff --git a/TCSlib/Cryptography/Authentication/Signatures/Lamport/TableCoins.lean b/TCSlib/Cryptography/Authentication/Signatures/Lamport/TableCoins.lean
new file mode 100644
index 000000000..87019f312
--- /dev/null
+++ b/TCSlib/Cryptography/Authentication/Signatures/Lamport/TableCoins.lean
@@ -0,0 +1,92 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+-/
+import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
+import TCSlib.Cryptography.Asymptotic.OneWay
+import Mathlib.Logic.Equiv.Prod
+import Mathlib.Tactic.Ring
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Lamport coin tapes as typed key tables
+
+## Main definitions
+
+* `tableCoins`: regroup a `2n²`-bit tape as the false and true `n`-bit preimages in each row.
+
+## Main results
+
+* `tableCoins_apply` and `tableCoins_symm`: the forward and inverse block equations.
+* `ofFn_tableCoins_symm`: the inverse equivalence serializes a table as `secretWord`.
+* `secretWord_tableCoins`: serializing the table of a tape recovers the tape's word.
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
+  2010, Protocol 137.1 and Theorem 137.2. This module is generic serialization glue for the
+  protocol's preimage table.
+-/
+
+namespace TCSlib.Cryptography.Authentication.LamportFill
+
+/-- The row-major tape width `n(2n)` equals the generator width `2n²`: `2 * n * n = n * (2 * n)`. -/
+theorem tableCoins_width (n : ℕ) : 2 * n * n = n * (2 * n) := by ring
+
+/-- A `2n²`-bit coin tape is equivalent to a table with an `n`-bit cell for each
+`(i,c) ∈ Fin n × Bool`. The first cell of each row is indexed by `false`, the second by
+`true`. Zero-width tapes and empty tables are included. -/
+def tableCoins (n : ℕ) : (Fin (2 * n * n) → Bool) ≃ Table n :=
+  ((((Equiv.arrowCongr (finCongr (tableCoins_width n)) (Equiv.refl Bool)).trans
+      (FunFamily.blocks n (2 * n))).trans
+      (Equiv.piCongrRight fun _ : Fin n =>
+        (FunFamily.blocks 2 n).trans
+          (Equiv.arrowCongr finTwoEquiv (Equiv.refl (Fin n → Bool))))).trans
+      (Equiv.curry (Fin n) Bool (Fin n → Bool)).symm)
+
+/-- The cell `(i,c)` of `tableCoins n x` is block `c` of the `i`th two-preimage row
+of `x`, with `false` selecting block zero and `true` block one: `tableCoins n x (i, c) =
+FunFamily.blocks 2 n (FunFamily.blocks n (2 * n) ((Equiv.arrowCongr (finCongr (tableCoins_width n))
+(Equiv.refl Bool)) x) i) (finTwoEquiv.symm c)`. -/
+theorem tableCoins_apply (n : ℕ) (x : Fin (2 * n * n) → Bool) (i : Fin n) (c : Bool) :
+    tableCoins n x (i, c) =
+      FunFamily.blocks 2 n
+        (FunFamily.blocks n (2 * n)
+          ((Equiv.arrowCongr (finCongr (tableCoins_width n)) (Equiv.refl Bool)) x) i)
+        (finTwoEquiv.symm c) := rfl
+
+/-- The inverse of `tableCoins` concatenates the two preimage cells of each row and then
+concatenates the rows, casting only between the equal widths `n(2n)` and `2n²`: `(tableCoins n).symm
+T = (Equiv.arrowCongr (finCongr (tableCoins_width n).symm) (Equiv.refl Bool)) ((FunFamily.blocks n
+(2 * n)).symm fun i => (FunFamily.blocks 2 n).symm fun j => T (i, finTwoEquiv j))`. -/
+theorem tableCoins_symm (n : ℕ) (T : Table n) :
+    (tableCoins n).symm T =
+      (Equiv.arrowCongr (finCongr (tableCoins_width n).symm) (Equiv.refl Bool))
+        ((FunFamily.blocks n (2 * n)).symm fun i =>
+          (FunFamily.blocks 2 n).symm fun j => T (i, finTwoEquiv j)) := rfl
+
+/-- The word of the inverse tape is exactly the row-major secret word:
+`List.ofFn ((tableCoins n).symm T) = secretWord T`.
+
+**Proof sketch.** Reading the width cast preserves the word. The block-equivalence inverse
+concatenates the words of its rows. Inside each row, the two-block inverse concatenates the
+false and true preimages, which is the published serialization equation for `secretWord`. -/
+theorem ofFn_tableCoins_symm {n : ℕ} (T : Table n) :
+    List.ofFn ((tableCoins n).symm T) = secretWord T := by
+  rw [tableCoins_symm, ofFn_arrowCongr_finCongr, FunFamily.ofFn_blocks_symm, secretWord_eq]
+  apply congrArg List.flatten
+  apply congrArg List.ofFn
+  funext i
+  rw [FunFamily.ofFn_blocks_symm, OneWay.flatten_ofFn_two]
+  rfl
+
+/-- Serializing the table obtained from a tape recovers the tape's word:
+`secretWord (tableCoins n x) = List.ofFn x`. -/
+theorem secretWord_tableCoins {n : ℕ} (x : Fin (2 * n * n) → Bool) :
+    secretWord (tableCoins n x) = List.ofFn x := by
+  rw [← ofFn_tableCoins_symm, Equiv.symm_apply_apply]
+
+end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Encoding
import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Advice
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Closing
import TCSlib.Cryptography.Authentication.Signatures.Lamport.InversionProbability
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lamport's one-time signatures

[PS10, Protocol 137.1]: for a one-way function `f`,
- `Gen(1^n)` samples `x_i^b ← U_n` for `i ∈ [n]` and `b ∈ {0, 1}`, and outputs
  `sk = (x_i^b)` and `pk = (f(x_i^b))`;
- `Sign_sk(m)` outputs `σ = (x_1^{m_1}, …, x_n^{m_n})`;
- `Ver_pk(m, σ)` accepts iff `f(σ_i) = f(x_i^{m_i})` for all `i`.

Theorem 137.2: if `f` is one-way, the scheme is one-time secure.

**The encoding.**
- `f` is a function family with `n`-bit inputs at parameter `n` (`lamportOWF`), given with a
  polynomial-time evaluator `E` on `⟨1^n, x⟩` that agrees with `f` on `n`-bit `x` (`hfE`, the
  form of `FunFamily.Easy`).
- The secret key is `Gen`'s `2n²` coins. Segment `i` (bits `2ni` to `2ni + 2n − 1`) is
  `x_i^0 ‖ x_i^1`.
- The public key is the tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩`, and a signature is the
  concatenation of the `n` revealed preimages: `n²` bits.
- The three algorithms are instances of the ch. 2–4 layer's block loop (`blockEncFun`), run over
  the message bits.

**Deviations, declared once here.**
- **`Ver` tests lengths first.** It rejects unless the message has `n` bits and the signature
  `n²`. So `E` is only ever evaluated on `n`-bit preimage candidates, where it agrees with `f`. An
  evaluator is unconstrained elsewhere, and a `Ver` evaluating it there could accept forgeries
  that do not invert `f`.
- **The one-way function is strong** ([PS10, Definition 27.3], `FunFamily.StrongOneWay`), the
  notes' "one-way function"; by §2.4 a weak one suffices.

## Contents

* `Signatures.Lamport.Encoding`: injectivity of the cryptographic tuple encoding.
* `Signatures.Lamport.Planted`: the typed planted experiment and safe-run coupling.
* `Signatures.Lamport.TableCoins`: the equivalence between key tapes and typed tables.
* `Signatures.Lamport.Averaging`: finite favourable-pair counting.
* `Signatures.Lamport.AveragingExtra`: optional-query counting and fixed-position selection.
* `Signatures.Lamport.Statistics`: independent-coordinate averaging.
* `Signatures.Lamport.Experiment`: the typed honest and planted probability bounds.
* `Signatures.Lamport.Advice`: binary advice and bounded decoding for the best position.
* `Signatures.Lamport.Blocks`: updating a fixed-width serialized tuple block.
* `Signatures.Lamport.Closing`: negligibility under the linear reduction loss.
* `Signatures.Lamport.InversionProbability`: transport to the actual machine inversion probability.
* `Signatures.Lamport.Machine`: the polynomial-time planting handler.
* `Signatures.Lamport.Seed`: the fair-bit and random-table seed equivalence.
* `Signatures.Lamport.MachineSpec`: functional contracts for planting, signing and extraction.
* `Signatures.Lamport.Nonabort`: nonaborting one-query runs have a safe query.
* `Signatures.Lamport.Realization`: T1 realization with an explicit coin equivalence.

## Main definitions

* `Authentication.lamportOWF`: `f` as a `FunFamily`.
* `Authentication.lamport`: Protocol 137.1 as a `SignatureScheme`, with correctness proved.

## Main results

* The ordinary `lamportHalf_eq`, emission and string-function equations expose the algorithms.
* `Authentication.lamportOWF_inLen`, `lamportOWF_outLen`, `lamportOWF_f`: the function-family fields.
* `Authentication.lamport_msgLen`, `lamport_sigLen`, `lamport_gen`, `lamport_sign`, `lamport_ver`:
  the signature-scheme data fields.
* `Authentication.lamportVerFun_sign`: correctness, `Ver` accepts honest signatures.
* `Authentication.lamport_oneTimeSecure` (Thm 137.2): one-time security from strong one-wayness.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.4, Protocol 137.1 and Theorem 137.2 (book pp. 136–138).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.PrivateKeyScheme (encodeList)

/-! ### Blocks and block loops -/

/-- The preimage `x_i^b` inside the segment `x_i^0 ‖ x_i^1` of `2n` bits. -/
def lamportHalf (n : ℕ) (b : Bool) (s : List Bool) : List Bool := if b then s.drop n else s.take n

/-- The selected preimage is the suffix after `n` bits for `true`, and the first `n` bits
for `false`. -/
theorem lamportHalf_eq (n : ℕ) (b : Bool) (s : List Bool) :
    lamportHalf n b s = if b then s.drop n else s.take n := rfl

/-- A half of a `2n`-bit segment has `n` bits. -/
theorem length_lamportHalf {n : ℕ} (b : Bool) {s : List Bool} (hs : s.length = 2 * n) :
    (lamportHalf n b s).length = n := by
  cases b <;> simp [lamportHalf, hs] <;> omega

/-- The concatenation of `q` blocks of `B` bits has `q · B` bits. -/
theorem length_flatten_ofFn {B : ℕ} : ∀ {q : ℕ} (g : Fin q → List Bool),
    (∀ i, (g i).length = B) → (List.ofFn g).flatten.length = q * B
  | 0, _, _ => by simp
  | q + 1, g, hg => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hg 0,
      length_flatten_ofFn (fun i => g i.succ) (fun i => hg i.succ), Nat.succ_mul]
    omega

/-- Segment `i` of the concatenation of `B`-bit blocks `g 0, …, g (q − 1)` is `g i`. -/
theorem coinBlock_flatten_ofFn {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ i, (g i).length = B)
    (i : Fin q) : coinBlock B i (List.ofFn g).flatten = g i := by
  rw [coinBlock_flatten (List.ofFn g) (fun c hc => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact hg j) i (by simp)]
  simp

/-- **The block loop over a message** (`blockEncFun` with one-bit blocks): its output is the
tuple of the emissions on the layouts `⟨⟨⟨u, ⟨pk, [m_i]⟩⟩, []⟩, segment i⟩`. -/
theorem blockEncFun_ofFn (G : List Bool → List Bool) (B : PolyExpr) (u pk : List Bool) {q : ℕ}
    (m : Fin q → Bool) (r : List Bool) :
    blockEncFun G (.const 1) B (blockState u pk (List.ofFn m) r) =
      encodeList (List.ofFn fun i : Fin q =>
        G (NUPPT.layout u (pairEncode pk [m i]) [] (coinBlock (B.eval u.length) i r))) := by
  have hlen : (List.ofFn m).length ≤ (blockState u pk (List.ofFn m) r).length := by
    simp only [blockState_eq, length_pairEncode, List.length_ofFn]
    omega
  rw [blockEncFun_eq]
  rw [blockEncFun_spec G (.const 1) B u pk (blockState u pk (List.ofFn m) r).length
    (List.ofFn m) r (by simpa using hlen)]
  simp only [PolyExpr.eval_const]
  rw [blockList_ofFn G _ u pk q m r _ (by simp only [List.length_ofFn] at hlen; omega)]

/-- **The tuple flattener** (`decListFun pairSndD`): on `⟨[], encodeList l⟩` it concatenates `l`. -/
theorem decListFun_pairSndD (l : List (List Bool)) :
    decListFun pairSndD (pairEncode [] (encodeList l)) = l.flatten := by
  have hlen : l.length ≤ (pairEncode [] (encodeList l)).length := by
    have := length_le_length_encodeList l
    simp only [length_pairEncode]
    omega
  rw [decListFun_eq]
  rw [decListFun_spec pairSndD [] _ l hlen]
  simp

/-! ### The algorithms as string functions -/

/-- `f(x)` on the layout `⟨⟨⟨1^n, y⟩, α⟩, x⟩`: `E(⟨1^n, x⟩)`. -/
def lamportEvalEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  E (pairEncode (NUPPT.inParam v) (NUPPT.inCoins v))

/-- The evaluation emission applies `E` to the parameter paired with the current coin block. -/
theorem lamportEvalEmit_eq (E : List Bool → List Bool) (v : List Bool) :
    lamportEvalEmit E v = E (pairEncode (NUPPT.inParam v) (NUPPT.inCoins v)) := rfl

/-- `Gen`'s emission on the layout `⟨⟨⟨1^n, y⟩, α⟩, x^0 ‖ x^1⟩`: the pair `⟨f(x^0), f(x^1)⟩`. -/
def lamportPairEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).take (NUPPT.inParam v).length)))
    (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).drop (NUPPT.inParam v).length)))

/-- The key-generation emission pairs the images of the first and second preimage blocks. -/
theorem lamportPairEmit_eq (E : List Bool → List Bool) (v : List Bool) :
    lamportPairEmit E v =
      pairEncode (E (pairEncode (NUPPT.inParam v)
          ((NUPPT.inCoins v).take (NUPPT.inParam v).length)))
        (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).drop (NUPPT.inParam v).length))) := rfl

/-- `Sign`'s emission on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, x^0 ‖ x^1⟩`: the preimage `x^b`. -/
def lamportSelEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then (NUPPT.inCoins v).drop (NUPPT.inParam v).length
  else (NUPPT.inCoins v).take (NUPPT.inParam v).length

/-- The signing emission chooses the second or first preimage block according to the message
bit in the argument. -/
theorem lamportSelEmit_eq (v : List Bool) :
    lamportSelEmit v =
      if (pairSndD (NUPPT.inArg v)).headD false then
        (NUPPT.inCoins v).drop (NUPPT.inParam v).length
      else (NUPPT.inCoins v).take (NUPPT.inParam v).length := rfl

/-- `Ver`'s selection on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, ⟨⟨y^0, y^1⟩, []⟩⟩` (a block of the
public key): `y^b`. -/
def lamportPkEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then pairSndD (pairFstD (NUPPT.inCoins v))
  else pairFstD (pairFstD (NUPPT.inCoins v))

/-- The public-key emission chooses the second or first image in the current encoded block
according to the message bit. -/
theorem lamportPkEmit_eq (v : List Bool) :
    lamportPkEmit v =
      if (pairSndD (NUPPT.inArg v)).headD false then pairSndD (pairFstD (NUPPT.inCoins v))
      else pairFstD (pairFstD (NUPPT.inCoins v)) := rfl

/-- The length of a public-key block `⟨⟨y^0, y^1⟩, []⟩` with `L`-bit images: `6L + 6`. -/
def lamportPkBlock (L : PolyExpr) : PolyExpr := .add (.mul (.const 6) L) (.const 6)

/-- The public-key block polynomial is `6L + 6`. -/
theorem lamportPkBlock_eq (L : PolyExpr) :
    lamportPkBlock L = .add (.mul (.const 6) L) (.const 6) := rfl

/-- `Gen` on the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with `2n²` coins `ρ`: `⟨pk, ρ⟩`, where `pk` is the
tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the `2n`-bit segments of `ρ`. -/
def lamportGenFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (blockEncFun (lamportPairEmit E) (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (List.replicate (NUPPT.inParam z).length true)
        (NUPPT.inCoins z)))
    (NUPPT.inCoins z)

/-- The generator word pairs the public-key block-loop output with the original preimage tape. -/
theorem lamportGenFun_eq (E : List Bool → List Bool) (z : List Bool) :
    lamportGenFun E z =
      pairEncode
        (blockEncFun (lamportPairEmit E) (.const 1) (.mul (.const 2) .var)
          (blockState (NUPPT.inParam z) [] (List.replicate (NUPPT.inParam z).length true)
            (NUPPT.inCoins z)))
        (NUPPT.inCoins z) := rfl

/-- `Sign` on the layout `⟨⟨⟨1^n, ⟨sk, m⟩⟩, α⟩, r⟩`: the concatenation of the `x_i^{m_i}`. -/
def lamportSignFun (z : List Bool) : List Bool :=
  decListFun pairSndD (pairEncode []
    (blockEncFun lamportSelEmit (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (pairSndD (NUPPT.inArg z)) (pairFstD (NUPPT.inArg z)))))

/-- The signing word concatenates the preimage blocks selected by the message bits. -/
theorem lamportSignFun_eq (z : List Bool) :
    lamportSignFun z =
      decListFun pairSndD (pairEncode []
        (blockEncFun lamportSelEmit (.const 1) (.mul (.const 2) .var)
          (blockState (NUPPT.inParam z) [] (pairSndD (NUPPT.inArg z))
            (pairFstD (NUPPT.inArg z))))) := rfl

/-- `Ver` on `⟨1^n, ⟨pk, ⟨m, σ⟩⟩⟩`: `[true]` iff `m` has `n` bits, `σ` has `n²` bits, and the
images of the `n`-bit blocks of `σ` are the public-key entries selected by `m`. -/
def lamportVerFun (L : PolyExpr) (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  [(decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length) &&
      decide ((pairSndD (pairSndD (pairSndD w))).length =
        (pairFstD w).length * (pairFstD w).length)) &&
    decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
        (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
          (pairSndD (pairSndD (pairSndD w)))) =
      blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
        (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w))) (pairFstD (pairSndD w))))]

/-- Verification conjoins the message and signature length tests with equality of the
signature-image word and the selected public-key word. -/
theorem lamportVerFun_eq (L : PolyExpr) (E : List Bool → List Bool) (w : List Bool) :
    lamportVerFun L E w =
      [(decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length) &&
          decide ((pairSndD (pairSndD (pairSndD w))).length =
            (pairFstD w).length * (pairFstD w).length)) &&
        decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
            (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
              (pairSndD (pairSndD (pairSndD w)))) =
          blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
            (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
              (pairFstD (pairSndD w))))] := rfl

/-! ### Efficiency -/

section Efficiency

variable {E : List Bool → List Bool} (hE : PolyTimeComputable E)

include hE in
/-- `f(x)` on a layout is polynomial-time. -/
theorem polyTimeComputable_lamportEvalEmit : PolyTimeComputable (lamportEvalEmit E) :=
  hE.comp (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)

include hE in
/-- `Gen`'s emission is polynomial-time. -/
theorem polyTimeComputable_lamportPairEmit : PolyTimeComputable (lamportPairEmit E) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hp := hu.pairEncode NUPPT.polyTimeComputable_inCoins
  have h := (hE.comp (hu.pairEncode ((polyTimeComputable_pairTakePoly .var).comp hp))).pairEncode
    (hE.comp (hu.pairEncode ((polyTimeComputable_pairDropPoly .var).comp hp)))
  convert h using 1
  funext v
  simp [lamportPairEmit, Function.comp_apply]

/-- `Sign`'s emission is polynomial-time. -/
theorem polyTimeComputable_lamportSelEmit : PolyTimeComputable lamportSelEmit := by
  have hp := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have h := polyTimeComputable_ite
    (polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    ((polyTimeComputable_pairDropPoly .var).comp hp)
    ((polyTimeComputable_pairTakePoly .var).comp hp)
  convert h using 1
  funext v
  simp [lamportSelEmit, Function.comp_apply]

/-- `Ver`'s selection is polynomial-time. -/
theorem polyTimeComputable_lamportPkEmit : PolyTimeComputable lamportPkEmit := by
  have hc := NUPPT.polyTimeComputable_inCoins
  have h := polyTimeComputable_ite
    (polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hc)
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp hc)
  convert h using 1

include hE in
/-- `Gen` is polynomial-time. -/
theorem polyTimeComputable_lamportGenFun : PolyTimeComputable (lamportGenFun E) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hst := hu.pairEncode ((polyTimeComputable_const []).pairEncode
    ((polyTimeComputable_unary.comp hu).pairEncode NUPPT.polyTimeComputable_inCoins))
  have h := ((blockEncFun_poly (polyTimeComputable_lamportPairEmit hE) (.const 1)
    (.mul (.const 2) .var)).comp hst).pairEncode NUPPT.polyTimeComputable_inCoins
  refine h.congr fun z => ?_
  simp only [lamportGenFun_eq, blockState_eq, Function.comp_apply]

/-- `Sign` is polynomial-time. -/
theorem polyTimeComputable_lamportSignFun : PolyTimeComputable lamportSignFun := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hArg := NUPPT.polyTimeComputable_inArg
  have hst := hu.pairEncode ((polyTimeComputable_const []).pairEncode
    ((polyTimeComputable_pairSndD.comp hArg).pairEncode (polyTimeComputable_pairFstD.comp hArg)))
  have h := (decListFun_poly polyTimeComputable_pairSndD).comp
    ((polyTimeComputable_const []).pairEncode
      ((blockEncFun_poly polyTimeComputable_lamportSelEmit (.const 1)
        (.mul (.const 2) .var)).comp hst))
  refine h.congr fun z => ?_
  simp only [lamportSignFun_eq, blockState_eq, Function.comp_apply]

include hE in
/-- `Ver` is polynomial-time: two length tests (`polyTimeComputable_lenEq`) and an equality of
two block loops (`polyTimeComputable_pairEq`).

**Proof sketch.** Project the parameter, public key, message and signature from the input.
Compare the message length with `n` and the signature length with `n²`, representing the latter
bound by a unary square. The two polynomial-time block loops produce the images of the
signature blocks and the public-key entries selected by the message. Compare these two words
and conjoin the result with the length tests. -/
theorem polyTimeComputable_lamportVerFun (L : PolyExpr) :
    PolyTimeComputable (lamportVerFun L E) := by
  have hu := polyTimeComputable_pairFstD
  have hpk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hσ := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h₁ : PolyTimeComputable fun w =>
      [decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length)] := by
    convert polyTimeComputable_lenEq.comp (hm.pairEncode hu) using 1
    funext w
    simp [Function.comp_apply]
  have h₂ : PolyTimeComputable fun w =>
      [decide ((pairSndD (pairSndD (pairSndD w))).length =
        (pairFstD w).length * (pairFstD w).length)] := by
    convert polyTimeComputable_lenEq.comp
      (hσ.pairEncode ((polyTimeComputable_unaryPoly (.mul .var .var)).comp hu)) using 1
    funext w
    simp [Function.comp_apply]
  have hX := (blockEncFun_poly (polyTimeComputable_lamportEvalEmit hE) (.const 1) .var).comp
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (hm.pairEncode hσ)))
  have hY := (blockEncFun_poly polyTimeComputable_lamportPkEmit (.const 1)
    (lamportPkBlock L)).comp
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (hm.pairEncode hpk)))
  have h₃ : PolyTimeComputable fun w =>
      [decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
          (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
            (pairSndD (pairSndD (pairSndD w)))) =
        blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
          (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
            (pairFstD (pairSndD w))))] := by
    refine (polyTimeComputable_pairEq.comp (hX.pairEncode hY)).congr fun w => ?_
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    apply congrArg (fun b : Bool => [b])
    apply decide_eq_decide.mpr
    simp only [blockState_eq]
  exact polyTimeComputable_and (polyTimeComputable_and h₁ h₂) h₃

/-! ### The machines -/

/-- The machine `Gen`, with `2n²` coins. -/
noncomputable def lamportGen : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_lamportGenFun hE) (.mul (.mul (.const 2) .var) .var)

/-- The machine `Sign`, deterministic. -/
noncomputable def lamportSign : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_lamportSignFun (.const 0)

/-- Lamport's generator uses the coin polynomial `2n²`: `(lamportGen hE).coins = .mul (.mul
(.const 2) .var) .var`. -/
theorem lamportGen_coins : (lamportGen hE).coins = .mul (.mul (.const 2) .var) .var := by
  unfold lamportGen
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- The generator's coin tape has `2n²` bits at parameter `n`: `(lamportGen hE).coinLen n = 2 * n *
n`. -/
theorem lamportGen_coinLen (n : ℕ) : (lamportGen hE).coinLen n = 2 * n * n := by
  rw [NUPPT.coinLen_eq, lamportGen_coins]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]

/-- Lamport's generator coin tapes are equivalent to its row-major preimage tables:
`lamportCoinTables hE n : (lamportGen hE).Coins n ≃ Table n`. -/
noncomputable def lamportCoinTables (n : ℕ) : (lamportGen hE).Coins n ≃ LamportFill.Table n :=
  (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl Bool)).trans
    (LamportFill.tableCoins n)

/-- The coin-table equivalence first casts the tape width to `2n²`, then groups its blocks:
`lamportCoinTables hE n = (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl
Bool)).trans (tableCoins n)`. -/
theorem lamportCoinTables_eq (n : ℕ) :
    lamportCoinTables hE n =
      (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl Bool)).trans
        (LamportFill.tableCoins n) := rfl

/-- The inverse coin-table equivalence serializes the table and casts back to the generator's
declared coin length: `(lamportCoinTables hE n).symm T = (Equiv.arrowCongr (finCongr
(lamportGen_coinLen hE n).symm) (Equiv.refl Bool)) ((tableCoins n).symm T)`. -/
theorem lamportCoinTables_symm (n : ℕ) (T : LamportFill.Table n) :
    (lamportCoinTables hE n).symm T =
      (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n).symm) (Equiv.refl Bool))
        ((LamportFill.tableCoins n).symm T) := rfl

/-- The coin tape for table `T` is exactly its row-major secret word: `List.ofFn ((lamportCoinTables
hE n).symm T) = secretWord T`. -/
theorem ofFn_lamportCoinTables_symm (n : ℕ) (T : LamportFill.Table n) :
    List.ofFn ((lamportCoinTables hE n).symm T) = LamportFill.secretWord T := by
  rw [lamportCoinTables_symm, ofFn_arrowCongr_finCongr, LamportFill.ofFn_tableCoins_symm]

/-- Serializing the table of a generator coin tape recovers that tape's word: `secretWord
(lamportCoinTables hE n ρ) = List.ofFn ρ`. -/
theorem secretWord_lamportCoinTables (n : ℕ) (ρ : (lamportGen hE).Coins n) :
    LamportFill.secretWord (lamportCoinTables hE n ρ) = List.ofFn ρ := by
  rw [← ofFn_lamportCoinTables_symm, Equiv.symm_apply_apply]

/-- Lamport's deterministic signer uses the zero coin polynomial: `lamportSign.coins = .const 0`. -/
theorem lamportSign_coins : lamportSign.coins = .const 0 := by
  unfold lamportSign
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- `Gen` on coins `ρ`: `⟨pk, ρ⟩`, `pk` the tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the
`2n`-bit segments `x_i^0 ‖ x_i^1` of `ρ`. -/
theorem runAt_lamportGen (n : ℕ) (ρ : (lamportGen hE).Coins n) :
    (lamportGen hE).runAt n [] ρ =
      pairEncode (encodeList (List.ofFn fun i : Fin n =>
          pairEncode
            (E (pairEncode (List.replicate n true) (lamportHalf n false
              (coinBlock (2 * n) i (List.ofFn ρ)))))
            (E (pairEncode (List.replicate n true) (lamportHalf n true
              (coinBlock (2 * n) i (List.ofFn ρ)))))))
        (List.ofFn ρ) := by
  rw [NUPPT.runAt_eq]
  unfold lamportGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [lamportGenFun, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]
  rw [show blockState (List.replicate n true) [] (List.replicate n true) (List.ofFn ρ) =
    blockState (List.replicate n true) [] (List.ofFn fun _ : Fin n => true) (List.ofFn ρ) by simp,
    blockEncFun_ofFn]
  simp [lamportPairEmit, lamportHalf]

/-- `Sign` on `⟨sk, m⟩`: the concatenation of the halves `x_i^{m_i}` of the `2n`-bit segments
of `sk`. -/
theorem runAt_lamportSign (n : ℕ) (sk : List Bool) (m : Fin n → Bool)
    (r : lamportSign.Coins n) :
    lamportSign.runAt n (pairEncode sk (List.ofFn m)) r =
      (List.ofFn fun i : Fin n => lamportHalf n (m i) (coinBlock (2 * n) i sk)).flatten := by
  rw [NUPPT.runAt_eq]
  unfold lamportSign
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [lamportSignFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode,
    pairSndD_pairEncode]
  rw [blockEncFun_ofFn, decListFun_pairSndD]
  congr 1
  simp [lamportSelEmit, lamportHalf]

end Efficiency

/-! ### The scheme -/

variable (L : PolyExpr) (f : ∀ n, (Fin n → Bool) → (Fin (L.eval n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hfE : ∀ n (x : Fin n → Bool), E (NUPPT.advInput n (List.ofFn x)) = List.ofFn (f n x))

/-- **The one-way function of Protocol 137.1** as a function family: `n`-bit inputs and
`L(n)`-bit outputs at parameter `n`. -/
def lamportOWF : FunFamily where
  inLen := .var
  outLen := L
  f := f

/-- Lamport's function family has input-length polynomial `n`. -/
theorem lamportOWF_inLen : (lamportOWF L f).inLen = .var := rfl

/-- Lamport's function family retains the supplied output-length polynomial `L`. -/
theorem lamportOWF_outLen : (lamportOWF L f).outLen = L := rfl

/-- Lamport's function family retains the supplied family `f`. -/
theorem lamportOWF_f : (lamportOWF L f).f = f := rfl

include hfE in
/-- On `n`-bit inputs, `E` returns `L(n)` bits (it agrees with `f`). -/
theorem length_lamportEval {n : ℕ} {x : List Bool} (hx : x.length = n) :
    (E (pairEncode (List.replicate n true) x)).length = L.eval n := by
  have h := hfE n (padFin n x)
  have hx' := Collection.ofFn_padFin_of_le (le_of_eq hx)
  simp only [hx, Nat.sub_self, List.replicate_zero, List.append_nil] at hx'
  rw [hx'] at h
  simp only [NUPPT.advInput_eq] at h
  rw [h, List.length_ofFn]

include hfE in
/-- **Correctness**: `Ver` accepts `Sign`'s signature under the generated keys.

**Proof sketch.** `runAt_lamportGen` and `runAt_lamportSign` unfold the keys and the signature.
The length tests pass (`length_flatten_ofFn`). On both sides of `Ver`'s equality, the block loop
is a tuple over the message bits (`blockEncFun_ofFn`). Block `i` of the signature is
`x_i^{m_i}` (`coinBlock_flatten_ofFn`); block `i` of the public key is the pair
`⟨f(x_i^0), f(x_i^1)⟩`, of `6L + 6` bits (`length_lamportEval`). Both entries are `f(x_i^{m_i})`. -/
theorem lamportVerFun_sign (n : ℕ) (m : Fin n → Bool) (rg : (lamportGen hE).Coins n)
    (rs : lamportSign.Coins n) :
    lamportVerFun L E (atParam n (pairEncode (pairFstD ((lamportGen hE).runAt n [] rg))
      (pairEncode (List.ofFn m) (List.ofFn (padFin (n * n) (lamportSign.runAt n
        (pairEncode (pairSndD ((lamportGen hE).runAt n [] rg)) (List.ofFn m)) rs)))))) =
      [true] := by
  rw [runAt_lamportGen]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [runAt_lamportSign]
  have hρ : (List.ofFn rg).length = 2 * n * n := by
    refine (List.length_ofFn (f := rg)).trans
      (((lamportGen hE).coinLen_eq n).trans ?_)
    simp only [lamportGen, NUPPT.coins_ofPolyTimeUniform,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hseg : ∀ i : Fin n, (coinBlock (2 * n) i (List.ofFn rg)).length = 2 * n := by
    intro i
    apply length_coinBlock
    rw [hρ]
    have := i.isLt
    nlinarith
  have hsel : ∀ i : Fin n, (lamportHalf n (m i) (coinBlock (2 * n) i (List.ofFn rg))).length = n :=
    fun i => length_lamportHalf _ (hseg i)
  have hσ := length_flatten_ofFn _ hsel
  have hpad := Collection.ofFn_padFin_of_le (le_of_eq hσ)
  simp only [hσ, Nat.sub_self, List.replicate_zero, List.append_nil] at hpad
  rw [hpad]
  have hy : ∀ (b : Bool) (i : Fin n), (E (pairEncode (List.replicate n true)
      (lamportHalf n b (coinBlock (2 * n) i (List.ofFn rg))))).length = L.eval n :=
    fun b i => length_lamportEval L f E hfE (length_lamportHalf b (hseg i))
  have hpk : ∀ i : Fin n, (pairEncode (pairEncode
      (E (pairEncode (List.replicate n true) (lamportHalf n false
        (coinBlock (2 * n) i (List.ofFn rg)))))
      (E (pairEncode (List.replicate n true) (lamportHalf n true
        (coinBlock (2 * n) i (List.ofFn rg)))))) []).length =
      (lamportPkBlock L).eval n := by
    intro i
    simp only [length_pairEncode, hy, lamportPkBlock, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, List.length_nil]
    ring
  simp only [lamportVerFun, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_ofFn, hσ, decide_true, Bool.true_and, List.cons.injEq,
    and_true, decide_eq_true_eq]
  have hflat : ∀ g : Fin n → List Bool,
      encodeList (List.ofFn g) = (List.ofFn fun i => pairEncode (g i) []).flatten := by
    intro g
    rw [encodeList_eq_flatMap]
    simp [List.flatMap_def, List.map_ofFn, Function.comp_def]
  rw [hflat, blockEncFun_ofFn, blockEncFun_ofFn]
  congr 1
  congr 1
  funext i
  simp only [lamportEvalEmit, lamportPkEmit, NUPPT.inParam_layout, NUPPT.inCoins_layout,
    NUPPT.inArg_layout, pairSndD_pairEncode, List.headD_cons, PolyExpr.eval_var,
    List.length_replicate]
  rw [coinBlock_flatten_ofFn _ hsel i, coinBlock_flatten_ofFn _ hpk i]
  cases m i <;> simp [lamportHalf]

include hfE in
/-- **Lamport's one-time signature scheme** [PS10, Protocol 137.1] for `f` with evaluator `E`:
`n`-bit messages, `n²`-bit signatures. -/
noncomputable def lamport : SignatureScheme where
  msgLen := .var
  sigLen := .mul .var .var
  gen := lamportGen hE
  sign := lamportSign
  ver := lamportVerFun L E
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sign_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  ver_poly := polyTimeComputable_lamportVerFun hE L
  correct := fun n m rg rs => lamportVerFun_sign L f E hE hfE n m rg rs

/-- Lamport signs messages of length `n`. -/
theorem lamport_msgLen : (lamport L f E hE hfE).msgLen = .var := rfl

/-- Lamport's signature-length polynomial is `n²`. -/
theorem lamport_sigLen : (lamport L f E hE hfE).sigLen = .mul .var .var := rfl

/-- Lamport uses its preimage-pair generator as the scheme's key generator. -/
theorem lamport_gen : (lamport L f E hE hfE).gen = lamportGen hE := rfl

/-- Lamport uses its deterministic selected-preimage signer. -/
theorem lamport_sign : (lamport L f E hE hfE).sign = lamportSign := rfl

/-- Lamport uses its length-guarded block verifier. -/
theorem lamport_ver : (lamport L f E hE hfE).ver = lamportVerFun L E := rfl

include hfE in
/-- On a serialized preimage table, key generation returns its public images and the table itself
[PS10, Protocol 137.1]: if `List.ofFn ρ = secretWord T`, then `(lamportGen hE).runAt n [] ρ =
pairEncode (publicWord (tablePublic (f n) T)) (secretWord T)`.

**Proof sketch.** Block `i` of `secretWord T` is `T (i, false) ‖ T (i, true)`
(`coinBlock_flatten_ofFn`); `lamportHalf` reads its halves, and `hfE` maps them to their images. -/
theorem runAt_lamportGen_table (n : ℕ) (T : LamportFill.Table n)
    (ρ : (lamportGen hE).Coins n) (hρ : List.ofFn ρ = LamportFill.secretWord T) :
    (lamportGen hE).runAt n [] ρ =
      pairEncode (LamportFill.publicWord (LamportFill.tablePublic (f n) T))
        (LamportFill.secretWord T) := by
  have hrow (i : Fin n) :
      (List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).length = 2 * n := by
    simp only [List.length_append, List.length_ofFn]
    omega
  have hhalf (i : Fin n) (b : Bool) :
      lamportHalf n b (coinBlock (2 * n) i (LamportFill.secretWord T)) =
        List.ofFn (T (i, b)) := by
    rw [LamportFill.secretWord_eq, coinBlock_flatten_ofFn _ hrow i]
    cases b <;> simp [lamportHalf_eq]
  have hE' (x : Fin n → Bool) :
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
    simpa only [NUPPT.advInput_eq] using hfE n x
  rw [runAt_lamportGen, hρ, LamportFill.publicWord_eq]
  congr 1
  apply congrArg encodeList
  apply congrArg List.ofFn
  funext i
  rw [hhalf i false, hhalf i true, hE', hE',
    LamportFill.tablePublic_eq, LamportFill.tablePublic_eq]

/-- On a serialized preimage table, signing returns the typed signature selected from that table,
independently of its signing coins [PS10, Protocol 137.1]: `lamportSign.runAt n (pairEncode
(secretWord T) (List.ofFn m)) r = List.ofFn (tableSignature T m)`. -/
theorem runAt_lamportSign_table (n : ℕ) (T : LamportFill.Table n) (m : Fin n → Bool)
    (r : lamportSign.Coins n) :
    lamportSign.runAt n (pairEncode (LamportFill.secretWord T) (List.ofFn m)) r =
      List.ofFn (LamportFill.tableSignature T m) := by
  rw [runAt_lamportSign, LamportFill.ofFn_tableSignature]
  have hrow (i : Fin n) :
      (List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).length = 2 * n := by
    simp only [List.length_append, List.length_ofFn]
    omega
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [LamportFill.secretWord_eq, coinBlock_flatten_ofFn _ hrow i]
  cases m i <;> simp [lamportHalf_eq]

include hE hfE in
/-- On the canonical layout of a table, the generator string function returns its public images
paired with its secret serialization [PS10, Protocol 137.1]: `lamportGenFun E (NUPPT.layout
(List.replicate n true) [] [] (secretWord T)) = pairEncode (publicWord (tablePublic (f n) T))
(secretWord T)`. -/
theorem lamportGenFun_table (n : ℕ) (T : LamportFill.Table n) :
    lamportGenFun E (NUPPT.layout (List.replicate n true) [] [] (LamportFill.secretWord T)) =
      pairEncode (LamportFill.publicWord (LamportFill.tablePublic (f n) T))
        (LamportFill.secretWord T) := by
  have h := runAt_lamportGen_table L f E hE hfE n T
    ((lamportCoinTables hE n).symm T) (ofFn_lamportCoinTables_symm hE n T)
  rw [NUPPT.runAt_eq] at h
  rw [ofFn_lamportCoinTables_symm (E := E) hE n T] at h
  unfold lamportGen at h
  rw [NUPPT.runAtL_ofPolyTimeUniform] at h
  simpa only [NUPPT.layout_eq, NUPPT.advInput_eq] using h

/-- On the canonical signing layout, the signing string function returns the selected preimage
vector [PS10, Protocol 137.1]: `lamportSignFun (NUPPT.layout (List.replicate n true) (pairEncode
(secretWord T) (List.ofFn m)) [] []) = List.ofFn (tableSignature T m)`. -/
theorem lamportSignFun_table (n : ℕ) (T : LamportFill.Table n) (m : Fin n → Bool) :
    lamportSignFun (NUPPT.layout (List.replicate n true)
      (pairEncode (LamportFill.secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (LamportFill.tableSignature T m) := by
  let r : lamportSign.Coins n := fun _ => false
  have hr : List.ofFn r = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_ofFn, NUPPT.coinLen_eq, lamportSign_coins, PolyExpr.eval_const]
  have h := runAt_lamportSign_table n T m r
  rw [NUPPT.runAt_eq] at h
  unfold lamportSign at h
  rw [NUPPT.runAtL_ofPolyTimeUniform, hr] at h
  simpa only [NUPPT.layout_eq, NUPPT.advInput_eq] using h

include hfE in
/-- Verification of a typed public table accepts exactly when each signature block maps to the image
selected by the corresponding message bit [PS10, Protocol 137.1]: `lamportVerFun L E (atParam n
(pairEncode (publicWord Y) (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] ↔ ∀ i, f n
(signatureBlock σ i) = Y (i, m i)`.

**Proof sketch.** Both length guards pass. The two block loops are tuple encodings of
the signature-block images and selected public images. Injectivity of the tuple encoding
and of bit-vector serialization turns their equality into coordinatewise equality. -/
theorem lamportVerFun_publicWord_iff (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (m : Fin n → Bool)
    (σ : Fin (n * n) → Bool) :
    lamportVerFun L E (atParam n (pairEncode (LamportFill.publicWord Y)
      (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] ↔
      ∀ i, f n (LamportFill.signatureBlock σ i) = Y (i, m i) := by
  have hb : FunFamily.blocks n n σ = fun i => LamportFill.signatureBlock σ i := by
    funext i k
    rw [FunFamily.blocks_apply, LamportFill.signatureBlock_eq]
  have hσ := FunFamily.ofFn_blocks_symm n n (FunFamily.blocks n n σ)
  rw [Equiv.symm_apply_apply, hb] at hσ
  have hsig (i : Fin n) : (List.ofFn (LamportFill.signatureBlock σ i)).length = n :=
    List.length_ofFn
  have hpk (i : Fin n) :
      (pairEncode (pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) []).length =
        (lamportPkBlock L).eval n := by
    simp only [length_pairEncode, List.length_ofFn, List.length_nil, lamportPkBlock_eq,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    ring
  have hE' (x : Fin n → Bool) :
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
    simpa only [NUPPT.advInput_eq] using hfE n x
  simp only [lamportVerFun_eq, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_ofFn, decide_true, Bool.true_and,
    List.cons.injEq, and_true, decide_eq_true_eq]
  rw [LamportFill.publicWord_flatten, hσ, blockEncFun_ofFn, blockEncFun_ofFn]
  have hleft : (fun i : Fin n =>
      lamportEvalEmit E (NUPPT.layout (List.replicate n true) (pairEncode [] [m i]) []
        (coinBlock n i (List.ofFn fun j => List.ofFn (LamportFill.signatureBlock σ j)).flatten))) =
        fun i => List.ofFn (f n (LamportFill.signatureBlock σ i)) := by
    funext i
    simp only [lamportEvalEmit_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout]
    rw [coinBlock_flatten_ofFn _ hsig i, hE']
  have hright : (fun i : Fin n =>
      lamportPkEmit (NUPPT.layout (List.replicate n true) (pairEncode [] [m i]) []
        (coinBlock ((lamportPkBlock L).eval n) i
          (List.ofFn fun j => pairEncode
            (pairEncode (List.ofFn (Y (j, false))) (List.ofFn (Y (j, true)))) []).flatten))) =
        fun i => List.ofFn (Y (i, m i)) := by
    funext i
    rw [coinBlock_flatten_ofFn _ hpk i]
    simp only [lamportPkEmit_eq, NUPPT.inArg_layout, NUPPT.inCoins_layout,
      pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons]
    cases m i <;> rfl
  simp only [PolyExpr.eval_var, List.length_replicate]
  rw [hleft, hright, LamportReduction.encodeList_ofFn_eq_iff]
  constructor
  · intro h i
    exact List.ofFn_injective (congrFun h i)
  · intro h
    funext i
    exact congrArg List.ofFn (h i)


/-- Machine codecs with equal move decoders, entry encoders and timeout values are equal. -/
private theorem lamport_codec_ext {ι α : Type} {spec : OracleSpec ι}
    (a b : MachineCodec spec α) (hd : a.decodeMove = b.decodeMove)
    (he : a.encodeEntry = b.encodeEntry) (ht : a.timeout = b.timeout) : a = b := by
  cases a
  cases b
  cases hd
  cases he
  cases ht
  rfl

/-- Lamport's forger codec is the canonical bit codec with query width `n`, answer width `n²` and
final width `n+n²`: `(lamport L f E hE hfE).forgerCodec n = bitCodec (fun _ : Fin 1 => n) (fun _ =>
n * n) (n + n * n)`. -/
theorem lamport_forgerCodec (n : ℕ) :
    (lamport L f E hE hfE).forgerCodec n =
      bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n) := by
  apply lamport_codec_ext
  · funext w
    rw [SignatureScheme.forgerCodec_decodeMove, bitCodec_decodeMove]
    simp only [lamport_msgLen, lamport_sigLen, PolyExpr.eval_var, PolyExpr.eval_mul]
  · funext e
    rw [SignatureScheme.forgerCodec_encodeEntry, bitCodec_encodeEntry]
  · rw [SignatureScheme.forgerCodec_timeout, bitCodec_timeout]
    simp only [lamport_msgLen, lamport_sigLen, PolyExpr.eval_var, PolyExpr.eval_mul]

-- Probability proofs read their laws rather than reducing the sample interpreter.
run_cmd do
  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))

/-- Against a serialized key table, every Lamport signing call has exactly the deterministic
selected-preimage law. The equality holds for every function of the answer and state:
`ProbComp.expect ((lamport L f E hE hfE).signImpl n (secretWord T) i m s) G = ProbComp.expect
(tableSigner T i m s) G`. -/
theorem lamport_signImpl_expect (n : ℕ) (T : LamportFill.Table n)
    (i : Fin 1) (m : Fin n → Bool) (s : Unit)
    (G : (Fin (n * n) → Bool) × Unit → ℝ) :
    ProbComp.expect
        ((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T) i m s) G =
      ProbComp.expect (LamportFill.tableSigner T i m s) G := by
  rw [SignatureScheme.signImpl_eq, LamportFill.tableSigner_eq]
  simp only [QueryImpl.ofComp_apply, ProbComp.expect_bind, ProbComp.expect_pure,
    lamport_sign, lamport_sigLen, PolyExpr.eval_mul, PolyExpr.eval_var,
    runAt_lamportSign_table, padFin_ofFn]
  exact ProbComp.expect_const _ _

/-- Logging preserves the equality between actual Lamport signing and typed table signing, including
the full appended query and answer log: `ProbComp.expect (((lamport L f E hE hfE).signImpl n
(secretWord T)).withLog i m s) G = ProbComp.expect ((tableSigner T).withLog i m s) G`. -/
theorem lamport_loggedSignImpl_expect (n : ℕ) (T : LamportFill.Table n)
    (i : Fin 1) (m : Fin n → Bool)
    (s : Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)))
    (G : (Fin (n * n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))) → ℝ) :
    ProbComp.expect
        (((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T)).withLog i m s) G =
      ProbComp.expect ((LamportFill.tableSigner T).withLog i m s) G := by
  simp only [QueryImpl.withLog_apply, ProbComp.expect_bind]
  exact lamport_signImpl_expect (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE)
    n T i m s.1 (fun ys =>
      ProbComp.expect (.pure (ys.1, (ys.2, s.2 ++ [⟨i, m, ys.1⟩]))) G)

include hfE in
/-- The actual one-query Lamport forgery game has exactly the typed honest-table success probability
[PS10, Definition 136.2 and proof of Theorem 137.2]: `accept ((lamport L f E hE hfE).forgeGame A 1
n) = honestProbability (f n) adv`, where `adv Y r = A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _
=> n * n) (n + n * n)) n 1 (publicWord Y) r`.

**Proof sketch.** Reindex key-generation coins by the table equivalence and use the generator
reader to identify public and secret keys. The signing machine ignores its signing coins, so
its call expectation is the deterministic table signer's expectation; the simulation
congruence theorem lifts this equality to the logged forger execution. The one-query
transcript reader identifies its output and first-query log. Finally the verifier reader
identifies acceptance with coordinatewise verification, and the freshness reader identifies
absence from the log with inequality to the optional query. -/
theorem lamport_forgeGame_accept_eq_honestProbability (A : NUPPT) (n : ℕ) :
    accept ((lamport L f E hE hfE).forgeGame A 1 n) =
      LamportFill.honestProbability (f n)
        (fun Y r => A.toCompOn
          (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
          n 1 (LamportFill.publicWord Y) r) := by
  classical
  rw [accept_eq, SignatureScheme.forgeGame_eq]
  simp only [ProbComp.prob_bind, ProbComp.prob_pure, decide_eq_true_eq,
    lamport_gen, lamport_forgerCodec]
  rw [← ProbComp.expect_sample_equiv (lamportCoinTables hE n).symm,
    LamportFill.honestProbability_eq]
  apply congrArg (ProbComp.expect (ProbComp.sample (LamportFill.Table n)))
  funext T
  have hgen := runAt_lamportGen_table
    (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE) n T
    ((lamportCoinTables hE n).symm T) (ofFn_lamportCoinTables_symm hE n T)
  rw [hgen, pairFstD_pairEncode, pairSndD_pairEncode]
  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
  funext r
  let codec := bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n)
  let tree := A.toCompOn codec n 1
    (LamportFill.publicWord (LamportFill.tablePublic (f n) T)) r
  have hcost : tree.CostBoundedBy (fun _ => 1) 1 :=
    A.toCompOn_costBoundedBy codec n 1 _ r
  have hsim (G : (Fin (n + n * n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))) → ℝ) :=
    ProbComp.expect_simulate_congr
      (((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T)).withLog)
      ((LamportFill.tableSigner T).withLog)
      (fun i m s H => lamport_loggedSignImpl_expect
        (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE) n T i m s H)
      tree ((), []) G
  rw [hsim, LamportFill.honest_transcript T tree hcost, ProbComp.expect_pure]
  simp only [SignatureScheme.accepts_iff, lamport_ver,
    lamportVerFun_publicWord_iff (L := L) (f := f) (E := E) (hfE := hfE),
    LamportFill.tablePublic_eq,
    LamportFill.honestSuccess_iff, LamportFill.honestOutput_eq]
  apply if_congr ?_ rfl rfl
  apply and_congr_right
  intro _
  exact LamportFill.fresh_firstLog_iff T tree _


/-- For every positive parameter, some fixed position with a fair planted bit gives reduction
success at least the actual one-query forgery probability divided by `2n` [PS10, averaging step in
the proof of Theorem 137.2]: if `0 < n`, then `∃ i : Fin n, accept ((lamport L f E hE hfE).forgeGame
A 1 n) / (2 * (n : ℝ)) ≤ ProbComp.expect (ProbComp.sample Bool) (fun c => redProbability (f n) adv
(i, c))`, with `adv` as in `lamport_forgeGame_accept_eq_honestProbability`.

**Proof sketch.** Read the actual forgery game as the typed honest probability, then apply
the counted favorable-pair bound and select a position at least as good as its average. -/
theorem lamport_exists_best_position (A : NUPPT) (n : ℕ) (hn : 0 < n) :
    ∃ i : Fin n, accept ((lamport L f E hE hfE).forgeGame A 1 n) / (2 * (n : ℝ)) ≤
      ProbComp.expect (ProbComp.sample Bool) (fun c =>
        LamportFill.redProbability (f n)
          (fun Y r => A.toCompOn
            (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
            n 1 (LamportFill.publicWord Y) r) (i, c)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [lamport_forgeGame_accept_eq_honestProbability]
  exact LamportFill.exists_best_position (f n) _
    (fun Y r => A.toCompOn_costBoundedBy _ n 1 (LamportFill.publicWord Y) r)

/-- **Theorem 137.2: Lamport's scheme is one-time secure** [PS10, Theorem 137.2] when `f` is a
(strong) one-way function.

**Proof sketch** (the source's reduction, with its probability coupling explicit).
1. Fix a forger `A` making at most one signing query, and let `ε(n)` be its forgery probability.
   Work at `n ≥ 1`; the zero parameter is a finite exception for negligibility. The inverter
   `B` receives `1^n` and `y = f(x)` for a uniform `n`-bit `x`.
2. For the averaging argument, choose `i ← [n]` and a fair bit `c`, generate the other key
   entries, and put `y` at position `(i,c)`. Answer query `m` only when `m_i ≠ c`; otherwise
   abort, since the planted preimage is unknown. A valid forgery with `m'_i = c` reveals
   `σ'_i` with `f(σ'_i) = y`.
3. Couple this experiment to an honest execution, choosing `(i,c)` independently of that
   honest execution. The reduction agrees with it whenever it avoids revealing the planted
   preimage. For a successful honest run with query `m` and fresh forged message `m'`, the
   jointly favorable pairs satisfy `m_i ≠ c = m'_i`. Their fraction is
   `#{i : m_i ≠ m'_i}/(2n) ≥ 1/(2n)`. With no query, their fraction is exactly `1/2`.
   This counts the joint event without asserting independence after conditioning on non-abort.
4. Averaging over successful honest runs gives inversion probability at least `ε(n)/(2n)`.
   A best position at each length is at least as good as the uniform-position average; supply
   it as `O(log n)` bits of non-uniform advice and sample only the fair bit `c`. Thus the
   machine need not sample an exactly uniform element of `[n]` from a fixed finite coin tape.
5. T1 (`Games.exists_handlerMachine`) realizes the handler on `⟨y,1^i⟩`, using a fair
   bit, a complete sampled table, and the forger's coins. A successful nonaborting typed run
   has a safe query, so the handler's real output is the extracted preimage. Bounded decoding
   expands the `Nat.size n`-bit best-position advice to unary; `NUPPT.exists_withAdvice`
   supplies it without changing the coin polynomial. One-wayness makes this fixed machine's
   inversion probability negligible. Since `ε(n) ≤ 2n·inv_B(n)` for `n ≥ 1`, polynomial-factor
   closure proves one-time security, with zero handled by the finite exception.

For zero-query successful runs the extraction fraction is `1/2`, rather than just `1/(2n)`. -/
theorem lamport_oneTimeSecure (hf : (lamportOWF L f).StrongOneWay) :
    (lamport L f E hE hfE).OneTimeSecure := by
  classical
  apply LamportReduction.oneTimeSecure_of_inversion_lower
    (lamport L f E hE hfE) (lamportOWF L f) hf
  intro A
  have hW (n : ℕ) : (lamportPkBlock L).eval n = 6 * L.eval n + 6 := by
    rw [lamportPkBlock_eq]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have hEval (n : ℕ) (x : Fin n → Bool) :
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
    simpa only [NUPPT.advInput_eq] using hfE n x
  obtain ⟨B, hB⟩ := LamportFill.exists_realization_machine L (lamportPkBlock L) f
    E (lamportGenFun E) lamportSignFun hE
    (polyTimeComputable_lamportGenFun hE) polyTimeComputable_lamportSignFun
    hW hEval (lamportGenFun_table L f E hE hfE) lamportSignFun_table
    coinBlock_flatten_ofFn A
  have hbest (n : ℕ) (hn : 0 < n) : ∃ i : Fin n,
      accept ((lamport L f E hE hfE).forgeGame A 1 n) / (2 * (n : ℝ)) ≤
        ProbComp.expect (ProbComp.sample Bool)
          (fun c => LamportFill.redProbability (f n)
            (LamportFill.machineForger L A n) (i, c)) := by
    simpa only [LamportFill.machineForger_eq_fun] using
      lamport_exists_best_position L f E hE hfE A n hn
  let idx : ℕ → ℕ := fun n => if hn : 0 < n then (Classical.choose (hbest n hn)).val else 0
  have hidx_le (n : ℕ) : idx n ≤ n := by
    dsimp only [idx]
    split_ifs with hn
    · exact (Classical.choose (hbest n hn)).isLt.le
    · exact Nat.zero_le n
  obtain ⟨C, hCcoins, hC⟩ := LamportFill.exists_withIndexAdvice B idx hidx_le
  refine ⟨C, fun n hn => ?_⟩
  have hnpos : 0 < n := hn
  let i : Fin n := Classical.choose (hbest n hnpos)
  have hi := Classical.choose_spec (hbest n hnpos)
  have hidx : idx n = i.val := by
    dsimp only [idx]
    rw [dif_pos hnpos]
  obtain ⟨φ, hφ⟩ := hB n
  let e : ((Bool × LamportFill.Table n) × A.Coins n) ≃ C.Coins n :=
    φ.trans (NUPPT.coinsCongr hCcoins.symm n)
  have hreal (y : Fin (L.eval n) → Bool) (T : LamportFill.Table n) (c : Bool)
      (r : A.Coins n)
      (hs : LamportFill.RedSuccess (f n) (LamportFill.machineForger L A n) y T r (i, c)) :
      ∃ x' : Fin n → Bool,
        C.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ f n x' = y := by
    obtain ⟨x', hout, hfx⟩ := hφ i y T c r hs
    refine ⟨x', ?_, hfx⟩
    change C.runAt n (List.ofFn y)
      (NUPPT.coinsCongr hCcoins.symm n (φ ((c, T), r))) = List.ofFn x'
    rw [LamportFill.runAt_indexAdvice hCcoins idx hC, hidx]
    exact hout
  have hInv := LamportFill.fairBit_redProbability_le_invProbAt (lamportOWF L f)
    n A C i (LamportFill.machineForger L A n) e hreal
  exact hi.trans (by simpa only [lamportOWF_f] using hInv)

end TCSlib.Cryptography.Authentication

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Advice.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.OneWayLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary advice for a best Lamport position

## Main definitions

* `indexBits n i`: an index bounded by `n` encoded using exactly `Nat.size n` bits.
* `expandIndex U`: expand binary index advice to unary using a parameter-bounded decoder.

## Main results

* `indexBits_value`: the encoded index reads back as `i`.
* `exists_withIndexAdvice`: a machine expecting unary index data can receive that index
  through binary non-uniform advice of exactly `Nat.size n` bits.

`Nat.size n` is the binary digit count, hence the added advice has logarithmic length.
The polynomial bound supplied to the machine constructor is the weaker `Nat.size n ≤ n`.
The zero parameter uses an empty binary word encoding zero.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2, choosing the best position as non-uniform advice.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity Turing TCSlib.Cryptography

/-- An index `i ≤ n` is encoded as the inverse of the published binary-number equivalence
at width `Nat.size n`. Its width is logarithmic, including an empty encoding at `n=0`. -/
noncomputable def indexBits (n i : ℕ) (hi : i ≤ n) : List Bool :=
  List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)

/-- The index word is the serialized inverse image of `i` under `bitsEquiv`: `indexBits n i hi =
List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)`. -/
theorem indexBits_eq (n i : ℕ) (hi : i ≤ n) : indexBits n i hi =
    List.ofFn ((bitsEquiv (Nat.size n)).symm ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩) := rfl

/-- The binary index word has exactly `Nat.size n` bits: `(indexBits n i hi).length = Nat.size n`.
-/
theorem length_indexBits (n i : ℕ) (hi : i ≤ n) :
    (indexBits n i hi).length = Nat.size n := by
  rw [indexBits_eq, List.length_ofFn]

/-- Its logarithmic width is bounded by the polynomial width `n`: `(indexBits n i hi).length ≤ n`.
-/
theorem length_indexBits_le (n i : ℕ) (hi : i ≤ n) : (indexBits n i hi).length ≤ n := by
  rw [length_indexBits]
  exact Nat.size_le.2 n.lt_two_pow_self

/-- Reading the binary index word gives the original natural number `i`: `OneWay.bitListToNat
(indexBits n i hi) = i`.

**Proof sketch.** Apply `bitsEquiv` to its inverse image, read the natural-number value
using `bitsEquiv_val`, then use the published equivalence between typed and list numerals. -/
theorem indexBits_value (n i : ℕ) (hi : i ≤ n) :
    OneWay.bitListToNat (indexBits n i hi) = i := by
  have h := congrArg Fin.val ((bitsEquiv (Nat.size n)).apply_symm_apply
    ⟨i, hi.trans_lt (Nat.lt_size_self n)⟩)
  rw [bitsEquiv_val, OneWay.bitsToNat_eq_bitListToNat] at h
  rw [indexBits_eq]
  exact h

/-- On a parameter-aware input `⟨1^n,⟨y,b⟩⟩`, decode the bounded binary index `b` to unary
and return `⟨y,U(⟨1^n,b⟩)⟩`: `expandIndex U w = pairEncode (pairFstD (pairSndD w)) (U (pairEncode
(pairFstD w) (pairSndD (pairSndD w))))`. -/
def expandIndex (U : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD w))
    (U (pairEncode (pairFstD w) (pairSndD (pairSndD w))))

/-- The expansion pairs the challenge with `U` applied to the parameter and binary index:
`expandIndex U w = pairEncode (pairFstD (pairSndD w)) (U (pairEncode (pairFstD w) (pairSndD
(pairSndD w))))`. -/
theorem expandIndex_eq (U : List Bool → List Bool) (w : List Bool) : expandIndex U w =
    pairEncode (pairFstD (pairSndD w))
      (U (pairEncode (pairFstD w) (pairSndD (pairSndD w)))) := rfl

/-- Expanding binary index advice is polynomial-time whenever the bounded decoder is:
`PolyTimeComputable U → PolyTimeComputable (expandIndex U)`. -/
theorem expandIndex_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable (expandIndex U) :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
    (hU.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- On canonical parameter-aware input, the bounded decoder expands `b` to its unary
numeric value: if `OneWay.bitListToNat b ≤ n` and `U (pairEncode p b) = List.replicate
(OneWay.bitListToNat b) true` whenever `OneWay.bitListToNat b ≤ p.length`, then `expandIndex U
(NUPPT.advInput n (pairEncode y b)) = pairEncode y (List.replicate (OneWay.bitListToNat b) true)`.
This reads `advInput` and pairing only through their public equations. -/
theorem expandIndex_advInput (U : List Bool → List Bool)
    (hU : ∀ p b : List Bool, OneWay.bitListToNat b ≤ p.length →
      U (pairEncode p b) = List.replicate (OneWay.bitListToNat b) true)
    (n : ℕ) (y b : List Bool) (hb : OneWay.bitListToNat b ≤ n) :
    expandIndex U (NUPPT.advInput n (pairEncode y b)) =
      pairEncode y (List.replicate (OneWay.bitListToNat b) true) := by
  simp only [expandIndex_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [hU _ b (by simpa only [List.length_replicate] using hb)]

/-- A machine expecting `⟨y,1^(i n)⟩` can instead receive `i n ≤ n` as non-uniform binary
advice of exactly `Nat.size n` bits, keeping its coin polynomial. This is the best-position
advice step in [PS10, proof of Theorem 137.2].

**Proof sketch.** The public bounded binary-to-unary decoder expands an index using `1^n`
as its output cap. Parameter-aware preprocessing composes that decoder with the original
machine. Hard-wire the binary word using `exists_withAdvice`, bounded by `Nat.size n ≤ n`.
The preprocessor recovers the chosen unary index at every parameter, including zero. -/
theorem exists_withIndexAdvice (A : NUPPT) (i : ℕ → ℕ) (hi : ∀ n, i n ≤ n) :
    ∃ B : NUPPT, B.coins = A.coins ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r := by
  obtain ⟨U, hU, hUread⟩ := OneWay.exists_unaryOf
  obtain ⟨D, hDcoins, _, _, hD⟩ := NUPPT.exists_compParam A
    (expandIndex_poly hU) polyTimeComputable_pairSndD
  let β : ℕ → List Bool := fun n => indexBits n (i n) (hi n)
  have hβ : ∀ n, (β n).length ≤ PolyExpr.var.eval n := by
    intro n
    rw [PolyExpr.eval_var]
    exact length_indexBits_le n (i n) (hi n)
  obtain ⟨B, hBcoins, hB⟩ := NUPPT.exists_withAdvice D β .var hβ
  refine ⟨B, hBcoins.trans hDcoins, fun n y r => ?_⟩
  have hvalue : OneWay.bitListToNat (β n) = i n := indexBits_value n (i n) (hi n)
  have hcap : OneWay.bitListToNat (β n) ≤ n := by rw [hvalue]; exact hi n
  rw [hB, hD, pairSndD_pairEncode, expandIndex_advInput U hUread n y (β n) hcap, hvalue]

/-- A same-coins machine with the indexed untyped activation equation has the corresponding
typed activation equation through the published `coinsCongr` equivalence: if `hcoins : B.coins =
A.coins` and `B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r` for all `n`,
`y`, `r`, then `B.runAt n y (NUPPT.coinsCongr hcoins.symm n r) = A.runAt n (pairEncode y
(List.replicate (i n) true)) r`. -/
theorem runAt_indexAdvice {A B : NUPPT} (hcoins : B.coins = A.coins)
    (i : ℕ → ℕ)
    (hB : ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (List.replicate (i n) true)) r)
    (n : ℕ) (y : List Bool) (r : A.Coins n) :
    B.runAt n y (NUPPT.coinsCongr hcoins.symm n r) =
      A.runAt n (pairEncode y (List.replicate (i n) true)) r := by
  rw [NUPPT.runAt_coinsCongr hcoins.symm, hB, ← NUPPT.runAt_eq]

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Averaging.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite position averaging for Lamport's reduction

## Main definitions

None.

## Main results

* `sum_favourable_bits`: a differing pair of message bits has one favourable plant bit.
* `one_le_favourable_sum`: distinct messages have at least one favourable position and bit.
* `favourable_expect_ge`: the favourable fraction is at least `1 / (2 |I|)`.
* `noQuery_expect_eq_half`: without a query the favourable fraction is exactly `1 / 2`.
* `exists_expect_sample_le`: a finite uniform average is bounded by a value it averages.
* `expect_favourable_of_success`: pointwise favourable mass bounds its average on successes.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 137.2. The finite arithmetic is generic glue for its reduction.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open Finset TCSlib.Cryptography.Games

/-- For two bits `a` and `b`, the number of bits `c` satisfying `a ≠ c = b` is one
when `a ≠ b`, and zero otherwise. -/
theorem sum_favourable_bits (a b : Bool) :
    (∑ c : Bool, if a ≠ c ∧ b = c then (1 : ℝ) else 0) = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> simp

/-- The number of position-bit pairs with `m i ≠ c = m' i` is the number of positions at
which the messages differ. [PS10, proof of Theorem 137.2]. -/
theorem sum_favourable_pairs {ι : Type} [Fintype ι] (m m' : ι → Bool) :
    (∑ p : ι × Bool, if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0) =
      ∑ i : ι, if m i ≠ m' i then (1 : ℝ) else 0 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => sum_favourable_bits (m i) (m' i)

/-- Distinct messages have at least one jointly favourable position and bit:
`1 ≤ ∑_(i,c) 1[m_i ≠ c = m'_i]`. [PS10, proof of Theorem 137.2].

**Proof sketch.** Extensional inequality supplies a differing coordinate. Its indicator is
one, and all other indicators in the sum are nonnegative. -/
theorem one_le_favourable_sum {ι : Type} [Fintype ι] {m m' : ι → Bool} (h : m ≠ m') :
    1 ≤ ∑ p : ι × Bool, if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0 := by
  classical
  have hex : ∃ i, m i ≠ m' i := by
    by_contra hh
    push_neg at hh
    exact h (funext hh)
  obtain ⟨i, hi⟩ := hex
  rw [sum_favourable_pairs]
  have hle := Finset.single_le_sum
    (s := Finset.univ) (a := i)
    (f := fun j => if m j ≠ m' j then (1 : ℝ) else 0)
    (fun j _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ i)
  calc
    1 = (if m i ≠ m' i then (1 : ℝ) else 0) := (if_pos hi).symm
    _ ≤ ∑ j : ι, if m j ≠ m' j then (1 : ℝ) else 0 := hle

/-- For distinct messages on a nonempty finite position type, uniform `(i,c)` is jointly
favourable with probability at least `1 / (2 |I|)`: if `m ≠ m'`, then `1 / (2 * (Fintype.card ι :
ℝ)) ≤ ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 :
ℝ) else 0)`. [PS10, proof of Theorem 137.2]. -/
theorem favourable_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    {m m' : ι → Bool} (h : m ≠ m') :
    1 / (2 * (Fintype.card ι : ℝ)) ≤
      ProbComp.expect (ProbComp.sample (ι × Bool))
        (fun p => if m p.1 ≠ p.2 ∧ m' p.1 = p.2 then (1 : ℝ) else 0) := by
  rw [ProbComp.expect_sample]
  simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  have hcount := one_le_favourable_sum h
  have hden : 0 ≤ ((Fintype.card ι : ℝ) * 2)⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcount hden
  simpa only [mul_one, one_div, mul_comm 2 (Fintype.card ι : ℝ)] using hmul

/-- When there was no signing query, a uniform position and bit agrees with the forged
message bit with probability exactly `1 / 2`: `ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p
=> if m' p.1 = p.2 then (1 : ℝ) else 0) = 1 / 2`. [PS10, proof of Theorem 137.2]. -/
theorem noQuery_expect_eq_half {ι : Type} [Fintype ι] [Nonempty ι] (m' : ι → Bool) :
    ProbComp.expect (ProbComp.sample (ι × Bool))
        (fun p => if m' p.1 = p.2 then (1 : ℝ) else 0) = 1 / 2 := by
  have hbit (b : Bool) : (∑ c : Bool, if b = c then (1 : ℝ) else 0) = 1 := by
    cases b <;> simp
  rw [ProbComp.expect_sample, Fintype.sum_prod_type]
  simp only [hbit, sum_const, card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  field_simp

/-- A uniform finite average has a position whose value is at least the average: `∃ i,
ProbComp.expect (ProbComp.sample ι) g ≤ g i`.

**Proof sketch.** A maximum exists on the nonempty finite type. Every term of the sum is at
most that maximum, so the uniform average is at most it. -/
theorem exists_expect_sample_le {ι : Type} [Fintype ι] [Nonempty ι] (g : ι → ℝ) :
    ∃ i, ProbComp.expect (ProbComp.sample ι) g ≤ g i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc
    ProbComp.expect (ProbComp.sample ι) g ≤
        ProbComp.expect (ProbComp.sample ι) (fun _ => g i) :=
      ProbComp.expect_mono _ (fun j => hi j (Finset.mem_univ j))
    _ = g i := ProbComp.expect_const _ _

/-- If nonnegative favourable mass is at least `b` on every successful output, its average
is at least `b` times the success probability: if `∀ a, 0 ≤ q a` and `∀ a, P a → b ≤ q a`, then `b *
ProbComp.prob c P ≤ ProbComp.expect c q`. This is the finite averaging step in [PS10, proof of
Theorem 137.2]. -/
theorem expect_favourable_of_success {α : Type} (c : ProbComp α) (P : α → Prop)
    (q : α → ℝ) (b : ℝ) (hq : ∀ a, 0 ≤ q a) (hP : ∀ a, P a → b ≤ q a) :
    b * ProbComp.prob c P ≤ ProbComp.expect c q := by
  classical
  rw [ProbComp.prob_eq_expect, ← ProbComp.expect_const_mul]
  apply ProbComp.expect_mono
  intro a
  by_cases ha : P a
  · simpa only [ha, if_true, mul_one] using hP a ha
  · simpa only [ha, if_false, mul_zero] using hq a

end TCSlib.Cryptography.Authentication.LamportReduction

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/AveragingExtra.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Optional-query and fair-bit position averaging

## Main definitions

None.

## Main results

* `optionQuery_favourable_expect_ge`: fresh forged messages have favourable fraction
  at least `1 / (2 |I|)`, with or without a query.
* `exists_position_fairBit_expect_ge`: some fixed position with a fresh fair bit performs
  at least as well as a uniform position and bit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 137.2. These are the counting and best-position steps of its reduction.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open TCSlib.Cryptography.Games

/-- If an optional queried message differs from the forged message, a uniform position and
bit avoids revealing the planted preimage and selects the forged preimage with probability
at least `1 / (2 |I|)`: if `q ≠ some m'`, then `1 / (2 * (Fintype.card ι : ℝ)) ≤ ProbComp.expect
(ProbComp.sample (ι × Bool)) (fun p => if (∀ m, q = some m → m p.1 ≠ p.2) ∧ m' p.1 = p.2 then (1 :
ℝ) else 0)`. An absent query imposes no avoidance constraint. [PS10, proof of Theorem 137.2].

**Proof sketch.** With a query, freshness gives distinct messages and the differing-coordinate
bound applies. Without a query, half of the position-bit pairs select the forged preimage;
this is at least `1 / (2 |I|)` because the position type is nonempty. -/
theorem optionQuery_favourable_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    (q : Option (ι → Bool)) (m' : ι → Bool) (hfresh : q ≠ some m') :
    1 / (2 * (Fintype.card ι : ℝ)) ≤
      ProbComp.expect (ProbComp.sample (ι × Bool))
        (fun p => if (∀ m, q = some m → m p.1 ≠ p.2) ∧ m' p.1 = p.2
          then (1 : ℝ) else 0) := by
  classical
  cases q with
  | none =>
    simp only [reduceCtorEq, false_implies, forall_const, true_and]
    rw [noQuery_expect_eq_half]
    have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card ι))
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  | some m =>
    have hne : m ≠ m' := by
      intro h
      exact hfresh (congrArg some h)
    simpa using (favourable_expect_ge hne)

/-- For every payoff `v(i,c)` on a nonempty finite position type and a bit, there is a
position whose average over a fair bit is at least the average over a uniform position and
fair bit: `∃ i, ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) ≤ ProbComp.expect
(ProbComp.sample Bool) (v i)`. [PS10, proof of Theorem 137.2].

**Proof sketch.** Apply finite maximum averaging to the payoff already averaged over the bit.
The published product-sampling equation identifies its average over positions with the
uniform-pair expectation. -/
theorem exists_position_fairBit_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    (v : ι → Bool → ℝ) :
    ∃ i, ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) ≤
      ProbComp.expect (ProbComp.sample Bool) (v i) := by
  obtain ⟨i, hi⟩ := exists_expect_sample_le
    (fun j : ι => ProbComp.expect (ProbComp.sample Bool) (v j))
  refine ⟨i, ?_⟩
  calc
    ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) =
        ProbComp.expect
          ((ProbComp.sample ι).bind fun j =>
            (ProbComp.sample Bool).bind fun c => .pure (j, c)) (fun p => v p.1 p.2) :=
      (Bridge.expect_sample_pair (fun p : ι × Bool => v p.1 p.2)).symm
    _ = ProbComp.expect (ProbComp.sample ι)
        (fun j => ProbComp.expect (ProbComp.sample Bool) (v j)) := by
      simp only [ProbComp.expect_bind, ProbComp.expect_pure]
    _ ≤ ProbComp.expect (ProbComp.sample Bool) (v i) := hi

end TCSlib.Cryptography.Authentication.LamportReduction

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Blocks.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Replacing a fixed-width block in a concatenated tuple

## Main definitions

None.

## Main results

* `flatten_ofFn_update`: replacing a block by prefix, replacement and suffix agrees with a
  function update before serialization.

## References

Generic list and finite-tuple glue; no textbook counterpart.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

/-- Replacing block `i` of a concatenation of `B`-bit blocks by the `B`-bit word `h` is
serialization of the updated tuple:
`take(iB, flatten(g)) ++ h ++ drop((i+1)B, flatten(g)) = flatten(update(g,i,h))`.

**Proof sketch.** Induct on the number of blocks and split the updated index into zero or a
successor. At zero, dropping the first block leaves the unchanged tail. At a successor,
taking and dropping pass the initial block, so the induction hypothesis applies to the tail;
the untouched initial block is then prepended. All length calculations use the given uniform
block-width equations. -/
theorem flatten_ofFn_update {B : ℕ} :
    ∀ {q : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
      (i : Fin q) (h : List Bool) (hh : h.length = B),
      (List.ofFn g).flatten.take (i.val * B) ++ h ++
          (List.ofFn g).flatten.drop ((i.val + 1) * B) =
        (List.ofFn (Function.update g i h)).flatten
  | 0, _, _, i, _, _ => i.elim0
  | q + 1, g, hg, i, h, hh => by
    have hflat : (List.ofFn g).flatten =
        g 0 ++ (List.ofFn (Fin.tail g)).flatten := by
      rw [List.ofFn_succ, List.flatten_cons, Fin.tail_def]
    cases i using Fin.cases with
    | zero =>
      have hupdate : Function.update g 0 h = Fin.cons h (Fin.tail g) := by
        have hu := Fin.update_cons_zero (x := g 0) (p := Fin.tail g) (z := h)
        simpa only [Fin.cons_self_tail] using hu
      rw [hflat, hupdate, List.ofFn_cons, List.flatten_cons]
      simp only [Fin.val_zero, Nat.zero_mul, List.take_zero, List.nil_append,
        Nat.zero_add, Nat.one_mul]
      rw [List.drop_left' (hg 0)]
    | succ j =>
      have hstart : (j.succ : Fin (q + 1)).val * B = (g 0).length + j.val * B := by
        simp only [Fin.val_succ, hg 0]
        ring
      have hend : ((j.succ : Fin (q + 1)).val + 1) * B =
          (g 0).length + (j.val + 1) * B := by
        simp only [Fin.val_succ, hg 0]
        ring
      have hupdate : Function.update g j.succ h =
          Fin.cons (g 0) (Function.update (Fin.tail g) j h) := by
        rw [Fin.cons_update, Fin.cons_self_tail]
      rw [hflat, hstart, hend, List.take_length_add_append,
        List.drop_length_add_append, hupdate, List.ofFn_cons, List.flatten_cons]
      have ht : ∀ k : Fin q, ((Fin.tail g) k).length = B := fun k => hg k.succ
      simpa only [List.append_assoc] using congrArg (List.append (g 0))
        (flatten_ofFn_update (Fin.tail g) ht j h hh)

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Closing.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closing Lamport's linear-loss reduction

## Main definitions

None.

## Main results

* `negligible_of_linear_bound`: a nonnegative function bounded by `2n` times a negligible
  nonnegative function for `n ≥ 1` is negligible.
* `oneTimeSecure_of_inversion_bound`: the same bound for each forger proves one-time security.

The zero parameter is excluded only from the eventual comparison supplied to
`Negligible.mono`; no value at zero is changed or assumed.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open Complexity TCSlib.Cryptography.Games

/-- If `e` and `p` are nonnegative, `p` is negligible, and `e(n) ≤ 2n·p(n)` for `n ≥ 1`,
then `e` is negligible. [PS10, final step of the proof of Theorem 137.2].

**Proof sketch.** Multiplication by `n` and then by two preserves negligibility. The eventual
comparison starts at one, so the zero parameter is a finite exception. -/
theorem negligible_of_linear_bound {e p : ℕ → ℝ} (hp : Negligible p)
    (hp0 : ∀ n, 0 ≤ p n) (he0 : ∀ n, 0 ≤ e n)
    (hbound : ∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * p n) : Negligible e := by
  have hmajorant : Negligible (fun n => (2 : ℝ) * ((n : ℝ) ^ 1 * p n)) :=
    (hp.mul_pow 1).const_mul 2
  apply hmajorant.mono
  refine ⟨1, fun n hn => ?_⟩
  have hnonneg : 0 ≤ (2 : ℝ) * ((n : ℝ) ^ 1 * p n) :=
    mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 1) (hp0 n))
  rw [abs_of_nonneg (he0 n), abs_of_nonneg hnonneg]
  simpa only [pow_one, mul_assoc] using hbound n hn

/-- A nonnegative advantage bounded by `2n` times the inversion probability of a fixed
machine against a strong one-way family is negligible for all parameters, with no condition
needed at zero: if `F.StrongOneWay`, `∀ n, 0 ≤ e n` and `∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * F.invProbAt B
n`, then `Negligible e`. [PS10, final step of the proof of Theorem 137.2]. -/
theorem negligible_of_inversion_bound (F : FunFamily) (hf : F.StrongOneWay) (B : NUPPT)
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n)
    (hbound : ∀ n ≥ 1, e n ≤ 2 * (n : ℝ) * F.invProbAt B n) : Negligible e :=
  negligible_of_linear_bound (hf.hard B) (F.invProbAt_nonneg B) he0 hbound

/-- A signature scheme is one-time secure if each forger yields a fixed machine whose
inversion probability against a strong one-way family bounds its forgery probability with
loss `2n` for `n ≥ 1`. [PS10, reduction conclusion in Theorem 137.2].

**Proof sketch.** Use each forger's own acceptance probability as its security majorant.
Polynomial-factor closure proves that majorant negligible; its pointwise bound is equality. -/
theorem oneTimeSecure_of_inversion_bound (S : SignatureScheme) (F : FunFamily)
    (hf : F.StrongOneWay)
    (hred : ∀ A : NUPPT, ∃ B : NUPPT, ∀ n ≥ 1,
      accept (S.forgeGame A 1 n) ≤ 2 * (n : ℝ) * F.invProbAt B n) : S.OneTimeSecure := by
  apply (S.oneTimeSecure_iff).2
  intro A
  obtain ⟨B, hB⟩ := hred A
  refine ⟨fun n => accept (S.forgeGame A 1 n), ?_, fun _ => le_rfl⟩
  exact negligible_of_inversion_bound F hf B _ (fun n => accept_nonneg _) hB

/-- The probability-form reduction `ε(n)/(2n) ≤ inv_B(n)` also implies one-time security.
[PS10, averaging bound and conclusion in Theorem 137.2]. -/
theorem oneTimeSecure_of_inversion_lower (S : SignatureScheme) (F : FunFamily)
    (hf : F.StrongOneWay)
    (hred : ∀ A : NUPPT, ∃ B : NUPPT, ∀ n ≥ 1,
      accept (S.forgeGame A 1 n) / (2 * (n : ℝ)) ≤ F.invProbAt B n) : S.OneTimeSecure := by
  apply oneTimeSecure_of_inversion_bound S F hf
  intro A
  obtain ⟨B, hB⟩ := hred A
  refine ⟨B, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
  have hden : 0 < (2 : ℝ) * (n : ℝ) := mul_pos (by norm_num) hn0
  have h := (div_le_iff₀ hden).1 (hB n hn)
  simpa only [mul_comm (F.invProbAt B n) (2 * (n : ℝ))] using h

end TCSlib.Cryptography.Authentication.LamportReduction

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Encoding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Complexity.TuringMachine.Encoding
import Mathlib.Data.List.OfFn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Injectivity of the cryptographic tuple encoding

## Main definitions

None.

## Main results

* `encodeList_injective`: equality of encoded lists implies equality of their blocks.
* `encodeList_eq_iff`: list encodings agree exactly when the lists agree.
* `encodeList_ofFn_eq_iff`: encodings of finite tuples agree exactly when the tuples agree.

## References

Generic encoding lemmas; no textbook counterpart. These use the list encoding of
[PS10, Definition 93.1] through its published equations only.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open Turing
open TCSlib.Cryptography.PrivateKeyScheme (encodeList encodeList_nil encodeList_cons)

/-- The nested-pair list encoding is injective: `encodeList xs = encodeList ys` implies
`xs = ys`.

**Proof sketch.** Induct on the first list. An empty encoding cannot equal a cons encoding,
since a pair encoding is nonempty. For two cons encodings, injectivity of pairing identifies
the heads and the encoded tails, and induction identifies the tails. -/
theorem encodeList_injective : Function.Injective encodeList := by
  have haux : ∀ xs ys : List (List Bool), encodeList xs = encodeList ys → xs = ys := by
    intro xs
    induction xs with
    | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
        rw [encodeList_nil, encodeList_cons] at h
        exact False.elim (pairEncode_ne_nil y (encodeList ys) h.symm)
    | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
        rw [encodeList_cons, encodeList_nil] at h
        exact False.elim (pairEncode_ne_nil x (encodeList xs) h)
      | cons y ys =>
        rw [encodeList_cons, encodeList_cons] at h
        have hp : (x, encodeList xs) = (y, encodeList ys) := pairEncode_injective h
        have hx : x = y := congrArg Prod.fst hp
        have hxs : xs = ys := ih ys (congrArg Prod.snd hp)
        exact congrArg₂ List.cons hx hxs
  intro xs ys h
  exact haux xs ys h

/-- Two nested-pair list encodings agree exactly when their lists of blocks agree: `encodeList xs =
encodeList ys ↔ xs = ys`. -/
theorem encodeList_eq_iff (xs ys : List (List Bool)) :
    encodeList xs = encodeList ys ↔ xs = ys :=
  ⟨fun h => encodeList_injective h, congrArg encodeList⟩

/-- Encodings of two tuples with the same finite index length agree exactly when the tuples
agree: `encodeList (List.ofFn g) = encodeList (List.ofFn h) ↔ g = h`. -/
theorem encodeList_ofFn_eq_iff {q : ℕ} (g h : Fin q → List Bool) :
    encodeList (List.ofFn g) = encodeList (List.ofFn h) ↔ g = h := by
  constructor
  · intro heq
    exact List.ofFn_injective (encodeList_injective heq)
  · intro heq
    exact congrArg (fun k : Fin q → List Bool => encodeList (List.ofFn k)) heq

end TCSlib.Cryptography.Authentication.LamportReduction

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Experiment.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The typed Lamport reduction and its average success

## Main definitions

* `honestOutput` and `HonestSuccess`: the honest typed forgery and its acceptance/freshness test.
* `Favourable`: the sole query avoids the planted preimage and the forgery uses it.
* `RedSuccess`: a nonaborting planted simulation whose extracted block inverts its challenge.
* `honestProbability` and `redProbability`: the honest and independently challenged averages.

## Main results

* `favourable_mass_of_success`: favorable position mass is at least `1/(2n)` on successes.
* `diagonal_red_of_success_favourable`: favorable honest successes invert their table entry.
* `averaged_redProbability_ge`: uniform planted reduction success is at least `H/(2n)`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 137.1 and Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography.Games
open scoped Classical

-- Keep elaboration on the published probability readers.
run_cmd do
  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))

section TypedExperiment

variable {n ℓ : ℕ} {ρ : Type}
  (g : (Fin n → Bool) → Fin ℓ → Bool)
  (adv : ((Fin n × Bool) → Fin ℓ → Bool) → ρ →
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) (Fin (n + n * n) → Bool))

/-- Evaluate the forger on the honest public table with deterministic table signing: `honestOutput g
adv T r = (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m)`. -/
def honestOutput (T : Table n) (r : ρ) : Fin (n + n * n) → Bool :=
  (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m)

/-- The honest output is functional evaluation against the selected-preimage signing function:
`honestOutput g adv T r = (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m)`. -/
theorem honestOutput_eq (T : Table n) (r : ρ) :
    honestOutput g adv T r =
      (adv (tablePublic g T) r).evalFn (fun _ m => tableSignature T m) := rfl

/-- An honest output succeeds when all its signature blocks verify and its message was
not the optional signing query [PS10, Definition 136.2]: `HonestSuccess g adv T r ↔ (∀ j, g
(signatureBlock σ j) = g (T (j, m j))) ∧ firstQuery (adv (tablePublic g T) r) ≠ some m`, where `(m,
σ) = splitBits (honestOutput g adv T r)`. -/
def HonestSuccess (T : Table n) (r : ρ) : Prop :=
  (∀ j, g (signatureBlock (splitBits (honestOutput g adv T r)).2 j) =
    g (T (j, (splitBits (honestOutput g adv T r)).1 j))) ∧
    firstQuery (adv (tablePublic g T) r) ≠ some (splitBits (honestOutput g adv T r)).1

/-- Honest success is coordinate verification together with inequality to the optional query:
`HonestSuccess g adv T r ↔ (∀ j, g (signatureBlock σ j) = g (T (j, m j))) ∧ firstQuery (adv
(tablePublic g T) r) ≠ some m`, where `(m, σ) = splitBits (honestOutput g adv T r)`. -/
theorem honestSuccess_iff (T : Table n) (r : ρ) :
    HonestSuccess g adv T r ↔
      (∀ j, g (signatureBlock (splitBits (honestOutput g adv T r)).2 j) =
        g (T (j, (splitBits (honestOutput g adv T r)).1 j))) ∧
      firstQuery (adv (tablePublic g T) r) ≠ some (splitBits (honestOutput g adv T r)).1 :=
  Iff.rfl

/-- A position-bit pair is favorable when its signing query is safe and its forged message
uses the planted bit [PS10, proof of Theorem 137.2]: `Favourable g adv T r p ↔ Safe (adv
(tablePublic g T) r) p.1 p.2 ∧ (splitBits (honestOutput g adv T r)).1 p.1 = p.2`. -/
def Favourable (T : Table n) (r : ρ) (p : Fin n × Bool) : Prop :=
  Safe (adv (tablePublic g T) r) p.1 p.2 ∧
    (splitBits (honestOutput g adv T r)).1 p.1 = p.2

/-- Favorability is signing-query safety conjoined with the forged message's planted bit:
`Favourable g adv T r p ↔ Safe (adv (tablePublic g T) r) p.1 p.2 ∧ (splitBits (honestOutput g adv T
r)).1 p.1 = p.2`. -/
theorem favourable_iff (T : Table n) (r : ρ) (p : Fin n × Bool) :
    Favourable g adv T r p ↔ Safe (adv (tablePublic g T) r) p.1 p.2 ∧
      (splitBits (honestOutput g adv T r)).1 p.1 = p.2 := Iff.rfl

/-- The planted reduction succeeds if it ends without abort and its extracted signature
block is a preimage of the challenge [PS10, proof of Theorem 137.2]: `RedSuccess g adv y T r p ↔ ∃
a, simulate (abortingImpl T p.1 p.2) (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false)
∧ g (signatureBlock (splitBits a).2 p.1) = y`. -/
def RedSuccess (y : Fin ℓ → Bool) (T : Table n) (r : ρ) (p : Fin n × Bool) : Prop :=
  ∃ a, simulate (abortingImpl T p.1 p.2)
      (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧
    g (signatureBlock (splitBits a).2 p.1) = y

/-- Reduction success means a pure nonaborting simulation output whose selected block
maps to the challenge: `RedSuccess g adv y T r p ↔ ∃ a, simulate (abortingImpl T p.1 p.2) (adv
(plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧ g (signatureBlock (splitBits a).2 p.1) =
y`. -/
theorem redSuccess_iff (y : Fin ℓ → Bool) (T : Table n) (r : ρ) (p : Fin n × Bool) :
    RedSuccess g adv y T r p ↔
      ∃ a, simulate (abortingImpl T p.1 p.2)
          (adv (plantedPublic g T p.1 p.2 y) r) false = .pure (a, false) ∧
        g (signatureBlock (splitBits a).2 p.1) = y := Iff.rfl

/-- Replacing a table coordinate by its present value leaves the table unchanged: `plantTable T i c
(T (i, c)) = T`. -/
theorem plantTable_self (T : Table n) (i : Fin n) (c : Bool) :
    plantTable T i c (T (i, c)) = T := by
  funext p
  rw [plantTable_eq]
  by_cases hp : p = (i, c)
  · rw [if_pos hp, hp]
  · rw [if_neg hp]

/-- Reduction success ignores the original table preimage at the planted position: `RedSuccess g adv
y (plantTable T p.1 p.2 x) r p ↔ RedSuccess g adv y T r p`. -/
theorem redSuccess_plant_iff (y : Fin ℓ → Bool) (T : Table n) (r : ρ)
    (p : Fin n × Bool) (x : Fin n → Bool) :
    RedSuccess g adv y (plantTable T p.1 p.2 x) r p ↔ RedSuccess g adv y T r p := by
  rw [redSuccess_iff, redSuccess_iff, plantedPublic_plant, abortingImpl_plant]

/-- A favorable successful honest run is a successful planted reduction when challenged
with the image of its own selected table entry [PS10, proof of Theorem 137.2]: if every `adv Y r`
has `(adv Y r).CostBoundedBy (fun _ => 1) 1`, `HonestSuccess g adv T r` and `Favourable g adv T r
p`, then `RedSuccess g adv (g (T p)) T r p`.

**Proof sketch.** Planting the present entry `T p` leaves the planted public table equal to the
honest one and the key unchanged (`plantedPublic_image`, `plantTable_self`). Safety then gives, by
`planted_coupling`, the nonaborting output `honestOutput g adv T r`. Acceptance at position `p.1`,
whose forged bit is `p.2`, says that its block maps to `g (T p)`. -/
theorem diagonal_red_of_success_favourable
    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1)
    (T : Table n) (r : ρ) (p : Fin n × Bool)
    (hs : HonestSuccess g adv T r) (hq : Favourable g adv T r p) :
    RedSuccess g adv (g (T p)) T r p := by
  obtain ⟨hacc, hfresh⟩ := (honestSuccess_iff g adv T r).1 hs
  obtain ⟨hsafe, hbit⟩ := (favourable_iff g adv T r p).1 hq
  apply (redSuccess_iff g adv (g (T p)) T r p).2
  refine ⟨honestOutput g adv T r, ?_, ?_⟩
  · rw [plantedPublic_image, plantTable_self]
    have h := planted_coupling T p.1 p.2 (T p) (adv (tablePublic g T) r)
      (hcost _ r) hsafe
    rw [plantTable_self, ← honestOutput_eq g adv T r] at h
    exact h
  · have h := hacc p.1
    rw [hbit] at h
    exact h

/-- On every successful honest run, favorable position-bit mass is at least `1/(2n)`;
the no-query case has mass exactly `1/2` [PS10, proof of Theorem 137.2]: if `HonestSuccess g adv T
r`, then `1 / (2 * (n : ℝ)) ≤ ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p => if
Favourable g adv T r p then (1 : ℝ) else 0)`.

**Proof sketch.** Freshness says that the optional first query differs from the forged message, so
`optionQuery_favourable_expect_ge` bounds the mass of the pairs that avoid the query and select the
forged bit. Each such pair is favourable (`favourable_iff`, `safe_iff`), and expectation is
monotone. -/
theorem favourable_mass_of_success [Nonempty (Fin n)] (T : Table n) (r : ρ)
    (hs : HonestSuccess g adv T r) :
    1 / (2 * (n : ℝ)) ≤ ProbComp.expect (ProbComp.sample (Fin n × Bool))
      (fun p => if Favourable g adv T r p then (1 : ℝ) else 0) := by
  have h := LamportReduction.optionQuery_favourable_expect_ge
    (firstQuery (adv (tablePublic g T) r)) (splitBits (honestOutput g adv T r)).1
    ((honestSuccess_iff g adv T r).1 hs).2
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply ProbComp.expect_mono
  intro p
  by_cases hp : Favourable g adv T r p
  · obtain ⟨hsafe, hbit⟩ := (favourable_iff g adv T r p).1 hp
    have hr : (∀ m, firstQuery (adv (tablePublic g T) r) = some m → m p.1 ≠ p.2) ∧
        (splitBits (honestOutput g adv T r)).1 p.1 = p.2 :=
      ⟨(safe_iff _ p.1 p.2).1 hsafe, hbit⟩
    simp only [if_pos hr, if_pos hp, le_refl]
  · have hr : ¬ ((∀ m, firstQuery (adv (tablePublic g T) r) = some m → m p.1 ≠ p.2) ∧
        (splitBits (honestOutput g adv T r)).1 p.1 = p.2) := by
      intro hh
      exact hp ((favourable_iff g adv T r p).2 ⟨(safe_iff _ p.1 p.2).2 hh.1, hh.2⟩)
    simp only [if_neg hr, if_neg hp, le_refl]

variable [Fintype ρ] [Nonempty ρ]

/-- Honest success probability averages over the complete key table and forger coins:
`honestProbability g adv = ProbComp.expect (ProbComp.sample (Table n)) (fun T => ProbComp.expect
(ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0)`. -/
noncomputable def honestProbability : ℝ :=
  ProbComp.expect (ProbComp.sample (Table n)) fun T =>
    ProbComp.expect (ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0

/-- Honest probability is the nested uniform expectation of the honest-success indicator:
`honestProbability g adv = ProbComp.expect (ProbComp.sample (Table n)) (fun T => ProbComp.expect
(ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0)`. -/
theorem honestProbability_eq : honestProbability g adv =
    ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
      ProbComp.expect (ProbComp.sample ρ) fun r => if HonestSuccess g adv T r then 1 else 0) := rfl

/-- The fixed-position reduction's success probability uses an independent challenge
preimage, a complete random table, and forger coins: `redProbability g adv p = ProbComp.expect
(ProbComp.sample (Fin n → Bool)) (fun x => ProbComp.expect (ProbComp.sample (Table n)) fun T =>
ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1 else 0)`. -/
noncomputable def redProbability (p : Fin n × Bool) : ℝ :=
  ProbComp.expect (ProbComp.sample (Fin n → Bool)) fun x =>
    ProbComp.expect (ProbComp.sample (Table n)) fun T =>
      ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1 else 0

/-- Fixed-position reduction probability is the nested average of its nonaborting inversion
indicator over independent challenge, key-table and forger samples: `redProbability g adv p =
ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x => ProbComp.expect (ProbComp.sample (Table
n)) fun T => ProbComp.expect (ProbComp.sample ρ) fun r => if RedSuccess g adv (g x) T r p then 1
else 0)`. -/
theorem redProbability_eq (p : Fin n × Bool) : redProbability g adv p =
    ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
      ProbComp.expect (ProbComp.sample (Table n)) fun T =>
        ProbComp.expect (ProbComp.sample ρ) fun r =>
          if RedSuccess g adv (g x) T r p then 1 else 0) :=
  rfl

/-- A uniform position-bit planted reduction succeeds with probability at least the honest
forgery probability divided by `2n` [PS10, proof of Theorem 137.2]: if every `adv Y r` has `(adv Y
r).CostBoundedBy (fun _ => 1) 1`, then `honestProbability g adv / (2 * (n : ℝ)) ≤ ProbComp.expect
(ProbComp.sample (Fin n × Bool)) (redProbability g adv)`.

**Proof sketch.** Favorable pairs occupy at least `1/(2n)` of every successful honest run.
On those pairs the planted simulation is safe and its extracted signature block inverts
the image of the corresponding honest preimage. The reduction ignores that preimage,
so coordinate resampling makes the challenge independent while preserving the average. -/
theorem averaged_redProbability_ge [Nonempty (Fin n)]
    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1) :
    honestProbability g adv / (2 * (n : ℝ)) ≤
      ProbComp.expect (ProbComp.sample (Fin n × Bool)) (redProbability g adv) := by
  classical
  have h := coordinate_reduction_bound
    (HonestSuccess g adv) (Favourable g adv)
    (fun x T r p => RedSuccess g adv (g x) T r p) (1 / (2 * (n : ℝ)))
    (favourable_mass_of_success g adv)
    (diagonal_red_of_success_favourable g adv hcost)
    (fun x x' T r p => by
      rw [← plantTable_update T p.1 p.2 x']
      exact redSuccess_plant_iff g adv (g x) T r p x')
  simpa only [honestProbability_eq, redProbability_eq, one_div_mul_eq_div] using h

/-- Some fixed position, while its planted bit remains fair, has reduction probability at
least `H/(2n)` [PS10, proof of Theorem 137.2]: if every `adv Y r` has `(adv Y r).CostBoundedBy (fun
_ => 1) 1`, then `∃ i : Fin n, honestProbability g adv / (2 * (n : ℝ)) ≤ ProbComp.expect
(ProbComp.sample Bool) (fun c => redProbability g adv (i, c))`. This is the position supplied as
advice. -/
theorem exists_best_position [Nonempty (Fin n)]
    (hcost : ∀ Y r, (adv Y r).CostBoundedBy (fun _ => 1) 1) :
    ∃ i : Fin n, honestProbability g adv / (2 * (n : ℝ)) ≤
      ProbComp.expect (ProbComp.sample Bool) (fun c => redProbability g adv (i, c)) := by
  obtain ⟨i, hi⟩ := LamportReduction.exists_position_fairBit_expect_ge
    (fun i : Fin n => fun c : Bool => redProbability g adv (i, c))
  exact ⟨i, (averaged_redProbability_ge g adv hcost).trans hi⟩

end TypedExperiment

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/InversionProbability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The planted reduction probability is bounded by machine inversion

## Main definitions

None.

## Main results

* `fairBit_redProbability_le_invProbAt`: a realization of successful typed reductions by a
  machine transfers the typed fair-bit success probability to the family's inversion game.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2. This is generic probability and machine transport glue.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity TCSlib.Cryptography.Games

/-- Suppose a machine's coins are a fair planting bit, a complete key table and forger coins,
and every successful typed planted run yields the machine's correctly encoded preimage.
Then the typed reduction's success averaged over the fair bit is at most the machine's
inversion probability against the function family: `ProbComp.expect (ProbComp.sample Bool) (fun c =>
redProbability (F.f n) adv (i, c)) ≤ F.invProbAt B n`, provided `RedSuccess (F.f n) adv y T r (i, c)
→ ∃ x', B.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ F.f n x' = y` for all `y`, `T`,
`c`, `r`. The preimage width is the family's actual input width, so no dependent width casts are
needed. [PS10, proof of Theorem 137.2].

**Proof sketch.** Read the machine inversion probability as the uniform probability that its
output encodes a preimage. Product sampling separates the challenge preimage and machine
coins. Reindex the latter by the given coin equivalence, and split the resulting product
sample into its bit, table and forger coins using the published product-sampling law.
Commute the independent bit and challenge samples on the typed side. All remaining samples
have the same order, and the realization hypothesis implies the pointwise event inclusion.
No query-cost assumption is needed for this transport: it is already encapsulated in the
realization hypothesis. -/
theorem fairBit_redProbability_le_invProbAt (F : FunFamily) (n : ℕ) (A B : NUPPT)
    (i : Fin (F.inLen.eval n))
    (adv : ((Fin (F.inLen.eval n) × Bool) → Fin (F.outLen.eval n) → Bool) →
      A.Coins n → OracleComp
        (bitSpec (fun _ : Fin 1 => F.inLen.eval n)
          (fun _ => F.inLen.eval n * F.inLen.eval n))
        (Fin (F.inLen.eval n + F.inLen.eval n * F.inLen.eval n) → Bool))
    (e : ((Bool × Table (F.inLen.eval n)) × A.Coins n) ≃ B.Coins n)
    (hreal : ∀ (y : Fin (F.outLen.eval n) → Bool) (T : Table (F.inLen.eval n))
        (c : Bool) (r : A.Coins n),
      RedSuccess (F.f n) adv y T r (i, c) →
        ∃ x' : Fin (F.inLen.eval n) → Bool,
          B.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ F.f n x' = y) :
    ProbComp.expect (ProbComp.sample Bool)
        (fun c => redProbability (F.f n) adv (i, c)) ≤ F.invProbAt B n := by
  classical
  rw [FunFamily.invProbAt_eq_uprob, ← Bridge.prob_sample_eq_uprob,
    ProbComp.prob_eq_expect, ← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  simp_rw [← ProbComp.expect_sample_equiv e]
  simp only [redProbability_eq]
  rw [ProbComp.expect_sample_comm]
  simp only [← Bridge.expect_sample_pair, ProbComp.expect_bind, ProbComp.expect_pure]
  apply ProbComp.expect_mono
  intro x
  apply ProbComp.expect_mono
  intro c
  apply ProbComp.expect_mono
  intro T
  apply ProbComp.expect_mono
  intro r
  by_cases hs : RedSuccess (F.f n) adv (F.f n x) T r (i, c)
  · have hwin := hreal (F.f n x) T c r hs
    rw [if_pos hs, if_pos hwin] <;> exact le_rfl
  · rw [if_neg hs]
    split_ifs <;> positivity

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Machine.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# String machine for Lamport's planted experiment

## Main definitions

* `advIn` replaces one fixed-width public-key block with a planted image.
* `run` signs from the sampled tape and records whether the planted half was requested.
* `out` extracts one signature block unless the run aborted.
* `handler` packages these string functions for T1.

The generator and signer are parameters, so this module does not import its consumer.
The generator is expected to return `⟨pk, tape⟩`; the signer is expected to implement the
deterministic Lamport string function. Their mathematical contracts belong to the consumer.

## Main results

All string functions are polynomial-time; every public definition has an equation reader.
The functional contracts and machine realization are proved in `MachineSpec` and
`Realization`; the owned Lamport module closes the security reduction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 137.1 and proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportMachine

open Complexity Turing TCSlib.Cryptography.Games

/-- The context's unary parameter is its first component: `u v = pairFstD v`. -/
def u (v : List Bool) : List Bool := pairFstD v
/-- `u v = pairFstD v`. -/
theorem u_eq (v : List Bool) : u v = pairFstD v := rfl
/-- The unary parameter projection is polynomial-time: `PolyTimeComputable u`, for `u : List Bool →
List Bool`. -/
theorem u_poly : PolyTimeComputable u := polyTimeComputable_pairFstD

/-- The context's challenge is the first component of its reduction input: `y v = pairFstD (pairFstD
(pairSndD v))`. -/
def y (v : List Bool) : List Bool := pairFstD (pairFstD (pairSndD v))
/-- `y v = fst (fst (snd v))`. -/
theorem y_eq (v : List Bool) : y v = pairFstD (pairFstD (pairSndD v)) := rfl
/-- The challenge projection is polynomial-time: `PolyTimeComputable y`, for `y : List Bool → List
Bool`. -/
theorem y_poly : PolyTimeComputable y :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)

/-- The planted position is the second component of the reduction input, encoded in unary: `pos v =
pairSndD (pairFstD (pairSndD v))`. -/
def pos (v : List Bool) : List Bool := pairSndD (pairFstD (pairSndD v))
/-- `pos v = snd (fst (snd v))`. -/
theorem pos_eq (v : List Bool) : pos v = pairSndD (pairFstD (pairSndD v)) := rfl
/-- The position projection is polynomial-time: `PolyTimeComputable pos`, for `pos : List Bool →
List Bool`. -/
theorem pos_poly : PolyTimeComputable pos :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)

/-- The handler seed is the second component of the context's second component: `seed v = pairSndD
(pairSndD v)`. -/
def seed (v : List Bool) : List Bool := pairSndD (pairSndD v)
/-- `seed v = snd (snd v)`. -/
theorem seed_eq (v : List Bool) : seed v = pairSndD (pairSndD v) := rfl
/-- The seed projection is polynomial-time: `PolyTimeComputable seed`, for `seed : List Bool → List
Bool`. -/
theorem seed_poly : PolyTimeComputable seed :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The planted half is the first seed bit, defaulting to false: `bit v = (seed v).headD false`. -/
def bit (v : List Bool) : Bool := (seed v).headD false
/-- `bit v = (seed v).headD false`. -/
theorem bit_eq (v : List Bool) : bit v = (seed v).headD false := rfl
/-- The planted bit is polynomial-time as a one-bit output: `PolyTimeComputable (fun v => [bit v])`,
for `bit : List Bool → Bool`. -/
theorem bit_poly : PolyTimeComputable (fun v => [bit v]) :=
  polyTimeComputable_headD.comp seed_poly

/-- The sampled preimage tape is the seed after its planted bit: `tape v = (seed v).drop 1`. -/
def tape (v : List Bool) : List Bool := (seed v).drop 1
/-- `tape v = (seed v).drop 1`. -/
theorem tape_eq (v : List Bool) : tape v = (seed v).drop 1 := rfl
/-- Removing the planted bit is polynomial-time: `PolyTimeComputable tape`, for `tape : List Bool →
List Bool`. -/
theorem tape_poly : PolyTimeComputable tape := polyTimeComputable_tail.comp seed_poly

/-- A canonical context exposes its unary parameter: `u (seedIn n z ω) = List.replicate n true`. -/
theorem u_seedIn (n : ℕ) (z ω : List Bool) :
    u (seedIn n z ω) = List.replicate n true := by
  rw [u_eq, seedIn_eq, pairFstD_pairEncode]

/-- A canonical context with input `⟨challenge,index⟩` exposes its challenge: `y (seedIn n
(pairEncode challenge index) ω) = challenge`. -/
theorem y_seedIn (n : ℕ) (challenge index ω : List Bool) :
    y (seedIn n (pairEncode challenge index) ω) = challenge := by
  simp only [y_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- A canonical context with input `⟨challenge,index⟩` exposes its unary position: `pos (seedIn n
(pairEncode challenge index) ω) = index`. -/
theorem pos_seedIn (n : ℕ) (challenge index ω : List Bool) :
    pos (seedIn n (pairEncode challenge index) ω) = index := by
  simp only [pos_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- A canonical context exposes its seed: `seed (seedIn n z ω) = ω`. -/
theorem seed_seedIn (n : ℕ) (z ω : List Bool) : seed (seedIn n z ω) = ω := by
  simp only [seed_eq, seedIn_eq, pairSndD_pairEncode]

/-- A seed beginning with `c` supplies the planted half `c`: `bit (seedIn n z (c :: ρ)) = c`. -/
theorem bit_seedIn (n : ℕ) (z ρ : List Bool) (c : Bool) :
    bit (seedIn n z (c :: ρ)) = c := by
  rw [bit_eq, seed_seedIn, List.headD_cons]

/-- A seed beginning with `c` leaves exactly the sampled preimage tape after it: `tape (seedIn n z
(c :: ρ)) = ρ`. -/
theorem tape_seedIn (n : ℕ) (z ρ : List Bool) (c : Bool) :
    tape (seedIn n z (c :: ρ)) = ρ := by
  rw [tape_eq, seed_seedIn]
  rfl

/-- A fixed polynomial width, encoded as a unary word of length `W(|u|)`: `width W v =
List.replicate (W.eval (u v).length) true`. -/
def width (W : PolyExpr) (v : List Bool) : List Bool := List.replicate (W.eval (u v).length) true
/-- `width W v = 1^(W(|u v|))`. -/
theorem width_eq (W : PolyExpr) (v : List Bool) :
    width W v = List.replicate (W.eval (u v).length) true := rfl
/-- A polynomial width is polynomial-time in the context: `PolyTimeComputable (width W)`, for `width
W : List Bool → List Bool`. -/
theorem width_poly (W : PolyExpr) : PolyTimeComputable (width W) :=
  (polyTimeComputable_unaryPoly W).comp u_poly

/-- The unary offset to block `i` at width `W(n)` has `i · W(n)` symbols: `offset W v =
List.replicate ((pos v).length * W.eval (u v).length) true`. -/
def offset (W : PolyExpr) (v : List Bool) : List Bool :=
  List.replicate ((pos v).length * W.eval (u v).length) true
/-- `offset W v = 1^(|pos v| · W(|u v|))`. -/
theorem offset_eq (W : PolyExpr) (v : List Bool) :
    offset W v = List.replicate ((pos v).length * W.eval (u v).length) true := rfl
/-- Block offsets are polynomial-time by the existing unary multiplication machine:
`PolyTimeComputable (offset W)`, for `offset W : List Bool → List Bool`. -/
theorem offset_poly (W : PolyExpr) : PolyTimeComputable (offset W) := by
  refine (OneWay.polyTimeComputable_unaryMulPair.comp (pos_poly.pairEncode (width_poly W))).congr ?_
  intro v
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    width_eq, offset_eq, List.length_replicate]

/-- The first preimage at the selected position consists of `n` bits after offset `2ni`: `first v =
((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length`. -/
def first (v : List Bool) : List Bool :=
  ((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length
/-- `first` is the first `n`-bit half of the selected preimage pair: `first v = ((tape v).drop
(offset (.mul (.const 2) .var) v).length).take (u v).length`. -/
theorem first_eq (v : List Bool) : first v =
    ((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length := rfl
/-- Selecting the first preimage is polynomial-time: `PolyTimeComputable first`, for `first : List
Bool → List Bool`. -/
theorem first_poly : PolyTimeComputable first :=
  TCSlib.Cryptography.takeLen_poly u_poly
    (TCSlib.Cryptography.dropLen_poly (offset_poly _) tape_poly)

/-- The second preimage is the next `n` bits after offset `2ni+n`: `second v = ((tape v).drop
((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length`. -/
def second (v : List Bool) : List Bool :=
  ((tape v).drop ((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length
/-- `second` is the second `n`-bit half of the selected preimage pair: `second v = ((tape v).drop
((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length`. -/
theorem second_eq (v : List Bool) : second v =
    ((tape v).drop ((offset (.mul (.const 2) .var) v).length +
      (u v).length)).take (u v).length := rfl
/-- Selecting the second preimage is polynomial-time: `PolyTimeComputable second`, for `second :
List Bool → List Bool`. -/
theorem second_poly : PolyTimeComputable second := by
  refine (TCSlib.Cryptography.takeLen_poly u_poly
    (TCSlib.Cryptography.dropLen_poly ((offset_poly (.mul (.const 2) .var)).append u_poly)
      tape_poly)).congr ?_
  intro v
  simp only [second_eq, List.length_append]

/-- The ordinary generated public key on the sampled tape: `honestPk G v = pairFstD (G (NUPPT.layout
(u v) [] [] (tape v)))`. -/
def honestPk (G : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairFstD (G (NUPPT.layout (u v) [] [] (tape v)))
/-- `honestPk G` runs `G` on the sampled preimage tape and reads its public-key component: `honestPk
G v = pairFstD (G (NUPPT.layout (u v) [] [] (tape v)))`. -/
theorem honestPk_eq (G : List Bool → List Bool) (v : List Bool) : honestPk G v =
    pairFstD (G (NUPPT.layout (u v) [] [] (tape v))) := rfl
/-- Generating the ordinary public key is polynomial-time when `G` is: `PolyTimeComputable G →
PolyTimeComputable (honestPk G)`. -/
theorem honestPk_poly {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
    PolyTimeComputable (honestPk G) :=
  polyTimeComputable_pairFstD.comp (hG.comp (NUPPT.polyTimeComputable_layout u_poly
    (polyTimeComputable_const []) (polyTimeComputable_const []) tape_poly))

/-- The replacement public-key block is `⟨⟨y,E(x¹)⟩,[]⟩` for bit false and
`⟨⟨E(x⁰),y⟩,[]⟩` for bit true: `replacement E v = pairEncode (pairEncode (if bit v then E
(pairEncode (u v) (first v)) else y v) (if bit v then y v else E (pairEncode (u v) (second v))))
[]`. -/
def replacement (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode (pairEncode
    (if bit v then E (pairEncode (u v) (first v)) else y v)
    (if bit v then y v else E (pairEncode (u v) (second v)))) []
/-- The replacement block plants the challenge in the selected half: `replacement E v = pairEncode
(pairEncode (if bit v then E (pairEncode (u v) (first v)) else y v) (if bit v then y v else E
(pairEncode (u v) (second v)))) []`. -/
theorem replacement_eq (E : List Bool → List Bool) (v : List Bool) : replacement E v =
    pairEncode (pairEncode
      (if bit v then E (pairEncode (u v) (first v)) else y v)
      (if bit v then y v else E (pairEncode (u v) (second v)))) [] := rfl
/-- Building the replacement public-key block is polynomial-time when `E` is: `PolyTimeComputable E
→ PolyTimeComputable (replacement E)`. -/
theorem replacement_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (replacement E) :=
  ((polyTimeComputable_ite bit_poly (hE.comp (u_poly.pairEncode first_poly)) y_poly).pairEncode
    (polyTimeComputable_ite bit_poly y_poly (hE.comp (u_poly.pairEncode second_poly)))).pairEncode
      (polyTimeComputable_const [])

/-- The adversary's public key replaces one width-`W(n)` block of the ordinary generated key
with the planted block: `advIn W E G v = (honestPk G v).take (offset W v).length ++ replacement E v
++ (honestPk G v).drop ((offset W v).length + (width W v).length)`. [PS10, proof of Theorem 137.2].
-/
def advIn (W : PolyExpr) (E G : List Bool → List Bool) (v : List Bool) : List Bool :=
  (honestPk G v).take (offset W v).length ++ replacement E v ++
    (honestPk G v).drop ((offset W v).length + (width W v).length)
/-- `advIn` keeps the prefix and suffix around the planted block: `advIn W E G v = (honestPk G
v).take (offset W v).length ++ replacement E v ++ (honestPk G v).drop ((offset W v).length + (width
W v).length)`. -/
theorem advIn_eq (W : PolyExpr) (E G : List Bool → List Bool) (v : List Bool) :
    advIn W E G v = (honestPk G v).take (offset W v).length ++ replacement E v ++
      (honestPk G v).drop ((offset W v).length + (width W v).length) := rfl
/-- Planting one public-key block is polynomial-time: `PolyTimeComputable E → PolyTimeComputable G →
PolyTimeComputable (advIn W E G)`.

**Proof sketch.** Compute both unary offsets by the existing multiplication primitive,
take the prefix and drop the suffix, then concatenate the replacement block between them. -/
theorem advIn_poly (W : PolyExpr) {E G : List Bool → List Bool}
    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) :
    PolyTimeComputable (advIn W E G) := by
  refine (((TCSlib.Cryptography.takeLen_poly (offset_poly W) (honestPk_poly hG)).append
      (replacement_poly hE)).append
    (TCSlib.Cryptography.dropLen_poly ((offset_poly W).append (width_poly W))
      (honestPk_poly hG))).congr ?_
  intro v
  simp only [advIn_eq, List.length_append]

/-- The context of a query or finalization input is its first component: `context w = pairFstD w`.
-/
def context (w : List Bool) : List Bool := pairFstD w
/-- `context w = fst w`. -/
theorem context_eq (w : List Bool) : context w = pairFstD w := rfl
/-- The context of an activation is polynomial-time: `PolyTimeComputable context`, for `context :
List Bool → List Bool`. -/
theorem context_poly : PolyTimeComputable context := polyTimeComputable_pairFstD

/-- The current abort state is the first component of the second input component: `state w =
pairFstD (pairSndD w)`. -/
def state (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- `state w = fst (snd w)`. -/
theorem state_eq (w : List Bool) : state w = pairFstD (pairSndD w) := rfl
/-- The current state projection is polynomial-time: `PolyTimeComputable state`, for `state : List
Bool → List Bool`. -/
theorem state_poly : PolyTimeComputable state :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The query message is the second component after the state and oracle index: `message w =
pairSndD (pairSndD (pairSndD w))`. -/
def message (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- `message w = snd (snd (snd w))`. -/
theorem message_eq (w : List Bool) : message w = pairSndD (pairSndD (pairSndD w)) := rfl
/-- The query message projection is polynomial-time: `PolyTimeComputable message`, for `message :
List Bool → List Bool`. -/
theorem message_poly : PolyTimeComputable message :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The context of a canonical handler query is its original seed context: `context
(PolyHandler.input n z ω s i x) = seedIn n z ω`. -/
theorem context_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    context (PolyHandler.input n z ω s i x) = seedIn n z ω := by
  simp only [context_eq, PolyHandler.input_eq, seedIn_eq, pairFstD_pairEncode]

/-- A canonical handler query exposes its state: `state (PolyHandler.input n z ω s i x) = s`. -/
theorem state_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    state (PolyHandler.input n z ω s i x) = s := by
  simp only [state_eq, PolyHandler.input_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- A canonical handler query exposes its message: `message (PolyHandler.input n z ω s i x) = x`. -/
theorem message_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    message (PolyHandler.input n z ω s i x) = x := by
  simp only [message_eq, PolyHandler.input_eq, pairSndD_pairEncode]

/-- A query is blocked precisely when its selected message bit is the planted bit: `blocked w =
decide (((message w).drop (pos (context w)).length).headD false = bit (context w))`. -/
def blocked (w : List Bool) : Bool :=
  decide (((message w).drop (pos (context w)).length).headD false = bit (context w))
/-- `blocked` tests equality of the query bit at the planted position and the planted half: `blocked
w = decide (((message w).drop (pos (context w)).length).headD false = bit (context w))`. -/
theorem blocked_eq (w : List Bool) : blocked w =
    decide (((message w).drop (pos (context w)).length).headD false = bit (context w)) := rfl
/-- Testing whether a query requests the planted half is polynomial-time: `PolyTimeComputable (fun w
=> [blocked w])`, for `blocked : List Bool → Bool`. -/
theorem blocked_poly : PolyTimeComputable (fun w => [blocked w]) := by
  have hq := polyTimeComputable_headD.comp
    (TCSlib.Cryptography.dropLen_poly (pos_poly.comp context_poly) message_poly)
  have hb := bit_poly.comp context_poly
  refine (polyTimeComputable_pairEq.comp (hq.pairEncode hb)).congr ?_
  intro w
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, blocked_eq,
    List.cons.injEq, and_true]

/-- A handler query returns the ordinary sampled-tape signature and sets the persistent
abort bit if the planted half was requested: `run S w = pairEncode (S (NUPPT.layout (u (context w))
(pairEncode (tape (context w)) (message w)) [] [])) [(state w).headD false || blocked w]`.
Continuing after an abort is harmless because finalization returns no candidate. [PS10, proof of
Theorem 137.2]. -/
def run (S : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode
    (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
    [(state w).headD false || blocked w]
/-- The query answer uses the sampled tape and records the disjunction of old and new aborts: `run S
w = pairEncode (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
[(state w).headD false || blocked w]`. -/
theorem run_eq (S : List Bool → List Bool) (w : List Bool) : run S w =
    pairEncode
      (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
      [(state w).headD false || blocked w] := rfl
/-- Query answering and the abort-state update are polynomial-time when `S` is: `PolyTimeComputable
S → PolyTimeComputable (run S)`. -/
theorem run_poly {S : List Bool → List Bool} (hS : PolyTimeComputable S) :
    PolyTimeComputable (run S) :=
  (hS.comp (NUPPT.polyTimeComputable_layout (u_poly.comp context_poly)
    ((tape_poly.comp context_poly).pairEncode message_poly)
    (polyTimeComputable_const []) (polyTimeComputable_const []))).pairEncode
      (polyTimeComputable_or (polyTimeComputable_headD.comp state_poly) blocked_poly)

/-- The final output is empty after an abort; otherwise it is block `i` of the forged signature
(the adversary's word begins with the `n` message bits): `out w = if (state w).headD false then []
else (((pairSndD (pairSndD w)).drop (u (context w)).length).drop (offset .var (context
w)).length).take (u (context w)).length`. [PS10, proof of Theorem 137.2]. -/
def out (w : List Bool) : List Bool :=
  if (state w).headD false then [] else
    (((pairSndD (pairSndD w)).drop (u (context w)).length).drop
      (offset .var (context w)).length).take (u (context w)).length
/-- Finalization suppresses aborted runs and extracts the selected signature block otherwise: `out
w = if (state w).headD false then [] else (((pairSndD (pairSndD w)).drop (u (context
w)).length).drop (offset .var (context w)).length).take (u (context w)).length`. -/
theorem out_eq (w : List Bool) : out w =
    if (state w).headD false then [] else
      (((pairSndD (pairSndD w)).drop (u (context w)).length).drop
        (offset .var (context w)).length).take (u (context w)).length := rfl
/-- Finalization is polynomial-time by three variable-prefix operations and one branch:
`PolyTimeComputable out`, for `out : List Bool → List Bool`. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_ite (polyTimeComputable_headD.comp state_poly) (polyTimeComputable_const [])
    (TCSlib.Cryptography.takeLen_poly (u_poly.comp context_poly)
      (TCSlib.Cryptography.dropLen_poly ((offset_poly .var).comp context_poly)
        (TCSlib.Cryptography.dropLen_poly (u_poly.comp context_poly)
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))))

/-- The planted Lamport handler has one abort bit and `1+2n²` seed bits, with the fair planted
half first: its fields are `stateLen = .const 1`, `seedLen = .add (.const 1) (.mul (.mul (.const 2)
.var) .var)`, `init = fun _ _ => false`, `run = run S`, `advIn = advIn W E G` and `out = out`. It
signs at most one query and extracts one candidate preimage. -/
def handler (W : PolyExpr) (E G S : List Bool → List Bool)
    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S) :
    PolyHandler 1 (fun _ => .var) (fun _ => .mul .var .var) where
  stateLen := .const 1
  seedLen := .add (.const 1) (.mul (.mul (.const 2) .var) .var)
  init := fun _ _ => false
  run := run S
  poly := run_poly hS
  advIn := advIn W E G
  advIn_poly := advIn_poly W hE hG
  out := out
  out_poly := out_poly

variable (W : PolyExpr) (E G S : List Bool → List Bool)
  (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S)

/-- The handler state-length polynomial is the constant one: `(handler W E G S hE hG hS).stateLen =
.const 1`. -/
theorem handler_stateLen : (handler W E G S hE hG hS).stateLen = .const 1 := rfl
/-- The handler seed-length polynomial is `1+2n²`: `(handler W E G S hE hG hS).seedLen = .add
(.const 1) (.mul (.mul (.const 2) .var) .var)`. -/
theorem handler_seedLen : (handler W E G S hE hG hS).seedLen =
    .add (.const 1) (.mul (.mul (.const 2) .var) .var) := rfl
/-- Every bit of the initial abort state is false: `(handler W E G S hE hG hS).init n i = false`. -/
theorem handler_init (n : ℕ) (i : Fin ((handler W E G S hE hG hS).stateLen.eval n)) :
    (handler W E G S hE hG hS).init n i = false := rfl
/-- The handler's query function is `run S`: `(handler W E G S hE hG hS).run = run S`. -/
theorem handler_run : (handler W E G S hE hG hS).run = run S := rfl
/-- The handler's adversary-input function is the planted public-key function: `(handler W E G S hE
hG hS).advIn = advIn W E G`. -/
theorem handler_advIn : (handler W E G S hE hG hS).advIn = advIn W E G := rfl
/-- The handler's output function is the signature-block extractor: `(handler W E G S hE hG
hS).out = out`. -/
theorem handler_out : (handler W E G S hE hG hS).out = out := rfl

end TCSlib.Cryptography.Authentication.LamportMachine

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/MachineSpec.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Functional contracts of the planted Lamport machine

## Main definitions

None.

## Main results

* `advIn_context` identifies the machine's public key with the typed planted public table.
* `run_input` identifies its query answer and abort flag.
* `out_nonabort` identifies its final signature-block extraction.

The exact finite-tuple `coinBlock` reader is passed as a parameter, so this helper neither
imports the owned consumer nor copies that consumer's public lemma.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity Turing TCSlib.Cryptography.Games
open TCSlib.Cryptography

/-- The serialized public table is the concatenation of its self-delimiting image-pair
blocks: `publicWord Y = (List.ofFn fun i : Fin n => pairEncode (pairEncode (List.ofFn (Y (i,
false))) (List.ofFn (Y (i, true)))) []).flatten`. This reads the public tuple encoding through
`encodeList_eq_flatMap`. -/
theorem publicWord_flatten {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) :
    publicWord Y = (List.ofFn fun i : Fin n =>
      pairEncode (pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) []).flatten := by
  rw [publicWord_eq, encodeList_eq_flatMap, List.flatMap_def, List.map_ofFn]
  rw [Function.comp_def]

section KeyWindows

variable (hcoin : ∀ {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
  (i : Fin q), coinBlock B i (List.ofFn g).flatten = g i)

include hcoin in
/-- Reading the first `n`-bit half of the selected sampled row returns `T(i,false)`:
`LamportMachine.first (seedIn n (pairEncode challenge (List.replicate i.val true)) (c :: secretWord
T)) = List.ofFn (T (i, false))`.

**Proof sketch.** On this context `first` takes `n` bits of `secretWord T` after the offset `2n·i`
(`first_eq`, `tape_seedIn`, `offset_eq`, `pos_seedIn`, `u_seedIn`). By `hcoin`, the `2n` bits there
are row `i`, that is `T (i, false) ‖ T (i, true)`, and the first `n` of them are `T (i, false)`. -/
theorem first_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
    LamportMachine.first (seedIn n (pairEncode challenge (List.replicate i.val true))
      (c :: secretWord T)) = List.ofFn (T (i, false)) := by
  rw [LamportMachine.first_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hrow := hcoin (B := 2 * n)
    (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
  rw [coinBlock_eq, ← secretWord_eq] at hrow
  have h := congrArg (fun w : List Bool => w.take n) hrow
  dsimp only at h
  rw [List.take_take, Nat.min_eq_left (by omega), List.take_left' List.length_ofFn] at h
  exact h

include hcoin in
/-- Reading the second `n`-bit half of the selected sampled row returns `T(i,true)`:
`LamportMachine.second (seedIn n (pairEncode challenge (List.replicate i.val true)) (c :: secretWord
T)) = List.ofFn (T (i, true))`.

**Proof sketch.** On this context `second` takes `n` bits of `secretWord T` after the offset `2n·i +
n` (`second_eq`, `tape_seedIn`, `offset_eq`, `pos_seedIn`, `u_seedIn`). By `hcoin`, the `2n` bits
after offset `2n·i` are row `i`, that is `T (i, false) ‖ T (i, true)`, and dropping its first `n`
bits leaves `T (i, true)`. -/
theorem second_context {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool) :
    LamportMachine.second (seedIn n (pairEncode challenge (List.replicate i.val true))
      (c :: secretWord T)) = List.ofFn (T (i, true)) := by
  rw [LamportMachine.second_eq, LamportMachine.tape_seedIn, LamportMachine.offset_eq,
    LamportMachine.pos_seedIn, LamportMachine.u_seedIn]
  simp only [List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hrow := hcoin (B := 2 * n)
    (fun j : Fin n => List.ofFn (T (j, false)) ++ List.ofFn (T (j, true)))
    (fun j => by simp only [List.length_append, List.length_ofFn]; omega) i
  rw [coinBlock_eq, ← secretWord_eq] at hrow
  have h := congrArg (fun w : List Bool => w.drop n) hrow
  dsimp only at h
  rw [List.drop_take, show 2 * n - n = n by omega, List.drop_drop,
    List.drop_left' List.length_ofFn] at h
  exact h

include hcoin in
/-- The machine's replacement block serializes the planted row, using the evaluator's
published agreement on `n`-bit inputs: `LamportMachine.replacement E (seedIn n (pairEncode
(List.ofFn challenge) (List.replicate i.val true)) (c :: secretWord T)) = pairEncode (pairEncode
(List.ofFn (plantedPublic g T i c challenge (i, false))) (List.ofFn (plantedPublic g T i c challenge
(i, true)))) []`. -/
theorem replacement_context {n ℓ : ℕ} (g : (Fin n → Bool) → Fin ℓ → Bool)
    (E : List Bool → List Bool)
    (hE : ∀ x : Fin n → Bool,
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
    LamportMachine.replacement E
        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
          (c :: secretWord T)) =
      pairEncode (pairEncode
        (List.ofFn (plantedPublic g T i c challenge (i, false)))
        (List.ofFn (plantedPublic g T i c challenge (i, true)))) [] := by
  rw [LamportMachine.replacement_eq, LamportMachine.bit_seedIn, LamportMachine.u_seedIn,
    LamportMachine.y_seedIn, first_context hcoin, second_context hcoin, hE, hE]
  cases c <;> simp [plantedPublic_eq]

include hcoin in
/-- On a canonical seed context, the machine's public-key input is exactly the serialized
typed planted table: if `W.eval n = 6 * ℓ + 6`, then `LamportMachine.advIn W E G (seedIn n
(pairEncode (List.ofFn challenge) (List.replicate i.val true)) (c :: secretWord T)) = publicWord
(plantedPublic g T i c challenge)`. The only generator/evaluator facts required are their stated
functional contracts; the owned Lamport module supplies them.

**Proof sketch.** The ordinary generated key is a concatenation of width `6ℓ+6` blocks.
The machine takes the blocks before `i`, inserts the planted block, and drops through block
`i`. The general fixed-width replacement lemma identifies this with updating row `i` before
serialization. Every other row retains both images. -/
theorem advIn_context {n ℓ : ℕ} (W : PolyExpr)
    (hW : W.eval n = 6 * ℓ + 6) (g : (Fin n → Bool) → Fin ℓ → Bool)
    (E G : List Bool → List Bool)
    (hE : ∀ x : Fin n → Bool,
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (g x))
    (hG : ∀ T : Table n,
      G (NUPPT.layout (List.replicate n true) [] [] (secretWord T)) =
        pairEncode (publicWord (tablePublic g T)) (secretWord T))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : Fin ℓ → Bool) :
    LamportMachine.advIn W E G
        (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
          (c :: secretWord T)) =
      publicWord (plantedPublic g T i c challenge) := by
  have hpk : LamportMachine.honestPk G
      (seedIn n (pairEncode (List.ofFn challenge) (List.replicate i.val true))
        (c :: secretWord T)) = publicWord (tablePublic g T) := by
    rw [LamportMachine.honestPk_eq, LamportMachine.u_seedIn, LamportMachine.tape_seedIn,
      hG, pairFstD_pairEncode]
  let rows : Fin n → List Bool := fun j => pairEncode (pairEncode
    (List.ofFn (g (T (j, false)))) (List.ofFn (g (T (j, true))))) []
  let plantedRows : Fin n → List Bool := fun j => pairEncode (pairEncode
    (List.ofFn (plantedPublic g T i c challenge (j, false)))
    (List.ofFn (plantedPublic g T i c challenge (j, true)))) []
  have hrows (j : Fin n) : (rows j).length = W.eval n := by
    simp only [rows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
    ring
  have hnew : (plantedRows i).length = W.eval n := by
    simp only [plantedRows, length_pairEncode, List.length_ofFn, List.length_nil, hW]
    ring
  have hupdate : Function.update rows i (plantedRows i) = plantedRows := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
    · have hp0 : (j, false) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
      have hp1 : (j, true) ≠ (i, c) := fun hp => hj (congrArg Prod.fst hp)
      rw [Function.update_of_ne hj]
      simp only [rows, plantedRows, plantedPublic_eq, if_neg hp0, if_neg hp1]
  have hnormal : publicWord (tablePublic g T) = (List.ofFn rows).flatten := by
    rw [publicWord_flatten]
    simp only [tablePublic_eq, rows]
  have hplant : publicWord (plantedPublic g T i c challenge) =
      (List.ofFn plantedRows).flatten := by
    rw [publicWord_flatten]
  simp only [LamportMachine.advIn_eq, hpk, replacement_context hcoin g E hE,
    LamportMachine.offset_eq, LamportMachine.width_eq, LamportMachine.pos_seedIn,
    LamportMachine.u_seedIn, List.length_replicate]
  simp only [hnormal, hplant]
  change (List.ofFn rows).flatten.take (i.val * W.eval n) ++ plantedRows i ++
    (List.ofFn rows).flatten.drop (i.val * W.eval n + W.eval n) =
      (List.ofFn plantedRows).flatten
  rw [show i.val * W.eval n + W.eval n = (i.val + 1) * W.eval n by ring,
    flatten_ofFn_update rows hrows i (plantedRows i) hnew, hupdate]

end KeyWindows

/-- The selected bit of a serialized message is its typed bit at that position: `((List.ofFn m).drop
i.val).headD false = m i`. -/
theorem headD_drop_ofFn {n : ℕ} (m : Fin n → Bool) (i : Fin n) :
    ((List.ofFn m).drop i.val).headD false = m i := by
  simp only [headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]

/-- On canonical input, the machine returns the typed signature and records the old abort
bit or equality `m_i=c`. This statement covers both safe and aborting calls. -/
theorem run_input {n : ℕ} (S : List Bool → List Bool)
    (hS : ∀ (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (T : Table n) (i : Fin n) (c bad : Bool) (challenge : List Bool)
    (j : Fin 1) (m : Fin n → Bool) :
    LamportMachine.run S (PolyHandler.input n
        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
        [bad] j (List.ofFn m)) =
      pairEncode (List.ofFn (tableSignature T m)) [bad || decide (m i = c)] := by
  have hb : LamportMachine.blocked (PolyHandler.input n
      (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
      [bad] j (List.ofFn m)) = decide (m i = c) := by
    rw [LamportMachine.blocked_eq, LamportMachine.context_input, LamportMachine.message_input,
      LamportMachine.pos_seedIn, LamportMachine.bit_seedIn, List.length_replicate,
      headD_drop_ofFn]
  simp only [LamportMachine.run_eq, LamportMachine.context_input, LamportMachine.state_input,
    LamportMachine.message_input, LamportMachine.u_seedIn, LamportMachine.tape_seedIn, hS,
    List.headD_cons, hb]

/-- A safe query from non-abort state returns the typed signature and a false abort bit: if `m i ≠
c`, then `LamportMachine.run S (PolyHandler.input n (pairEncode challenge (List.replicate i.val
true)) (c :: secretWord T) [false] j (List.ofFn m)) = pairEncode (List.ofFn (tableSignature T m))
[false]`. -/
theorem run_safe {n : ℕ} (S : List Bool → List Bool)
    (hS : ∀ (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (T : Table n) (i : Fin n) (c : Bool) (challenge : List Bool)
    (j : Fin 1) (m : Fin n → Bool) (hm : m i ≠ c) :
    LamportMachine.run S (PolyHandler.input n
        (pairEncode challenge (List.replicate i.val true)) (c :: secretWord T)
        [false] j (List.ofFn m)) =
      pairEncode (List.ofFn (tableSignature T m)) [false] := by
  rw [run_input S hS]
  simp only [hm, decide_false, Bool.false_or]

/-- Finalization in non-abort state returns exactly the selected block of the typed forged
signature, after its first `n` message bits: if `LamportMachine.pos (seedIn n z ρ) = List.replicate
i.val true`, then `LamportMachine.out (pairEncode (seedIn n z ρ) (pairEncode [false] (List.ofFn
a))) = List.ofFn (signatureBlock (splitBits a).2 i)`.

**Proof sketch.** With state `[false]`, `out` drops the `n` message bits, then `n·i` more bits, and
takes `n` (`out_eq`, `u_seedIn`, `offset_eq`, `hz`). After the message the word is `List.ofFn
(splitBits a).2` (`splitBits_snd`, `ofFn_natAdd_eq_drop`), and its block `i` is the signature block
(`FunFamily.ofFn_blocks`, `signatureBlock_eq`). -/
theorem out_nonabort {n : ℕ} (i : Fin n) (z ρ : List Bool)
    (a : Fin (n + n * n) → Bool)
    (hz : LamportMachine.pos (seedIn n z ρ) = List.replicate i.val true) :
    LamportMachine.out (pairEncode (seedIn n z ρ) (pairEncode [false] (List.ofFn a))) =
      List.ofFn (signatureBlock (splitBits a).2 i) := by
  rw [LamportMachine.out_eq, LamportMachine.state_eq, LamportMachine.context_eq]
  simp only [LamportMachine.context_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    Bool.false_eq_true,
    if_false, LamportMachine.u_seedIn, LamportMachine.offset_eq, hz,
    List.length_replicate, PolyExpr.eval_var]
  have hs : List.ofFn (splitBits a).2 = (List.ofFn a).drop n := by
    have hsplit : (splitBits a).2 = fun j => a (Fin.natAdd n j) := by
      funext j
      exact splitBits_snd a j
    rw [hsplit, ofFn_natAdd_eq_drop]
  rw [← hs, ← FunFamily.ofFn_blocks n n (splitBits a).2 i]
  apply congrArg List.ofFn
  funext k
  rw [FunFamily.blocks_apply, signatureBlock_eq]

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Nonabort.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading nonabort as query safety

## Main definitions

None.

## Main results

* `safe_of_nonabort`: a nonaborting one-query planted transcript has a safe query.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography.Games

/-- A planted run with at most one query ending with a false abort bit queried no message
that reveals the planted cell [PS10, proof of Theorem 137.2]: if `tree.CostBoundedBy (fun _ => 1) 1`
and `simulate (abortingImpl T i c) tree false = .pure (a', false)`, then `Safe tree i c`.

**Proof sketch.** An immediate return has no query. A query leaves cost zero, so its
continuation is a return; the final abort flag is exactly equality of its selected bit with
the planted bit. A false flag therefore says that the query was safe. -/
theorem safe_of_nonabort {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (a' : α)
    (hsim : simulate (abortingImpl T i c) tree false = .pure (a', false)) :
    Safe tree i c := by
  cases tree with
  | pure a =>
    apply (safe_iff _ i c).2
    intro m hm
    rw [firstQuery_pure] at hm
    cases hm
  | query j m k =>
    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (abortingAnswer T i c m))
      (by simpa only [Nat.sub_self] using (hk.2 (abortingAnswer T i c m)))
    rw [simulate_query, abortingImpl_apply, OracleComp.pure_bind, ha, simulate_pure] at hsim
    have hp : (a, false || decide (m i = c)) = (a', false) := OracleComp.pure.inj hsim
    have hb : decide (m i = c) = false := by
      simpa only [Bool.false_or] using congrArg Prod.snd hp
    have hm : m i ≠ c := of_decide_eq_false hb
    apply (safe_iff _ i c).2
    intro m' hm'
    rw [firstQuery_query, Option.some.injEq] at hm'
    rw [← hm']
    exact hm

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Planted.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The fixed-position Lamport planting coupling

## Main definitions

* `plantTable` replaces one preimage in a typed Lamport key table.
* `tableSignature` selects one preimage per message bit.
* `plantedPublic` replaces one image without reading its preimage.
* `firstQuery` and `Safe` record whether the sole query avoids the planted cell.
* `abortingImpl` answers safe queries and remembers an unsafe query.

## Main results

* `planted_coupling`: on the safe branch of a computation with at most one query,
  the planted implementation returns the honest output and never aborts.
* `extract_planted`: an accepting signature with the planted message bit inverts
  the planted image.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 137.1 and Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography TCSlib.Cryptography.Games
open Complexity Turing

/-- A table has an `n`-bit preimage at each coordinate `(i,c)`: `Table n = ((Fin n × Bool) → Fin n →
Bool)`. -/
abbrev Table (n : ℕ) := (Fin n × Bool) → Fin n → Bool

/-- The type of tables is the function type `(Fin n × Bool) → Fin n → Bool`. -/
theorem Table_eq (n : ℕ) : Table n = ((Fin n × Bool) → Fin n → Bool) := rfl

/-- Serialize a public table as the tuple of its pairs of images: `publicWord Y =
PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n => pairEncode (List.ofFn (Y (i, false)))
(List.ofFn (Y (i, true))))`. -/
def publicWord {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
    pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true))))

/-- The public word is the tuple of the encoded pairs `⟨Y(i,0),Y(i,1)⟩`: `publicWord Y =
PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n => pairEncode (List.ofFn (Y (i, false)))
(List.ofFn (Y (i, true))))`. -/
theorem publicWord_eq {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) :
    publicWord Y = PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
      pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) := rfl

/-- Serialize a preimage table in row order, with its false and true cells adjacent: `secretWord T =
(List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten`. -/
def secretWord {n : ℕ} (T : Table n) : List Bool :=
  (List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten

/-- The secret word concatenates `T(i,0) ‖ T(i,1)` for consecutive rows `i`: `secretWord T =
(List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten`. -/
theorem secretWord_eq {n : ℕ} (T : Table n) :
    secretWord T =
      (List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten :=
  rfl

/-- A serialized table contains `n` rows of `2n` bits, hence `2n²` bits: `(secretWord T).length =
2 * n * n`. -/
theorem length_secretWord {n : ℕ} (T : Table n) : (secretWord T).length = 2 * n * n := by
  have hrow : (List.length ∘ fun i : Fin n =>
      List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))) = fun _ => n + n := by
    funext i
    simp only [Function.comp_apply, List.length_append, List.length_ofFn]
  rw [secretWord_eq, List.length_flatten, List.map_ofFn, hrow, List.ofFn_const,
    List.sum_replicate]
  simp only [nsmul_eq_mul, Nat.cast_id]
  ring

/-- Replace preimage `(i,c)` by `x`, leaving every other cell unchanged: `plantTable T i c x p = if
p = (i, c) then x else T p`. -/
def plantTable {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    (p : Fin n × Bool) : Fin n → Bool :=
  if p = (i, c) then x else T p

/-- Planting returns `x` at the selected cell and `T p` elsewhere: `plantTable T i c x p = if p =
(i, c) then x else T p`. -/
theorem plantTable_eq {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    (p : Fin n × Bool) :
    plantTable T i c x p = if p = (i, c) then x else T p := rfl

/-- The planted cell contains `x`: `plantTable T i c x (i, c) = x`. -/
theorem plantTable_at {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    plantTable T i c x (i, c) = x := by
  simp only [plantTable, if_true]

/-- A cell different from `(i,c)` retains its original preimage: if `p ≠ (i, c)`, then `plantTable T
i c x p = T p`. -/
theorem plantTable_ne {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    {p : Fin n × Bool} (hp : p ≠ (i, c)) : plantTable T i c x p = T p := by
  rw [plantTable_eq, if_neg hp]

/-- Planting a table is the ordinary update of its selected coordinate: `plantTable T i c x =
Function.update T (i, c) x`. -/
theorem plantTable_update {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) : plantTable T i c x = Function.update T (i, c) x := by
  funext p
  rw [plantTable_eq, Function.update_apply]

/-- The signature is the flattened table of preimages selected by the message bits: `tableSignature
T m j = T (k.1, m k.1) k.2` with `k = finProdFinEquiv.symm j`. -/
def tableSignature {n : ℕ} (T : Table n) (m : Fin n → Bool) : Fin (n * n) → Bool :=
  fun j => T ((finProdFinEquiv.symm j).1, m (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm j).2

/-- At the flattened index for `(i,k)`, the signature reads bit `k` of `T(i,m i)`: `tableSignature T
m (finProdFinEquiv (i, k)) = T (i, m i) k`. -/
theorem tableSignature_apply {n : ℕ} (T : Table n) (m : Fin n → Bool)
    (i k : Fin n) : tableSignature T m (finProdFinEquiv (i, k)) = T (i, m i) k := by
  simp only [tableSignature, Equiv.symm_apply_apply]

/-- The word of a selected signature concatenates the selected preimage words: `List.ofFn
(tableSignature T m) = (List.ofFn fun i : Fin n => List.ofFn (T (i, m i))).flatten`. -/
theorem ofFn_tableSignature {n : ℕ} (T : Table n) (m : Fin n → Bool) :
    List.ofFn (tableSignature T m) =
      (List.ofFn fun i : Fin n => List.ofFn (T (i, m i))).flatten := by
  have hblocks : FunFamily.blocks n n (tableSignature T m) = fun i => T (i, m i) := by
    funext i k
    rw [FunFamily.blocks_apply, tableSignature_apply]
  have h := FunFamily.ofFn_blocks_symm n n (FunFamily.blocks n n (tableSignature T m))
  rw [Equiv.symm_apply_apply, hblocks] at h
  exact h

/-- A message avoiding the planted cell has exactly its original signature: if `m i ≠ c`, then
`tableSignature (plantTable T i c x) m = tableSignature T m`.

**Proof sketch.** Entry `j` of either signature reads the cell `(k.1, m k.1)` with `k =
finProdFinEquiv.symm j`. That cell is not `(i, c)`, since `k.1 = i` would give `m i = c`, so
`plantTable_ne` returns its original preimage. -/
theorem tableSignature_plant_of_safe {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) (m : Fin n → Bool) (hm : m i ≠ c) :
    tableSignature (plantTable T i c x) m = tableSignature T m := by
  funext j
  simp only [tableSignature]
  have hp : ((finProdFinEquiv.symm j).1, m (finProdFinEquiv.symm j).1) ≠ (i, c) := by
    intro h
    have hi := congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    simp only at hi hc
    rw [hi] at hc
    exact hm hc
  rw [plantTable_ne T i c x hp]

/-- The public table applies the one-way map to every preimage: `tablePublic g T p = g (T p)`. -/
def tablePublic {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (p : Fin n × Bool) : Y := g (T p)

/-- The public image at cell `p` is `g (T p)`: `tablePublic g T p = g (T p)`. -/
theorem tablePublic_eq {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (p : Fin n × Bool) : tablePublic g T p = g (T p) := rfl

/-- Replace the public image at `(i,c)` by `y`, without knowing a preimage of `y`: `plantedPublic g
T i c y p = if p = (i, c) then y else g (T p)`. -/
def plantedPublic {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y) (p : Fin n × Bool) : Y :=
  if p = (i, c) then y else g (T p)

/-- The planted public table reads `y` at `(i,c)` and the original images elsewhere: `plantedPublic
g T i c y p = if p = (i, c) then y else g (T p)`. -/
theorem plantedPublic_eq {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y) (p : Fin n × Bool) :
    plantedPublic g T i c y p = if p = (i, c) then y else g (T p) := rfl

/-- When `y=g(x)`, the planted public table is the honest public table of the updated key. -/
theorem plantedPublic_image {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    plantedPublic g T i c (g x) = tablePublic g (plantTable T i c x) := by
  funext p
  by_cases hp : p = (i, c)
  · simp only [plantedPublic, tablePublic, plantTable, hp, if_true]
  · simp only [plantedPublic, tablePublic, plantTable, hp, if_false]

/-- The planted public table ignores the original preimage at its planted coordinate: `plantedPublic
g (plantTable T i c x) i c y = plantedPublic g T i c y`. -/
theorem plantedPublic_plant {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (x : Fin n → Bool) (y : Y) :
    plantedPublic g (plantTable T i c x) i c y = plantedPublic g T i c y := by
  funext p
  by_cases hp : p = (i, c)
  · rw [plantedPublic_eq, plantedPublic_eq, if_pos hp, if_pos hp]
  · rw [plantedPublic_eq, plantedPublic_eq, if_neg hp, if_neg hp,
      plantTable_ne T i c x hp]

/-- Extract the `i`-th preimage block from a flattened signature: `signatureBlock σ i = fun k => σ
(finProdFinEquiv (i, k))`. -/
def signatureBlock {n : ℕ} (σ : Fin (n * n) → Bool) (i : Fin n) : Fin n → Bool :=
  fun k => σ (finProdFinEquiv (i, k))

/-- Extracted block `i` reads the flattened signature at indices `(i,k)`: `signatureBlock σ i = fun
k => σ (finProdFinEquiv (i, k))`. -/
theorem signatureBlock_eq {n : ℕ} (σ : Fin (n * n) → Bool) (i : Fin n) :
    signatureBlock σ i = fun k => σ (finProdFinEquiv (i, k)) := rfl

/-- An accepting signature on a message with bit `c` at `i` supplies a preimage of `g(x)`
under the planted public table [PS10, Theorem 137.2]: if `∀ j, g (signatureBlock σ j) =
plantedPublic g T i c (g x) (j, m j)` and `m i = c`, then `g (signatureBlock σ i) = g x`. -/
theorem extract_planted {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (x : Fin n → Bool) (m : Fin n → Bool)
    (σ : Fin (n * n) → Bool)
    (hacc : ∀ j, g (signatureBlock σ j) = plantedPublic g T i c (g x) (j, m j))
    (hm : m i = c) : g (signatureBlock σ i) = g x := by
  have h := hacc i
  rw [plantedPublic_eq, hm, if_pos rfl] at h
  exact h

/-- A computation of cost zero under unit query costs is a return: if `tree.CostBoundedBy (fun _
=> 1) 0`, then `∃ a, tree = .pure a`. -/
theorem exists_pure_of_cost_zero {ι α : Type} {spec : OracleSpec ι}
    (tree : OracleComp spec α) (h : tree.CostBoundedBy (fun _ => 1) 0) :
    ∃ a, tree = .pure a := by
  cases tree with
  | pure a => exact ⟨a, rfl⟩
  | query j m k =>
    have hcost := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 0).1 h
    omega

/-- The first query of a typed signature-forging computation, or `none` if it returns: `firstQuery
(.pure a) = none` and `firstQuery (.query j m k) = some m`. -/
def firstQuery {n : ℕ} {α : Type} :
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α → Option (Fin n → Bool)
  | .pure _ => none
  | .query _ m _ => some m

/-- A return has no first query: `firstQuery (.pure a : OracleComp (bitSpec (fun _ : Fin 1 => n)
(fun _ => n * n)) α) = none`. -/
theorem firstQuery_pure {n : ℕ} {α : Type} (a : α) :
    firstQuery (.pure a : OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) = none := rfl

/-- A query node's first query is its own message: `firstQuery (.query j m k) = some m`. -/
theorem firstQuery_query {n : ℕ} {α : Type} (j : Fin 1) (m : Fin n → Bool)
    (k : (Fin (n * n) → Bool) → OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) :
    firstQuery (.query j m k) = some m := rfl

/-- The deterministic typed signing oracle returns the table's selected preimages: `tableSigner T =
QueryImpl.ofComp fun _ m => .pure (tableSignature T m)`. -/
def tableSigner {n : ℕ} (T : Table n) :
    QueryImpl (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => .pure (tableSignature T m)

/-- The table signer is the stateless implementation of `m ↦ pure (tableSignature T m)`:
`tableSigner T = QueryImpl.ofComp (fun _ m => .pure (tableSignature T m))`. -/
theorem tableSigner_eq {n : ℕ} (T : Table n) :
    tableSigner T = QueryImpl.ofComp (fun _ m => .pure (tableSignature T m)) := rfl

/-- The log of a computation with at most one query consists of its first query and answer,
or is empty if it returns immediately: `firstLog T (.pure a) = []` and `firstLog T (.query j m k) =
[⟨j, m, tableSignature T m⟩]`. -/
def firstLog {n : ℕ} {α : Type} (T : Table n) :
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α →
      QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))
  | .pure _ => []
  | .query j m _ => [⟨j, m, tableSignature T m⟩]

/-- A return has an empty first-query log: `firstLog T (.pure a : OracleComp (bitSpec (fun _ : Fin 1
=> n) (fun _ => n * n)) α) = []`. -/
theorem firstLog_pure {n : ℕ} {α : Type} (T : Table n) (a : α) :
    firstLog T (.pure a : OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) = [] := rfl

/-- A query node's first-query log contains exactly its message and deterministic answer: `firstLog
T (.query j m k) = [⟨j, m, tableSignature T m⟩]`. -/
theorem firstLog_query {n : ℕ} {α : Type} (T : Table n) (j : Fin 1) (m : Fin n → Bool)
    (k : (Fin (n * n) → Bool) → OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) :
    firstLog T (.query j m k) = [⟨j, m, tableSignature T m⟩] := rfl

/-- A computation with at most one query against the logged deterministic signer returns its
functional evaluation and exactly its first-query log: if `tree.CostBoundedBy (fun _ => 1) 1`, then
`simulate (tableSigner T).withLog tree ((), []) = .pure (tree.evalFn (fun _ m => tableSignature T
m), ((), firstLog T tree))`.

**Proof sketch.** An immediate return has no log. At a query, the signer returns its selected
preimages and appends one entry. Unit query cost leaves cost zero for the continuation, so
the continuation is a return and appends no further entry. -/
theorem honest_transcript {n : ℕ} {α : Type} (T : Table n)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) :
    simulate (tableSigner T).withLog tree ((), []) =
      .pure (tree.evalFn (fun _ m => tableSignature T m), ((), firstLog T tree)) := by
  cases tree with
  | pure a => rw [simulate_pure, OracleComp.evalFn_pure, firstLog_pure]
  | query j m k =>
    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (tableSignature T m))
      (by simpa only [Nat.sub_self] using hk.2 (tableSignature T m))
    simp only [simulate_query, QueryImpl.withLog_apply, tableSigner_eq, QueryImpl.ofComp_apply,
      OracleComp.pure_bind, ha, simulate_pure, OracleComp.evalFn_query,
      OracleComp.evalFn_pure, firstLog_query, List.nil_append]

/-- Freshness against the first-query log is exactly inequality with the optional first
message: no logged entry queried `m` if and only if `firstQuery tree ≠ some m`. -/
theorem fresh_firstLog_iff {n : ℕ} {α : Type} (T : Table n)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (m : Fin n → Bool) :
    (∀ e ∈ firstLog T tree, e.2.1 ≠ m) ↔ firstQuery tree ≠ some m := by
  cases tree <;> simp [firstLog, firstQuery]

/-- The logged one-query signing run has an output and log whose freshness condition is
equivalent to avoiding the optional first query, for any projection of a forgery's message: if
`tree.CostBoundedBy (fun _ => 1) 1`, then `∃ a log, simulate (tableSigner T).withLog tree ((), []) =
.pure (a, ((), log)) ∧ a = tree.evalFn (fun _ m => tableSignature T m) ∧ ((∀ e ∈ log, e.2.1 ≠
message a) ↔ firstQuery tree ≠ some (message a))`. -/
theorem exists_honest_transcript {n : ℕ} {α : Type} (T : Table n)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (message : α → Fin n → Bool) :
    ∃ a log, simulate (tableSigner T).withLog tree ((), []) = .pure (a, ((), log)) ∧
      a = tree.evalFn (fun _ m => tableSignature T m) ∧
      ((∀ e ∈ log, e.2.1 ≠ message a) ↔ firstQuery tree ≠ some (message a)) := by
  exact ⟨_, _, honest_transcript T tree hcost, rfl, fresh_firstLog_iff T tree _⟩

/-- The sole signing query, if present, avoids the planted cell: `Safe tree i c ↔ ∀ m, firstQuery
tree = some m → m i ≠ c`. -/
def Safe {n : ℕ} {α : Type}
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (i : Fin n) (c : Bool) : Prop :=
  ∀ m, firstQuery tree = some m → m i ≠ c

/-- Safety means that every message recorded as the first query has bit different from `c`: `Safe
tree i c ↔ ∀ m, firstQuery tree = some m → m i ≠ c`. -/
theorem safe_iff {n : ℕ} {α : Type}
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (i : Fin n) (c : Bool) :
    Safe tree i c ↔ ∀ m, firstQuery tree = some m → m i ≠ c := Iff.rfl

/-- The aborting oracle answers an unsafe query with zero and answers a safe one honestly:
`abortingAnswer T i c m = if m i = c then zeroBits _ else tableSignature T m`. -/
def abortingAnswer {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (m : Fin n → Bool) :
    Fin (n * n) → Bool :=
  if m i = c then zeroBits _ else tableSignature T m

/-- An aborting answer is zero when `m i=c`, and otherwise is the original signature. -/
theorem abortingAnswer_eq {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (m : Fin n → Bool) :
    abortingAnswer T i c m = if m i = c then zeroBits _ else tableSignature T m := rfl

/-- The aborting answer ignores the original preimage at the planted coordinate: `abortingAnswer
(plantTable T i c x) i c m = abortingAnswer T i c m`. -/
theorem abortingAnswer_plant {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) (m : Fin n → Bool) :
    abortingAnswer (plantTable T i c x) i c m = abortingAnswer T i c m := by
  rw [abortingAnswer_eq, abortingAnswer_eq]
  by_cases hm : m i = c
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, tableSignature_plant_of_safe T i c x m hm]

/-- The planted implementation remembers whether an unsafe query has occurred: `abortingImpl T i c j
m bad = .pure (abortingAnswer T i c m, bad || decide (m i = c))`. -/
def abortingImpl {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) :
    QueryImpl (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) Bool unifSpec :=
  fun _ m bad => .pure (abortingAnswer T i c m, bad || decide (m i = c))

/-- A call returns the aborting answer and sets its abort bit to `bad ∨ (m i=c)`. -/
theorem abortingImpl_apply {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (j : Fin 1) (m : Fin n → Bool) (bad : Bool) :
    abortingImpl T i c j m bad =
      .pure (abortingAnswer T i c m, bad || decide (m i = c)) := rfl

/-- The aborting implementation ignores the original preimage at its planted coordinate:
`abortingImpl (plantTable T i c x) i c = abortingImpl T i c`. -/
theorem abortingImpl_plant {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) :
    abortingImpl (plantTable T i c x) i c = abortingImpl T i c := by
  funext j m bad
  rw [abortingImpl_apply, abortingImpl_apply, abortingAnswer_plant]

/-- A safe call agrees with the updated key and leaves the abort bit false: if `m i ≠ c`, then
`abortingImpl T i c j m false = .pure (tableSignature (plantTable T i c x) m, false)`. -/
theorem abortingImpl_safe {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) (j : Fin 1) (m : Fin n → Bool) (hm : m i ≠ c) :
    abortingImpl T i c j m false = .pure (tableSignature (plantTable T i c x) m, false) := by
  rw [abortingImpl_apply, abortingAnswer_eq, if_neg hm,
    tableSignature_plant_of_safe T i c x m hm]
  simp only [hm, decide_false, Bool.false_or]

/-- A safe run with at most one signing query has exactly the honest output for the updated
key and never aborts [PS10, Theorem 137.2]: if `tree.CostBoundedBy (fun _ => 1) 1` and `Safe tree i
c`, then `simulate (abortingImpl T i c) tree false = .pure (tree.evalFn (fun _ m => tableSignature
(plantTable T i c x) m), false)`.

**Proof sketch.** A return needs no coupling. At a query, safety says that the queried message
does not reveal the planted cell, so its answer is exactly the updated key's honest answer.
The remaining computation has query cost zero and is a return; therefore the final outputs
agree and the abort flag stays false. -/
theorem planted_coupling {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (hsafe : Safe tree i c) :
    simulate (abortingImpl T i c) tree false =
      .pure (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m), false) := by
  cases tree with
  | pure a => rw [simulate_pure, OracleComp.evalFn_pure]
  | query j m k =>
    have hm : m i ≠ c := (safe_iff _ i c).1 hsafe m (firstQuery_query j m k)
    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero
      (k (tableSignature (plantTable T i c x) m))
      (by simpa only [Nat.sub_self] using (hk.2 (tableSignature (plantTable T i c x) m)))
    rw [simulate_query, abortingImpl_safe T i c x j m hm, OracleComp.pure_bind, ha,
      simulate_pure, OracleComp.evalFn_query, ha, OracleComp.evalFn_pure]

/-- Run a fixed-position planted forger and extract block `i`, returning zero after an abort:
`extractionExperiment T i c tree signature = (simulate (abortingImpl T i c) tree false).bind (fun
res => .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i))`. -/
def extractionExperiment {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) : ProbComp (Fin n → Bool) :=
  (simulate (abortingImpl T i c) tree false).bind fun res =>
    .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i)

/-- The extraction experiment simulates the aborting implementation and selects the `i`-th
signature block when the final abort bit is false: `extractionExperiment T i c tree signature =
(simulate (abortingImpl T i c) tree false).bind (fun res => .pure (if res.2 then zeroBits n else
signatureBlock (signature res.1) i))`. -/
theorem extractionExperiment_eq {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    extractionExperiment T i c tree signature =
      (simulate (abortingImpl T i c) tree false).bind (fun res =>
        .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i)) := rfl

/-- The extraction experiment ignores the original preimage at the planted coordinate:
`extractionExperiment (plantTable T i c x) i c tree signature = extractionExperiment T i c tree
signature`. -/
theorem extractionExperiment_plant {n : ℕ} {α : Type} (T : Table n) (i : Fin n)
    (c : Bool) (x : Fin n → Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    extractionExperiment (plantTable T i c x) i c tree signature =
      extractionExperiment T i c tree signature := by
  rw [extractionExperiment_eq, extractionExperiment_eq, abortingImpl_plant]

/-- The fixed-position reduction builds the planted public table, runs the forger against
the aborting signer, and extracts the `i`-th signature block: `plantedExperiment g T i c y adv
signature = extractionExperiment T i c (adv (plantedPublic g T i c y)) signature`. -/
def plantedExperiment {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y)
    (adv : ((Fin n × Bool) → Y) →
      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) : ProbComp (Fin n → Bool) :=
  extractionExperiment T i c (adv (plantedPublic g T i c y)) signature

/-- The planted experiment is extraction after running the adversary on the planted public
table: `plantedExperiment g T i c y adv signature = extractionExperiment T i c (adv (plantedPublic g
T i c y)) signature`. -/
theorem plantedExperiment_eq {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y)
    (adv : ((Fin n × Bool) → Y) →
      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    plantedExperiment g T i c y adv signature =
      extractionExperiment T i c (adv (plantedPublic g T i c y)) signature := rfl

/-- The entire planted experiment ignores the original preimage at `(i,c)`, `plantedExperiment g
(plantTable T i c x) i c y adv signature = plantedExperiment g T i c y adv signature`; this is the
coordinate-invariance hypothesis for sampling that preimage independently. -/
theorem plantedExperiment_plant {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y)
    (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool) (y : Y)
    (adv : ((Fin n × Bool) → Y) →
      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    plantedExperiment g (plantTable T i c x) i c y adv signature =
      plantedExperiment g T i c y adv signature := by
  rw [plantedExperiment_eq, plantedExperiment_eq, plantedPublic_plant,
    extractionExperiment_plant]

/-- A safe, accepting honest run whose forged message uses the planted bit produces an
inverse of the planted image in the reduction experiment [PS10, Theorem 137.2]: if
`tree.CostBoundedBy (fun _ => 1) 1`, `Safe tree i c`, and the updated-key honest output `a`
satisfies `∀ j, g (signatureBlock (signature a) j) = plantedPublic g T i c (g x) (j, message a j)`
and `message a i = c`, then `∃ z, extractionExperiment T i c tree signature = .pure z ∧ g z = g x`,
where `a = tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)`.

**Proof sketch.** The safe coupling identifies the reduction's output with the honest forged
signature block and keeps its abort bit false. Acceptance at the planted position then says
that applying the one-way map to that block gives the planted image. -/
theorem favorable_extraction {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y)
    (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) (message : α → Fin n → Bool)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (hsafe : Safe tree i c)
    (hacc : ∀ j, g (signatureBlock
        (signature (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m))) j) =
      plantedPublic g T i c (g x)
        (j, message (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)) j))
    (hm : message (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)) i = c) :
    ∃ z, extractionExperiment T i c tree signature = .pure z ∧ g z = g x := by
  refine ⟨signatureBlock
    (signature (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m))) i, ?_, ?_⟩
  · rw [extractionExperiment_eq, planted_coupling T i c x tree hcost hsafe,
      OracleComp.pure_bind]
    rfl
  · exact extract_planted g T i c x _ _ hacc hm

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Realization.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Realizing the planted Lamport experiment as a machine

## Main definitions

* `machineForger`: a machine forger on a typed public-key table, with budget one.

## Main results

* `exists_realization_machine`: T1 realizes every nonaborting successful planted transcript
  by an actual machine output, with an explicit uniform coin equivalence.

The generator, signer, evaluator, and fixed-width block reader are parameters. Their
functional contracts are assumptions about algorithms, rather than additional hardness
assumptions. The owned Lamport module discharges them from its published readers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open Complexity Turing TCSlib.Cryptography.Games
open TCSlib.Cryptography

/-- Run a machine forger on the serialized typed public table, using the canonical
message/signature codec and a budget of one signing query: `machineForger L A n Y r = A.toCompOn
(bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n)) n 1 (publicWord Y) r`. -/
def machineForger (L : PolyExpr) (A : NUPPT) (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))
      (Fin (n + n * n) → Bool) :=
  A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
    n 1 (publicWord Y) r

/-- The typed machine forger is `A.toCompOn` on the serialized public table: `machineForger L A n Y
r = A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n)) n 1 (publicWord Y) r`.
-/
theorem machineForger_eq (L : PolyExpr) (A : NUPPT) (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
    machineForger L A n Y r =
      A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
        n 1 (publicWord Y) r := rfl

/-- As a function of the public table and coins, the machine forger is the canonical
one-query `toCompOn` construction: `machineForger L A n = fun Y r => A.toCompOn (bitCodec (fun _ :
Fin 1 => n) (fun _ => n * n) (n + n * n)) n 1 (publicWord Y) r`. This form also reads it beneath an
opaque expectation. -/
theorem machineForger_eq_fun (L : PolyExpr) (A : NUPPT) (n : ℕ) :
    machineForger L A n = fun Y r =>
      A.toCompOn (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
        n 1 (publicWord Y) r := rfl

/-- Every typed machine-forger tree has unit-query cost at most one: `(machineForger L A n Y
r).CostBoundedBy (fun _ => 1) 1`. -/
theorem machineForger_cost (L : PolyExpr) (A : NUPPT) (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (r : A.Coins n) :
    (machineForger L A n Y r).CostBoundedBy (fun _ => 1) 1 := by
  rw [machineForger_eq]
  exact A.toCompOn_costBoundedBy _ _ _ _ _

/-- The planted experiment's successful nonaborting outputs are actual inverter outputs: `∃ B :
NUPPT, ∀ n, ∃ φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n, ∀ i y T c r, RedSuccess (f n)
(machineForger L A n) y T r (i, c) → ∃ x', B.runAt n (pairEncode (List.ofFn y) (List.replicate i.val
true)) (φ ((c, T), r)) = List.ofFn x' ∧ f n x' = y`, given the evaluator, generator, signer and
block-reader contracts `hEval`, `hGen`, `hSign` and `hcoin`. The machine uses one fair seed bit, one
random table, and the forger's own random tape. [PS10, machine-realization step in the proof of
Theorem 137.2].

**Proof sketch.** T1 gives a machine for the polynomial-time planting handler. Reindex its
seed by the public seed/table equivalence. On a successful planted transcript the final
abort flag is false, so its sole query was safe. A return needs no oracle call; a safe query
has the ordinary sampled-table signature and leaves the false handler state unchanged.
The remaining tree has cost zero and is a return. Thus the handler simulation and the
typed planted simulation have the same output. T1's output equation and the public
nonabort-extraction contract identify the actual machine output with that signature block. -/
theorem exists_realization_machine
    (L W : PolyExpr)
    (f : ∀ n, (Fin n → Bool) → Fin (L.eval n) → Bool)
    (E G S : List Bool → List Bool)
    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S)
    (hW : ∀ n, W.eval n = 6 * L.eval n + 6)
    (hEval : ∀ n (x : Fin n → Bool),
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x))
    (hGen : ∀ n (T : Table n),
      G (NUPPT.layout (List.replicate n true) [] [] (secretWord T)) =
        pairEncode (publicWord (tablePublic (f n) T)) (secretWord T))
    (hSign : ∀ n (T : Table n) (m : Fin n → Bool),
      S (NUPPT.layout (List.replicate n true) (pairEncode (secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (tableSignature T m))
    (hcoin : ∀ {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
      (i : Fin q), coinBlock B i (List.ofFn g).flatten = g i)
    (A : NUPPT) :
    ∃ B : NUPPT, ∀ n,
      ∃ φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n,
        ∀ (i : Fin n) (y : Fin (L.eval n) → Bool) (T : Table n) (c : Bool) (r : A.Coins n),
          RedSuccess (f n) (machineForger L A n) y T r (i, c) →
            ∃ x' : Fin n → Bool,
              B.runAt n (pairEncode (List.ofFn y) (List.replicate i.val true))
                  (φ ((c, T), r)) = List.ofFn x' ∧
                f n x' = y := by
  let H := LamportMachine.handler W E G S hE hG hS
  obtain ⟨B, hB⟩ := exists_handlerMachine A (.const 1)
    (fun _ : Fin 1 => PolyExpr.var) (fun _ => PolyExpr.mul .var .var)
    (.add .var (.mul .var .var)) H
  refine ⟨B, fun n => ?_⟩
  obtain ⟨ψ, hψ⟩ := hB n
  have hseed : H.seedLen.eval n = 1 + 2 * n * n := by
    simp only [H, LamportMachine.handler_seedLen, PolyExpr.eval_add, PolyExpr.eval_const,
      PolyExpr.eval_mul, PolyExpr.eval_var]
  have hstate : H.stateLen.eval n = 1 := by
    simp only [H, LamportMachine.handler_stateLen, PolyExpr.eval_const]
  -- T1's query, answer and output widths, read through the `PolyExpr.eval` equations.
  have hd : PolyExpr.var.eval n = n := PolyExpr.eval_var n
  have he : (PolyExpr.mul .var .var).eval n = n * n := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_var]
  have ho : (PolyExpr.add .var (.mul .var .var)).eval n = n + n * n := by
    rw [PolyExpr.eval_add, he, PolyExpr.eval_var]
  let toSeed : (Bool × Table n) ≃ (Fin (H.seedLen.eval n) → Bool) :=
    (seedCoins n).symm.trans
      (Equiv.arrowCongr (finCongr hseed.symm) (Equiv.refl Bool))
  let φ : ((Bool × Table n) × A.Coins n) ≃ B.Coins n :=
    (toSeed.prodCongr (Equiv.refl (A.Coins n))).trans ψ
  refine ⟨φ, fun i y T c r hred => ?_⟩
  let z := pairEncode (List.ofFn y) (List.replicate i.val true)
  let ω := toSeed (c, T)
  have hω : List.ofFn ω = c :: secretWord T := by
    change List.ofFn ((Equiv.arrowCongr (finCongr hseed.symm) (Equiv.refl Bool))
      ((seedCoins n).symm (c, T))) = c :: secretWord T
    rw [ofFn_arrowCongr_finCongr, ofFn_seedCoins_symm]
  have hinit : H.init n = fun _ => false := by
    funext j
    exact LamportMachine.handler_init W E G S hE hG hS n j
  have hinitWord : List.ofFn (H.init n) = [false] := by
    rw [hinit, List.ofFn_const, hstate]
    rfl
  have hadv : H.advInput n z ω = publicWord (plantedPublic (f n) T i c y) := by
    simp only [PolyHandler.advInput_eq, H, LamportMachine.handler_advIn, hω, z]
    exact advIn_context hcoin W (hW n) (f n) E G (hEval n) (hGen n) T i c y
  let tree := machineForger L A n (plantedPublic (f n) T i c y) r
  have hcost : tree.CostBoundedBy (fun _ => 1) 1 := machineForger_cost L A n _ r
  obtain ⟨a₀, habort, hinverts⟩ := (redSuccess_iff (f n) (machineForger L A n) y T r (i, c)).1 hred
  change simulate (abortingImpl T i c) tree false = .pure (a₀, false) at habort
  have hsafe : Safe tree i c := safe_of_nonabort T i c tree hcost a₀ habort
  have hrunread : H.run = LamportMachine.run S :=
    LamportMachine.handler_run W E G S hE hG hS
  -- A safe query at T1's widths is answered by its table signature, cast to the answer width.
  have hcall : ∀ (j : Fin 1) (m : Fin (PolyExpr.var.eval n) → Bool), m (Fin.cast hd.symm i) ≠ c →
      H.impl n z ω j m (H.init n) = .pure (fun k => tableSignature T
        (fun l => m (Fin.cast hd.symm l)) (Fin.cast he k), H.init n) := by
    intro j m hm
    rw [PolyHandler.impl_apply]
    apply congrArg OracleComp.pure
    apply PolyHandler.answer_of_run_eq H
    simp only [hrunread, hω, hinitWord]
    rw [List.ofFn_congr hd m, List.ofFn_congr he]
    simp only [Fin.cast_cast]
    simp only [Fin.cast_refl, id_eq]
    simpa only [z] using run_safe S (hSign n) T i c (List.ofFn y) j _ hm
  -- The planted simulation at any widths equal to T1's: substitute the widths, then read the
  -- typed tree. A return needs no query; a safe query keeps the false state.
  have htransport : ∀ (d e o q : ℕ) (Y : List Bool) (hd : d = n) (he : e = n * n)
      (ho : o = n + n * n), q = 1 → Y = publicWord (plantedPublic (f n) T i c y) →
      ∀ impl : QueryImpl (bitSpec (fun _ : Fin 1 => d) (fun _ => e))
        (Fin (H.stateLen.eval n) → Bool) unifSpec,
      (∀ (j : Fin 1) (m : Fin d → Bool), m (Fin.cast hd.symm i) ≠ c →
        impl j m (H.init n) = .pure (fun k => tableSignature T
          (fun l => m (Fin.cast hd.symm l)) (Fin.cast he k), H.init n)) →
      simulate impl (A.toCompOn (bitCodec (fun _ : Fin 1 => d) (fun _ => e) o) n q Y r)
        (H.init n) = .pure (fun k => a₀ (Fin.cast ho k), H.init n) := by
    intro d e o q Y hd he ho hq hY impl himpl
    subst d e o q Y
    simp only [Fin.cast_refl, id_eq] at himpl ⊢
    rw [← machineForger_eq L A n]
    change simulate impl tree (H.init n) = .pure (a₀, H.init n)
    cases ht : tree with
    | pure a =>
      rw [ht] at habort
      have hp : (a, false) = (a₀, false) :=
        OracleComp.pure.inj (by simpa only [simulate_pure] using habort)
      have haa : a = a₀ := congrArg Prod.fst hp
      rw [simulate_pure, haa]
    | query j m k =>
      rw [ht] at habort hcost hsafe
      have hm : m i ≠ c := (safe_iff _ i c).1 hsafe m (firstQuery_query j m k)
      have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
      obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (tableSignature T m))
        (by simpa only [Nat.sub_self] using hk.2 (tableSignature T m))
      have hp : (a, false) = (a₀, false) := OracleComp.pure.inj (by
        simpa only [simulate_query, abortingImpl_apply, abortingAnswer_eq, if_neg hm,
          hm, if_false, decide_false, Bool.false_or, OracleComp.pure_bind, ha, simulate_pure]
          using habort)
      have haa : a = a₀ := congrArg Prod.fst hp
      rw [simulate_query, himpl j m hm, OracleComp.pure_bind, ha, simulate_pure,
        haa]
  obtain ⟨a, s, hsimulation, houtput⟩ := hψ z ω r
  have hsim := htransport _ _ _ _ _ hd he ho (PolyExpr.eval_const 1 n) hadv (H.impl n z ω) hcall
  have hp : (a, s) = (fun k => a₀ (Fin.cast ho k), H.init n) :=
    OracleComp.pure.inj (hsimulation.symm.trans hsim)
  have ha : a = fun k => a₀ (Fin.cast ho k) := congrArg Prod.fst hp
  have hs : s = H.init n := congrArg Prod.snd hp
  rw [ha, hs] at houtput
  have hresult : H.result n z ω (H.init n) (fun k => a₀ (Fin.cast ho k)) =
      List.ofFn (signatureBlock (splitBits a₀).2 i) := by
    rw [PolyHandler.result_eq, show H.out = LamportMachine.out from
      LamportMachine.handler_out W E G S hE hG hS, hω, hinitWord, List.ofFn_congr ho]
    simp only [Fin.cast_cast]
    simp only [Fin.cast_refl, id_eq]
    apply out_nonabort i z (c :: secretWord T) a₀
    simpa only [z] using LamportMachine.pos_seedIn n (List.ofFn y)
      (List.replicate i.val true) (c :: secretWord T)
  refine ⟨signatureBlock (splitBits a₀).2 i, ?_, hinverts⟩
  change B.runAt n z (ψ (ω, r)) = List.ofFn (signatureBlock (splitBits a₀).2 i)
  exact houtput.trans hresult

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Seed.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
import Mathlib.Data.List.OfFn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A fair planting bit and a uniform Lamport table

## Main definitions

* `seedCoins`: a seed of `1 + 2n²` bits is a fair bit paired with a Lamport preimage table.

## Main results

* `seedCoins_apply` and `seedCoins_symm`: forward and inverse equations.
* `ofFn_seedCoins_symm`: the inverse seed word is `c :: secretWord T`.
* `ofFn_seedCoins`: the seed word decomposes into its planting bit and table serialization.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 137.2. This is generic seed serialization glue for its reduction.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

/-- The seed width `1 + 2n²` is the successor width `2n² + 1`: `1 + 2 * n * n = 2 * n * n + 1`. -/
theorem seedCoins_width (n : ℕ) : 1 + 2 * n * n = 2 * n * n + 1 :=
  Nat.add_comm _ _

/-- A seed of `1 + 2n²` bits is equivalent to a Boolean planting bit and a typed key table:
`seedCoins n : (Fin (1 + 2 * n * n) → Bool) ≃ Bool × Table n`. The bit is the first seed entry and
the table occupies the remaining entries in row order. -/
def seedCoins (n : ℕ) : (Fin (1 + 2 * n * n) → Bool) ≃ Bool × Table n :=
  ((Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)).trans
    (Fin.consEquiv (fun _ : Fin (2 * n * n + 1) => Bool)).symm).trans
      ((Equiv.refl Bool).prodCongr (tableCoins n))

/-- `seedCoins n x` consists of the first entry of `x` and the table represented by its
remaining entries, after the equality cast to successor width: `seedCoins n x = (x' 0, tableCoins n
(Fin.tail x'))`, where `x' = (Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)) x`.
-/
theorem seedCoins_apply (n : ℕ) (x : Fin (1 + 2 * n * n) → Bool) :
    seedCoins n x =
      (((Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)) x) 0,
        tableCoins n
          (Fin.tail ((Equiv.arrowCongr (finCongr (seedCoins_width n))
            (Equiv.refl Bool)) x))) := rfl

/-- The inverse seed equivalence prepends `c` to the coin tape represented by `T`, and casts
back from successor width to `1 + 2n²`: `(seedCoins n).symm (c, T) = (Equiv.arrowCongr (finCongr
(seedCoins_width n).symm) (Equiv.refl Bool)) (Fin.cons c ((tableCoins n).symm T))`. -/
theorem seedCoins_symm (n : ℕ) (c : Bool) (T : Table n) :
    (seedCoins n).symm (c, T) =
      (Equiv.arrowCongr (finCongr (seedCoins_width n).symm) (Equiv.refl Bool))
        (Fin.cons c ((tableCoins n).symm T)) := rfl

/-- The inverse seed word is the planting bit followed by the serialized key table:
`List.ofFn ((seedCoins n).symm (c,T)) = c :: secretWord T`. -/
theorem ofFn_seedCoins_symm {n : ℕ} (c : Bool) (T : Table n) :
    List.ofFn ((seedCoins n).symm (c, T)) = c :: secretWord T := by
  rw [seedCoins_symm, ofFn_arrowCongr_finCongr, List.ofFn_cons, ofFn_tableCoins_symm]

/-- Every seed word is its extracted planting bit followed by its extracted key table's
serialization: `List.ofFn x = (seedCoins n x).1 :: secretWord (seedCoins n x).2`. -/
theorem ofFn_seedCoins {n : ℕ} (x : Fin (1 + 2 * n * n) → Bool) :
    List.ofFn x = (seedCoins n x).1 :: secretWord (seedCoins n x).2 := by
  have h := ofFn_seedCoins_symm (seedCoins n x).1 (seedCoins n x).2
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/Statistics.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sampling a planted coordinate independently

## Main definitions

None.

## Main results

* `coordinate_reduction_bound`: a pointwise favorable-position bound and a
  coordinate-invariant reduction give the same bound with the challenge sampled
  independently of the table.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography.Games
open scoped Classical

-- Keep elaboration on the published probability readers.
run_cmd do
  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))

/-- Suppose every successful honest run has favorable position mass at least `b`, and
every successful favorable run makes a reduction succeed when challenged at its own
table coordinate. If the reduction ignores that original coordinate, the average
reduction success for an independent challenge is at least `b` times honest success: if `∀ T r, P T
r → b ≤ 𝔼 p, [Q T r p]`, `∀ T r p, P T r → Q T r p → R (T p) T r p` and `∀ x x' T r p, R x
(Function.update T p x') r p ↔ R x T r p`, then `b * 𝔼 T, 𝔼 r, [P T r] ≤ 𝔼 p, 𝔼 x, 𝔼 T, 𝔼 r, [R x T
r p]`, writing `𝔼 v, h v` for `ProbComp.expect (ProbComp.sample V) (fun v => h v)` with `T : Table
n`, `r : ρ`, `p : Fin n × Bool`, `x : Fin n → Bool`, and `[A]` for `if A then (1 : ℝ) else 0`.

**Proof sketch.** Bound the reduction's position average pointwise by favorable mass
on successful honest runs, and by zero on unsuccessful ones. Average over tables and
forger coins. Exchange the position average with those samples. Finally use the
coordinate-invariance hypothesis to sample the challenge preimage independently
(`ProbComp.expect_sample_coord`). This is generic probability glue for the planting
argument of [PS10, Theorem 137.2]. -/
theorem coordinate_reduction_bound {n : ℕ} [Nonempty (Fin n)]
    {ρ : Type} [Fintype ρ] [Nonempty ρ]
    (P : Table n → ρ → Prop)
    (Q : Table n → ρ → (Fin n × Bool) → Prop)
    (R : (Fin n → Bool) → Table n → ρ → (Fin n × Bool) → Prop)
    (b : ℝ)
    (hgood : ∀ T r, P T r → b ≤
      ProbComp.expect (ProbComp.sample (Fin n × Bool))
        (fun p => if Q T r p then (1 : ℝ) else 0))
    (himp : ∀ T r p, P T r → Q T r p → R (T p) T r p)
    (hinv : ∀ x x' T r p,
      R x (Function.update T p x') r p ↔ R x T r p) :
    b * ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if P T r then (1 : ℝ) else 0)) ≤
      ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p =>
        ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
          ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
            ProbComp.expect (ProbComp.sample ρ)
              (fun r => if R x T r p then (1 : ℝ) else 0)))) := by
  have hpoint (T : Table n) (r : ρ) :
      b * (if P T r then (1 : ℝ) else 0) ≤
        ProbComp.expect (ProbComp.sample (Fin n × Bool))
          (fun p => if R (T p) T r p then (1 : ℝ) else 0) := by
    by_cases hp : P T r
    · simp only [hp, if_true, mul_one]
      refine (hgood T r hp).trans (ProbComp.expect_mono _ fun p => ?_)
      by_cases hq : Q T r p
      · have hr := himp T r p hp hq
        simp only [hq, hr, if_true, le_refl]
      · simp only [hq, if_false]
        split_ifs <;> positivity
    · simp only [hp, if_false, mul_zero]
      exact ProbComp.expect_nonneg _ (fun p => by split_ifs <;> positivity)
  calc
    b * ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if P T r then (1 : ℝ) else 0)) =
      ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => b * (if P T r then (1 : ℝ) else 0))) := by
      symm
      calc
        ProbComp.expect (ProbComp.sample (Table n))
            (fun T => ProbComp.expect (ProbComp.sample ρ)
              (fun r => b * (if P T r then (1 : ℝ) else 0))) =
          ProbComp.expect (ProbComp.sample (Table n))
            (fun T => b * ProbComp.expect (ProbComp.sample ρ)
              (fun r => if P T r then (1 : ℝ) else 0)) := by
          apply congrArg (ProbComp.expect (ProbComp.sample (Table n)))
          funext T
          exact ProbComp.expect_const_mul (ProbComp.sample ρ) b
            (fun r => if P T r then (1 : ℝ) else 0)
        _ = b * ProbComp.expect (ProbComp.sample (Table n))
            (fun T => ProbComp.expect (ProbComp.sample ρ)
              (fun r => if P T r then (1 : ℝ) else 0)) :=
          ProbComp.expect_const_mul (ProbComp.sample (Table n)) b
            (fun T => ProbComp.expect (ProbComp.sample ρ)
              (fun r => if P T r then (1 : ℝ) else 0))
    _ ≤ ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => ProbComp.expect (ProbComp.sample (Fin n × Bool))
            (fun p => if R (T p) T r p then (1 : ℝ) else 0))) :=
      ProbComp.expect_mono _ (fun T => ProbComp.expect_mono _ (hpoint T))
    _ = ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample (Fin n × Bool))
          (fun p => ProbComp.expect (ProbComp.sample ρ)
            (fun r => if R (T p) T r p then (1 : ℝ) else 0))) := by
      apply congrArg (ProbComp.expect (ProbComp.sample (Table n)))
      funext T
      exact ProbComp.expect_sample_comm
        (fun r p => if R (T p) T r p then (1 : ℝ) else 0)
    _ = ProbComp.expect (ProbComp.sample (Fin n × Bool))
        (fun p => ProbComp.expect (ProbComp.sample (Table n))
          (fun T => ProbComp.expect (ProbComp.sample ρ)
            (fun r => if R (T p) T r p then (1 : ℝ) else 0))) :=
      ProbComp.expect_sample_comm
        (fun T p => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if R (T p) T r p then (1 : ℝ) else 0))
    _ = ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p =>
        ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
          ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
            ProbComp.expect (ProbComp.sample ρ)
              (fun r => if R x T r p then (1 : ℝ) else 0)))) := by
      apply congrArg (ProbComp.expect (ProbComp.sample (Fin n × Bool)))
      funext p
      exact ProbComp.expect_sample_coord p
        (fun x T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if R x T r p then (1 : ℝ) else 0))
        (fun x x' T => by
          apply congrArg (ProbComp.expect (ProbComp.sample ρ))
          funext r
          rw [hinv x x' T r p])

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication/Signatures/Lamport/TableCoins.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Asymptotic.OneWay
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lamport coin tapes as typed key tables

## Main definitions

* `tableCoins`: regroup a `2n²`-bit tape as the false and true `n`-bit preimages in each row.

## Main results

* `tableCoins_apply` and `tableCoins_symm`: the forward and inverse block equations.
* `ofFn_tableCoins_symm`: the inverse equivalence serializes a table as `secretWord`.
* `secretWord_tableCoins`: serializing the table of a tape recovers the tape's word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 137.1 and Theorem 137.2. This module is generic serialization glue for the
  protocol's preimage table.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

/-- The row-major tape width `n(2n)` equals the generator width `2n²`: `2 * n * n = n * (2 * n)`. -/
theorem tableCoins_width (n : ℕ) : 2 * n * n = n * (2 * n) := by ring

/-- A `2n²`-bit coin tape is equivalent to a table with an `n`-bit cell for each
`(i,c) ∈ Fin n × Bool`. The first cell of each row is indexed by `false`, the second by
`true`. Zero-width tapes and empty tables are included. -/
def tableCoins (n : ℕ) : (Fin (2 * n * n) → Bool) ≃ Table n :=
  ((((Equiv.arrowCongr (finCongr (tableCoins_width n)) (Equiv.refl Bool)).trans
      (FunFamily.blocks n (2 * n))).trans
      (Equiv.piCongrRight fun _ : Fin n =>
        (FunFamily.blocks 2 n).trans
          (Equiv.arrowCongr finTwoEquiv (Equiv.refl (Fin n → Bool))))).trans
      (Equiv.curry (Fin n) Bool (Fin n → Bool)).symm)

/-- The cell `(i,c)` of `tableCoins n x` is block `c` of the `i`th two-preimage row
of `x`, with `false` selecting block zero and `true` block one: `tableCoins n x (i, c) =
FunFamily.blocks 2 n (FunFamily.blocks n (2 * n) ((Equiv.arrowCongr (finCongr (tableCoins_width n))
(Equiv.refl Bool)) x) i) (finTwoEquiv.symm c)`. -/
theorem tableCoins_apply (n : ℕ) (x : Fin (2 * n * n) → Bool) (i : Fin n) (c : Bool) :
    tableCoins n x (i, c) =
      FunFamily.blocks 2 n
        (FunFamily.blocks n (2 * n)
          ((Equiv.arrowCongr (finCongr (tableCoins_width n)) (Equiv.refl Bool)) x) i)
        (finTwoEquiv.symm c) := rfl

/-- The inverse of `tableCoins` concatenates the two preimage cells of each row and then
concatenates the rows, casting only between the equal widths `n(2n)` and `2n²`: `(tableCoins n).symm
T = (Equiv.arrowCongr (finCongr (tableCoins_width n).symm) (Equiv.refl Bool)) ((FunFamily.blocks n
(2 * n)).symm fun i => (FunFamily.blocks 2 n).symm fun j => T (i, finTwoEquiv j))`. -/
theorem tableCoins_symm (n : ℕ) (T : Table n) :
    (tableCoins n).symm T =
      (Equiv.arrowCongr (finCongr (tableCoins_width n).symm) (Equiv.refl Bool))
        ((FunFamily.blocks n (2 * n)).symm fun i =>
          (FunFamily.blocks 2 n).symm fun j => T (i, finTwoEquiv j)) := rfl

/-- The word of the inverse tape is exactly the row-major secret word:
`List.ofFn ((tableCoins n).symm T) = secretWord T`.

**Proof sketch.** Reading the width cast preserves the word. The block-equivalence inverse
concatenates the words of its rows. Inside each row, the two-block inverse concatenates the
false and true preimages, which is the published serialization equation for `secretWord`. -/
theorem ofFn_tableCoins_symm {n : ℕ} (T : Table n) :
    List.ofFn ((tableCoins n).symm T) = secretWord T := by
  rw [tableCoins_symm, ofFn_arrowCongr_finCongr, FunFamily.ofFn_blocks_symm, secretWord_eq]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [FunFamily.ofFn_blocks_symm, OneWay.flatten_ofFn_two]
  rfl

/-- Serializing the table obtained from a tape recovers the tape's word:
`secretWord (tableCoins n x) = List.ofFn x`. -/
theorem secretWord_tableCoins {n : ℕ} (x : Fin (2 * n * n) → Bool) :
    secretWord (tableCoins n x) = List.ofFn x := by
  rw [← ofFn_tableCoins_symm, Equiv.symm_apply_apply]

end TCSlib.Cryptography.Authentication.LamportFill

## ===== TCSlib/Cryptography/Authentication.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Authentication.MAC.FromPRF
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Advice
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Closing
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Encoding
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
import TCSlib.Cryptography.Authentication.Signatures.Lamport.InversionProbability
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
import TCSlib.Cryptography.Hashing.FromDiscreteLog
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Authentication: MACs and signatures

The authentication constructions and games of [PS10, Chapter 5]. The hashing interface and
discrete-log construction are indexed in `TCSlib.Cryptography.Hashing`.
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Encoding` — shared encodings for the games and algorithms.
* `MAC.Defs` — the MAC interface and unforgeability game.
* `MAC.FromPRF` — the PRF-based MAC, correctness proof and security statement.
* `Signatures.Defs` — the signature interface and forgery games.
* `Signatures.Lamport` — the one-time signature construction from a strong one-way function.
* `Signatures.HashAndSign` — signatures for the hash family's full domain when the digest width fits.
* `Defs` — shared facade for the MAC, signature, and hash interfaces.
* `Hashing.FromDiscreteLog` — the discrete-log hash family used alongside these
  constructions.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
