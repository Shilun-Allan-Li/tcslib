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
