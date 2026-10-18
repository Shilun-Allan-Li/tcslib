# External audit pack — epoch C1 and S1a, fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). Epoch
C1 is the light epoch of the chapter fills. It has four batches (C1a–C1d),
plus S1a, the four light configuration-graph lemmas split off from summit
batch S1. **42 audited-true statements** were filled, from the closed
statement gates P0, P3.1, P3.2, P4.1, P4.2, P4.3 and P4.4.

The integration record is `audits/ch34-c1-integration.md` (attached). The
fills are on PR #17 (`integrate/epoch-c1`). Fill gates close on zero blockers
and zero majors (`workflow.md` §4). The duplication rule
(`audits/TEMPLATE.md`, failure mode 5) is in force.

**The audit object.** Every proof is kernel-checked (see the maintainer's
replay). What you audit is the **surface**:

- the sanctioned public exports;
- the maintainer's pre-issue shared lemmas;
- the private helpers;
- route fidelity to the binding statement-gate derivations;
- docstrings;
- duplication.

## What changed (verify)

| Batch | Files (owned) | Targets | New public declarations (sanctioned in the brief) |
|---|---|---|---|
| C1a | `TuringMachine/NondeterministicSpace`, `SpaceComplexity/{NSPACE, SpaceClasses, Inclusions}` | 9 | none |
| C1b | `SpaceComplexity/{ZeroSpace, Examples}`, `TuringMachine/CounterProgRun` | 13 | `Complexity.evenScanTM`, `Complexity.evenScanTM_decidesInTime` |
| C1c | `TuringMachine/{OracleAgreement, OracleNondeterministic}`, `ClassOracle/Classes` | 10 | `Turing.OracleNDTM.fixChoice`, `.stepWith_eq_fixChoice_step`, `.stepWith_eq_of_ne_qQuery`, `.runWith_workTapes_invariant`, `.queryString_runWith_length_le` |
| C1d | `Formulas/{QBF, QBFEncoding}`, `ClassPSPACE/{Games, TQBF}`, `SpaceComplexity/Logspace/Reductions`, `Diagonalization/Relativization` | 6 | none (one sanctioned import, `TQBF → Inclusions`) |
| S1a | `SpaceComplexity/ConfigGraph` | 4 | `outSummary_eq_accept_iff`, `outSummary_append_congr`, `NDTM.coreSum_runWith`, `FinNDTM.not_acceptsWithin_zero` |

**Maintainer pre-issue promotions** land shared lemmas so that the batches
cite instead of copying. They are part of this gate:

- `44853c6f`:
  - `Turing.MultiTapeTM.spaceUsed_le_mul_succ` (`Finite.lean`);
  - `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff` (`ClassNP/NTIME.lean`),
    through which `Complexity.DTIME_subset_NTIME` is re-proved, statement
    unchanged;
  - `Complexity.SPACE.mono_const` and
    `Turing.FinTM.computesInSpace_zero_of_k_eq_zero`
    (`SpaceComplexity/Basic.lean`);
  - a documentation bullet in `NSPACE.lean` (P4.1 note 6).
- `447a6cc3`:
  - `Turing.NDTM.fixChoice` and `Turing.NDTM.stepWith_eq_fixChoice_step`
    (`Nondeterministic.lean`);
  - `Turing.MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps` and
    `…mem_image_workTapePos_of_ne_none` (`ConfigCount.lean`). Through these,
    the received lemmas `abs_pos_lt_card_visited` and `mem_visited_of_ne_none`
    are re-proved as one-line instances, statements unchanged.

## Brief for the auditor

1. **Statement freeze and scope.** From the attached patches and sources,
   confirm per batch:
   - no existing statement, definition or attribution changed;
   - only target bodies and new helpers changed, plus the sanctioned
     status-text and docstring-appendix edits;
   - out-of-scope sorries in shared files (`Inclusions` 2, `Classes` 4,
     `TQBF` 4, `Logspace/Reductions` 4, `Relativization` 3, `ConfigGraph` 3)
     are byte-identical.

   The maintainer's declaration-level freeze is attached.
2. **The new public surface.** Blind-restate each of the 11 sanctioned exports
   and the 8 promoted declarations from its statement. Is each true as
   stated, correctly named and attributed, and placed in its natural home?
   - **C1c's E1–E5** are the oracle twins of the plain-NDTM `fixChoice` layer.
     Check that the two layers are consistent and that neither duplicates
     the other's proofs.
   - **The re-derived** `DTIME_subset_NTIME`, `abs_pos_lt_card_visited` and
     `mem_visited_of_ne_none` keep their statements byte-identical. Verify
     this.
3. **Route fidelity.** Compare each proof with its brief's binding route (the
   statement-gate derivations quoted in each brief). Points to check:
   - **C1a:** the visited-set equality, not an inequality; the short-prefix
     inclusion as its own lemma.
   - **C1b:** exactly two machines, with the parity machine exported once;
     S9 by `sim_run` at headroom 1.
   - **C1c:** one prefix induction K serving all four agreement theorems,
     the deterministic ones as its constant-word instance.
   - **C1d:** the enumeration via the explicit rank (R1–R6).
   - **S1a:** the window, splice, count and pad route of Q3; the
     nondeterministic window facts as instances of the promoted run-generic
     lemmas.

   Report any proof that re-derives a cited lemma instead of citing it.
4. **The citation rule.** C1d's `PSPACE_eq_P_of_pspaceComplete_mem_P` was
   filled modulo C1a's `P_subset_PSPACE`. With both landed, its print has no
   `sorryAx`. Confirm that the integrated form is a genuine citation.
5. **Duplication (failure mode 5).** The maintainer reproduced each brief's
   copy-text screen before (`df2da2ed`) and after:
   - **C1a, C1d and S1a:** no new pair of their own.
   - **C1b:** one cross-file pair, `evenLang_mem_LOGSPACE` ↔
     `evenLang_mem_SPACE_zero`, at 82% and 60% of 131- and 179-character
     bodies. The brief pre-named it: both are the exported scanner plus the
     zero-tape bridge.
   - **C1c:** five in-file pairs at 54–65%:
     - `POracle_subset_NPOracle` ← `P_subset_POracle`;
     - three among the agreement theorems;
     - `runWith_headBlank` ← `stepWith_eq_of_ne_qQuery`.

   Rule on each pair: glue or copy. Rule also on C1c's E4/E5 against
   `Oracle.lean`'s private `runFrom_workTapes_invariant` and the tail of
   `queryString_length_le`. The brief pre-named them as a disclosed
   adaptation family, but the screen did not pair them.
6. **Docstrings.** Report any docstring made false. The status-text updates
   ("sorried" labels, "(spec, fill pending)" tags) and the flagged appendices
   must describe the delivered proofs.
7. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Integrity.** Every delivery's `SHA256SUMS` is OK (the zips are not
  attached, so this is an attestation). The runtime shims are excluded and
  unreferenced, and no agent script was run. The integrated files are
  byte-identical to the delivered sources.
* **Freeze** (`audits/logs/c1-integration-freeze.log`): only target bodies
  changed in each owned file, and the added publics are exactly the
  sanctioned exports.
* **Replay** (`audits/logs/c1-integration-replay.log`): 196 modules, the
  downstream closure of every changed module, on top of the merged G1, with
  fresh `.olean`s: **0 errors**. The owned files keep exactly their
  out-of-scope sorries.
* **Axioms** (`audits/logs/c1-integration-axioms.{lean.txt,log}`): 56 prints
  within the standard triple, with no `sorryAx`. The promotions' prints are in
  `audits/logs/c1-preissue-promotion-axioms.log` and in the S1a probe output.
* **Promotion replays**:
  - `audits/logs/c1-preissue-promotion-replay.log`: 204 modules at 0 errors
    (`ComputationalModels` excluded);
  - `audits/logs/s1a-preissue-promotion-replay.log`: 49 modules at 0 errors.
* **Lint** (`audits/logs/c1-integration-stylelint.log`): 0 FAIL in six
  directories.
* **Screens** (`audits/logs/c1-integration-screens/`): before and after for
  each batch, with the exact file lists (`file-lists.txt`). The screen script
  `audits/evidence/retrofit/copy-text-screen.py` is attached, as are the
  owned sources and every comparison source **except**
  `Build/Catalog.lean` (579 KB, comparison-only in C1a's list, no pair
  involving it). It is identified by its Git blob at `df2da2ed`, `5f582dd83dc557f3bc6e5f912d01b53c97b10856`, on the
  public repository.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/ch34-c1-fill-findings.md`. The gate closes on zero blockers and zero
majors.
