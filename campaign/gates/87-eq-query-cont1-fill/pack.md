# External audit pack — E-Q cont1, the stage query's main machine (PR #176, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1-E (the nondeterministic time hierarchy's
diagonalizer, [AB09, proof of Theorem 3.2 and Figure 3.1]). The fill brief E-Q cont1
(`campaign/fills/eq/briefs/eq-fill-query-cont1.md`, the copy dispatched with its 4 `@ANCESTOR@`
placeholders filled as `43fe918f`) has one target in
`TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean`: the stage query's main machine, the
contract `hmain` that checkpoint 1 (PR #173, gate 83) reduced `Turing.NTimeDiag.exists_queryTM` to.

The worker (Claude, a single fill) delivered it **complete**
(`campaign/fills/eq/reports/eq-fill-query-cont1-REPORT.md`; evidence
`campaign/fills/eq/evidence/eq-fill-query-cont1/`): all seven checkpoints, `exists_queryTM`
proved, the file's one sorry left `exists_diagonalizer`'s (out of scope). The maintainer's review
(`campaign/fills/eq/reviews/fill-cont1/REVIEW.md`, with `maintainer-notes.md`): **land with edits;
0 blockers, 0 majors, 4 minors, 9 notes**, and the maintainer's F14. **The user ruled
(2026-10-27): land as recommended** — the landing edits E1–E5, F4 ratified (below), the subjects
reworded with authorship and trailers kept, four duplication-ledger entries; F11 (the frozen proof
sketch's resync) left to the deferred docstring cleanup.

**The head:** `lean/eq-cont1-landing` at `cecd76a0f996411d5371f91e8d4e3757e122fd60`, nine commits
on the campaign tip after #174 (`evidence/patches/`):
- the worker's eight commits `21dd053c` … `e952bc50`, cherry-picked from the verified bundle,
  their subjects reworded without campaign labels (the review's F10 list) and two bodies' leaf
  labels replaced by the leaves' names; author and trailers unchanged; their file at the eighth
  equals the delivered head's;
- `cecd76a0`, the maintainer's landing edits: E1–E4, the review's tested diff
  (`campaign/fills/eq/reviews/fill-cont1/out/25-landing-edits.diff`; the result equals the review's
  tested file, SHA-256 `2e29f0d8…`), and E5, the proof sketches of nine privates the policy linter
  flags (F14).

## What changed (verify)

| Class | Change |
|---|---|
| **Target's body** | `Turing.NTimeDiag.exists_queryTM`: the landed `suffices` on `hmain`, now closed by `exact qy_main hf hg` |
| **Privates** | 3 → 214: the main machine `qyM₁` over the kit `QyKit`, its setup, locator round and loop, the input seek, the stage code, the two writers, the private leaves `qyCmpTM` (a framed length comparison) and `qyEmitTM` (a repeating emitter), and their run lemmas |
| **Frozen** | every public statement (22 → 22), every landed private, `exists_diagonalizer` and its docstring |
| **Imports** | none added |
| **Text** | the new docstrings; the module header's status (E4); the `**Implementation status.**` paragraph (region (d)) |

**F4, ratified:** the brief named scan folds for the `n ≥ 3` test and the power-of-two test; the
proof uses the private comparator for `n ≥ 3` and decides the rung by building the next rung
`2^{X⁴}` in unary and comparing it with `1^{n+1}` (no power-of-two test is needed).

## Brief for the auditor

1. **Correctness.** Is `exists_queryTM` proved as stated? In particular:
   - the kit and its calls; the setup (`qy_setup_long`, `qy_setup_short`);
   - one round as a `Turing.Round` with its three escapes (`qy_round`), and the loop's ledger
     (`qy_loop`, `qy_ledger`: the passed rungs summing to `2 ℓ_s`, the polylogarithmic terms linear);
   - the writers (`qy_mid_run`, `qy_top_run`) and the words they emit (`qy_writer_word`);
   - `qy_main`, whose statement is the landed `hmain` verbatim.
2. **Route conformance.** F4 (ratified) and the refinements in the report's "Route refinements
   against the brief": are they within the brief's allowances (private leaves L2 and L6 only;
   published rows wherever one exists)?
3. **Rule 10** (with the scope of 2026-10-23). The review's maximal seal makes all 275
   semireducible, non-instance TCSlib definitions of other files irreducible, the 34 the new code
   reaches among them, and erases the four `@[simp]` ones; the body elaborates sealed with 0 errors,
   and its 289 controls close unsealed and fail sealed (`out/16-seal-summary.txt`,
   `out/27-land-seal-summary.txt` at the E1–E4 file; E5 is docstring text only). The worker's own
   seal (43 definitions, 43 controls) is in the evidence's `seal/`. The review classified 2,949
   tactic-argument rows (`out/14-tactic-args.txt`). Is any other-file definition unfolded or closed
   by reduction?
4. **Rule 11** and the 88 new public constants, all derived instances of private types and their
   auxiliaries (F7).
5. **Duplication.** The worker's screens (`screens/`: 120 new pairs, 0 gone, every new pair with
   an owned-file declaration), the review's dispositions (F2, F5, F6) and the four ledger entries
   (`campaign/duplication-ledger.md`, RO-1, NB-1, RC-1, QF-1). E3 re-points two `Nat.bits`
   lemmas to Mathlib's `Nat.size` facts. The maintainer's screen at the landing head:
   ⟨summary⟩.
6. **The public-facing text** after E1, E4 and E5; F11's frozen sketch (deferred).
7. **The landing.** Are the cherry-picks the delivered commits (patch-ids), and the maintainer's
   commit exactly E1–E5?

## Repository-side attestations (verify or challenge)

- **Elaboration** of the landed file against `oleans-lnfapi4` (the snapshot of the tree after
  #174, the tip's Lean): one warning, `exists_diagonalizer`'s sorry (`evidence/elab.out`). The
  review's audit at the E1–E4 file: `exists_queryTM` and all 1,323 local constants but
  `exists_diagonalizer` within `[propext, Classical.choice, Quot.sound]` (`out/28-land-audit.out`).
- **Freeze:** `out/28-land-checks.txt` (base → landed: 22 → 22 public, only the target's body).
- **Lint:** `Diagonalization` 0 FAIL, 3 WARN over 5 files (the file's size among them;
  `evidence/lint-head-Diagonalization.txt`); the policy linter: the file's size only.
- **Replay:** `replay-leqc1.sh` (`evidence/merged-tree/`), `NTimeDiagonalizer`, `NTimeHierarchy`
  and the `Diagonalization` facade from `oleans-lnfapi4`. ⟨Running.⟩

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/87-eq-query-cont1-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `eq-query-cont1-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
