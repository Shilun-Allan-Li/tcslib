# External audit pack — B6 F5: the ruler device's boundary test (PR #133, a fill gate)

Campaign: the Arora-Barak chapter 4 plan, B6 (the space hierarchy's hosts). The fill brief F5
(`campaign/fills/b6/briefs/b6-fill-rulerdevice.md`) targets the three machine contracts of the
bounded-prefix ruler device in `TCSlib/Complexity/TuringMachine/Build/InputDevice.lean` (host H5):
the restoring boundary test `Turing.exists_rulerTestTM`, the call rows
`Turing.exists_rulerDeviceTM` and the host `Turing.exists_rulerHostTM`.

The worker's delivery (`campaign/fills/b6/reports/rulerdevice-1-REPORT.md`; a recovery delivery
after a lost workspace, rebuilt from a fresh clone) proves **the boundary test**; the other two
stay `sorry`. The maintainer's review is `campaign/fills/b6/reviews/rulerdevice-1/REVIEW.md`. **It
lands as a partial.**

**The head:** `lean/b6-f5-partial` at `9e7dd574`: the review's head `9af530e2` (two commits on the
campaign branch at `dac6b3b0`) with the campaign branch merged in after #132 (`e9e97970`; no
conflict, the PR's own files byte-unchanged):
- `8a887ed0`: the worker's commit `f9810ddf`, cherry-picked from its verified bundle;
- `9af530e2`: the maintainer's.
  - **The joint move** (the user's ruling on the review's F1, 2026-10-18): the module imports
    `Build/Catalog` and builds the test's table from `Turing.tapeAction`, its step from
    `Turing.step_of_tapeAction_move`, replacing the delivery's private copy (`rd_move`,
    `rd_move_apply`).
  - **Public-facing docstrings** (the review's F2): the target's implementation note; the two
    open targets keep their base proof sketches without the delivery's appendices; the module
    status names the proved test and drops a records path.
  - Two blank-line nits.

## Brief for the auditor

1. **Freeze.** 15 → 15 publics, 0 → 9 privates; the only body change is the target's
   (`evidence/freeze.txt`). The import added is `Build/Catalog`, by the user's ruling: does it
   create a cycle, or change any downstream statement?
2. **The proof of `exists_rulerTestTM`:** a hand-built one-tape controller moving the input head
   and the ruler head in the same step; one forward-and-return trajectory identified by a single
   induction, exact time `2ℓ + 2`, `C = 2`. Is it correct for every `ℓ > 0` and `p ≥ ℓ`,
   including `p = ℓ` (the verdict `yes`) and the empty payload? Does it restore both heads and
   change no tape and no output?
3. **Rule 10:** after the maintainer's swap to `tapeAction`, does the proof read every other
   file's definition only through published lemmas? The seal of ten definitions
   (`evidence/B6F5LandSeal.lean.txt`, `evidence/seal-axioms.out`) passes; is the list complete?
4. **The swap's fidelity:** the table's five actions as `tapeAction 0 a none b q` against the
   delivery's `rd_move q a b` (`evidence/landing.patch`). Same semantics?
5. **What remains admitted:** `exists_rulerDeviceTM` and `exists_rulerHostTM` only; do their
   docstrings still state binding proof sketches, now without appendices?
6. **Public-facing text:** the new and changed docstrings carry no campaign labels.

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lseam2`: 0 errors; 2 warnings, the two open targets' `sorry`
  (lines 436, 500) (`evidence/elab-InputDevice.out`).
- **Seal and axioms:** with `MultiTapeTM.step`, `runFrom`, `Action.apply`, `moveInputPos`,
  `FinTM.bufferTape`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `MultiTapeTM.outputSymbol`,
  `Cfg.init` and `tapeAction` made `local irreducible`, the module elaborates; `exists_rulerTestTM`
  depends on `[propext, Classical.choice, Quot.sound]` (`evidence/seal-axioms.out`).
- **The review** (on the delivery): integrity (10/10 sums, the bundle, the patch), scope, a seal of
  nine definitions with a control, the 111-check import probe (0 errors), rule 11, the sweep logs
  (80/80 modules, 35 → 34 sorries).
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 38 files (`evidence/lint.txt`).
- **Screen (v3)**, the brief's 11 files plus `Build/Catalog` (`evidence/screen-population.txt`):
  699 → 707 declarations, 487 → 488 pairs; the one new pair is in-file, `rd_trace_step` against
  `rd_read_nat` at 81% (`evidence/screen-before.txt`, `screen-after.txt`, `pairdiff.txt`).
- **Replay:** `replay-l133.sh`: the changed modules' downstream closure on the merged tree (4 modules: `TuringMachine/Build/InputDevice`, `TuringMachine/UniversalK`, `TuringMachine/SelfUniversal`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 4 of 4, 0 failed, static-equal (5) (`evidence/replay-l133.*`, `evidence/down-l133.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/51-b6-f5-rulerdevice-fill/findings.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `b6-f5-rulerdevice-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
