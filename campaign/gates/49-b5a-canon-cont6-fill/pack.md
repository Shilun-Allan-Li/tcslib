# External audit pack — the canonizer's continuation 6 (PR #131, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, B5a, the polynomial canonizer
`Turing.MachineFormat.exists_polyCanonizer` (`TCSlib/Complexity/TuringMachine/CodeSimulator.lean`).
Its remaining admission is the private grammar-stage stub `exists_canonGrammarStage`. Continuation
6 (`campaign/fills/b5a/briefs/b5a-fill-canon-cont6.md`) completed phases 1 and 2 of 4 (the
worker's report: `campaign/fills/b5a/reports/canon-7-REPORT.md`), adding five proved private
lemmas. The maintainer's review is `campaign/fills/b5a/reviews/canon-cont6/REVIEW.md`. **It lands
as a partial.**

**The head:** `lean/canon-cont6-partial` at `aababd27`, stacked on #130 (`CodeSimulator`'s
downstream closure contains `UniversalK`, which #130 changes), two commits:
- `f703beaa`: the worker's commit `a406c7ee`, cherry-picked from its verified bundle;
- `aababd27`: the maintainer's. The review's F1 makes two steps of `exists_canonRecordRound` read
  `Cfg.mapState` through `mapState_workTapes` / `mapState_workTapePos` pointwise, instead of
  closing by definitional unfolding. The worker's two new "fill appendix" paragraphs are removed.

## Brief for the auditor

1. **Freeze.** 12 → 12 publics, 144 → 149 privates; no statement changed (`evidence/freeze.txt`).
2. **The five lemmas:**
   - the fresh-anchor return adapter `canonReturnAdapter`;
   - its C2 instance `exists_canonRecordRound`;
   - the skipper-to-counter-loop link `canonCounterRepeat`, with `canonRepeat_orbit` and
     `canonRepeat_last`.

   Are they correct, on the brief's route, and what phase 3 (the stage) needs?
3. **Rule 10:** after F1's fix, does the new code read every other file's definition only through
   published lemmas? The review's seal of 13 definitions found F1; the fix passes it.
4. **What remains admitted:** the headline reaches `sorryAx` only through
   `exists_canonGrammarStage` (`evidence/elab-CodeSimulator.out`).

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lx2b`: 0 errors; 2 warnings, the stub and
  `exists_uniformSimulator`, as at the base.
- **The review:** integrity; the import probes 241/241, 118/118 and 15/15; the v3 screen 2,416
  declarations, with no new pair.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN.
- **Replay:** `replay-lc6.sh`, 9 modules (`CodeSimulator`'s downstream closure), chained from
  `oleans-lu2s`. **Passed (user, 2026-10-18):** 9 of 9 at `aababd27`, 0 failed, static-equal (7).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/49-b5a-canon-cont6-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `b5a-canon-cont6-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
