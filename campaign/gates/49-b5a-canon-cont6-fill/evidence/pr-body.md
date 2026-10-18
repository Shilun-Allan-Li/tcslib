# PR #131 body, as retrieved 2026-10-18 (head `aababd27`)

## Canonizer continuation 6: the return adapter and the counter-loop link (a partial landing)

This lands the canonizer continuation-6 fill's partial delivery (2026-10-17; the worker's report and
the maintainer's review are recorded in the campaign records under `audits/`) in
`TuringMachine/CodeSimulator.lean`. The headline `Turing.MachineFormat.exists_polyCanonizer` still
depends on the private stub `exists_canonGrammarStage`, as before.

**Stacked on #130** (the U2-S landing): `CodeSimulator`'s downstream closure includes `UniversalK`,
which #130 changes, so the replays chain. Merge #130 first; this PR is then retargeted to the
campaign branch.

### What

Two commits.
- **`f703beaa`**, the worker's commit `a406c7ee`, cherry-picked from its verified bundle. It adds
  five proved private lemmas:
  - the fresh-anchor return adapter `canonReturnAdapter`;
  - its C2 instance `exists_canonRecordRound`;
  - the generic skipper-to-counter-loop link `canonCounterRepeat`, with `canonRepeat_orbit` and
    `canonRepeat_last`.
- **`aababd27`**, the maintainer's:
  - the review's F1: two steps of `exists_canonRecordRound` now read `Cfg.mapState` through
    `mapState_workTapes` / `mapState_workTapePos`, applied pointwise, instead of closing by
    definitional unfolding;
  - the worker's two new appendix paragraphs are removed. The progress is in the records.

No public declaration, statement or admission is added or changed.

### Checks

- **Elaboration** against `oleans-lx2b`: 0 errors. 2 warnings, the stub and
  `exists_uniformSimulator`, as at the base.
- **Axioms:** `exists_polyCanonizer` reaches `sorryAx` only through `exists_canonGrammarStage`.
- **Freeze:** 12 → 12 publics; 144 → 149 privates (the five).
- **The review:**
  - a seal of 13 other-file definitions around the new code (F1 found this way, then fixed);
  - the import probes 241/241, 118/118 and 15/15;
  - the v3 screen 2,416 declarations, no new pair.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN.
- **Replay:** `replay-lc6.sh`, 9 modules (`CodeSimulator`'s downstream closure), chained from
  `oleans-lu2s` (#130's replay).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

