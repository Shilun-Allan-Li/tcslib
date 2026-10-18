# PR #123's body, as retrieved 2026-10-17 (head `c567568f`)

## C1-W: the bounded choice writer's contract, proved

This PR lands **`Turing.ndWriterTM_run_block`** (`TuringMachine/Build/NDHost.lean`), C1 wave 1's fill
W. The proof is the fill worker's own draft, from its environment-blocked delivery of 2026-10-17
(`audits/c1-fill-agent-reports/writer-1-REPORT.md`). The maintainer's review repaired it
(`audits/evidence/c1/fills/writer-1/REVIEW.md`), and the user ruled on 2026-10-17 that it lands
by a maintainer PR and a fill gate.

**Stacked on #122.** The replay closures overlap. Merge #121 and #122 first.

### What

Two commits: the proof (`7fdd7797`) and the `TuringMachine` facade's `Build/NDHost` entry
(`c567568f`). No statement, definition or public declaration changes.

- **The proof:** one induction over the written prefix, the brief's route, using published lemmas
  only (`NDTM.stepWith_of_some`, `NDTM.runWith_append`/`_cons`/`_nil`, the `Action.apply_*`
  field equations, `FinTM.bufferTape_append`, `Cfg.workTapeSymbols_eq`). It unfolds only
  `ndWriterTM` (this file's frozen definition) and its own private `wr_cfg`.
- **Six private helpers:** `wr_cfg` (the configuration after writing a prefix), `wr_tape_append`,
  `wr_cfg_nil`, `wr_cfg_scan`, `wr_cfg_stepWith` and `wr_prefix`.
- **The review's repairs:**
  - four one-line fixes to the worker's draft (an `rfl` after `Action.apply_state`, `↓reduceIte`
    for `if_pos rfl` twice, and two `simp only` lemmas);
  - one merge: the draft's two step lemmas, a 91% screen pair, are one lemma
    (`wr_cfg_stepWith`), which branches on the scanned cell.
- **Docstrings:** the module's status texts no longer call the writer sorried. The worker's
  "Fill appendix" is not landed.

### Checks (maintainer, against `oleans-lndnf`)

- **Elaboration:** 0 errors, 0 warnings. The module had one `sorry` and now has none.
- **Axioms:** `ndWriterTM_run_block` and the seven assembly theorems that pass the writer
  (`guessRunTM_runWith_handoff`, `_handoff_state`, `_live`, `guessRunTM_runWith`,
  `guessRunTM_haltsWithin`, `guessRunTM_accepts_iff`, `guessRunTM_silent_spec`) use
  `propext`, `Classical.choice` and `Quot.sound`.
- **Freeze:** 25 → 25 publics, 2 → 8 privates (the six helpers). No statement changed. The only
  body changes are `ndWriterTM_run_block`'s proof and `guessRunTM_runWith_handoff`'s docstring.
- **Lint:** 0 FAIL; `TuringMachine/` stays at 63 WARN. Records in
  `audits/evidence/c1/fills/writer-1/land/`.
- **Screen** (the brief's 7-file population): 780 → 787 declarations, 1,018 → 1,020 pairs, 380,649 → 380,919 characters. The two
  new pairs are `guessRunCfg`/`wr_cfg` (56%, 50%), within the file. The base equals the brief's
  measured base exactly.
- **Replay:** `replay-lc1w.sh`, 2 modules (`Build/NDHost` and the `TuringMachine` facade),
  chained from `oleans-lndapi2` (#122's replay).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

