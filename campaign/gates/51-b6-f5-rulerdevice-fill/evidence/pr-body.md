## The ruler device's boundary test, proved (B6 F5 phase 1, a partial landing)

`TuringMachine/Build/InputDevice.lean`: **`Turing.exists_rulerTestTM` is proved**, the restoring
suffix-boundary test of the bounded-prefix ruler device (host H5). The call rows
`Turing.exists_rulerDeviceTM` and the host `Turing.exists_rulerHostTM` stay sorried with their
proof sketches. The module's sorry count goes 3 → 2.

**Commits** (on the campaign branch at `dac6b3b0`):
- `8a887ed0`: the fill worker's commit `f9810ddf`, cherry-picked from its verified bundle
  (prerequisite `94b986d4`; the owned file is unchanged from there to the tip). It adds 11
  private `rd_` declarations.
- `9af530e2`: the maintainer's.
  - **The joint move** (the user's ruling on the review's F1, 2026-10-18): the module imports
    `Build/Catalog` and builds the test's table from `Turing.tapeAction`, its step from
    `Turing.step_of_tapeAction_move`, instead of the delivery's private copy (`rd_move`,
    `rd_move_apply`). That leaves 9 private declarations. The phase-2 brief authorizes the same
    import.
  - **Public-facing docstrings** (the review's F2): the target's implementation note, without
    campaign labels; the two open targets keep their proof sketches and lose the delivery's
    appendices; the module status names the proved test and drops a stale records path.
  - Two blank-line nits.

### Checks (maintainer, against `oleans-lseam2`, #124's replay)

- **Elaboration:** exit 0; the two open targets' sorry warnings only (lines 436, 500).
- **Seal and axioms:** with ten other-file definitions `local irreducible` (`MultiTapeTM.step`,
  `runFrom`, `Action.apply`, `moveInputPos`, `FinTM.bufferTape`, `Cfg.inputSymbol`,
  `Cfg.workTapeSymbols`, `MultiTapeTM.outputSymbol`, `Cfg.init`, `tapeAction`), the module
  elaborates; `exists_rulerTestTM` depends on `[propext, Classical.choice, Quot.sound]` only.
- **Freeze:** 15 → 15 public, 0 → 9 private; the only body change is the target's.
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 38 files (the tip's count).
- **Screen (v3)**, the brief's 11 files plus `Build/Catalog`: 699 → 707 declarations,
  487 → 488 pairs. The one new pair is in-file, `rd_trace_step` against `rd_read_nat` at 81%
  (the shared `bufferTape_nat` lookup), as the review found; no cross-file pair.

### Review

The maintainer's review of the delivery verified integrity (10/10 sums, the bundle, the patch),
scope (owned regions only, no statement changed), the elaboration at base and tip, a seal of nine
definitions with a control, the 111-check import probe, rule 11, lint and the screens. Records:
`campaign/fills/b6/reviews/rulerdevice-1/`, the worker's report
`campaign/fills/b6/reports/rulerdevice-1-REPORT.md`.

### Replay

At the merged state: the campaign branch after #132 (`e9e97970`) was merged into this branch, with
no conflict and this PR’s files byte-unchanged. `replay-l133.sh`: the changed modules' downstream closure on the merged tree (4 modules: `TuringMachine/Build/InputDevice`, `TuringMachine/UniversalK`, `TuringMachine/SelfUniversal`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 4 of 4, 0 failed, static-equal (5) (`campaign/gates/51-b6-f5-rulerdevice-fill/evidence/replay-l133.*`, `campaign/gates/51-b6-f5-rulerdevice-fill/evidence/down-l133.txt`).

### Gate

Gate 51 (`campaign/gates/51-b6-f5-rulerdevice-fill/`): pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

