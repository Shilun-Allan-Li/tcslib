# Gate 167 round 3: resolutions

The round-3 mirror is `items/ram-tm/prog2/PROG2Mirror.lean.txt`, 1,295 lines; round 2's is kept
as `PROG2Mirror-r2.lean.txt`. It elaborates with 0 errors and 67 sorried statements
(`prog2/mirror.log`).

| # | Severity | Resolution |
|---|---|---|
| G167-02 | major | `StartUp` joins the edit set (header and design §4). The program's code locations are restated over the extended code: `xcodeAt_headCode`, `xcodeAt_mainStmt`, `xcodeAt_tailCode`, `xcodeAt_dispatcher`, `xcodeAt_startCode`. `steps_start` is restated over the projection (`steps_start_proj`) and as an extended run with its footprint (`xsteps_start`). Its memory calculations (`startMem`, `rel_startMem`, `agreeOutside_startMem`) stay over `List Instr`. The header names exactly which files change. |
| G167-05 | minor | Readers: `XStmt.silent_leaf` (all six silent leaves), `calls_seq`, `calls_ite`, `calls_while`, `calls_leaf`, `xcells_eq`, `xcellCount_eq` and `xstoreLocal_eq`. `XSetting.cells` has `XSetting.cells_eq`. No other new landing definition lacks a reader. |
| G167-07 | minor | The footprint is part of the simulation. `XSetting.cells` is `[-max(2Q, 25 + 4·disp), lim.space)`, and `XFinished.run` is now an `XStepsIn` run within it, so `xsim` freezes the per-step obligation. The header and `xsim`'s sketch name the route: `stepsIn_straight`, footprint versions of the expression, condition and call lemmas, `XStepsIn.of_stepsIn_proj`, and the new `xStepsIn_mono` and `xStepsIn_trans` (in place, `WordRAM.XStepsIn.mono` and `.trans` in `Extended`). `xcompileProgram_correct`'s sketch composes `xsteps_start`, `xsim` and the tail within `xcells`, which equals the setting's cells for the whole-program setting. |
| G167-08 | minor | `check_emit_vs_verdict` (emitting `-3` emits `true`; returning `-3` rejects), `check_missing_entry` and `check_zero_depth` (the outermost call has no run). |
| R2-N1 – N8 | note | No change needed. |
