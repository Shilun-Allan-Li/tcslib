# Gate 167 round 3 minors: resolutions (round 4 text)

Round 3 was **CLEAR** (0 blockers, 0 majors, 2 minors; `findings-r3.md`). Both minors are
wording repairs to the mirror's header and the design note; no statement changed. The mirror is
`items/ram-tm/prog2/PROG2Mirror.lean.txt`, 1,311 lines; round 3's text is kept as
`PROG2Mirror-r3.lean.txt`. It elaborates with 0 errors and the same 67 sorried statements
(`prog2/mirror.log`, on `oleans-cl169-cl166`).

| # | Severity | Resolution |
|---|---|---|
| G167-R3-01 | minor | The header no longer calls `StartUp` untouched: it keeps its straight-line code and memory calculations, and `steps_start` changes. `ProgramCode`'s migration list now names `mainCode` (to `List XInstr`, with `tailCode` under `.base`), `codeAt_bodiesCode` and `codeAt_bodies` (its `code` becomes an `XProgram`, `XCodeAt` throughout; its one caller is `WholeProgram`'s `bodyAt`), and lists the layout definitions and `List Instr` parts that keep their types. The header and design §4 separate the unchanged base-instruction lemmas from the footprint companions H2 adds (expression, condition, call-frame and dispatcher runs, with state-dependent address bounds for indirect loads and stores; the start-up's is `xsteps_start`). |
| G167-05 | minor | `XSetting.xlim` is marked **mirror only**, in its docstring, the header and design §4: in place `Light.Limits` carries `input`, the setting's `input` field is `lim.input`, and `S.xlim` is `S.lim`. No new public name. |
| N1 – N5 | note | No change needed. N3's route (segment footprint obligations with state-dependent bounds) is carried into the H2 brief. |
