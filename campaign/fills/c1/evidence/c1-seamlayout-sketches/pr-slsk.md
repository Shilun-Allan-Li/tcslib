**The seam layout's proof sketches** (`Build/SeamLayout`), docstrings only: a `**Proof sketch.**`
paragraph for each of the 14 long private proofs that lacked one (gate 59's resolutions, row 2;
policy §3). The code is identical to the campaign branch's with comments stripped; no statement,
public declaration or import changes. A docstring-only PR needs no gate (the user's ruling).

**Commits:** `ff8d5f10` (on the seam layout's landing `126127b8`), and `6efc5be0`, the campaign
branch after #154 merged in (clean; `SeamLayout` was unchanged there since `126127b8`).

**Checks:** against `oleans-lun2` (the campaign's Lean tree) the module elaborates with no output;
no line over 100 characters; the added text (83 lines) has no campaign labels, paths or dates.

**Replay:** `replay-lslsk.sh`, `SeamLayout`'s downstream closure (7 modules: `SeamLayout`,
`NDCodeSimulator`, `Diagonalization/NTimeHierarchy`, `Diagonalization`, `UniversalK`,
`SelfUniversal`, the `TuringMachine` facade), chained from `oleans-lun2`. **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
