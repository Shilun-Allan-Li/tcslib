# B5a, the uniform simulator (PR #170, a fill gate): resolutions

**Gate:** the fill gate of PR #170 (`lean/b5a-unisim-landing` at `101434fd`). Pack `pack.md`;
bundle SHA-256 `b69054e065388b77e883e7d5872ca9afaea003c7c64c56fbc978ba044f73727e` (132 sections),
the records at `06d98035`. **Findings: pending.**

**Merge state. #170: not yet clear to merge** (2026-10-27): it waits for this gate. `replay-lb5am`
passed (user, 2026-10-27): 10 of 10 modules, static-equal (0 mismatches; `CodeSimulator`
sorry-free; `NTimeHierarchy`'s one sorry is `ntime_hierarchy`; `evidence/merged-tree/`) at the head
`101434fd`, whose base is the campaign branch. Its snapshot is `oleans-lb5am`. Against it, the axiom
prints of the target, targets 3–8, `NPOracle_EXPCOM_subset_EXP` and
`Complexity.baker_gill_solovay` are all `[propext, Classical.choice, Quot.sound]`
(`evidence/merged-tree/B5aDownstreamAxioms.*`): **Baker–Gill–Solovay is admission-free**, and the
status lines of `Codes2Tape`, `EXPCOM` and `Relativization` are accurate.
