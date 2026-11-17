# Statement recheck of the 14 admissions (2026-11-17, against `complexity/ram-simulation` at `8fe5003d`, whose Lean is `main` `5cb25d52`)

- **Statements:** all 14 elaborate on the branch (main builds them, `oleans-cc91f4`). Their
  class targets unfold to the shapes the stage-2 simulation delivers (`RamDefs.out.txt`). The
  nine tier 3 bound arithmetics close with `logSpace ≥ 1` and `logSpace ≤ S`. **No statement
  change is needed.**
- **Cited names:** all 51 identifiers cited in the three files' docstrings exist in the build
  (`RamCited.out.txt`, one hit each; `HaltsWithin.mono` resolves to `WordRAM.HaltsWithin.mono`
  among three).
- **Stale line pointers:** six of the eight `File.lean:line` pointers in the docstrings have
  drifted (Catalog 2033 → 2219, Embed 241 → 253, InputCall 294 → 291, Seam 813 → 886,
  AlphabetReduction 546 → 545, Constructible 485 → 480 and 329 → 324). InputLength 473 and
  WordRAM/Basic 62–63 are still right. The fills drop line numbers from the sketches they
  rewrite (`briefs/COMMON.md` rule 5).
- **Missing readers for tier 3 (rule 10):** `mem_DTIME_iff` (ClassP/DTIME), `mem_NSPACE_iff`
  and `FinNDTM.decidesInSpace_iff` (SpaceComplexity/NSPACE), `NL_eq` (SpaceClasses), and
  equations for `outputOf`, `simTime`, `simSpace` (RAMSimulation/Simulation). Existing:
  `mem_SPACE_iff`, `decidesInSpace_iff`, `computesInSpace_iff`, `LOGSPACE_eq`, `mem_P_iff`,
  `decidesInTime_iff`, `spaceConstructible_iff`, `logSpace_eq`.
