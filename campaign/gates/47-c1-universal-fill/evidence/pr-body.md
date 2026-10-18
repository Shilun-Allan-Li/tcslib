# PR #129 body, as retrieved 2026-10-18 (head `3a1678d1`)

## C1-UN: three of the universal's four targets proved (a partial landing)

This lands the C1-UN fill's partial delivery (2026-10-17; the worker's report and the maintainer's
review are recorded in the campaign records under `audits/`). The file is
`Diagonalization/NTimeHierarchy.lean`.

| Target | Status |
|---|---|
| `Turing.exists_ndAcceptsWithin_decider` (BF) | **proved**, from the universal and the exhaustive decider (both cited stubs) |
| `Complexity.ntime_hierarchy_of_pos` (H′) | **proved**, modulo `Complexity.ntime_hierarchy` |
| `Complexity.NTIME_linear_ssubset_square` (S) | **proved**, modulo `Complexity.ntime_hierarchy` |
| `Turing.exists_timed_universal_NDTM` (UN) | still `sorry`. The setup's scratch cleanup needs a published contract for the pair extractor's halting configuration (the worker's escalation, confirmed by the review). |

### What

Two commits on the campaign tip; one file.
- **`8449bdd3`**, the worker's commit `483fb579`, cherry-picked from its verified bundle. It
  contains the three proofs.
- **`3a1678d1`**, the maintainer's: the worker's "fill appendix" paragraphs are folded into
  public-facing docstrings, and the module's status text is corrected. Docstrings only.

No statement or declaration is added or changed.

### Checks

- **Elaboration** against `oleans-lx2b` (the tip's snapshot): 0 errors. 2 `sorry` warnings, the
  universal and `ntime_hierarchy` (the module had 5).
- **Axioms:** the three proved results reach `sorryAx` only through those cited stubs, and E's.
- **Freeze:** 5 → 5 publics. The only body changes are the three proofs.
- **The review:**
  - a seal test with the 8 other-file definitions the proofs reach;
  - the 72-check import probe;
  - the v3 screen, 67 → 70 declarations with no new pair.
- **Lint:** `Diagonalization/` 0 FAIL, 1 WARN, unchanged.
- **Replay:** `replay-lun.sh`, 2 modules (`NTimeHierarchy` and the `Diagonalization` facade), from
  `oleans-lx2b`. Its closure is disjoint from #124's, so the two can merge in either order.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

