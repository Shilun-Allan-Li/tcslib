# PR #130 body, as retrieved 2026-10-18 (head `0530e5c6`)

## U2-S: the universal startup's first phase (a partial landing)

This lands the U2-S fill's partial delivery (2026-10-17; the worker's report and the maintainer's
review are recorded in the campaign records under `audits/`) in `TuringMachine/UniversalK.lean`.
The target `Turing.exists_selfStartupTMK` stays `sorry`.

### What

Two commits on the campaign tip; one file.
- **The worker's commit `259a349d`**, cherry-picked from its verified bundle. It adds 15 proved
  private helpers (`ss_*`):
  - the cleaned-canonizer bundle and its contracts;
  - the suffix-uniform first halt of the prefix;
  - the restarted returning capture, with its first return, silence and space bound;
  - the tape layout.
- **The maintainer's commit:** the worker's "fill appendix" paragraph is removed. The progress
  is in the records. Docstring only.

No public declaration, statement or admission is added or changed.

### Checks

- **Elaboration** against `oleans-lx2b`: 0 errors. 3 warnings, the module's three existing
  contracts, as at the base.
- **Freeze:** 12 → 12 publics; 0 → 15 privates.
- **The review:** axioms within `[propext, Classical.choice, Quot.sound]`; a seal test with 21
  other-file definitions; the 174-check import probe; the v3 screen 655 → 668 declarations,
  with no new pair.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN.
- **Replay:** `replay-lu2s.sh`, 3 modules (`UniversalK`, `SelfUniversal` and the `TuringMachine`
  facade), from `oleans-lx2b`. It overlaps #124 only in the facade, which nothing imports but the
  root.

### For the continuation (the review)

- **An API gap:** the buffered composite's second-phase fields are published at a different
  tape-index type; a cast-indexed pair (`rfl`) is drafted.
- **Phase 3 cites the seam-layout contract** (#124, round 2 in its gate). A standalone fill
  proves it.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

