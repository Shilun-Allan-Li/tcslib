# PR #125's body, as retrieved 2026-10-17 (head `4ab012d9`)

## §13d G4, continuation 1: the partial's landing (layout bridges and the cascade reordering)

This lands the G4 continuation-1 fill's partial delivery (2026-10-17;
`audits/s13d-agent-reports/g4-cont1-REPORT.md`), reviewed in
`audits/evidence/s13d-g4-cont1-fill/REVIEW.md`. **Both targets stay sorried:**
`exists_zoneRebalanceTM` and `exists_zoneExtendTM` (`Build/ZoneRebalance.lean`). The proved
pieces are on the brief's route and are carried into continuation 2. This follows the precedent
of G4's first partial.

**Stacked on #124** (the seam-layout contract), keeping the replay chain linear: every PR in the
stack reaches the `TuringMachine` facade. Merge #121 through #124 first.

### What

One file, `Build/ZoneRebalance.lean`; two commits.
- **`778f9ada`**, the worker's commit `66765b0c`, cherry-picked from the verified bundle:
  - the four phase-0 re-pointings (statements preserved; every replacement lemma public);
  - 13 private helpers: the two layout bridges, the offset formulas, a generic field-layout
    comparison, both seek preconditions, the total cascade's side-pass reordering
    `zr_cascade_passes`, and `zr_left_two_walks`, the arithmetic of the worker's escalation;
  - no public declaration and no admission.
- **`4ab012d9`**, the maintainer's:
  - the review's F1: one step of `zr_zonedTape_right_fields` reads `FinTM.bufferTape` through
    `bufferTape_nat` rather than by definitional reduction (rule 10);
  - the extension appendix's escalation label `E1` → `cont1-E1` (it collided with the first
    round's E1), with the review's path.

### Checks (maintainer)

- **Elaboration** against `oleans-lndnf`: 0 errors. The two targets' `sorry` warnings, as at the
  base.
- **The review** (against `oleans-lbapi4` and `oleans-lndnf`):
  - axioms standard for all 31 privates;
  - the import probe 338/338;
  - no other file's private constant;
  - the sealed-definition check passes with F1's fix.
- **Lint:** 0 FAIL, warnings unchanged; widest line 99.
- **Screen** (the brief's 10-file population): 795 → 808 declarations, 437 → 439 pairs, 127,810 →
  127,994 characters (the base is the brief's measured base). The two new pairs are within the file,
  `zr_pair_pass`/`zr_inPass_out` (72%, 62%), as the review found; no cross-file pair
  (`land/screen-*.txt`).
- **Replay:** `replay-lg4c1.sh`, 2 modules (`Build/ZoneRebalance` and the `TuringMachine` facade),
  chained from `oleans-lseam` (#124's replay).

### Continuation 2 (for the record)

- **The review's F2:** the left route is one cell short. A route amendment within the permitted
  rows (an unadjusted first walk, or one extra one-cell step) goes into the cont2 brief.
- **Restate** one seek precondition: the extension's second seek runs on an altered tape.
- **The phase-1 contracts as checkpoints:** the right pass, the return home, the left pass,
  `ℓ = 0`, the clear, the assembly.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

