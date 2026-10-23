# U2-S continuation 1: integration erratum to `startup-cont1-REPORT.md`

**Scope.** One statement of the worker's report (`startup-cont1-REPORT.md`, beside this file, blob
`36fbcf37…`), as corrected at integration. The report itself stays as delivered. Sources: the
maintainer's review (`campaign/fills/u2s/reviews/startup-cont1/REVIEW.md`, F3) and gate 63, the
fill gate of PR #147 (`campaign/gates/63-u2s-startup-cont1-fill/`, minor 2). It does not change
the delivered Lean: `Turing.exists_selfStartupTMK` is proved, admission-free once the seam layout
(#145) is in.

## The probe inventory

The worker's extended probe (`U2SWorkerProbe121.lean`) has **121 checks of 118 distinct names**:
`Turing.Cfg.workTapeSymbols_eq`, `Turing.step_of_tapeAction_move` and `Turing.FinTM.bufferTape_eq`
are each checked twice. The new code also cites four public lemmas the probe lacks:
`Turing.FinTM.bufferTape_left`, `Turing.FinTM.moveInputPos_neg_val`,
`Turing.MultiTapeTM.runFrom_zero` and `Turing.Cfg.ext`. The full-file elaborations resolved them, so
this is an inventory gap, not an admission. The corrected probe, deduplicated with the four added,
has 122 checks of 122 names and elaborates with 0 errors as a standalone import against the merged
tree's snapshot (`campaign/gates/63-u2s-startup-cont1-fill/evidence/round1/U2SProbeDedup.*`).
