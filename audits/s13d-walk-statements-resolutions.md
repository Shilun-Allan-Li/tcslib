# §13d walk statement gate (G4's ruler): resolutions (round 1; gate CLOSED)

**Gate:** the lockstep walk unit (`audits/s13d-walk-statements-pack.md`; bundle SHA-256
`66f5d2706e470117524a45b2057569b765b555ddf2316193b541d4dd40622b6d`, 50 sections, folder 28):
`walkTM` and its framed row, the skip as its instance, `framedContract` (with `sweepContract` its
instance), `seekPost`, and the walk, seek and scan contracts.

**Round 1** (`audits/s13d-walk-statements-findings.md`, verbatim): **PASS, 0 blockers, 0 majors,
2 minors.** The auditor could not run Lean. It independently regenerated both unit files, re-ran
the base screen and the affected tiling, and checked every wrapper's fields against its row.
**The gate is closed.** The unit lands in PR #109.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The G4 hosts survey asks a length-`m` ruler to move both heads `m` cells; `walkTM` moves them `m + 1` (one past the delimiter) | **Erratum, recorded here; the survey is kept unchanged as evidence.** G4's fill brief uses the actual convention and the auditor's adjustment. For a positive distance `m`, step the ruler head once alone, then walk over the ruler's tail (length `m − 1`), so the other head moves exactly `m`. Distance `0` is a separate stationary branch. Ruler restoration and the control transitions are costed in the fill. |
| 2 | minor | The walk's sketch named `catalog_pass_contract`, which the proof does not use, and explained the walk through the skip, now its corollary | **Fixed in PR #109:** the sketch describes the forward configurations, the blank transition, and `catalog_trace_run` with the stationary return family. |

## Rulings (adopted)

All six brief items are accepted:
- the walk, including the empty ruler, zero direction and extra moved heads;
- the skip instance;
- the constructor and `sweepContract`;
- the six wrappers;
- the approved mirror pair;
- the records, with the two corrections.

## Carried

To G4's fill brief:
- finding 1's convention adjustment;
- the auditor's reminder that ruler construction and doubling, scratch-buffer coexistence,
  cleanup and the complete geometric cost remain the fill's obligations, under the surveyed
  public round and composition hosts.
