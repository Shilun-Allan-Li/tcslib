# The seam-layout contract (PR #124): resolutions

**Gate:** the statement gate of PR #124, `Turing.exists_seamLayoutTM` in
`TuringMachine/Build/SeamLayout.lean` (sorried). Pack: `audits/seam-layout-statements-pack.md`,
preserved as dispatched. Round 1's bundle: folder `43-seam-layout-statements-gate/` (SHA-256
`1ab146c0…4385`).

## Round 1: FAIL (0 blockers, 2 majors, 1 minor, 7 notes)

The findings are in `audits/seam-layout-statements-findings.md`, verbatim. The maintainer's review
(`audits/evidence/c1/seam-layout/gate43-review.md`) verified every finding at `0355da56`: all true,
at the auditor's severities.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The sketch does not compose the cited catalog contracts (no head in `[0, |s|]` meets `skipBackTM_run_ofCfg`'s hypothesis; copy and clear already return their heads). | **Fixed in round 2:** eight phases joined by `phaseHostTM`, each naming how the previous endpoint meets its row's `_run_ofCfg` hypothesis; two leaves (aligned pairs, the unary split), each with the reason no row serves; the exact time `T = 2n − r + 4h + 5q + 2|v| + 23 ≤ 18(n + 1)`, checked by a simulation of the rows' own tables (14,400 and 110,887 instances; `r2/sim-*.txt`). |
| 2 | major | `T` was chosen after the configuration, so it could depend on the input; the universal startup needs a code-uniform exact first exit. | **Fixed in round 2 by the user's ruling (2026-10-18): accept the statement change.** `∀ a v q r, r ≤ |s| → ∃ T ≤ C·(|s| + 1), ∀ {z} d, …, d.workTapePos src = r → …`: the start and end are verbatim; only the time's dependence is restricted. The round-1 form is a corollary, so the other consumers lose nothing. A fixed time formula in the statement was the alternative not taken. |
| 3 | minor | The probe never applied the contract, and used a local stand-in for `bufferTape_of_neg`; the PR body and the pack overstate it. | **True.** The round-2 probe (`r2/SeamLayoutConsumerR2.lean.txt`) applies the contract: the round-1 corollary, the universal startup's exit with its tapes `k` and `k + 1`, and `Rep`'s fields from R1′'s capture endpoint through #122's `FinTM.bufferTape_of_neg`, assembled by `Rep_iff`. The PR body is corrected; the round-1 pack is preserved. |

**The user's other rulings (2026-10-18):**
- **Who proves it: a standalone fill**, along round 2's eight-phase sketch, after round 2's gate.
  U2-S's continuation may then import `Build/SeamLayout` (no cycle) and cite it. (U2-S's delivery
  built no split leaf, so there was nothing to promote.)
- **The stack:** #125 and #126 (gates 44 and 45 passed) are restacked below #124, so they can merge
  while this round 2 is gated.

## Round 2

- **The head:** `lean/seam-layout` at `45b79f5f`, on #126's `5fd5dce8`: the round-1 commit and the
  review's patch (`r2/r2-seamlayout.patch`, SHA-256 `7d53196e…3a51`), with the docstrings and the
  facade entry reworded in public-facing terms (no campaign labels; the user's preference of
  2026-10-17).
- **Checks:** elaboration against `oleans-lc1w`, 0 errors, the contract's `sorry` only; the freeze
  flags the intended statement change; the round-2 probe has only its inline contract's `sorry`.
- **Replay:** `replay-lseam2.sh`, 2 modules, chained from `oleans-lx2b`. **Passed (user,
  2026-10-18):** 2 of 2 at `45b79f5f`, 0 failed, static-equal (1).

## Round 2: PASS (0 blockers, 0 majors, 1 minor, 11 notes)

Gate 46 (dispatch folder `46-seam-layout-statements-r2-gate/`, bundle SHA-256 `301f6081…a347`).
The findings are in `findings-r2.md`, verbatim. The maintainer's review
(`campaign/items/c1/seam-layout/gate46-review.md`) verified every finding at `45b79f5f`: all
true, at the auditor's severities.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The PR description kept the superseded fill plan (U2-S's private leaf promoted), round 1's check and replay identifiers (`oleans-lndnf`; `replay-lseam.sh` from `oleans-lc1w`), and miscounted the route ("eight exact `_run_ofCfg` contracts and two named leaves"). | **Fixed in the records; no `.lean` change.** The PR description is replaced by `campaign/items/c1/seam-layout/r2/pr-body-gate46.md`: the standalone-fill ruling; round 2's checks and replay (`replay-lseam2.sh` from `oleans-lx2b`, passed); eight phases, six catalog rows and two leaves. It also records the merged stack and the moved paths. Round 1's records (`pack.md`, `findings.md`, `campaign/items/c1/seam-layout/pr-body.md`, `gate43-review.md`) and `r2/pr-body.md` (as dispatched) are preserved; this row records their supersession. |
| 2–12 | note | Integrity and the freeze; achievability with `C = 18`; the phase joins and the exact time; the three consumers; non-vacuity and the edge cases; docstrings, imports and reuse; the attestations; lint. | **No action.** Notes 3–9 carry forward to the standalone fill's brief (the route, the time ledger, the edge cases): the review's section (c). |

**The gate closes (PASS).** #124's statement is final. The standalone fill proves it along the
eight-phase sketch.
