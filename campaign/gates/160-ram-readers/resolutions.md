# Gate 160 resolutions

## Round 1: HOLD (0 blockers, 1 major, 1 minor, 8 notes; `findings.md`, verbatim)

The eight reader statements were found correct (G160-04 to G160-07, G160-10). Neither finding
changes them.

- **G160-01 (major), resolved in the records and by a scope decision.** The tier 3 brief named
  four admitted dependencies, called them "three", and missed two more. Its prescribed route
  for `mem_P_of_decides` uses `WordRAM.HaltsWithin.mono` and `HaltsWithin.touches_le`, which
  are admitted in `Programs/WordRAM/Extended.lean`. That file has 18 admissions in all: the
  extended RAM's run calculus, on which tier 2 also rests.
  - **Seyoon (2026-11-17): add them to the work as tier 0** (`fill-ram-steps`). The scope is now
    32 admissions in four tiers (`items/ram-tm/PLAN.md` §0). Tier 3 is dispatched only after
    tier 0 has landed, so its route reaches no admitted `HaltsWithin` helper.
  - **Tier 3 brief corrected** (`briefs/fill-ram-classes.md`): a table of the six dependencies
    with their tiers and status, replacing the miscounted list.
  - **`COMMON.md`:** every fill whose target reaches `sorryAx` must now report a dependency walk
    listing the admitted declarations reached. The walk is modeled on the chapters 3–4 probe
    `CloseHeadlines`, because an axiom print cannot tell them apart.
  - **Tier 0 needs readers for the vendored run calculus.** `Extended.lean` reads
    `WordRAM.step`, `effect` and `Steps` from `Programs/WordRAM/Steps.lean`, which published no
    general equations for them. Seyoon (2026-11-17) approved four readers there, marked as TCSlib
    additions in the vendored header: `step_def`, `effect_def`, `Steps.zero_iff` and
    `Steps.succ_iff`. They are added to this PR. The vendored definitions and lemmas are
    unchanged.
- **G160-02 (minor), repaired.** The docstrings of `simTime_eq` and `simSpace_eq` now state
  their formulas. `FinNDTM.decidesInSpace_iff`'s docstring now states the all-branch halting,
  exact-length space and acceptance clauses. Commit `7ee903a4`.

PR #370's head moves from `e75d2907` to `25040f43`:
1. the G160-02 docstrings;
2. the four vendored readers.

Round 2 audits that head. The gate's run 2, on the intermediate head `7ee903a4`, was stopped at
30/265 when the vendored readers were added. The evidence is from run 3.
