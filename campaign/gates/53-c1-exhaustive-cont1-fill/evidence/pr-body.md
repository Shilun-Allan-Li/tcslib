## The exhaustive replay of a fixed NDTM, proved (C1-E continuation 1, a full landing)

`ClassNP/ExhaustiveReplay.lean`: **`Turing.FinNDTM.exists_exhaustiveDecider` is proved.** One
deterministic machine `E` decides a fixed NDTM's acceptance within `C·2^{C·(T + 1)}` steps
wherever every branch halts within `T` ([AB09, §3.2, proof of Theorem 3.2]), with
`C = 18·N.k + 41` depending only on the machine and no `|z|` term. Through the proved
`Turing.ndAcceptsWithin_decider_of_universal` (`BF := E(UN)`), the exponential decider
`Turing.exists_ndAcceptsWithin_decider` now has exactly one open dependency: the universal NDTM
`Turing.exists_timed_universal_NDTM`.

**Commits** (on the campaign branch at `3638965b`):
- the fill worker's 16 commits `1eabca5e..041c82ab`, cherry-picked from its verified bundle
  (prerequisite `9e77d2b2`; the owned file is unchanged from there to the tip); the first adds
  the three authorized imports alone. They add 183 private `xr_` declarations and no public one;
- `b5629b91`, the maintainer's (the review's suggested fix, verified there):
  - `xr_branch_inputPos_le` closes by `simpa [NDTM.initCfg_eq]` rather than through simp's
    unfolding of `NDTM.initCfg` (rule 10; the review's F1);
  - the private section's header in public-facing terms (F2); the module's main results;
  - `ClassNP`'s contents line and `exists_ndAcceptsWithin_decider`'s docstring: the replay is no
    longer called pending.

**The user's rulings (2026-10-18):**
- **The route's one deviation is accepted** (the review's F4): the brief's obligation 4 returned
  the heads to `0` between replays; the proof leaves them in place and uses translation invariance
  (`xr_runWith_shift`), clearing a radius `2L` around each head. It is sound because the replay
  lemma holds from any configuration; the worker disclosed it.
- **Proof sketches follow up** (F3): 24 private proofs over 20 lines have no "Proof sketch"
  (policy §3); the six main lemmas get sketches in a docstring-only follow-up.
- **File size:** 3,245 lines (the lint's size warning); file size alone is not a driver (the
  user's standing ruling).

### Checks (maintainer, against `oleans-lc6m`, #131's replay at the merged state)

- **Elaboration:** `ExhaustiveReplay` 0 errors, 0 warnings; the target and
  `ndAcceptsWithin_decider_of_universal` depend on `[propext, Classical.choice, Quot.sound]`.
  `NTimeHierarchy` (docstring edit) 0 errors, its two remaining sorries; `ClassNP` 0 errors.
- **Freeze:** 2 → 2 public, 0 → 183 private; the only body change is the target's.
- **Lint:** `ClassNP` 0 FAIL, 16 WARN over 21 files (the size warning above);
  `Diagonalization` 0 FAIL.

### Review

The maintainer's review of the delivery verified integrity (47/47 sums, the bundle, 16 linear
commits, patch = bundle = file), scope (three hunks in the owned regions, statements frozen),
elaboration at the base and the tip, a rule-10 seal of 31 other-file definitions with controls,
rule 11, the brief's 64-check and the worker's 260-check probes (0 errors), the screen (297 → 428
declarations, 106 → 228 pairs, all 122 new pairs inside the file, none touching the hazards),
lint, and the worker's 77-module sweep (sorry warnings 19 → 18). Records:
`campaign/fills/c1/reviews/exhaustive-cont1/`; the worker's report
`campaign/fills/c1/reports/exhaustive-2-REPORT.md`.

### Replay

At the merged state: the campaign branch after #132 (`e9e97970`) was merged into this branch, with
no conflict and this PR’s files byte-unchanged. `replay-l136.sh`: the changed modules' downstream closure on the merged tree (4 modules: `ClassNP/ExhaustiveReplay`, `ClassNP`, `Diagonalization/NTimeHierarchy`, `Diagonalization`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 4 of 4, 0 failed, static-equal (2) (`campaign/gates/53-c1-exhaustive-cont1-fill/evidence/replay-l136.*`, `campaign/gates/53-c1-exhaustive-cont1-fill/evidence/down-l136.txt`).

### Gate

Gate 53 (`campaign/gates/53-c1-exhaustive-cont1-fill/`): pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

