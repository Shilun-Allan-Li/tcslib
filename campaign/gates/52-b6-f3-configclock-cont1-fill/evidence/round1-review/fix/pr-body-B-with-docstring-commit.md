## The configuration clock's components, proved (B6 F3 continuation 1, a partial landing)

`SpaceComplexity/WindowClock.lean`: six private lemmas toward the configuration-clock windowed
runner `Turing.exists_configWindowRunnerTM`, which stays sorried with its proof sketch. No public
declaration and no admission is added; the module's sorry count is unchanged.

**Commits** (on the campaign branch at `dac6b3b0`):
- `169cc6c2`: the fill worker's commit `c887ee89`, cherry-picked from its verified bundle
  (prerequisite `94b986d4`; the owned file is unchanged from there to the tip). It adds:
  - `cw_field_total` and `cw_record_clock`: the clock arithmetic at the actual record (the
    record's field cells `k(2s + 1) + posWidth |x| + 2`, and the all-true word over
    `c = C + |Q| + 8` passes, of width at most `c · L` and value large enough for every round up
    to `configBound + 1`, the extra halt-test round included);
  - `cw_leftTM`, `cw_left_run`: the one-cell left move;
  - `cw_copy_constant`: a field's constant mapped copy;
  - `cw_clear_patch`: the clock's clear after the runner.
- `b160813c`: the maintainer's, docstrings only:
  - the target's partial paragraph in public-facing terms, headed "Implementation status." (the
    review's rewording, without campaign labels);
  - the module status: the stale records path and the gate label go; the proved private lemmas
    are named.
- `⟨SHA⟩`: the maintainer's, docstring only (gate 52, minor 8): the implementation status
  paragraph now says that the clock these lemmas prepare is Route A's over field cells
  (`W = c · F ≤ c · L`), copied one field at a time with the blank separators skipped, and that
  the Route A sketch's whole-layout construction (`W := c_M · L` by `copyTM`/`scanTM`, text
  before this landing, unchanged) is an alternative that is not implemented and would also
  have to handle the separators.

### Checks (maintainer, against `oleans-lseam2`, #124's replay)

- **Elaboration:** exit 0; the target's sorry warning only (line 420; line 426 after
  `⟨SHA⟩`, against `oleans-l134`).
- **Freeze:** 4 → 4 public, 5 → 11 private; the only body change is the target's (its docstring).
- **Lint:** `SpaceComplexity` 0 FAIL, 81 WARN over 107 files.
- **Screen (v3)**, the brief's 21 files: 1,048 declarations, 510 pairs, 147,693 characters,
  byte-for-byte the review's after-screen on the delivery; 0 new pairs.

### Review

The maintainer's review of the delivery verified integrity (10/10 sums, the bundle, the patch),
scope (owned regions only, no statement changed, rule 11), the elaboration at base and tip, the
axiom walks, a rule-10 seal of 17 definitions with a control, the 134-check import probe and the
consumer probe, lint, and the screens (1,043 → 1,048 declarations, 510 → 510 pairs, 0 new).
Records: `campaign/fills/b6/reviews/configclock-cont1/`; the worker's report
`campaign/fills/b6/reports/configclock-cont1-REPORT.md`. The worker's escalation E2 (an
adjacent-write identity with no public lemma) is real but not a blocker. **Ruled (user,
2026-10-18): option B**, a public `Turing.wordPatch_append` in `Build/StepClock`, by PR #139
with its own API gate (56). It is not part of this landing; F3's continuation 2 cites it.

### Replay

At the merged state: the campaign branch after #132 (`e9e97970`) was merged into this branch, with
no conflict and this PR’s files byte-unchanged. `replay-l134.sh`: the changed modules' downstream closure on the merged tree (2 modules: `SpaceComplexity/WindowClock`, `SpaceComplexity`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (1) (`campaign/gates/52-b6-f3-configclock-cont1-fill/evidence/replay-l134.*`, `campaign/gates/52-b6-f3-configclock-cont1-fill/evidence/down-l134.txt`).

After `⟨SHA⟩` (docstring only; the closure is the same 2 modules): `replay-l134b.sh`, chained
from `oleans-l132b`, pinning blob `dd542c8b`. **⟨Pending / Passed (user, date): 2 of 2,
0 failed, static-equal (1)⟩** (`campaign/gates/52-b6-f3-configclock-cont1-fill/evidence/round1-fix/`).

### Gate

Gate 52 (`campaign/gates/52-b6-f3-configclock-cont1-fill/`): **PASS, 0 blockers, 0 majors,
1 minor, 12 notes; closed.** The minor (documentation synchronization) is fixed by `⟨SHA⟩`
and this body.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

