# External audit pack — B6 F3 continuation 1: the configuration clock's components (PR #134, a fill gate)

Campaign: the Arora-Barak chapter 4 plan, B6 (the space hierarchy's hosts). The fill brief F3
cont1 (`campaign/fills/b6/briefs/b6-fill-configclock-cont1.md`) targets the configuration-clock
windowed runner `Turing.exists_configWindowRunnerTM`
(`TCSlib/Complexity/SpaceComplexity/WindowClock.lean`), what `Complexity.space_hierarchy`'s
diagonalizer cites.

The worker's delivery (`campaign/fills/b6/reports/configclock-cont1-REPORT.md`) proves six private
components; **the target stays `sorry`**. The maintainer's review is
`campaign/fills/b6/reviews/configclock-cont1/REVIEW.md`. **It lands as a partial.**

**The head:** `lean/b6-f3-cont1-partial` at `c2c53ee5`: the review's head `b160813c` (two commits on
the campaign branch at `dac6b3b0`) with the campaign branch merged in after #132 (`e9e97970`; no
conflict, the PR's own files byte-unchanged):
- `169cc6c2`: the worker's commit `c887ee89`, cherry-picked from its verified bundle;
- `b160813c`: the maintainer's, docstrings only: the target's partial paragraph in public-facing
  terms ("Implementation status.", the review's rewording), and the module status without the
  stale records path and gate label.

## Brief for the auditor

1. **Freeze.** 4 → 4 publics, 5 → 11 privates; no statement changed; the target's only change is
   its docstring (`evidence/freeze.txt`).
2. **The six components** (`cw_*`):
   - `cw_field_total`, `cw_record_clock`: the record's field cells, `k(2s + 1) + posWidth |x| + 2`,
     and the all-true word over `c = C + |Q| + 8` passes of them: width at most `c · L`, and a
     value exceeding the runner's cost for every round up to `configBound + 1`, the extra
     halt-test round included. Is the arithmetic right, and is `c` a per-machine constant?
   - `cw_leftTM`, `cw_left_run`: the one-cell left move, a leaf.
   - `cw_copy_constant`: one field's constant mapped copy.
   - `cw_clear_patch`: the clear of the clock after the runner, leaving the clock tape blank.

   Are they correct, on the brief's route, and what the writer (the continuation) needs?
3. **The worker's escalation E2** (the review's F1): merging two adjacent constant writes needs an
   identity whose only proof is `Build/RecordTable`'s private `rt_adjacentWrites`. Is it real? Is
   it a blocker for the writer, given that the identity is a short interval case split? (Ruled by
   the user on 2026-10-18: a public `Turing.wordPatch_append` in `Build/StepClock`, PR #139 with
   its own gate 56; it is not part of this landing, and F3's continuation 2 cites it.)
4. **Rule 10:** do the components read every other file's definition only through published
   lemmas? The review's seal of 17 definitions, with a control, passes
   (`campaign/fills/b6/reviews/configclock-cont1/out/`).
5. **The text:** the target's "Implementation status." paragraph and the module status, against
   the proved lemmas; no campaign labels. The Route A sketch's `W := c_M · L` through
   `copyTM`/`scanTM` is left as a valid alternative; is that acceptable, or misleading?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lseam2`: 0 errors; 1 warning, the target's `sorry` (line 420)
  (`evidence/elab-WindowClock.out`).
- **The review** (on the delivery): integrity (10/10 sums, the bundle, the patch), scope, rule 11,
  elaboration at base and tip, the axiom walks, the seal, the 134-check import probe and the
  consumer probe (0 errors), lint 0 FAIL, and the v3 screen 1,043 → 1,048 declarations,
  510 → 510 pairs, 0 new.
- **Lint:** `SpaceComplexity` 0 FAIL, 81 WARN over 107 files (`evidence/lint.txt`).
- **Screen (v3)** at the head, the brief's 21 files (`evidence/screen-head.txt`, `pairdiff.txt`
  against the review's after-screen): 1,048 declarations, 510 pairs, 147,693
  characters, byte-equal to the review's after-screen on the delivery; 0 new pairs.
- **Replay:** `replay-l134.sh`: the changed modules' downstream closure on the merged tree (2 modules: `SpaceComplexity/WindowClock`, `SpaceComplexity`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (1) (`evidence/replay-l134.*`, `evidence/down-l134.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/52-b6-f3-configclock-cont1-fill/findings.md`. The gate closes when it has zero
blockers and zero majors.

**Deliver your findings as a downloadable Markdown file named
`b6-f3-configclock-cont1-fill-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
