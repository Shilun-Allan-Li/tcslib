## The bounded input window copier, proved (C1-WC continuation 1, a full landing from a repaired draft)

`TuringMachine/Build/InputWindow.lean`: **`Turing.exists_inputWindowCopyTM` is proved.** From
its entry, with the input head on the `p`-th input symbol and a delimited counter word of value
`d` on tape `j`, one machine copies the window `y = (z.drop p).take d` onto tape `dst` within
`6·(|y| + 1) + 2|w|` steps and not before, leaving every other tape, head and the output
unchanged. It is the window R (the interpreter core) copies, through which UN reads its input.

**How it was proved.** The fill worker's host could not fetch the dependency cache (its network
proxy refused part of it), so the worker wrote the proof without Lean and delivered it as an
unchecked draft (`fill-c1-window-cont1.zip`, round 3, REPORT Appendix C). The maintainer's review
extracted it verbatim and elaborated it here: it failed with 7 errors, and 14 mechanical repairs
make it check (two layout parse errors, two renamed Mathlib lemmas, an `apply Cfg.ext rfl`, the
`counterLoopOrbit` abbreviation's rewriting, and their knock-ons). No statement, route or
declaration changed. **By the user's ruling (2026-10-18)** it lands as a maintainer-verified
fill, as C1-W did in #123.

**Commits** (on the campaign branch at `2d4253e6`):
- `9f72288d` (author: the worker): the draft with the repairs R1–R14 (16 private `iw_`
  declarations and the target's proof);
- `d192b0f9`, the maintainer's (the review's L1–L6): public-facing docstrings; one closing step
  by `simp` instead of `decide`, which evaluated `CounterLoopState`'s derived `DecidableEq`
  (rule 10); the module's and the `TuringMachine` facade's status: proved.

The route is the brief's: the counter loop over a one-step body, embedded by R1 along `0 ↦ dst`,
`1 ↦ j`, with the exit join through `MultiTapeTM.agreeOn_iff` / `runFrom_eq_of_agreeOn` (no
`phaseHostTM`, which is outside the file's imports); `C = 6` by the brief's ledger.

### Checks (maintainer, against `oleans-lc6m`, #131's replay at the merged state)

- **Elaboration:** 0 errors, 0 warnings; `exists_inputWindowCopyTM` depends on
  `[propext, Classical.choice, Quot.sound]`.
- **Freeze:** 1 → 1 public, 0 → 16 private; the only body change is the target's. No import
  added.
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 38 files (the tip's).

### Review

`campaign/fills/c1/reviews/window-cont1-r3/REVIEW.md`: the delivery's integrity (28/28 sums, the
bundle, the commit = patch = file); the draft's verbatim extraction and its elaboration
(`out/elab-draft-verbatim.txt`); the repairs (`out/repairs.diff`), each with its reason; the
repaired and landing files at the base, the tip and #132's head (0 errors); a rule-10 seal of 16
other-file definitions with 4 controls; rule 11; the brief's 57-check probe and an 84-check
extension (0 errors); the four edge cases as compiled examples; the screen (264 declarations,
103 pairs; the one new pair is in-file at 62%); lint. The worker's report is
`campaign/fills/c1/reports/window-3-REPORT.md`.

### Replay

At the merged state: the campaign branch after #132 (`e9e97970`) was merged into this branch, with
no conflict and this PR’s files byte-unchanged. `replay-l137.sh`: the changed modules' downstream closure on the merged tree (2 modules: `TuringMachine/Build/InputWindow`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (0) (`campaign/gates/54-c1-window-cont1-fill/evidence/replay-l137.*`, `campaign/gates/54-c1-window-cont1-fill/evidence/down-l137.txt`).

### Gate

Gate 54 (`campaign/gates/54-c1-window-cont1-fill/`): pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

