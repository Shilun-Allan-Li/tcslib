# External audit pack — C1-WC continuation 1: the bounded input window copier (PR #137, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09,
Theorem 3.2]). The fill brief WC cont1 (`campaign/fills/c1/briefs/c1-fill-window-cont1.md`)
targets `Turing.exists_inputWindowCopyTM` (`TCSlib/Complexity/TuringMachine/Build/InputWindow.lean`):
one machine that copies the window `y = (z.drop p).take d` of its native input onto a work tape,
where `d` is the value of a delimited counter word `w` on another tape, within `C·(|y| + 1) + 2|w|`
steps and not before, framing every other tape, head and the output. The interpreter core R
copies its input window with it.

**How it lands (the user's ruling, 2026-10-18): a maintainer-verified fill.** The worker's host
could not fetch the dependency cache, so the worker wrote the proof without Lean and delivered it
as an unchecked draft (`campaign/fills/c1/reports/window-3-REPORT.md`, Appendix C). The
maintainer's review (`campaign/fills/c1/reviews/window-cont1-r3/REVIEW.md`) extracted it verbatim:
7 errors; **14 mechanical repairs (R1–R14) make it elaborate with 0 errors and 0 warnings**, with
no declaration, route step or statement changed. The C1-W / #123 precedent.

**The head:** `lean/c1-window-fill` at `9d8ab646`: the review's head `d192b0f9` (two commits on the
campaign branch at `2d4253e6`) with the campaign branch merged in after #132 (`e9e97970`; no
conflict, the PR's own files byte-unchanged):
- `9f72288d` (author: the worker): the draft with the repairs R1–R14, 16 private `iw_`
  declarations and the target's proof;
- `d192b0f9` (the maintainer's, the review's L1–L6): public-facing docstrings; one closing step by
  `simp` instead of `decide`, which evaluated `CounterLoopState`'s derived `DecidableEq` (rule 10);
  the module's and the `TuringMachine` facade's status, proved.

## Brief for the auditor

1. **Faithfulness of the proof to the gated statement.** The statement is frozen (`evidence/freeze.txt`:
   1 → 1 public, 0 → 16 private, the only body change the target's; no import added). Does the
   proof establish it for every `p`, `w` and input, including the four edge cases the review
   compiled as in-module examples (`campaign/fills/c1/reviews/window-cont1-r3/out/edge-cases.out`, empty: 0 errors, 0 warnings): `d = 0`
   (the exhaustion branch, no round), `p = |z|` (the loop escapes at round 1), `|y| < d` (the
   window stops at the input's end) and a padded counter word `[true, false, false]` (value 1,
   width 3)? `p ≤ |z|` needs no hypothesis: it is the input head's `Fin` bound.
2. **The constant.** `C = 6` by the brief's ledger. Is the time bound `6·(|y| + 1) + 2|w|` right,
   and is "not before" (the first arrival at `done`) proved, not only the bound?
3. **The repairs** (`campaign/fills/c1/reviews/window-cont1-r3/out/repairs.diff`, each with its reason in the review's table): are all 14
   mechanical (layout, renamed Mathlib lemmas, `apply Cfg.ext rfl`, the `counterLoopOrbit`
   abbreviation, knock-ons), with no change of statement or route?
4. **The route.** The counter loop over a one-step body, embedded by R1 along `0 ↦ dst`, `1 ↦ j`,
   with the exit join through `MultiTapeTM.agreeOn_iff` / `runFrom_eq_of_agreeOn` (no
   `phaseHostTM`, which is outside the file's imports). Is that the brief's route, with no second
   loop, host or embedding written?
5. **Rule 10.** The review's seal of 16 other-file definitions with 4 controls
   (`campaign/fills/c1/reviews/window-cont1-r3/out/seal-IWSealS3*.out`, `campaign/fills/c1/reviews/window-cont1-r3/out/landing-IWSealS3*.out`); the `decide` fix. Does any step close only
   because another file's definition reduces?
6. **Duplication** (disclosed by the maintainer, 2026-10-21, after the review). The private
   `iw_patch` is, up to names and the alphabet, `Build/StepClock`'s public `Turing.wordPatch` (a
   tape with a word written over an interval); `iw_patch_true` reads it at a constant word, and
   `iw_patch_append` appends one cell. The copy-text screen pairs none of them (the identifiers
   differ; `evidence/screen-patch.txt`, with StepClock at #139's head and WindowClock at #134's;
   both definitions excerpted in `evidence/patch-excerpts.lean.txt`).
   `Build/InputWindow` imports only `Build/CounterLoop`, and the brief authorized no import, so it
   could not cite `wordPatch`. The maintainer proposes recording it as a design-parallel watch item
   in the duplication ledger, re-pointed to `wordPatch` in the user's dedup window. Is that the
   right classification, or is it copied material needing acknowledgment?
7. **Public-facing text:** the 16 docstrings, the module status and the facade's line carry no
   campaign labels.

## Repository-side attestations (verify or challenge)

- **Elaboration** (maintainer, against `oleans-lc6m`): `Build/InputWindow` 0 errors, 0 warnings;
  `exists_inputWindowCopyTM` depends on `[propext, Classical.choice, Quot.sound]`
  (`evidence/elab-InputWindow-axioms.out`). The review also elaborated the landing at the base
  (`oleans-lseam2`) and on #132's head (`oleans-l132`): 0 errors.
- **The review:** the delivery's integrity (28/28 sums, the bundle, commit = patch = file); the
  verbatim extraction and its elaboration; the repairs; rule 11; the brief's 57-check probe and an
  84-check extension (0 errors); the screen (264 declarations, 103 pairs; the one new pair is
  in-file at 62%); lint.
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 38 files (`evidence/lint.txt`).
- **Replay:** `replay-l137.sh`: the changed modules' downstream closure on the merged tree (2 modules: `TuringMachine/Build/InputWindow`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (0) (`evidence/replay-l137.*`, `evidence/down-l137.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/54-c1-window-cont1-fill/findings.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `c1-window-cont1-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
