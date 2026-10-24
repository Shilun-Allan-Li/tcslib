# External audit pack — C1, the replay canonizer (PR #160, a fill gate), round 2

**Round 1** (`findings.md`; resolutions `resolutions.md`): FAIL, 0 blockers, 1 major, 1 minor, 11
notes. The major: the private `rc_workReads2_length` re-proved `(workReadsK 2).length = 9`, the
`k = 2` case of the published `Turing.StepBlock.length_workReadsK`. The minor: the private
abbreviation `RcT` broke the file's `rc_` prefix. Both are fixed in this PR.

**The head:** `lean/c1-replaycanon` at `1cc8ab39`. Since round 1's head `73c99430` it has merged
the campaign branch twice (`dd7b126a`, after #158 and #159; `1cc8ab39`, records only) and one fix
commit, `4cb0c670` (`evidence/c1-replaycanon-landing/round1-fix/gate72-fix.patch`). Its Lean diff
from the campaign branch is still `NDCodeSimulator` and `NTimeHierarchy` only. This bundle's Lean
files are from `1cc8ab39`, and its records from the records commit that the dispatch prompt names.

| File | Change since round 1 |
|---|---|
| `TuringMachine/NDCodeSimulator` | `rc_workReads2_length`: its proof is `rw [StepBlock.length_workReadsK]` then `rfl` (core's `3 ^ 2 = 9`), its docstring names the lemma, its statement unchanged; `RcT` renamed `rc_State` with its eight uses (`rc_body`, `rc_body_primrec`, `rc_round_primrec`) |

The campaign merges bring #158 (`SpaceComplexity/WindowClock`) and #159 (`Build/Seam` and seven
files that use the phase host, `CodeSimulator` and `Build/StepBlock` among them); neither touches
this PR's two files.

## Brief for the auditor

1. **The fix.** Is the major resolved: does `rc_workReads2_length` now consume the published
   lemma, with nothing re-proved? Is the rename complete (no `RcT` left, every use renamed), and is
   `rc_body`'s only statement change the type's name?
2. **No regression.** The fixed file elaborates, its seal holds, and its axioms are unchanged
   (below). Is anything else in the file changed?
3. **The merged tree.** The two campaign merges are clean and leave this PR's diff unchanged. The
   replay runs this PR's closure on the tree after #159.
4. **Duplication.** The screen at the head against the campaign tip (the C1 draft's 16-file
   population; `round1-fix/screen-rcan2-*`): at the tip 541 declarations, 173 pairs, 86,076
   characters (round 1's base exactly, though #159 touched two files of the population); at the
   head 565, 176 and 86,371. Against the tip the three new pairs are round 1's (two cross-file
   idiom pairs, 62% and 55%, and one in-file, 58%); against round 1's head no pair is new or gone
   (`pairdiff-head-vs-tip.txt`, `pairdiff-head-vs-round1.txt`). Does the fix change any pair?
5. **Round 1's other points.** Is anything in round 1's resolutions unaddressed?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lphf`, the campaign's tree after #159): `NDCodeSimulator` with
  no diagnostic (`round1-fix/elab-NDCodeSimulator.out`).
- **Seal:** round 1's seal (21 definitions, 22 controls) re-run on the fixed file
  (`round1-fix/NDCSSeal.*`): the only errors are the 22 controls (lines 89–166); the home, from line
  168, elaborates sealed.
- **Axioms:** the canonizer, the core and the bridge on `[propext, Classical.choice, Quot.sound]`
  (`round1-fix/NDCSAx.out`). On the replayed snapshot of this head (`oleans-lrcan3`) the universal
  NDTM is on the same three (`round1-fix/UniversalAx3.out`).
- **Freeze** against round 1's head (`round1-fix/freeze-vs-round1.txt`): 3 → 3 public, 49 → 49
  private; `RcT` removed and `rc_State` added; `rc_body`'s statement renamed only; the bodies of
  `rc_workReads2_length`, `rc_body_primrec` and `rc_round_primrec` changed.
- **Lint:** `TuringMachine` 0 FAIL, 68 WARN over 83 files; no added line over 100 characters.
- **Replay:** `replay-lrcan3.sh`, the two files' closure (4 modules) at `1cc8ab39`, chained from
  `oleans-lphf`. **Passed (user, 2026-10-24): 4 of 4**, 0 failed, static-equal (1:
  `ntime_hierarchy`) (`round1-fix/replay/`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/72-c1-replaycanon-fill/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `c1-replaycanon-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
