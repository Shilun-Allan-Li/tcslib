# Review of gate 52's findings (PR #134, B6 F3 continuation 1, a fill gate)

Read-only review by the maintainer's review sub-agent, 2026-10-21. Paths below are relative to
`$S/review/gate52/` (`S` = the session scratchpad). The findings were treated as data.

**Inputs.**
- Findings `findings.md`: byte-equal to the records copy at the campaign tip `397763c8`
  (`campaign/gates/52-b6-f3-configclock-cont1-fill/findings.md`).
- The bundle `exchange/outbox/gates/52-b6-f3-configclock-cont1-fill-gate/b6-f3-configclock-cont1-bundle.md`:
  SHA-256 `972806574c70a20165c9e02a9027752562191a685bf7eed1aa87e685e3c1d2a4`, the auditor's hash.
- The PR head `c2c53ee5`, with parents `b160813c` and `e9e97970`; `WindowClock.lean` blob `3c49ffb4`.
- My worktree `wt/` (detached at `c2c53ee5`, with the `.lake/packages` link), the snapshot
  `oleans-l134`, and `tools/leanelab.sh` only, one elaboration at a time.
- No build command, no screen run, and no edit to any other worktree or to `wt-hk`.

**Verdict.** All 13 findings are **true**, at the auditor's severities.
- **Minor 8 is true**, with four concrete mismatches. Two of them are in frozen text that predates
  this landing, and two are in the PR body.
- A docstring-only fix in the text this landing introduced is drafted and checked. It is optional
  for closure.
- **The gate closes** (PASS, 0 blockers, 0 majors).
- Notes 4, 5 and 9 produce carry-forwards for continuation 2. Note 10 needs records wording only.
  No other note needs action.

## Findings

| # | Sev. | Verdict | Evidence | Proposed resolution |
|---|---|---|---|---|
| 1 | note | **True.** The bundle hash and its 21 distinct sections match. The bundle's Lean section, inside its code fence, equals blob `3c49ffb4`. Applying the two patches of `landing.patch` to `dac6b3b0` gives `9baf1502`, then `3c49ffb4` (tree = `b160813c`'s). Declarations go from 4/5 to 4/11 (public/private), with one `sorry` and 312 → 452 lines. With comments stripped, `b160813c`'s code equals `169cc6c2`'s (documentation only), and every base code line is present, in order | `out/01-integrity.txt` | None |
| 2 | note | **True.** `recordLength = F + k + 2` holds, with `2 ≤ F ≤ L ≤ 2F` and `n + 2 ≤ 2^p`. The exponent gap is `(C+q)(F−1) + 3F − 2 ≥ 4`. F2's `C` is chosen before `∀ x`, so `c = C + q + 8` is a constant for each machine. The conclusion of `cw_record_clock` is F2's certification hypothesis verbatim. A brute-force check of 19,200 cases (k, s ≤ 3; n < 40; q ≤ 4; C ≤ 5) finds no failure, and the boundary case gives `p=1, F=3, L=5, B=4, W=30`, with cost ≤ 30 | `out/02-arithmetic.txt`, `out/09-target.txt` | None |
| 3 | note | **True.** `tapeAction i 0 none .neg true` writes nothing and emits nothing (the output field is `none`). The table ignores the state, so from `true` the head moves left again: a live anchor, not a halt | `out/03-leaf.txt` | None |
| 4 | note | **True.** `cw_copy_constant` keeps every cell outside its interval. `skipTM_run_ofCfg` needs a blank cell at `pos + |w|`. The auditor's counterexample (`w = [e]`, cell 1 nonblank) holds. The delivery review's sentence "the cell past the written run is blank" (`REVIEW.md`, "On route and reusable?") holds only under the blank clock precondition and append-only writes | `out/04-copy-constant.txt` | **Carry to cont2**, item C1. Records: qualify the review's sentence in the resolutions; the review stays as written |
| 5 | note | **True.** `cw_clear_patch` cites only `.1` of `clearTM_run_ofCfg`. The "no earlier `done`" and head-envelope clauses are not exported. At F2's endpoint, `hb` comes from the writer's blank exterior and `w'.length = w.length` (`WindowRun.lean:1089`) | `out/05-clear.txt` | **Carry**, items C2 and C3 |
| 6 | note | **True.** `rt_adjacentWrites` is private (`RecordTable.lean:3199`) at `dac6b3b0` and at `c2c53ee5`. Neither commit has a `wordPatch_append`. #139 is open, and its head `4fcb1a7f` has `theorem wordPatch_append` (`StepClock.lean:111`). The ruling (B, 2026-10-18) is recorded in the pack | `out/06-e2.txt` | No new action. The cont2 draft already follows the ruling. #134's PR body is corrected under minor 8 |
| 7 | note | **True.** I rebuilt the 17-definition seal on the merged head's blob: it elaborates against `oleans-l134` with only the target's warning, and its control fails at `bufferTape [true] 0 = some true` by `rfl`. Every `rw`/`simp`/`dsimp` argument in the six new declarations is a published lemma, a hypothesis or a local `let`; none is `unfold` or `delta`. The only `unfold` in the file is the frozen bridge's `unfold FinTM.configBound` (line 139). It was disclosed, and it is already on gate 34's unfold-site scan | `out/07-seal-*.out`, `out/07-args.txt` | None. Optional cont2 note C5 |
| 8 | minor | **True** (details below) | `out/08-*` | **Fix (PR body, both options)**, plus the docstring fix (option 1) or a deferral (option 2) |
| 9 | note | **True.** The remaining obligations are as listed. `windowRun_stop_unique` is public (`WindowRun.lean:269`). Nothing in the six components contradicts the statement | `out/09-target.txt` | **Carry**, items C6 and C7. The partial status stays |
| 10 | note | **True.** Spot-checked records: 10/10 checksums OK; base and tip elaboration, the two probes and the seal each show 0 errors and only the target's warning; the probe has 134 `#check`s; all 11 privates use only standard axioms; both sweeps ran 176/176 in order, with 28 admissions in 11 modules. **Reviewer addition:** a fresh elaboration of the merged head against `oleans-l134` gives the `420:8` warning only, and fresh axiom prints equal the review's `out/19`, line for line | `out/10-records.txt`, `out/00-elab-head-l134.out`, `out/10-axioms-l134.out` | Records wording: an evidence-based audit, not a fresh kernel replay by the auditor |
| 11 | note | **True.** `screen-head.txt` is byte-equal to the review's `out/30`: 1,048 declarations, 510 pairs, 147,693 characters, 0 new pairs. The only WindowClock pair is the frozen bridge's (67%). Lint: 0 FAIL, 81 WARN over 107 files. Widest line: 96 characters | `out/11-screen-lint.txt`, `out/01-integrity.txt` | None |
| 12 | note | **True.** Parents and diff as stated. The script pins `3c49ffb4`, requires `e9e97970` as an ancestor and that `replay-l132b` passed, and copies from `oleans-l132b`. Result: 2/2, 0 failed, static total 1. **The campaign tip `397763c8` has no `TCSlib/` change since `e9e97970`.** #134 is mergeable (CLEAN) | `out/12-replay.txt` | None |
| 13 | note | **True** (notation only) | `out/13-notation.txt` | None |

## Minor 8 in detail

**The mismatches** (`out/08-minor8-evidence.txt`):
- **M1 (Lean text, frozen).** The Route A paragraph (head lines 383–393) is byte-identical to the
  base `dac6b3b0`. It describes the clock as written over the whole layout: `W := c_M · L`, by
  "copying the record's layout `c_M` times … (`Turing.copyTM`, `Turing.skipTM`,
  `Turing.scanTM`…)". The construction in use counts field cells only (`W = c · F ≤ c · L`) and
  writes them with the constant mapped copy, skips and the one-cell move. The width `c_M · L` is
  still a valid numerical alternative.
- **M2 (Lean text, frozen; the same paragraph).** `joinFields` places one blank cell between
  fields (`List.intercalate [none]`, `Catalog.lean:11771`). The framed forms of `copyTM`,
  `copyMapTM` and `scanTM` all take a word delimited by blanks (`FinTM.bufferTape w`). As written,
  each pass would stop at the first separator.
- **M3 (PR body).** The Review section says that E2's ruling "is pending". It was ruled B on
  2026-10-18 (`Turing.wordPatch_append`, PR #139, gate 56).
- **M4 (PR body; a reviewer addition).** The body says the Route A sketch "describes a valid route
  and is left as is", which holds for the width only. It also says the Implementation status
  paragraph "states the route in use (`W = c · F ≤ c · L` …, by `copyMapTM` …)". At the head, that
  paragraph contains neither `c · F` nor `copyMapTM`: it says "width at most `c · L`" and
  "constant mapped copy".
- "Main definitions: None" can stay: the section lists public definitions, and `cw_leftTM` is
  private.

**What is frozen and what changed.**
- **Frozen.** The Route A paragraph, M1 and M2, is part of the target docstring before the status
  paragraph. It predates this landing and was byte-unchanged by it. Rewording it is a **deferred
  item**, for the docstring-cleanup pass or the maintainer at continuation 2's integration. That
  rewording would also drop its frozen campaign labels: "S1b's plan, design §12.8a §4 step 5" (line
  392), and "proved today; the RD-3 gate's minor 3" (line 395). The other frozen labels in the file
  (lines 16, 86, 107 and 377) are listed in `out/08-labels.txt`.
- **Changed by this landing, and fixable now.** The "Implementation status." paragraph and the
  module status were introduced or changed by `b160813c`. Neither contains a campaign label
  (`out/08-labels.txt`). The module status is accurate.
- The auditor's first proposed fix is applied in the status paragraph: label the older
  construction as an unimplemented alternative. Six lines are inserted after line 411, and no
  existing line changes.

```
The clock these lemmas prepare is Route A's over field cells, of width `W = c · F ≤ c · L`,
where `F` counts the field cells. The fields are separated by blank cells and a mapped copy
reads one blank-delimited word, so the clock is copied one field at a time and the separators
are skipped, not written. The construction over the whole layout sketched above
(`W := c_M · L`, by `Turing.copyTM` and `Turing.scanTM`, which also read one blank-delimited
word) is an alternative that is not implemented; it would also have to handle the separators.
```

**Checks of the Lean fix** (`fix/minor8-status-paragraph.diff`; `out/08-fix-checks.txt`,
`out/08-elab-fix-l134.out`, `out/08-labels.txt`):
- It applies to `c2c53ee5`, and the blob goes `3c49ffb4` → **`dd542c8b7698d6d27d88608dfaafab1b65fc4f37`**,
  452 → 458 lines.
- It elaborates against `oleans-l134` with exit 0 and **exactly the head's diagnostics**: the
  target's sorry warning, moved from line 420 to line 426 by the six inserted lines. The unpatched
  baseline on the same snapshot is in `out/00-elab-head-l134.out`.
- With comments stripped, the code equals the head's. So the freeze is unchanged, and so is the v3
  screen, which strips comments (`copy-text-screen-v3.py`, `strip`): no re-screen is needed.
- No line is over 100 characters (the widest is 96). Lint on `SpaceComplexity`: 0 FAIL, 81 WARN
  over 107 files, and WindowClock is 458 lines, 4 public / 11 private.
- The new lines contain no campaign label.

**Optional ride-along (reviewer addition).** The docstring of `cw_left_run` says "restores the
native input position". The input position is never moved, so "keeps" is the accurate word.
- The hunk is `fix/optional-left-run-wording.diff`; combined with the main fix it is
  `fix/minor8-plus-optional-wording.diff`.
- The combined blob is `b50cdbb19b1ac9c6018c074d25a7358c8f95b826`. It elaborates against
  `oleans-l134` with only the `426:8` warning (`out/08-elab-fix-plus-optional-l134.out`). The line
  count is unchanged.

### The two options for the maintainer

1. **Option 1 (recommended): fix #134 now.** The text is this landing's own, and the re-replay is
   the same 2 modules.
   - #139 has not replayed yet: there is no `oleans-l139*`, and gate 50's record has #139
     replaying after #134. Its chain would then start from `oleans-l134b` instead of `oleans-l134`.
   - Steps:
     1. Commit `fix/minor8-status-paragraph.diff` (or the combined diff) on
        `lean/b6-f3-cont1-partial` and push it.
     2. Replay with `fix/replay-l134b.sh`. It is derived from `replay-l134.sh`; only the pin, the log
        and the output tree change, and it was not run. Pin `b50cdbb1…` if the optional hunk is
        taken.
     3. Replace the PR body with `fix/pr-body-B-with-docstring-commit.md`, filling in `⟨SHA⟩` and the
        replay status.
   - This is a `.lean` change, so it needs a commit to #134 and a re-replay.
2. **Option 2: defer the Lean part**, as gate 44 did with minor 3 and gate 49 with minor 13.
   - Replace the PR body with `fix/pr-body-A-no-lean-commit.md`.
   - The status-paragraph sentence rides on continuation 2's landing, which rewrites that
     paragraph. Carry-forward C4 tells it to keep the note.
   - The Route A paragraph goes to the docstring-cleanup pass.
   - No Lean change and no replay.

**The PR body (both options).** M3 becomes "Ruled (user, 2026-10-18): option B, a public
`Turing.wordPatch_append` in `Build/StepClock`, by PR #139 with its own API gate (56). It is not
part of this landing; F3's continuation 2 cites it." M4 is corrected, and the Gate line records the
closure. The live body is byte-equal to the pack's snapshot (`out/pr134-body-live.md`).

## Fixes

| File | Touches `.lean`? | Effect |
|---|---|---|
| `fix/minor8-status-paragraph.diff` | **yes** (docstring only) | Option 1: a commit to #134 and a re-replay of 2 modules |
| `fix/optional-left-run-wording.diff`, `fix/minor8-plus-optional-wording.diff` | **yes** (docstring only) | Optional, with option 1 |
| `fix/replay-l134b.sh` | no (a script, not run) | Option 1's re-replay |
| `fix/pr-body-A-no-lean-commit.md`, `fix/pr-body-B-with-docstring-commit.md` | no (PR text) | The PR-body replacement for option 2 or option 1 |
| `fix/cont2-draft-carryforwards.diff` (and the amended copy `fix/cont2-draft/…DRAFT.md`) | no (records; push straight to the campaign branch) | Folds C0–C7 into the cont2 draft |

## Carry-forwards for F3 continuation 2 (`fix/cont2-draft-carryforwards.diff`)

The draft already absorbs E2's ruling, the per-field round, the passes, the rewinds, the
contract and phase 2. It should also absorb the following:
- **C0 (issue-time line numbers).** With option 1, the file at the base has 458 lines: the target
  is at 426, the `sorry` at 456, and the status paragraph spans 404–424. Without it: 452, 420,
  450 and 404–418.
- **C1 (note 4): the clock's blank suffix.** This is a hypothesis of the per-field round,
  re-established at `p + |f|`: every clock cell from the write position on is blank. The clock
  skip needs it, and `cw_copy_constant` does not supply it. It holds initially by the blank clock
  precondition and afterwards because the writes only append.
- **C2 (note 5): cuts and envelopes.** `cw_copy_constant` and `cw_clear_patch` export only their
  rows' endpoints. The seams need the first-return cut (`seamCompTM_run_ofCfg`'s `hcut`) and the
  head envelopes. Take them from the rows' second and third clauses under the same `hw`, or extend
  the helpers, which region (a) allows.
- **C3 (note 5).** At F2's `halted`/`left` endpoint, `cw_clear_patch`'s `hb` comes from the
  writer's blank exterior and `w'.length = w.length`. No second patch-normalization lemma is needed.
- **C4 (minor 8).**
  - Under "Read first": the Route A sketch's whole-layout writer is an alternative not in use,
    because the separators are blank. The brief's field-by-field writer refines the sketch and
    binds.
  - Region (c): when the target is proved, keep a short note of the construction used, rather than
    deleting the paragraph, while the frozen sketch stands.
- **C5 (note 7, optional).** The frozen bridge's `unfold FinTM.configBound` predates rule 10. It
  stays outside the seal and is not the worker's to change.
- **C6 (note 9).**
  - **One constant `C`** must dominate the time constant (`cw_time_bound`'s `A + 4c + D + 10`), the
    head constant (`cw_head_bound`'s `C_R · (c + 1)`) and the space clause together.
  - **Silence and space** are target clauses for the composite, not only endpoint facts.
- **C7 (note 9), for the maintainer's pre-ship.** The framed rows' lemmas (`copyMapTM_run_ofCfg`,
  `skipTM_run_ofCfg`, `clearTM_run_ofCfg`) state the output only at their endpoints. Before issue,
  confirm and name the published route to the writer's intermediate output clause (the
  pre-ship-contracts rule).
- **Unchanged.** The screen base, ⟨SCREEN⟩, is unaffected by a docstring commit, because the screen
  strips comments.

## Reviewer additions (records; optional)

- **Pack, line 13.** "the review's head `b160813c`" is ambiguous: the delivery review's head is the
  worker's `c887ee89`, cherry-picked as `169cc6c2`. If it is touched, read it as "the PR's pre-merge
  head `b160813c`". No erratum is required.
- **The delivery review's note-4 sentence** is qualified in the resolutions, row 4.

## Ready-to-paste rows for `campaign/gates/52-b6-f3-configclock-cont1-fill/resolutions.md`

Fill in `⟨SHA⟩`, `⟨date⟩` and the replay status. Keep one of the two row-8 variants. The evidence
paths assume this review's `out/` and `fix/` are copied to `evidence/round1-review/`.

```markdown
# B6 F3 continuation 1 (PR #134, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #134 (`lean/b6-f3-cont1-partial` at `c2c53ee5`): six private
components of the configuration-clock runner `Turing.exists_configWindowRunnerTM` in
`SpaceComplexity/WindowClock.lean` (`cw_field_total`, `cw_record_clock`, `cw_leftTM`,
`cw_left_run`, `cw_copy_constant`, `cw_clear_patch`); the target stays `sorry` (a partial). Pack
`pack.md`; bundle SHA-256 `972806574c70a20165c9e02a9027752562191a685bf7eed1aa87e685e3c1d2a4`
(21 sections; folder `52-b6-f3-configclock-cont1-fill-gate/`). Replay passed (user, 2026-10-21):
2 of 2, static-equal (1).

**Round 1** (`findings.md`, verbatim; received 2026-10-21): **PASS, 0 blockers, 0 majors, 1 minor,
12 notes. The gate is closed.** The maintainer's review sub-agent verified every finding at
`c2c53ee5`: all true, at the auditor's severities (`evidence/round1-review/REVIEW.md`). The audit is
evidence-based: the auditor reproduced the source, patch and freeze checks and inspected the logs,
without rerunning Lean. The review re-elaborated the merged head against `oleans-l134` (the target's
warning only), re-ran the 17-definition seal (passes; the control fails as intended) and the axiom
prints (equal to the delivery review's).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 8 | minor | Documentation synchronization: the Route A sketch's present-tense `copyTM`/`scanTM` construction (`W := c_M · L`) is not the field-cell construction being developed, and a blank-separated record is not one delimited word for those rows; the PR body still calls E2's ruling "pending". | **True; fixed** in `⟨SHA⟩` (`evidence/round1-review/fix/minor8-status-paragraph.diff`), docstring only: blob `3c49ffb4` → `dd542c8b`, 452 → 458 lines. The Route A paragraph (lines 383–393) is frozen text, byte-identical to the base `dac6b3b0`; the fix is in the Implementation status paragraph this landing introduced. It states that the clock these lemmas prepare is Route A's over field cells (`W = c · F ≤ c · L`), copied one field at a time with the blank separators skipped, and that the sketch's whole-layout construction is an alternative, not implemented, that would also have to handle the separators (`joinFields` intercalates a blank; `copyTM`, `copyMapTM` and `scanTM` read one blank-delimited word). Checks (`evidence/round1-review/out/08-*`): applies to `c2c53ee5`; elaborates against `oleans-l134` with exactly the head's one diagnostic, the target's sorry warning (line 420 → 426); comment-stripped code unchanged, so the freeze and the v3 screen (which strips comments) are unchanged; `SpaceComplexity` lint 0 FAIL, 81 WARN over 107 files; no line over 100; no campaign label. **The PR body is replaced:** E2 ruled B (user, 2026-10-18: `Turing.wordPatch_append`, PR #139, gate 56); the Route A sentence corrected (a valid width, not the construction in use); the claim that the status paragraph named `W = c · F` and `copyMapTM` is now true. **Deferred:** rewording the frozen Route A paragraph itself, with its labels ("S1b's plan, design §12.8a §4 step 5"; "proved today; the RD-3 gate's minor 3"), to the docstring-cleanup pass. |
| 8 | minor | (variant without a Lean commit) | **True.** Four mismatches (`evidence/round1-review/REVIEW.md`, "Minor 8"): the frozen Route A paragraph (lines 383–393, byte-identical to `dac6b3b0`) describes the whole-layout writer, which as written would stop at the record's first blank separator; the PR body called E2 pending and overstated what the status paragraph says. **PR body: fixed** (E2 ruled B, user 2026-10-18: `Turing.wordPatch_append`, PR #139, gate 56; the Route A sentence corrected). **Lean text: deferred** (user, ⟨date⟩): the status-paragraph clarification (drafted and checked, `evidence/round1-review/fix/minor8-status-paragraph.diff`: the target's warning only, at 426; lint 0 FAIL) rides on F3 continuation 2's landing, which rewrites that paragraph and is told to keep the note; the frozen Route A paragraph goes to the docstring-cleanup pass. A commit on #134 now would need a re-replay of its closure. |
| 4 | note | The constant copy is correct; the following skip also needs the writer's blank-suffix invariant (the delivery review's "the cell past the written run is blank" uses route context). | **True; carried** to continuation 2's brief (the per-field round assumes the clock blank from the write position on and re-establishes it at `p + |f|`). **Records:** the delivery review's sentence holds under the blank clock precondition and append-only writes, not from `cw_copy_constant` alone (counterexample `w = [e]`, destination cell 1 nonblank); the review is kept as written. |
| 5 | note | The clear is correct; first-return and intermediate head/output clauses must still come from the public row APIs. | **True; carried:** `cw_copy_constant` and `cw_clear_patch` export only their rows' endpoints; the seams' cuts and the head envelopes come from `copyMapTM_run_ofCfg`'s and `clearTM_run_ofCfg`'s further clauses (or the helpers are extended); at F2's endpoint `cw_clear_patch`'s hypothesis comes from the writer's blank exterior and `w'.length = w.length`. |
| 9 | note | The target remains a construction obligation: writer, embedding, dispatch, composed first-return/silence/space proofs and the common constant. | **True; carried:** one constant for time, heads and space; silence and space proved for the composite; at pre-ship, the published route to the writer's intermediate output clause is confirmed. The partial status stays until the target is proved. |
| 6 | note | E2 was real but no blocker; follow the recorded ruling; #139's theorem is not proved by this landing. | **True. No action here:** continuation 2's draft cites `wordPatch_append` (#139, gate 56); #134's PR body now records the ruling (minor 8). |
| 10 | note | The execution attestations are supported by the records; not a fresh replay by the auditor. | **True. No action:** recorded above as an evidence-based audit. |
| 1–3, 7, 11–13 | notes | Integrity and the freeze; the clock arithmetic and the per-machine pass count; the leaf; rule 10 and MIG-1; the screen and lint; the merged-tree replay; notation. | **True. No action.** Note 7: the frozen bridge's `unfold FinTM.configBound` predates rule 10 and is on gate 34's unfold-site scan. |

**Carried to F3 continuation 2's brief** (`evidence/round1-review/fix/cont2-draft-carryforwards.diff`):
the clock's blank suffix (note 4); cuts and envelopes, and the clear's hypothesis at F2's endpoint
(note 5); the Route A sketch's whole-layout writer is an alternative not in use, and region (c)
keeps a note of the construction used (minor 8); one constant, silence and space, and the pre-ship
check of the silence route (note 9); the frozen bridge's `unfold` is outside the seal (note 7);
the issue-time line numbers.
```

With option 1, add this after the table:

```markdown
**Re-replay for the fix: ⟨passed (user, ⟨date⟩)⟩:** `replay-l134b.sh`, 2 of 2 at `⟨SHA⟩`, 0 failed,
static-equal (1), from `oleans-l132b` (`evidence/round1-fix/replay-l134b.*`).
```

## Merge status

- **Option 1: #134 is not yet clear to merge.** It needs the docstring commit, a pass of
  `replay-l134b.sh` (run by the user) and the new PR body. It is clear once the replay passes and
  the gate is recorded. Its base is already the campaign branch.
- **Option 2: #134 is clear to merge once the PR body is replaced and the resolutions are
  recorded.**
  - The gate is closed, and the replay at `c2c53ee5` passed.
  - The base is the campaign branch.
  - The campaign tip `397763c8` has no `TCSlib/` change since `e9e97970`, and GitHub reports the
    PR mergeable (CLEAN).
- Either way, #139 replays after #134 merges, from #134's snapshot (`oleans-l134b` or `oleans-l134`).

## Decisions for the maintainer or the user

1. Option 1 (commit the docstring fix now) or option 2 (defer it to continuation 2's landing).
2. With option 1: whether to include the optional `cw_left_run` wording hunk ("restores" →
   "keeps").
3. Whether to apply `fix/cont2-draft-carryforwards.diff` to the cont2 draft. It is a records file,
   pushed straight to the campaign branch.
