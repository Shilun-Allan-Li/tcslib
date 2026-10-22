# External audit pack — adjacent word patches join (PR #139, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, B6 (the space hierarchy's windowed runner with the
configuration-count clock, [AB09, §4.1.3, Theorem 4.8]). The user's "Everything" rule
(2026-10-16, `policy.md` §1): every definition a brief's route reads gets a published equation
before the brief is dispatched.
- **Why:** the review of the configuration-clock runner's continuation 1 (B6-F3;
  `campaign/fills/b6/reviews/configclock-cont1/REVIEW.md`, its F1 on the worker's escalation E2)
  found that the runner's clock writer joins adjacent field writes, and that the only statement
  of that fact is `Build/RecordTable`'s private `rt_adjacentWrites`. It verified two resolutions:
  A, a private constant-fill lemma in the owned file, and B, a public `wordPatch_append` in
  `Build/StepClock`. **The user ruled B on 2026-10-18**; F3's continuation brief issues after it
  lands.
- **The head:** `lean/wordpatch-append` at `1cd66f1b`: one commit `23120c3e` on the campaign
  branch at `3e14cf34`, then merges of the campaign branch after #132 (`4fcb1a7f`) and after
  #133, #134, #136, #138 and #140 (`1cd66f1b`; no conflict, `Build/StepClock` byte-unchanged).
  Its Lean diff from the campaign tip is exactly `Build/StepClock`.

| File | Change |
|---|---|
| `TuringMachine/Build/StepClock` | **`Turing.wordPatch_append`**: `wordPatch (wordPatch ct cp u) (cp + u.length) v = wordPatch ct cp (u ++ v)`, after `wordPatch_of_not_mem`, with the review's proof verbatim (option B of `suggested-fix.diff`); the module's "Main definitions" list names it. |

- **Evidence:** `evidence/`:
  - `wordpatch.patch` (the head's diff from `3e14cf34`);
  - `elab-StepClock-axioms.out` (the module at the head with `#print axioms` appended);
  - `WordPatchSeal.lean.txt`/`.out` (the proof verbatim, renamed, against the module without it,
    with `FinTM.bufferTape` and `wordPatch` sealed; the output is the axioms line only) and
    `WordPatchSealControl.lean.txt`/`.out` (two `rfl` controls, failing as intended);
  - `lint-build.txt`; `screen.txt` and `screen-population.txt` (the copy-text screen v3);
  - `recordtable-excerpt.lean.txt` (`rt_adjacentWrites`, verbatim);
  - `windowclock-134-excerpt.lean.txt` (F3 cont1's `cw_copy_constant` and `cw_clear_patch`,
    verbatim from #134's head `b160813c`, now merged with docstring changes only: the shapes the
    writer's endpoints take);
  - the replay's script, list, log and static check; `pr-body.md`.
- **The bundle** also contains `Build/StepClock` at the head, the F3 review and its
  `suggested-fix.diff`, and `SpaceComplexity/WindowClock` at the head (the consumer, with F3 cont1's
  landing, #134, merged: its six private helpers, two of them excerpted).

## Brief for the auditor

1. **Faithfulness.** Is the identity right for every `ct`, `cp`, `u` and `v`, including `u = []`
   and `v = []`, and every cell `q` (inside `u`'s interval, inside `v`'s, and outside both)? Is
   the docstring an exact reading of it?
2. **Sufficiency.** Does it give the clock writer's per-field endpoint in the form the F3 review
   describes (`wordPatch … (List.replicate a e)`, the shape of F2's clock endpoint and of
   `cw_clear_patch`'s hypothesis), so that adjacent constant writes join without a private
   interval lemma? Is `rt_adjacentWrites` (excerpted) exactly this statement with `wordPatch`
   unfolded, so that it can later re-point?
3. **Rule 10 in the proof.** It reads `FinTM.bufferTape` only through `FinTM.bufferTape_nat`, and
   `wordPatch` only through its two published cell equations. Does the seal (both definitions
   `local irreducible`) cover every other-file definition the proof could reach, and do the
   controls show the seal is effective?
4. **Duplication.** The screen pairs `wordPatch_append` with nothing, `rt_adjacentWrites`
   included (the proofs differ). Should the statement-level overlap with `rt_adjacentWrites` be
   ledgered now, or only when `RecordTable` re-points (the review's note)?
5. **Public-facing text:** the docstring and the new contents line carry no campaign labels,
   paths or dated rulings (the module's older header text is out of scope).
6. **No collateral change:** one lemma and one contents line; no `@[simp]`; no existing
   declaration changed.

## Repository-side attestations (verify or challenge)

- **Elaboration** (maintainer, against `oleans-lc6m`, #131's replay at the merged state):
  `Build/StepClock` 0 errors, 0 warnings. **Axioms:** `wordPatch_append` depends on
  `[propext, Classical.choice, Quot.sound]` (`evidence/elab-StepClock-axioms.out`).
- **Seal:** `evidence/WordPatchSeal.out` (0 errors) and `evidence/WordPatchSealControl.out` (the
  two controls' expected errors).
- **Lint** (at the merged head `1cd66f1b`): `TuringMachine/Build` 0 FAIL, 30 WARN over 39 files,
  the campaign tip's count (`Build/Rewind` is the 39th; `StepClock`'s existing size warning;
  1,205 lines, 9 public / 33 private). No new line over 100
  characters.
- **Screen (v3):** `Build/StepClock`, `Build/RecordTable`, `SpaceComplexity/WindowClock`,
  `Build/WindowRun`: 176 declarations, 19 pairs; `wordPatch_append` is in none
  (`evidence/screen.txt`).
- **Replay:** ⟨REPLAY⟩

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/56-wordpatch-append/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `wordpatch-append-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
