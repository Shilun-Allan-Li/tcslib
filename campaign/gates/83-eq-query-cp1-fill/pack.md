<!-- DRAFT (maintainer, 2026-10-27): staged before #171 merges. At the PR: fill every ⟨…⟩, re-run
the elaboration against #171's replay snapshot into evidence/, write the replay, build the
bundle; then remove this comment. -->

# External audit pack — E-Q checkpoint 1, the guard and the reduction (PR ⟨#⟩, a light fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1-E (the nondeterministic time hierarchy's
diagonalizer, [AB09, proof of Theorem 3.2]). The fill brief E-Q
(`campaign/fills/eq/briefs/eq-fill-query.md`) has one target in
`TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean`: the stage query in linear time,
`Turing.NTimeDiag.exists_queryTM`.

Megafill D's worker delivered **checkpoint 1**, a partial
(`campaign/fills/megafill/reports/megafill-d-REPORT.md`; `fill-eq-query-cp1.zip`). It proves a
linear guard and reduces the target to a machine for the query on the unary word of every input's
length (`hmain`), which stays `sorry`. The maintainer's review is
`campaign/fills/eq/reviews/fill-cp1/REVIEW.md`. **The user ruled (2026-10-27):** checkpoint 1
lands now with the review's landing edits E1–E5, after the API PR #171, its guard re-pointed to
#171's rows. The continuation (cont1) proves `hmain` on the landed tree.

**The head:** `⟨branch⟩` at `⟨head, 40 characters⟩`, four commits on #171's merged head `91a1ad87`
(`evidence/patches/`). The worker's two subjects are reworded without the campaign label (the
review's F8); their author is the delivery's, and their patch-ids equal the delivered commits'.
- `8841044d`: the worker's import overlay (the delivered `fabce3bb`), the eight imports the brief
  authorized (`Mathlib.Data.Nat.Log`, `Build/StepClock`, `Build/InputCall`,
  `Build/Contract/Catalog`, `Build/Contract/Seam`, `Build/Primitives`, `Build/Rewind`,
  `BufferWords`), cherry-picked from the verified bundle;
- `4d93a8fe`: the worker's checkpoint 1 (the delivered `9d93626d`), cherry-picked: `qy_guard`,
  `qy_guard_decider`, `qy_query_of_main` and the target's `suffices`;
- `1fd6a15d`: the maintainer's E1–E5 (the review's `out/25-landing-edits.diff`): two
  docstring corrections (F3, F4), one tactic step (F6: `refine congrArg (fun b => [b]) ?_` for
  `apply congrArg List.singleton`), one blank line (F8), the status paragraph (F5);
- `a5c22dd9`: the maintainer's re-point. `qy_guard_decider` cites
  `Turing.FinTM.computesFunInTime_allTrue` and `Turing.FinTM.computesFunInTime_decideEq` (#171) in
  place of its private copies (54 lines removed), and the module imports `Build/WordTests`. Its
  docstring's "which public row it is not" sentence (E2) is rewritten to the one fact no row
  covers, the length bound.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target's body** | `Turing.NTimeDiag.exists_queryTM`: `sorry` → a `suffices` on `hmain`, closed by `qy_query_of_main`; `hmain` is `sorry` |
| **Privates** | 0 → 3: `qy_guard`, `qy_guard_decider`, `qy_query_of_main`, at the home before the target |
| **Frozen** | every public statement (22 → 22) and every other body (`evidence/prepared-laplusm/freeze-NTimeDiagonalizer.txt`: the one body change is the target's) |
| **Imports** | the eight above and `Build/WordTests`; no `Diagonalization` module in their closure |
| **Text** | the three privates' docstrings; the target's `**Implementation status.**` paragraph |

## Brief for the auditor

1. **The proofs.** Are the three privates correct, and does the target's `suffices` state exactly
   the brief's `hmain` (on every word, `[]` when `|x| ≤ 2`)?
   - `qy_guard`: `query_of_not_guard` off the guard.
   - `qy_guard_decider`: the all-true test with three fixed-word cuts (`[]`, `[true]`,
     `[true, true]`) by `computesFunInTime_cond`, each linear.
   - `qy_query_of_main`: the guard chooses between the supplied machine and the constant `[]`;
     the bound absorbs `n ≤ g n` (`Complexity.timeConstructible_iff`).
2. **The re-point** (`a5c22dd9`). Does `qy_guard_decider` use #171's rows as published, with no
   copy of them left in the file? Is its rewritten docstring true ("No public row decides the
   length bound")?
3. **Rule 10** (with the scope of 2026-10-23). The review's seal (32 definitions, the four
   `@[simp]` ones erased) re-run on the landing, `Build/WordTests` inlined
   (`evidence/prepared-laplusm/EQSeal_*`, generator `evidence/scripts/mkseal_v2.py`):
   - sealed, the module body has 0 errors;
   - its 39 controls (35 delta `rfl` and `simp` controls, 4 usage controls, `incFixed`'s among
     them) all fail sealed (74 errors) and all close unsealed (35 PASS).

   Does any step close only because another file's definition reduces? `hcut`'s `simp [he]` passes
   a hypothesis, on a goal with no TCSlib constant.
4. **The text.** Are the docstrings and the status paragraph accurate and public-facing?
   - The target's docstring keeps its earlier campaign references ("C1-E", "the P3.3 gate's round
     2"): they predate this PR and are in the deferred docstring cleanup.
   - No new text carries a campaign label, path or date.
5. **What remains admitted.** The target and `exists_diagonalizer` reach `sorryAx`, the former
   through `hmain` only. Is that the brief's dependency structure?

## Repository-side attestations (verify or challenge)

- **Elaboration**, prepared against `oleans-laplusm` (the tree after #169) with `Build/WordTests`
  inlined (`evidence/prepared-laplusm/NTimeDiagonalizerCatAx.*`): exactly the two `sorry` warnings
  (the target and `exists_diagonalizer`); the three privates on `[propext, Classical.choice,
  Quot.sound]`.
- **Elaboration and seal against `oleans-lwords`** (#171's replay snapshot, the PR's base tree;
  `evidence/lwords/`): the module at the head, with five axiom prints, has exactly the two `sorry`
  warnings (lines 402 and 472) and the privates on the standard three; the seal re-run on the real
  module gives the same results (body 0 errors sealed; 39 controls fail sealed and close
  unsealed).
- **Freeze** (`declfreeze.py` v4, base the campaign tip's file): 22 → 22 public, 0 → 3 private,
  the one authorized body change.
- **Lint** (`evidence/prepared-laplusm/lint-head-Diagonalization.txt`): `Diagonalization` 0 FAIL,
  2 WARN over 5 files, the base's; `NTimeDiagonalizer` 498 lines, 22 public / 3 private. No line
  over 100 characters.
- **The review** (`campaign/fills/eq/reviews/fill-cp1/`): the bundle's integrity, the v3 screen,
  the duplication tiles and the import probes, on the delivery; E1–E5 tested at its head.
- **Replay:** the downstream closure, 2 modules (`NTimeDiagonalizer` and the `Diagonalization`
  facade, `evidence/prepared-laplusm/down-leqcp1.txt`), from `oleans-lwords`. **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/83-eq-query-cp1-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `eq-query-cp1-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
