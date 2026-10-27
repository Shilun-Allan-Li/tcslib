Lands checkpoint 1 of the stage query's fill (`Turing.NTimeDiag.exists_queryTM`, `Diagonalization/NTimeDiagonalizer`): the linear-time guard, and the reduction of the target to a machine computing the query on the unary word of every input's length. That main machine stays `sorry`; the continuation proves it. The user ruled (2026-10-27) that checkpoint 1 lands now, with the review's landing edits E1–E5, after #171, its guard citing #171's word tests.

**Commits**
- `8841044d`: the worker's import overlay (delivered as `fabce3bb`), the eight imports the brief authorized.
- `4d93a8fe`: the worker's checkpoint 1 (delivered as `9d93626d`):
  - `qy_guard`: the query off its guard is empty;
  - `qy_guard_decider`: a linear decider of the guard;
  - `qy_query_of_main`: the reduction;
  - the target's `suffices`.
- `1fd6a15d`: the review's landing edits E1–E5:
  - two docstring corrections;
  - one tactic step that no longer closes by reducing `List.singleton`;
  - one blank line;
  - the status paragraph.
- `a5c22dd9`: the guard cites `Turing.FinTM.computesFunInTime_allTrue` and `computesFunInTime_decideEq` from `Build/WordTests` (#171) in place of its private copies (54 lines removed).
- The campaign merged in (no Lean change).

The worker's two subjects are reworded without the campaign label; their author and patch-ids are the delivery's.

**Checks** (against the snapshot after #171)
- **Elaboration:** exactly the file's two `sorry` warnings, the target and `exists_diagonalizer`. The three privates use only the standard axioms.
- **Rule 10:** the review's seal of 32 definitions, with the four `@[simp]` ones erased. The body has 0 errors sealed, and all 39 controls fail sealed and close unsealed.
- **Freeze:** 22 → 22 public statements, 0 → 3 private; the one body change is the target's.
- **Lint:** 0 FAIL, the base's warnings.

**Merge conditions:** a light fill gate (gate 83), and the replay of the 2-module downstream closure (`NTimeDiagonalizer` and the `Diagonalization` facade).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
