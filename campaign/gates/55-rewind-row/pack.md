# External audit pack — a public rewind row (PR #138, an API gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09,
Theorem 3.2]). The user's "Everything" rule (2026-10-16, `policy.md` §1): every definition a
brief's route reads gets a published equation before the brief is dispatched.
- **Why:** the review of the interpreter core's round-3 delivery (C1-R;
  `campaign/fills/c1/reviews/core-cont1-r3/REVIEW.md`, gap 2, "Work-tape rewinds") found that
  the core's startup needs three rewinds of a work-tape head, from just past a word `w` (possibly
  empty, as at `t = 0`) back to the word's start at cell `0`, with every other tape framed. No
  row in the core's import closure states one: the input rewind (`FinTM.timed_rewind`) moves the
  input head, and the field-layout seekers `seekStartTM`/`skipBackTM` need nonempty fields and a
  blank between the head and the word. The user ruled on 2026-10-18 that a public row is
  published first, and the core's continuation brief issues after it lands.
- **The head:** `lean/rewind-row` at `518769e9`: one commit `684f3d88` on the campaign branch at
  `e0bfc458`, then a merge of the campaign branch after #132 (`e9e97970`; no conflict, both files
  byte-unchanged). Its Lean diff from the campaign tip is exactly the two files below.

| File | Change |
|---|---|
| `TuringMachine/Build/Rewind` (new, 220 lines; imports `Build/Catalog` only) | `Turing.RewindPhase` (`start`, `back`, `done`); `Turing.rewindTM k i`; **`Turing.rewindTM_run_ofCfg`**, its framed run (below). Two private helpers: `rw_cfg` (the trace's frame) and `rw_step` (one step over it). |
| `TuringMachine` (the facade) | imports the module and lists it in its contents ("Proved."). |

**The contract.** For a word `u`, `n ≤ |u|` and a configuration `d` in state `start` whose tape
`i` reads `bufferTape u` on the cells from relative position `-1` to `n - 1`, counted from
`pos − n` (`pos` the head of tape `i`):
1. `runFrom d (n + 2)` is `d` with state `done` and the head of tape `i` at `pos − n`, every other
   field unchanged;
2. the state is not `done` at any `t < n + 2`;
3. for `t ≤ n + 2`, the head of tape `i` lies in `[pos − n − 1, pos]` and every other head is
   fixed.

The head's own cell and every cell right of it are arbitrary. `done` is a stationary live anchor
(`inputMoveAction 0 .done`), as in every catalog seek. The statement has
`skipBackTM_run_ofCfg`'s form (excerpted), so the catalog's composition rows consume it the same
way.

- **Evidence:** `evidence/`:
  - `rewind.patch` (the head's diff from `e0bfc458`);
  - `elab-Rewind-axioms.out` (the module at the head with `#print axioms` for its two public
    constants appended);
  - `RewindProbe.lean.txt`/`.out` (the module sealed, plus the two consumers' forms derived from
    the public contract alone; its body is the head's, without the `maxHeartbeats` header and
    with one docstring line rewrapped);
  - `RewindSealControl.lean.txt`/`.out` (the control);
  - `lint-build.txt`, `lint-tm.txt`;
  - `screen.txt` and `screen-population.txt` (the copy-text screen v3);
  - the replay's script, list, log and static check;
  - `pr-body.md`.
- **Excerpts** (verbatim, each with its line range, extracted by name):
  - `catalog-excerpts.lean.txt`: `Build/Catalog`'s `tapeAction`, `inputMoveAction`, the two
    published step lemmas, `SeekPhase`, the private `catalogSeekCfg` and `catalog_seek_step`,
    `skipBackTM` and `skipBackTM_run_ofCfg`;
  - `simulation-excerpts.lean.txt`: `FinTM.bufferTape` and its two published equations;
  - `xr-rewind-excerpt.lean.txt`: the exhaustive replay's private `xr_rewindTM` and its run
    lemma, at #136's head `b5629b91` (not merged).
- **The bundle** also contains the module and the facade at the head, `Configuration` and
  `Deterministic` (the machine model, in full), the C1-R review, and the duplication ledger.

## Brief for the auditor

1. **Faithfulness.**
   - Is the time `n + 2` exact: one step left from `start`, `n` steps left in `back` over `u`'s
     first `n` symbols (read right to left), one step right at the blank at relative `-1`?
   - Is the endpoint exactly the configuration stated, every field (state, input head, work
     tapes, heads, output), for every `n ≤ |u|`, including `n = 0` and `u = []`?
   - Is the not-earlier clause right, and is the head-range clause (`[pos − n − 1, pos]`, the
     other heads fixed) right for every `t ≤ n + 2`?
   - Is the hypothesis `hu` the right one: exactly the cells the run reads (relative `-1` to
     `n - 1`), with `n ≤ |u|` making them `u`'s symbols? Is anything assumed that the run does
     not need, or missing that it does?
2. **Sufficiency.**
   - **C1-R's rewinds** (the review's gap 2): from `bufferTape w` with the head at `|w|`, `w`
     possibly empty, reach head `0` in `O(|w| + 1)` steps with every other tape framed. The
     probe's first example derives this (`n = |u|`, the endpoint at head `0`) from the contract
     alone. Does it, and is the contract's form the one the catalog's composition and embedding
     rows consume (compare `skipBackTM_run_ofCfg`)?
   - **The exhaustive replay's form** (the probe's second example): any head `p₀ ≤ |u|`.
     `xr_rewindTM` (excerpted) runs over its own state type, so re-pointing it to this row needs
     a state embedding and is not part of this PR. Is that right?
3. **Rule 10 in the row's own proof.** The proof unfolds only its own file's `rewindTM` and
   `rw_cfg`. With `tapeAction`, `inputMoveAction`, `FinTM.bufferTape`, `MultiTapeTM.step`,
   `MultiTapeTM.runFrom`, `Cfg.workTapeSymbols`, `moveInputPos` and `Action.apply` made
   `local irreducible`, the module elaborates (`RewindProbe`), and a control
   (`bufferTape u (-1) = none` by `rfl`) fails under the same seal. Does the seal cover every
   other-file definition the proof could reach? Do the `rfl` field goals after
   `step_of_tapeAction_move` (in `rw_step` and `h0`) close without unfolding another file's
   definition?
4. **Duplication** (disclosed and acknowledged). `rw_cfg` reproduces Catalog's private
   `catalogSeekCfg` at 79/79 = 100%, both ways: the same record update over `RewindPhase`
   instead of `SeekPhase`. Catalog's helper is private, so the new module cannot cite it.
   **Acknowledged by the user on 2026-10-18 before this gate** as debt RW-1 (`campaign/backlog.md`
   §1 RW-1, excerpted in `evidence/backlog-RW-1.md`, and `campaign/duplication-ledger.md`, in
   full): one public frame over any state type, cited from both files, in the user's dedup window
   with Catalog's next edit.
   Verify the ledger's count (1 of the module's 5 declarations, 79 characters). Also verify that
   the screen's other pairs on the module are design-parallel and not copies:
   - `rewindTM` against `skipBackTM`, 80% and 69% (the same table without the `gap` step);
   - `rewindTM` against `seekStartTM`, `skipTM` and `seekEndTM` (53–56%);
   - `rewindTM_run_ofCfg` against Catalog's private `a2_mapSetup_run` (52%, 84 of its 163
     characters): the run-by-induction idiom (`induction t`, `runFrom_succ_eq_step'`);
   - `rw_step` against `catalog_seek_step`: no pair at or above half.
5. **Public-facing text:** the module's docstrings and its header carry no campaign labels,
   paths or dated rulings.
6. **No collateral change:** a new module and one facade import and line; no `@[simp]`
   attribute; no existing declaration changed.

## Repository-side attestations (verify or challenge)

- **Elaboration** (maintainer, against `oleans-lc6m`, #131's replay at the merged state): the
  module, 0 errors, 0 warnings. **Axioms:** `rewindTM` depends on none;
  `rewindTM_run_ofCfg` depends on `[propext, Classical.choice, Quot.sound]`
  (`evidence/elab-Rewind-axioms.out`). The facade elaborates only with the module's `.olean`,
  which the replay builds.
- **Seal:** `evidence/RewindProbe.out` (the axioms line only: 0 errors under the seal) and
  `evidence/RewindSealControl.out` (the control's expected error).
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 39 files (the count before the module);
  `TuringMachine` 0 FAIL (`evidence/lint-*.txt`).
- **Screen (v3):** the module with `Build/Catalog` and the exhaustive replay at #136's head, 563
  declarations, 416 pairs (`evidence/screen.txt`); the module's pairs are the ones in item 4.
- **Replay:** `replay-lrw2.sh`: the changed modules' downstream closure on the merged tree (2 modules: `TuringMachine/Build/Rewind`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (0) (`evidence/replay-lrw2.*`, `evidence/down-lrw2.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/55-rewind-row/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `rewind-row-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
