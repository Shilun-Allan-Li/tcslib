# External audit pack — the controller-stopped writer and guess-then-run host (PR #174, an API gate)

**Why this PR.** The linear normal form `Turing.FinNDTM.exists_codeNDTM_accepts_linear`
(`ClassNP/NDNormalForm`) is one of the two contracts the nondeterministic time hierarchy rests on.
Its route (`campaign/items/c1/nf/NF-route-design.md`) guesses a display of one record per step of
the simulated machine, a word of unknown length, and then verifies it deterministically.
`Turing.guessRunTM` composes only the bounded choice writer, whose block length the setup fixes
before the guess. The controller-stopped flavor of `Turing.ndWriterTM` had a definition and no
contract (its statement was drafted on 2026-10-17, `campaign/items/c1/nf-writer/`, and never
landed). **The user ruled (2026-10-27), NF's D1 (A) and D2 (A):** the maintainer proves the
contract, and adds a controller-stopped guess-then-run host in `Build/NDHost`, in the same PR,
beside `guessRunTM`, which stays unchanged (E-D's route cites it).

**The PR:** #174 on `lean/nf-ndhost-api`, head `248aecec9879ecfc83c57d8384bbc19d4937cf4a`, five
commits on the campaign tip `d07187db`, whose Lean is the tree after #172 (`evidence/patches/`):
- `782d4f4a`: `Turing.ndWriterTM_run_controller`; the writer's private helpers generalized from
  the trivial controller to any controller state, and `ndWriterTM_run_block` re-proved on them;
- `8d3e4453`: the controller-stopped host `Turing.guessCtlRunTM` and its five lemmas;
- `6a842bfb`: the new proofs routed through published equations (rule 10);
- `c87bbb2d`: one line wrapped;
- `248aecec`: the module header (comments only; the code is identical to `c87bbb2d` with comments
  stripped).

The probes and the screen ran at `c87bbb2d`; the elaboration of the head file at `248aecec` has
no diagnostic.

## What changed (verify)

| Class | Declarations |
|---|---|
| **New public** | `Turing.ndWriterTM_run_controller`; `Turing.GuessRunPhase.CtlState` and its `Fintype` and `DecidableEq` instances; `Turing.guessCtlRunPhases`, `Turing.guessCtlRunRed`, `Turing.guessCtlRunTM`; `Turing.guessCtlRunTM_runWith_handoff`, `_runWith`, `_stop_of_halted`, `_accepts_of`, `_stream_of_accepts` |
| **Re-proved** | `Turing.ndWriterTM_run_block` (statement unchanged), on the generalized helpers |
| **Private** | changed: `wr_cfg` (a writer-state parameter), `wr_cfg_nil`, `wr_cfg_scan`, `wr_cfg_stepWith` (any `δ`, `stop`, `bounded`), `wr_prefix`; added: `wr_prefix_controller` |
| **Frozen** | every public statement: 25 → 37 public, none removed, none changed (`evidence/freeze-NDHost*.txt`) |
| **Text** | the module header's design notes, definitions and results; `guessRunTM_silent_spec`'s stale "proved modulo the writer" corrected (its axioms are the standard three) |

## Brief for the auditor

1. **The writer's contract.** Is `ndWriterTM_run_controller` the right public form?
   - It is stated along one word `w` with its first stop `m` (`m < |w|`; no stop before `m`;
     a stop at `m`), because the controller's trajectory depends on the bits. Its second clause
     covers the prefixes of `w` up to `m`, not every word.
   - The written cells are those of `w.take m`; the writer ignores what they held.
   - Is the re-proof of `ndWriterTM_run_block` on the generalized helpers sound, with its
     statement unchanged?
2. **The host.** Is `guessCtlRunTM` the intended shape: `guessRunTM`'s six phases, with the
   unbounded writer under the controller `q₀`, `δ`, `stop` in the guess phase, over a tape blank
   from the setup's head on (`hblank`, every cell at or right of the head) and just before it
   (`hleft`)? Check the edge `m = 0` (the controller stops at once: an empty stream, the step
   right from a blank cell, the rewind over nothing).
3. **The lemmas.**
   - `_runWith_handoff`: the time `TP + 2m + 9`, the stream `(w.drop (TP + 1)).take m`.
   - `_runWith`: the whole branch, halted by `TP + 2m + TQ + 11`, with output the run's output
     followed by the verdict bit.
   - `_stop_of_halted`: a halted branch has a first stop `m` with `TP + 1 + m < |w|`, using
     only the setup's run to its exit. Is the liveness argument right in both cases (still in
     the setup, and still in the writer)?
   - `_accepts_of`, `_stream_of_accepts`: forward at every budget beyond the branch's time, and
     backward under `hV` (every stream that first stops the controller at its end reaches a
     verdict). The backward direction pads the accepting word and uses absorption. Is any
     hypothesis stronger than a consumer can meet, or vacuous? NF's verifier always reaches a
     verdict.
   - There is no all-branch halting lemma, on purpose: a stream that never stops the controller
     never ends the guess, and NF claims no halting.
4. **Rule 10** (the scope of 2026-10-23). The changed code (the writer's helpers and contracts,
   and the new section) is sealed over 17 other-file TCSlib definitions, with the four `@[simp]`
   ones erased (`evidence/NDHostSealed.*`, generator `evidence/scripts/mkseal_nf.py`): 0
   diagnostics.
   - The controls (`evidence/NDHostSealControl.*`): 16 `rfl` controls and 4 `simp` controls
     close unsealed (20 `PASS` messages) and fail sealed; the recursive `NDTM.runWith` has a
     usage control instead (`runWith [b] c = stepWith b c`), which closes unsealed and fails
     sealed. 21 sealed failures, each at its own line.
   - The `simp`, `rw` and `unfold` arguments of the changed code name no other-file definition
     (`NDTM.phaseHostND`, `ndWriterTM`, `guessCtlRunPhases`, `guessCtlRunRed`, `guessRunCfg` and
     `wr_cfg` are this file's). The configuration and action renamings are read through their
     `simps` field lemmas (`StateRenaming`), the start through `NDTM.initCfg_eq`,
     `MultiTapeTM.initCfg_eq` and `Cfg.init`'s fields, the step through `NDTM.stepWith_of_some`.
   - `guessRunTM`'s own proofs (unchanged, from 2026-10-17) still unfold `Cfg.mapState` and
     `NDTM.stepWith`; they predate the rule and are not in this PR's scope.
5. **Duplication.**
   - **The API-copy search** (`evidence/api-copy-search.txt`): no branch, local landing or
     delivery has the new statements.
   - **The text screen** over a 14-file population (`evidence/screen/`; base the tip's tree at
     `940671e0`, head `c87bbb2d`): ⟨SCREEN⟩.
   - **Semantic:** does any new lemma re-derive a published one? The writer's contract is new;
     the host's lemmas are those of a new host.
   - Is the additive design, a second host beside `guessRunTM` with parallel proofs, the right
     call over one writer-parameterized host with `guessRunTM` as its instance (which would
     change `guessRunTM`'s definition bodies and re-prove its lemmas)?
6. **Consumers.** `NDHost`'s downstream closure is `Diagonalization/NTimeHierarchy` and the
   `TuringMachine` and `Diagonalization` facades. `NTimeHierarchy` cites `guessRunTM`,
   `guessRunTM_silent_spec`, `ndWriterTM_run_block`, `GuessRunPhase.State`, `phaseHostND`, and
   `streamStartCfg` with its field lemmas: every one of them is unchanged in statement (and, but
   for `ndWriterTM_run_block`'s proof, in body).
7. **Records.** Are the new docstrings and the module header accurate and public-facing?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lhh` (the snapshot of the tree after #172):
  - the head module with ten axiom prints appended (`evidence/NDHostAx.*`): 0 diagnostics; the
    six new theorems and `ndWriterTM_run_block`, `guessRunTM_runWith_handoff`,
    `guessRunTM_accepts_iff`, `guessRunTM_silent_spec` all on
    `[propext, Classical.choice, Quot.sound]`;
  - the sealed copy: 0 diagnostics.
- **Freeze** (`declfreeze.py` v4, `evidence/freeze-NDHost.txt`): 25 → 37 public, 7 → 8 private,
  the one public body change `ndWriterTM_run_block` (`freeze-NDHost-allowed.txt`: none
  unauthorized with it allowed).
- **Lint:** `TuringMachine` 0 FAIL, 68 WARN over 85 files, as at the base; only `NDHost`'s lines
  change: its size (1,256 → 2,023 lines), and check 8's list, where the new state family, phases
  and redirects join their bounded twins (`GuessRunPhase.State`, `guessRunPhases`,
  `guessRunRed`), which carry the same warning (`evidence/lint-*-TuringMachine.txt`). The policy
  linter `scripts/style_lint.py`: the base's findings, the size line's count only
  (`style-lint-*-NDHost.txt`). No line over 100 characters.
- **Replay:** `NDHost`'s downstream closure, 4 modules (`evidence/merged-tree/down-lnfapi.txt`),
  chained from `oleans-lhh`, pinning the head's blob `ae9cc5dd`. **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/85-nf-ndhost-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `nf-ndhost-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
