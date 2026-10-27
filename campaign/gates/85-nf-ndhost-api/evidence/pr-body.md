An additive API PR in `TuringMachine/Build/NDHost`: the contract of the choice writer's controller-stopped flavor, and a guess-then-run host built on it. The linear normal form's fill (`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, `ClassNP/NDNormalForm`) guesses a display of unknown length, so it needs both. `Turing.guessRunTM` composes only the bounded writer, whose block the setup fixes in advance. The user ruled (2026-10-27) that the maintainer proves the contract and adds the host beside `guessRunTM`, in this file, with `guessRunTM` unchanged.

**Commits**
- `782d4f4a`: `Turing.ndWriterTM_run_controller`. If a choice word first stops the controller after `m` bits, its first `m + 1` bits write those `m` bits from the head and reach `done`, and no shorter prefix does. The writer's private helpers are generalized from the trivial controller to any controller state, and the bounded contract `ndWriterTM_run_block` is re-proved on them (statement unchanged).
- `8d3e4453`: the controller-stopped host `Turing.guessCtlRunTM` (the phases, redirects and state family of `guessRunTM`, with the controller writer in the guess phase), and its lemmas:
  - `guessCtlRunTM_runWith_handoff`: through the guess and the rewind, at time `TP + 2m + 9`;
  - `guessCtlRunTM_runWith`: the whole branch, through the run's first verdict;
  - `guessCtlRunTM_stop_of_halted`: a halted branch has passed a stop of the controller;
  - `guessCtlRunTM_accepts_of`, `guessCtlRunTM_stream_of_accepts`: acceptance, forward at every budget beyond the branch's time, and backward.
- `6a842bfb`: the new proofs read other files' definitions only through their published equations (`Cfg.mapState`'s and `Action.mapState`'s field lemmas, `Cfg.init`'s, `NDTM.initCfg_eq`, `MultiTapeTM.initCfg_eq`, `NDTM.stepWith_of_some`).
- `c87bbb2d`: one line wrapped.
- `248aecec`: the module header lists the new contract and host, and marks `guessRunTM_silent_spec` proved (it has been since the bounded writer's contract was); comments only.

**Checks** (against the snapshot of the tree after #172)
- **Elaboration:** 0 diagnostics. The new theorems and the re-proved `ndWriterTM_run_block` use only the standard axioms.
- **Rule 10:** the changed code, sealed over the 17 other-file definitions it reaches with the four `@[simp]` ones erased, has 0 diagnostics. The 21 controls close unsealed and fail sealed.
- **Freeze:** 25 → 37 public, none removed, no statement changed; the one public body change is `ndWriterTM_run_block`'s.
- **Lint:** 0 FAIL, the base's warnings.

**Merge conditions:** an API gate (gate 85), and the replay of the downstream closure (`NDHost`, `NTimeHierarchy` and the two facades).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
