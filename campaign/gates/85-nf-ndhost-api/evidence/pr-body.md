An API PR in `TuringMachine/Build/NDHost`: the contract of the choice writer's controller-stopped flavor, and one guess-then-run host over the writer, of which `Turing.guessRunTM` is now the bounded instance. The linear normal form's fill (`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, `ClassNP/NDNormalForm`) guesses a display of unknown length, so it needs both. The user ruled (2026-10-27) that the maintainer proves the contract and adds the host here. The first version added a second host beside `guessRunTM`; its screen found the new host reproducing `guessRunTM`'s definitions and proofs (18 of the file's 45 declarations in one family), and the user ruled to generalize instead.

**The design**
- `Turing.guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej`: the phase host over a setup, the choice writer with the controller `q₀`, `δ`, `stop` and the flavor `bounded`, the step right, the rewind, the run and the verdict leaf, with its state family `Turing.GuessRunPhase.CtlState`, phases `Turing.guessCtlRunPhases` and redirects `Turing.guessCtlRunRed`.
- `Turing.guessRunTM` and its `GuessRunPhase.State`, `guessRunPhases`, `guessRunRed` and the two instances are the bounded, trivial-controller instances. **Every public statement is unchanged**; their definition bodies now name the general ones.
- The handoff and the rest of a branch are proved once (private `gr_handoff`, `gr_runWith_of_handoff`), for any writer whose run on the stream is given; `guessRunTM_runWith_handoff` and `guessRunTM_runWith` are now corollaries, through `ndWriterTM_run_block`.
- The writer's prefix induction and first stop are proved once, for any controller and flavor (private `wr_prefix_gen`, `wr_run_first_stop`); `ndWriterTM_run_block` and the new `ndWriterTM_run_controller` are their instances.

**New public declarations**
- `Turing.ndWriterTM_run_controller`: if a choice word first stops the controller after `m` bits, its first `m + 1` bits write those `m` bits from the head and reach `done`, and no shorter prefix does. The writer's private helpers are generalized from the trivial controller to any controller state.
- The controller-stopped instance's lemmas: `guessCtlRunTM_runWith_handoff`, `guessCtlRunTM_runWith`, `guessCtlRunTM_stop_of_halted` (a halted branch has passed a stop of the controller), `guessCtlRunTM_accepts_of` and `guessCtlRunTM_stream_of_accepts` (acceptance, forward and backward).

**Checks** (against the snapshot of the tree after #172)
- **Elaboration:** 0 diagnostics. The 16 theorems of the host family use only the standard axioms.
- **Rule 10:** the changed code, sealed in its five regions over the 17 other-file definitions it reaches with the four `@[simp]` ones erased, has 0 diagnostics; the 21 controls close unsealed and fail sealed. No other-file definition is passed to `simp`, `rw` or `unfold`.
- **Freeze:** 25 → 37 public, none removed, every signature unchanged.
- **Lint:** 0 FAIL, the base's warnings.

**Merge conditions:** an API gate (gate 85), and the replay of the downstream closure (`NDHost`, `NTimeHierarchy` and the two facades).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
