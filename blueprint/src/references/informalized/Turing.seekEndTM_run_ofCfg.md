<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.seekEndTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeking the End of a Field Sequence

**Claim.** Under the stated tape-content and running-state hypotheses, the seeking machine reaches the done phase after $L+1$ steps at the end of the field sequence. It is not done earlier, and throughout the run the selected head stays between its starting position and the end while every other work-tape head remains fixed.

**Proof.** Let $L$ be the total field offset. The proof first establishes that the joined sequence has length $L-1$, so its final cell is at position $L-1$ and every cell at or beyond $L$ is blank (`length_joinFields_add_one`). The tape-content hypothesis then identifies every scanned symbol along the path with the corresponding value of the field sequence. In particular, the final cell at offset $L$ is blank.

For each $r$ from $0$ through $L$, define a candidate configuration whose selected tape head has advanced by $r$ cells from its starting position. Its phase is `run` at the initial position, and thereafter is `gap` exactly when the preceding cell was blank; otherwise it is `run`. The tape-reading hypothesis ensures that the symbol scanned in this candidate is the field-sequence symbol at offset $r$. Since the words are nonempty, consecutive cells of the joined sequence cannot both be blank (`fieldsTape_no_double_blank`). This rules out mistaking an internal separator for the terminal blank: whenever the current cell is blank before the end, the preceding-cell test places the machine in `run`, where it advances one cell and enters `gap`.

The transition rule therefore carries each candidate configuration at offset $r<L$ to the candidate at offset $r+1`, moving only the selected head one cell to the right. This step calculation is packaged by the catalogued seek-step fact (`catalog_seek_step`). At offset $L$ the scanned cell is blank and the phase is `gap`; the next transition changes the state to `done` without moving any work-tape head. The resulting configuration is fixed by subsequent steps. The general pass-contract lemma (`catalog_pass_contract`) now gives the endpoint after $L+1$ steps, excludes the done state at all earlier times, and propagates the bounds on the selected head and the fixed positions of all other heads. The endpoint has the required form because a zero input movement leaves the input position unchanged (`moveInputPos_zero`), as also expressed by the input-move step formula (`step_of_inputMoveAction`).

**Key facts.** `Turing.length_joinFields_add_one`, `Turing.fieldsTape_no_double_blank`, `Turing.catalog_seek_step`, `Turing.catalog_pass_contract`, `Turing.moveInputPos_zero`, `Turing.step_of_inputMoveAction`.
