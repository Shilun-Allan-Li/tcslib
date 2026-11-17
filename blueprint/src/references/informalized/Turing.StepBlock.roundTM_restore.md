<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundTM_restore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoring the Tapes

**Claim.** Given a table split as the concatenation of `before` and `tail`, the round machine starting at the table-tail configuration based on the post-action configuration returns to that configuration with both auxiliary heads at $0$ and the exit label determined by `live`. It takes $|tail|+|table|+|word|+15$ steps and satisfies the round-span property.

**Proof.** The proof runs five tape phases in order. It first scans the tail of the table to its end, then returns across the full table to its beginning. The hypothesis $table=before\mathbin{++}tail$ identifies the scanned suffix with `tail`; the list-buffer suffix fact `bufferTape_suffix` supplies the corresponding tape contents. Next, the summary head crosses the blank gap at the origin, then returns across `word` to the origin. Finally, it moves two places left to position $0$ and exits through the anchor specified by `live`. The skip and return run results give the endpoint head positions and show that each scan reaches its done state only at its endpoint. The clearing-free phases preserve the round window because they do not move the input head or the original tape heads (`inputPos_runFrom_of_inputTape_eq_zero` and `roundWindow_frame`); `roundData_window` supplies the window for the underlying post-action configurations. Each phase, including its host-machine redirect, contributes a round-span segment by `roundTM_phase`, and `RoundSpan.add` joins the five segments. Their durations are respectively $|tail|+2$, $|table|+4$, $2$, $|word|+4$, and $3$, which sum to $|tail|+|table|+|word|+15$.

**Key facts.** `Turing.MultiTapeTM.inputPos_runFrom_of_inputTape_eq_zero`, `Turing.StepBlock.RoundSpan.add`, `Turing.StepBlock.bufferTape_suffix`, `Turing.StepBlock.mirror_ne_summary`, `Turing.StepBlock.mirror_ne_table`, `Turing.StepBlock.roundData_stateCell`, `Turing.StepBlock.roundData_window`, `Turing.StepBlock.roundTM_phase`, `Turing.StepBlock.roundWindow_frame`, `Turing.StepBlock.twoMoveTM_run`, `Turing.skipBackTM_run_ofCfg`, `Turing.skipTM_run_ofCfg`.
