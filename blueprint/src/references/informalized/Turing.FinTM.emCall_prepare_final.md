<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_prepare_final -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Prepared Configuration

**Claim.** If the run of $M$ on $\mathrm{arg}$ has output $\mathrm{cap}$ at time $T$, then the embedded evaluator configuration after the right-boundary scan is the call-layout frame with zero cleared banks and the evaluator at its return state.

**Proof.** Compare the configurations field by field. Their states, input-head positions, and output lists agree by unfolding the evaluator, capture, scan, and frame definitions. For each work-tape index, the embedding is the identity, so the selected-tape property of $\mathrm{embedEmitCfg}$ says that the embedded tape contents are exactly those of the evaluator; the selected-position property gives the same equality for head positions (`Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`). Unfolding the layouts then identifies the argument and capture buffers, the run's data tapes and heads, and the visited-span and origin-marker tapes with the corresponding frame components. The hypothesis that the run outputs $\mathrm{cap}$ supplies the equality needed to identify the capture buffer with the frame's cap tape. These component equalities establish the claimed configuration equality.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`.
