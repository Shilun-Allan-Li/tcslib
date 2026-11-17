<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.cell_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Work-Tape Cell Update

**Claim.** After one machine step, the indicator that a work-tape head is at position $z$ is given by the cell-head rule applied to the current snapshot and the indicators for positions $z-1,z,z+1$. The content at position $z$ is given by the cell-content rule applied to the current snapshot, the indicator that the head was at $z$, and its current content.

**Proof.** Split according to whether the current configuration is halted. If its state is `none`, the machine step leaves the configuration unchanged. The cell-head rule returns the current middle-position indicator, while the cell-content rule returns the existing cell content, so both assertions follow.

If the state is some $q$, the machine applies the transition action at $q$. For the head position, the action moves the head by one of the three signed amounts: positive, zero, or negative. Accordingly, the head is at $z$ afterward exactly when it was at $z-1$, $z$, or $z+1$, respectively. These are precisely the three cases in the cell-head rule.

For the cell content, the action updates the tape only at the old head position. The update formula for work tapes (`Turing.Action.apply_workTapes`) expresses the new tape as the old tape updated there with the transition's written symbol, or with the old scanned symbol if no symbol is specified. If $z$ is the old head position, this is exactly the cell-content rule; if $z$ differs from the old head position, the update leaves the content at $z$ unchanged, again as prescribed by that rule.

**Key facts.** `Turing.Action.apply_workTapes`.
