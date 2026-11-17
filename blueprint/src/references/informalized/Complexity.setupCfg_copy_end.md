<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_copy_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Guide Copying Step

**Claim.** In the copy phase for $|x|$ copied symbols, with input head at $|x|+1$ and guide head at $|x|$, one step enters copy-return phase and extends the partial guide to $|x|+1$ copied cells, preserving the remaining configuration data.

**Proof.** At input position $|x|+1$, the input head reads no symbol, as established for setup configurations by `setupCfg_input`. The copy-phase transition therefore takes its end-of-input branch: it writes the next guide symbol at the current guide coordinate, choosing the origin symbol when $|x|=0$ and the interior symbol otherwise, without moving either head. The identity `copyGuide_next` says precisely that updating the partial guide at coordinate $|x|$ produces the guide for $|x|+1$ copied cells. `setupCfg_apply` translates this action into the resulting setup configuration, and `moveInputPos_zero` confirms that the input-head position is unchanged.

**Key facts.** `Complexity.setupCfg_input`, `Complexity.copyGuide_next`, `Complexity.setupCfg_apply`, `Turing.moveInputPos_zero`.
