<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldHalt_safe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety under the halting action

**Claim.** Applying the stationary halting action to a safe configuration yields another safe configuration.

**Proof.** The halting action has no successor state, leaves every work-tape position unchanged, and makes no tape writes. Its input-head movement is zero. Consequently, the condition excluding the fresh initial state and the nonnegativity of each head position are preserved. Since the tapes are unchanged, the condition that each nonnegative cell’s origin flag agrees with whether its position is zero is preserved as well.
