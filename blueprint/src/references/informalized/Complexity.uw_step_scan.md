<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_step_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordinary transition outside the query state

**Claim.** For a configuration in state $0$, either choice bit produces exactly the configuration obtained by applying the designated machine’s transition action for that choice, state, and currently scanned symbols.

**Proof.** Unfold the definition of one step. Since the configuration’s state is $0$, the machine is in the nonhalting branch. State $0$ is distinct from the designated query state, so the query-handling branch is not taken. The step therefore applies the transition action for choice $b$, state $0$, and the symbols currently scanned on the input and work tapes, as claimed.
