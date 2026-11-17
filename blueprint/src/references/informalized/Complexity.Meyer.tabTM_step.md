<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachine.lean :: Complexity.Meyer.tabTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tabulation Machine Step

**Claim.** From the specified configuration, one step of the tabulation machine is obtained by applying its transition action to the scanned input and work-tape symbols.

**Proof.** First identify the scanned work-tape-symbol function of the given configuration. At each original tape index it returns that tape's contents at its head position; at each of the three auxiliary indices it returns the corresponding auxiliary tape's contents at its head position. This is exactly the function formed by combining those two groups of scanned symbols. Unfolding the machine's step therefore selects its transition action using the given state and these scanned symbols. Since the state is the specified present state, the step is that action applied to the configuration, as claimed.
