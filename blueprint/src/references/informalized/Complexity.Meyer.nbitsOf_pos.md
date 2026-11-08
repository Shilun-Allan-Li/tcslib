<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachine.lean :: Complexity.Meyer.nbitsOf_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Number of Selector Bits

**Claim.** For every finite type $S$ with decidable equality and every natural number $k$, the number of selector states for $S$ and $k$ is positive.

**Proof.** The selector-state type contains the state constructor with no selected state, empty output register, and no selected tape, together with the two Boolean values set to false. Hence the type is nonempty. The cardinality of a finite type is positive exactly when the type is nonempty, so the number of selector states is positive.
