<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableau.lean :: Complexity.tabFamily_hasFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in bound for the tableau family

**Claim.** Every gate in every circuit of the tableau circuit family has at most two inputs; its input list has no repetitions, and each NOT gate has exactly one input.

**Proof.** Fix an input length $n$. The circuit at that length is the tableau circuit with the specified time bound. The theorem that each such circuit is fan-in two (Complexity.cfgTab_isFaninTwo) gives precisely the asserted properties: every gate's argument list has length at most two, has no repeated entries, and has length one whenever its gate is NOT. Since the argument applies to every $n$, it holds throughout the family.

**Key facts.** `Complexity.cfgTab_isFaninTwo`.
