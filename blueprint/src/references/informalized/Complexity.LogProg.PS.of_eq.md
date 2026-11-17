<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PS.of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Equality and Semantics

**Claim.** If two register records are equal, any terminating and bounded semantics property holding from one record also holds from the other.

**Proof.** Substitute the equality of the register records into the given semantic hypothesis. The starting configurations then coincide, so the hypothesis is exactly the desired conclusion.
