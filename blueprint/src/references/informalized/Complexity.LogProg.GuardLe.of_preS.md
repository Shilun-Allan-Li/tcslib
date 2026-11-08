<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.GuardLe.of_preS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bound Guard

**Claim.** If the program precondition holds at a configuration and every register value is at most $B$, then the configuration satisfies the guard requiring both properties.

**Proof.** By definition, the guard is the conjunction of the program precondition and the bound on every register. The two hypotheses are exactly those conjuncts, so pairing them proves the claim.
