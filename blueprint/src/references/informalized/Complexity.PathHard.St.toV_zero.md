<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero State Register Vector

**Claim.** The register vector of the state whose fifteen registers are all zero assigns zero to every position.

**Proof.** To prove equality of the two functions, compare their values at an arbitrary position. Every position is one of the fifteen register positions; the state `zero` has value zero in each, so its register vector has value zero there. Thus it agrees everywhere with the function constantly equal to zero.
