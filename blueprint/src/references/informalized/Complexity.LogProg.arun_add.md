<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.arun_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Abstract Run Lengths

**Claim.** For any register program, oracle, input, initial configuration, and natural numbers $s,t$, running for $s+t$ steps is the same as running first for $s$ steps and then for $t$ additional steps.

**Proof.** The abstract run is the iterate of the one-step transition function. The iterate-addition law says that iterating a function for a sum of two times is the same as composing the two iterates. Since addition is commutative, apply this law with the order of the two summands exchanged; the resulting composition first runs for $s$ steps and then for $t$ more, as claimed.
