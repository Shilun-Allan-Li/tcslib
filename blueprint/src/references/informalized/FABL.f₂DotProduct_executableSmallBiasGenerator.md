<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.f₂DotProduct_executableSmallBiasGenerator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing with the Executable Generator

**Claim.** The dot product of γ with the generated vector equals the dot product of s with the sum of the corresponding powers of r weighted by γ.

**Proof.** Expand both dot products as finite sums. Distribute each coordinate γₓ across the inner sum over field coordinates, and use associativity and commutativity of multiplication to write each term as (γₓ times the corresponding coordinate of the power) times the coordinate of s. Swap the two finite sums, then factor each coordinate of s out of the inner sum over x. The resulting expression is exactly the dot product of the weighted power sum with s.
