<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.totalStableInfluence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Total Stable Influence

**Claim.** For $0\leq\rho\leq1$, the total stable influence of any real-valued function on the Boolean cube is nonnegative.

**Proof.** The total stable influence is the sum, over all coordinates, of the stable influence at that coordinate. Each summand is nonnegative by the coordinatewise nonnegativity theorem (`stableInfluence_nonneg`), so the finite sum is nonnegative.

**Key facts.** `FABL.stableInfluence_nonneg`.
