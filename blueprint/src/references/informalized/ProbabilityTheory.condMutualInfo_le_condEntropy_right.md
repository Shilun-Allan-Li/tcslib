<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_le_condEntropy_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound by the second conditional entropy

**Claim.** The conditional mutual information satisfies $I[X:Y\mid Z;\mu]\le H[Y\mid Z;\mu]$.

**Proof.** By symmetry of conditional mutual information (`condMutualInfo_comm`), exchange $X$ and $Y$. Apply the bound by the first conditional entropy (`condMutualInfo_le_condEntropy_left`) to the reordered variables; its right-hand side is $H[Y\mid Z;\mu]$, as required.

**Key facts.** `ProbabilityTheory.condMutualInfo_le_condEntropy_left`.
