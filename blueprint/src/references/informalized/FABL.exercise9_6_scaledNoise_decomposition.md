<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.exercise9_6_scaledNoise_decomposition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaled noise decomposition

**Claim.** For every real $\delta$, cube function $f$, and point $x$, the noise operator at parameter $(1-\delta)$ times the two-four noise root is the finite sum of its actions on the degree parts, with degree-$k$ term weighted by $(1-\delta)^k$.

**Proof.** Expand the noise operator at parameter $(1-\delta)\,\rho$ into its degree parts, where $\rho$ is the two-four noise root (`noiseOperator_eq_sum_degreePart`). For each degree $k$, the noise operator sends the homogeneous degree-$k$ part to $\rho^k$ times that part (`noiseOperator_degreePart`). Thus the corresponding summand is $((1-\delta)\rho)^k f^{=k}(x)= (1-\delta)^k\rho^k f^{=k}(x)$, which is precisely $(1-\delta)^k$ times the degree-$k$ term in the expansion of the noise operator at $\rho$. Summing these equalities over $k=0,\ldots,n$ proves the decomposition.

**Key facts.** `FABL.noiseOperator_eq_sum_degreePart`, `FABL.noiseOperator_degreePart`.

**Caveat.** The supplied proof establishes only the stated finite decomposition; it does not prove the broader hypercontractivity claims described in the informal statement.
