<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean :: jl_concentration_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-vector Johnson–Lindenstrauss concentration

**Claim.** Under the stated Gaussian marginal and independence assumptions, the probability that the random matrix distorts the squared norm of a fixed vector by more than the relative tolerance $\varepsilon$ is at most $2e^{-k\varepsilon^2/8}$.

**Proof.** Apply the established single-vector concentration theorem via the chi-squared bound (`jl_concentration_single_via_chi_squared`) with the given matrix, vector, and tolerance. Its hypotheses are precisely the stated positive row count, measurability, Gaussian entry laws, independence within rows and across rows, and $0<\varepsilon<1$. It yields the asserted probability bound.

**Key facts.** `jl_concentration_single_via_chi_squared`.
