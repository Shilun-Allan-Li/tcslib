<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_contraction_of_unit_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneous Extension of the Unit Bound

**Claim.** A bound on the unit weighted moment sphere extends to every vector as $F(f)\leq G(f)^{2/p}$.

**Proof.** Every summand of $G(f)$ is nonnegative, so $G(f)\geq0$. If $G(f)=0$, positivity of each weight forces every $|f_i|^p$ to vanish, and hence every coordinate of $f$ is zero; the desired inequality then follows with both sides zero. If $G(f)>0$, use the homogeneous normalization to scale $f$ to a vector $cf$ with $G(cf)=1$ and $F(cf)=F(f)/G(f)^{2/p}$. The assumed unit-sphere bound gives $F(f)/G(f)^{2/p}\leq1$. Multiplying by the positive quantity $G(f)^{2/p}$ proves the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_normalization`.
