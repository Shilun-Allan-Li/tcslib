<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityGaussianMass_lt_delta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Mass Below Twice Small-Set Mass

**Claim.** For every $q\in\mathbb{N}$, the Gaussian mass $1/(q+2)$ is strictly less than twice the uniform measure of the associated small set.

**Proof.** The small-set mass differs from the Gaussian mass by less than half the Gaussian mass (`fknOptimalitySmallSetMass_approx`). In particular, the lower side of this absolute-value bound gives $\mu(A)>\alpha-\alpha/2=\alpha/2$, where $\alpha=1/(q+2)$. Multiplying by $2$ gives $\alpha<2\mu(A)$.

**Key facts.** `FABL.fknOptimalitySmallSetMass_approx`.
