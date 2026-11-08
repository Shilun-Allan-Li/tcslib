<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.eventually_gaussianMass_sq_log_div_two_lt_boundary_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Boundary Asymptotic Bound

**Claim.** For all sufficiently large integers $q$, $\frac{m_q^2}{2}\log(1/m_q)<b_q^2$, where $m_q$ is the prescribed Gaussian mass and $b_q$ is its Gaussian isoperimetric boundary value.

**Proof.** The Gaussian main term is positive, and the Gaussian boundary is asymptotic to that main term. Consequently, their ratio tends to $1$ and is eventually greater than $1/2$. Multiplying by the positive main term shows that half the main term is eventually strictly below the boundary. Both quantities are nonnegative, so squaring preserves this strict inequality. The identity for the square of the Gaussian main term identifies its square after division by $4$ with $m_q^2\log(1/m_q)/2$, giving the claimed bound.

**Key facts.** `FABL.eventually_half_fknOptimalityGaussianMain_lt_boundary`, `FABL.fknOptimalityGaussianBoundary_pos`, `FABL.fknOptimalityGaussianMain_pos`, `FABL.fknOptimalityGaussianMain_sq`.
