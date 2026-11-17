<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.eventually_gaussianMass_sq_log_div_four_lt_smallSetWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Set Fourier Weight Bound

**Claim.** For all sufficiently large integers $q$, the level-one Fourier weight of the small-set indicator exceeds $\frac{m_q^2}{4}\log(1/m_q)$, where $m_q=1/(q+2)$ is the prescribed Gaussian mass.

**Proof.** For all sufficiently large $q$, the square of the Gaussian boundary value exceeds $m_q^2\log(1/m_q)/2$. For every $q$, the small-set indicator's level-one Fourier weight is strictly greater than half the square of that boundary value. Combining these inequalities gives a strict lower bound by $m_q^2\log(1/m_q)/4$.

**Key facts.** `FABL.eventually_gaussianMass_sq_log_div_two_lt_boundary_sq`, `FABL.fknOptimalitySmallSetWeight_gt_half_boundary_sq`.
