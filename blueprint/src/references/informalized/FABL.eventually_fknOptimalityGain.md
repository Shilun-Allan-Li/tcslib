<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.eventually_fknOptimalityGain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eventual Fourier Weight Gain

**Claim.** For all sufficiently large integers $q$, the level-one Fourier weight of the small-set indicator is at least $\frac{1}{36}\Delta_q^2\log(1/\Delta_q)$, where $\Delta_q$ is twice its uniform mass.

**Proof.** For all sufficiently large $q$, two eventual bounds hold simultaneously: $\Delta_q<1$, and the level-one Fourier weight is strictly greater than $m_q^2\log(1/m_q)/4$, where $m_q$ is the prescribed Gaussian mass. The comparison theorem for $\Delta_q$ under the condition $\Delta_q<1$ gives $\Delta_q^2\log(1/\Delta_q)\le 9m_q^2\log(1/m_q)$. Multiplying by $1/36$ bounds the desired expression by $m_q^2\log(1/m_q)/4$, which is strictly below the Fourier weight. Thus the claimed weak inequality holds eventually.

**Key facts.** `FABL.eventually_fknOptimalityDelta_lt_one`, `FABL.eventually_gaussianMass_sq_log_div_four_lt_smallSetWeight`, `FABL.fknOptimalityDelta_sq_log_le`.
