<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.fourierEstimatorFailureBits_eq_clog_two_mul_denominator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure bits for reciprocal parameters

**Claim.** If the positive rational parameter is $1/d$ for a positive natural number $d$, then its failure-bit count is $\operatorname{clog}_2(2d)$.

**Proof.** Substitute $\delta=1/d$ into the defining expression. Since $d>0$, the reciprocal is nonzero and the quotient simplifies in the rationals to $2d$. The ceiling of the natural number $2d$ is itself, so the failure-bit count is $\operatorname{clog}_2(2d)$.
