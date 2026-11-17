<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.normalizedCorrelatedPairSum_crossMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cross Moment of the Normalized Pair Sum

**Claim.** For the correlated pair of sign vectors, the expected product of the two coordinates of their normalized sum is $\rho$.

**Proof.** The two coordinates of the normalized pair sum are the linear forms in the two sign vectors whose coefficient at each index is $(\sqrt n)^{-1}$. The coordinate identities and the normalized-margin identity express the desired product as the product of these linear forms. The expected product of linear forms with coefficients $a_i$ is $\rho\sum_i a_i^2$ (\texttt{FABL.pmfExpectation_correlatedPairPMF_linearForm_mul}). For these coefficients, $\sum_i a_i^2=1$ when $n>0$ (\texttt{FABL.sum_normalizedCoefficient_sq}). Substitution yields $\rho$.

**Key facts.** `FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum`, `FABL.correlationSecondCoordinate_normalizedCorrelatedPairSum`, `FABL.normalizedMargin_eq_linearForm`, `FABL.pmfExpectation_correlatedPairPMF_linearForm_mul`, `FABL.sum_normalizedCoefficient_sq`.
