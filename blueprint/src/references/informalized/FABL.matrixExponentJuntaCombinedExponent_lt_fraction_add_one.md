<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaCombinedExponent_lt_fraction_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combined Exponent Bound

**Claim.** For positive rational $\omega$ and natural $k$, with $c=\lceil\omega k/(\omega+1)\rceil$, one has $\max\{\omega(k-c),c\}<\frac{\omega}{\omega+1}k+1$.

**Proof.** The solver exponent is at most the cutoff, by `matrixExponentJuntaSolverExponent_le_cutoff`; hence the maximum of the two is the cutoff. The balanced exponent equals $\frac{\omega}{\omega+1}k$ by `matrixExponentJuntaBalancedExponent_eq_fraction`. Finally, `matrixExponentJuntaCutoff_lt_balancedExponent_add_one` says that the cutoff is strictly less than the balanced exponent plus one. Combining these gives the desired strict bound.

**Key facts.** `FABL.matrixExponentJuntaSolverExponent_le_cutoff`, `FABL.matrixExponentJuntaBalancedExponent_eq_fraction`, `FABL.matrixExponentJuntaCutoff_lt_balancedExponent_add_one`.
