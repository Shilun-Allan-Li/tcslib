<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.totalInfluence_eq_majority_of_isMajorityFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total influence of majority functions

**Claim.** If a Boolean function agrees with the sign of the sum of its input coordinates whenever that sum is nonzero, then it has the same total influence as the majority function.

**Proof.** The given agreement condition implies that the function is monotone (FABL.IsMajorityFunction.monotone); majority is monotone as well (FABL.majority_monotone). For any monotone Boolean function, total influence equals the sum of its singleton Fourier coefficients (FABL.totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone). Apply this identity to both functions. The characterization of equality of these singleton-coefficient sums says it is equivalent to agreement with majority on every input whose coordinate sum is nonzero (FABL.sum_fourierCoeff_singleton_eq_majority_iff). The hypothesis supplies precisely that agreement, so the sums, and hence the total influences, are equal.

**Key facts.** `FABL.IsMajorityFunction.monotone`, `FABL.majority_monotone`, `FABL.totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone`, `FABL.sum_fourierCoeff_singleton_eq_majority_iff`.
