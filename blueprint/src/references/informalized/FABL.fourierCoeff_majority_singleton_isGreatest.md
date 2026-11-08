<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLargestFourierCoefficient.lean :: FABL.fourierCoeff_majority_singleton_isGreatest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Largest Majority Fourier Coefficient

**Claim.** For odd dimension $2m+1$, every majority Fourier coefficient has absolute value at most the coefficient at any singleton, and that singleton coefficient is the greatest value in the range of absolute Fourier coefficients.

**Proof.** To show that the singleton value belongs to the range, take the coordinate set $\{i\}$. The singleton coefficient equals the odd majority influence (\(\texttt{FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence}\)), which is positive (\(\texttt{FABL.oddMajorityInfluence_pos}\)); hence its absolute value is the coefficient itself. For any coordinate set $S$, the bound on the absolute value of a majority coefficient by the singleton coefficient (\(\texttt{FABL.abs_fourierCoeff_majority_le_singleton}\)) shows that every value in the range is at most this attained value. These two facts give the greatest element.

**Key facts.** `FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence`, `FABL.oddMajorityInfluence_pos`, `FABL.abs_fourierCoeff_majority_le_singleton`.
