<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UnateFunctions.lean :: FABL.totalInfluence_toReal_le_majority_of_unate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unate influence bound

**Claim.** The total influence of a unate Boolean function is at most the total influence of majority on the same number of coordinates.

**Proof.** For each coordinate $i$, unateness means that the function is either nondecreasing or nonincreasing in that coordinate. The characterization of unateness by its first-level Fourier coefficient (\texttt{abs\_fourierCoeff\_singleton\_eq\_influence\_iff\_isUnateInCoordinate}) therefore identifies the coordinate influence with the absolute value of that coefficient. Summing these coordinatewise equalities expresses total influence as the sum of the absolute first-level coefficients. The bound on that sum by majority's total influence (\texttt{sum\_abs\_fourierCoeff\_singleton\_le\_totalInfluence\_majority}) completes the proof.

**Key facts.** `FABL.abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate`, `FABL.sum_abs_fourierCoeff_singleton_le_totalInfluence_majority`.
