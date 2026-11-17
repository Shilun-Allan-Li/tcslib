<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLargestFourierCoefficient.lean :: FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton coefficient of odd majority

**Claim.** For majority on $2m+1$ coordinates, the Fourier coefficient at any singleton set equals the odd-majority influence, $\binom{2m}{m}/2^{2m}$.

**Proof.** For a monotone Boolean function, the influence of coordinate $i$ equals the singleton Fourier coefficient (`FABL.influence_eq_fourierCoeff_singleton_of_monotone`). Majority is monotone (`FABL.majority_monotone`), so this applies. The Boolean influence agrees with the real-valued influence of the sign-valued function (`FABL.booleanInfluence_eq_influence_toReal`), and the influence of odd majority is the central-binomial ratio defining the odd-majority influence (`FABL.booleanInfluence_majority_odd_eq_oddMajorityInfluence`). Combining these identities proves the formula.

**Key facts.** `FABL.influence_eq_fourierCoeff_singleton_of_monotone`, `FABL.majority_monotone`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_majority_odd_eq_oddMajorityInfluence`.
