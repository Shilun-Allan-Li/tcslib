<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.fourierWeightAtLevel_one_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Majority Level-One Weight

**Claim.** For every natural number $m$, majority on $2m+1$ coordinates has level-one Fourier weight equal to $(2m+1)$ times the square of its odd-majority influence.

**Proof.** Express the level-one weight as the sum of squared singleton Fourier coefficients (`fourierWeightAtLevel_one_eq_sum_singleton`). Since majority is monotone, each singleton coefficient equals the corresponding influence (`influence_eq_fourierCoeff_singleton_of_monotone`, using `majority_monotone`). The real-valued influence agrees with the Boolean influence (`booleanInfluence_eq_influence_toReal`), and by symmetry every coordinate's Boolean influence for odd majority is the same quantity, `oddMajorityInfluence m` (`booleanInfluence_majority_odd_eq_oddMajorityInfluence`). There are $2m+1$ coordinates, so summing their identical squared influences gives the formula.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.majority_monotone`, `FABL.influence_eq_fourierCoeff_singleton_of_monotone`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_majority_odd_eq_oddMajorityInfluence`.
